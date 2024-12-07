from huggingface_hub import list_repo_files
from huggingface_hub.utils import RepositoryNotFoundError
import re
import requests
import os
from dotenv import load_dotenv
import sys
import time
from tqdm import tqdm

def get_huggingface_ranges():
    # 你的 Hugging Face 仓库 ID
    repo_id = "colorlessboy/mathlib4-thms"
    
    try:
        # 尝试获取文件名列表
        file_names = list_repo_files(repo_id=repo_id, repo_type="dataset")
    except RepositoryNotFoundError:
        print("Uploaded ranges:", [])
        return []
    except Exception as e:
        # 捕获其他异常
        print(f"An error occurred: {e}")
        print("Uploaded ranges:", [])
        return []
    
    # 用于存放解析后的结果
    parsed_numbers = []
    # 正则表达式匹配模式
    pattern = r"theorems-(\d+)-(\d+)\.zip"
    
    # 遍历文件名并解析
    for file_name in file_names:
        match = re.match(pattern, file_name)
        if match:
            start_num, end_num = match.groups()
            parsed_numbers.append((int(start_num), int(end_num)))
    
    parsed_numbers.sort()
    print("Uploaded ranges:", parsed_numbers)
    return parsed_numbers

def get_github_workflow_states():
    # GitHub 仓库信息
    owner = "ColorlessBoy"
    repo = "mathlib-inspector"
    url = f"https://api.github.com/repos/{owner}/{repo}/actions/runs?per_page=500&page=1"

    # GitHub Personal Access Token (可选，但推荐，避免频率限制)
    # 替换为你的 GitHub 令牌
    load_dotenv()  # 自动加载 .env 文件中的变量
    token = os.getenv("GITHUB_TOKEN")
    headers = {
        "Authorization": f"Bearer {token}",
        "Accept": "application/vnd.github.v3+json"
    }
    # 提取 Tag 的最后两位数字
    def extract_last_two_numbers(tag):
        if not tag or not tag.startswith("v"):
            return None, None
        parts = tag.split(".")
        if len(parts) >= 2:
            return int(parts[-2]), int(parts[-1])
        return None, None
    # 获取 Tag 信息的辅助函数
    def get_tag_for_commit(commit_sha):
        tag_url = f"https://api.github.com/repos/{owner}/{repo}/git/refs/tags"
        tag_response = requests.get(tag_url, headers=headers)
        if tag_response.status_code != 200:
            return None
        tags = tag_response.json()
        # 查找匹配的 Tag
        for tag in tags:
            if tag["object"]["sha"] == commit_sha:
                n1, n2 = extract_last_two_numbers(tag["ref"].replace("refs/tags/", ""))
                if n1 is None:
                    return None
                return n1, n2
        return None

    def get_in_progress_workflows():
        # 获取 Workflow 运行数据
        response = requests.get(url, headers=headers)
        if response.status_code != 200:
            print(f"Error: Unable to fetch workflows (status code: {response.status_code})")
            return []
        
        data = response.json()
        # 筛选状态为 in_progress 的 Workflow，并获取 Tag 信息
        in_progress_tags = []
        for run in data.get("workflow_runs", []):
            if run["status"] == "in_progress":
                tag = get_tag_for_commit(run["head_sha"])
                if tag is not None:
                    in_progress_tags.append(tag)
        return in_progress_tags

    # 打印正在运行的 Workflow 信息
    in_progress_tags = get_in_progress_workflows()
    in_progress_tags.sort()
    print("in processing ranges:", in_progress_tags)
    return in_progress_tags


def run_commit(start: int, end: int, version_prefix: str):
    # 文件路径
    script_dir = os.path.dirname(os.path.abspath(__file__))
    target_file = os.path.join(script_dir, ".github/workflows/lean_action_ci.yml")

    # 搜索和替换的模式
    search_pattern1 = r"^(\s*)(lake env lean --run MathlibInspector\.lean thms\.txt output) (\d+) (\d+) (\d+) (\d+)"
    replace_template1 = r"\1\2 {start} {end} \5 \6"

    search_pattern2 = r"^(\s*)(poetry run python extract_thms\.py -t thms\.txt -o output -d colorlessboy/mathlib4-thms -s) (\d+) (-e) (\d+)"
    replace_template2 = r"\1\2 {start} \4 {end}"

    # 检查文件是否存在
    if not os.path.isfile(target_file):
        print(f"Error: File '{target_file}' not found!")
        return

    # 读取文件内容
    with open(target_file, "r") as file:
        lines = file.readlines()

    # 替换内容
    updated_lines = []
    for line in lines:
        line = re.sub(search_pattern1, replace_template1.format(start=start, end=end), line)
        line = re.sub(search_pattern2, replace_template2.format(start=start, end=end), line)
        updated_lines.append(line)

    # 写入文件
    with open(target_file, "w") as file:
        file.writelines(updated_lines)

    print(f"Updated file with range {start} to {end}")

    # Git 提交和打标签
    tag = f"{version_prefix}.{start}.{end}"
    os.system(f"git add {target_file}")
    os.system(f'git commit -m "Update range to {start}-{end}"')
    os.system(f"git tag {tag}")
    os.system("git push origin main")
    os.system(f"git push origin {tag}")
    print(f"Pushed tag {tag} to GitHub.")

def find_missing_ranges(finished_ranges, in_progress_ranges, total_length, increment):
    """
    找出未完成的 ranges。
    - finished_ranges: 已完成的 ranges
    - in_progress_ranges: 正在进行的 ranges
    - total_length: 总数据长度
    - increment: 每次处理的范围大小
    """
    total_ranges = finished_ranges + in_progress_ranges
    total_ranges.sort()
    next_ranges = []
    if len(total_ranges) > 0:
        for idx in range(1, len(total_ranges)):
            if total_ranges[idx][0] > total_ranges[idx-1][1]:
                # 前一个的end小于后一个的start
                for new_start in range(total_ranges[idx-1][1], total_ranges[idx][0], increment):
                    next_ranges.append((new_start, min(new_start+increment, total_ranges[idx][0])))
    if len(total_ranges) == 0 or total_ranges[-1][1] < total_length:
        for new_start in range(total_ranges[-1][1] if len(total_ranges) != 0 else 0, total_length, increment):
            next_ranges.append((new_start, min(new_start + increment, total_length)))
    return next_ranges

if __name__ == "__main__":
    # 默认参数
    DEFAULT_INCREMENT = 4096
    DEFAULT_VERSION = "v0.0.1"

    increment = int(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_INCREMENT
    version_prefix = sys.argv[2] if len(sys.argv) > 2 else DEFAULT_VERSION

    with open('thms.txt', 'r') as f:
        total_length = len(f.readlines())
    
    while True:
        try:
            finished_ranges = get_huggingface_ranges()
            in_progress_ranges = get_github_workflow_states()
            next_ranges = find_missing_ranges(finished_ranges, in_progress_ranges, total_length, increment)
            print('next_ranges', next_ranges)
            if len(next_ranges) == 0:
                break
            elif len(in_progress_ranges) < 20:
                print(len(in_progress_ranges))
                for start, end in tqdm(next_ranges[:20 - len(in_progress_ranges)], desc="Committing"):
                    run_commit(start, end, version_prefix)
            sleep_time = 10 * 60
        except Exception as e:
            print(e)
            sleep_time = 1 * 60

        interval = 1  # 更新进度条的间隔，单位：秒
        for _ in tqdm(range(0, sleep_time, interval), desc="Sleeping", unit="s"):
            time.sleep(interval)
        