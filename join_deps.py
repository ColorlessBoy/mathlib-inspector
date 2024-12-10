
from huggingface_hub import HfApi, list_repo_files, hf_hub_download
from huggingface_hub.utils import RepositoryNotFoundError
import sys
from dotenv import load_dotenv

def get_huggingface_thms(head: str):
    repo_id = "colorlessboy/mathlib4-thms"
    # 获取文件名列表
    file_names = list_repo_files(repo_id=repo_id, repo_type="dataset")
    # 用于存放解析后的结果
    parsed_files = [name for name in file_names if name.startswith(head)]
    filepaths: list[str] = []
    for name in parsed_files:
        filepath = hf_hub_download(repo_id=repo_id, repo_type="dataset", filename=name)
        print(f"download {name}")
        filepaths.append(filepath)
    return file_names, filepaths

def get_join_thms(head: str):
    filenames, filepaths = get_huggingface_thms(head)
    thms = []
    for filepath in filepaths:
        with open(filepath, 'r') as f:
            thms.extend([line.strip() for line in f.readlines()])
    return filenames, list(set(thms))

def upload_file(file: str):
    # 上传数据集到 Hugging Face
    api = HfApi()
    repo_id = "colorlessboy/mathlib4-thms"

    try:
        api.dataset_info(repo_id)
        print(f"数据集 {repo_id} 已存在。")
    except RepositoryNotFoundError:
        print(f"数据集 {repo_id} 不存在，正在创建...")
        api.create_repo(repo_id, repo_type="dataset")
    api.upload_file(
        path_or_fileobj=file,  # 传递文件对象
        path_in_repo=file,
        repo_id=repo_id,
        repo_type="dataset",
    )
    print(file, "上传成功")  # 上传成功提示

def delete_file(file: str):
    """删除 Hugging Face 数据集中的指定文件。"""
    api = HfApi()
    repo_id = "colorlessboy/mathlib4-thms"

    try:
        api.dataset_info(repo_id)
        print(f"数据集 {repo_id} 已存在，准备删除文件 {file}...")
    except RepositoryNotFoundError:
        print(f"数据集 {repo_id} 不存在，无法删除文件 {file}。")
        return
    # 删除文件
    api.delete_file(
        path_in_repo=file,
        repo_id=repo_id,
        repo_type="dataset"
    )
    print(f"{file} 删除成功")

if __name__ == "__main__":
    load_dotenv()
    head = sys.argv[1] if len(sys.argv) > 1 else 'thms_dep1'
    filenames, deps = get_join_thms(head)
    if len(deps) > 0:
        deps.sort()
        print(f"开始写入{head}={len(deps)}...")
        with open(f"{head}.txt", "w") as f:
            f.writelines([line + "\n" for line in deps])
        print(f"成功写入{head}")
        for filename in filenames:
            delete_file(filename)
        upload_file(f"{head}.txt")
