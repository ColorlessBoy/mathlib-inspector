import re
import os
import sys

# 默认参数
DEFAULT_START = 0
DEFAULT_INCREMENT = 8000
DEFAULT_VERSION = "v0.0.28"

# 从命令行获取参数
start = int(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_START
increment = int(sys.argv[2]) if len(sys.argv) > 2 else DEFAULT_INCREMENT
version_prefix = sys.argv[3] if len(sys.argv) > 3 else DEFAULT_VERSION

# 文件路径
script_dir = os.path.dirname(os.path.abspath(__file__))
target_file = os.path.join(script_dir, ".github/workflows/lean_action_ci.yml")

# 搜索和替换的模式
search_pattern1 = r"^(\s*)(lake env lean --run MathlibInspector\.lean thms\.txt output) \d+ \d+"
replace_template1 = r"\1\2 {start} {end}"

search_pattern2 = r"^(\s*)(poetry run python extract_thms\.py -t thms\.txt -o output -d colorlessboy/mathlib4-thms -s) (\d+) (-e) (\d+)"
replace_template2 = r"\1\2 {start} \4 {end}"

# 检查文件是否存在
if not os.path.isfile(target_file):
    print(f"Error: File '{target_file}' not found!")
    sys.exit(1)

while True:
    end = start + increment

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

    # 更新范围
    start += increment

    # 是否继续
    cont = input("Continue to next range? (y/n): ")
    if cont.lower() != "y" and len(cont) > 0:
        print("Script terminated by user.")
        break