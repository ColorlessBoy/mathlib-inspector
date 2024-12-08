from huggingface_hub import list_repo_files, hf_hub_download
import re
from dotenv import load_dotenv
import zipfile
import os
from pathlib import Path
from tqdm import tqdm


load_dotenv()

def get_huggingface_ranges():
  print("开始加载zip文件列表...")
  # 你的 Hugging Face 仓库 ID
  repo_id = "colorlessboy/mathlib4-thms"
  # 获取文件名列表
  file_names = list_repo_files(repo_id=repo_id, repo_type="dataset")
  # 用于存放解析后的结果
  parsed_files = []
  # 正则表达式匹配模式
  pattern = r"thms-(\d+)-(\d+)\.zip"
  # 遍历文件名并解析
  for file_name in file_names:
    match = re.match(pattern, file_name)
    if match:
      start_num, end_num = match.groups()
      parsed_files.append((int(start_num), int(end_num), file_name))
  parsed_files.sort()
  print("成功加载zip文件列表")
  return [entry[-1] for entry in parsed_files]

zip_files = get_huggingface_ranges()
print('zip_files', zip_files)

def load_zip_file(filename: str): 
  extract_path = os.path.join("output", Path(filename).stem)
  # 检查 extract_path 是否非空
  if os.path.exists(extract_path) and any(os.scandir(extract_path)):
      print(f"{extract_path} 已存在且非空，跳过下载和解压。")
      return extract_path
  print(f"开始下载{filename}...")
  repo_id = "colorlessboy/mathlib4-thms"
  filepath = hf_hub_download(repo_id=repo_id, repo_type="dataset", filename=filename)
  with zipfile.ZipFile(filepath, 'r') as zip_ref:
    zip_ref.extractall(extract_path)
  print(f"成功下载{filename}")
  return extract_path

folder_path = load_zip_file(zip_files[0])  

def get_all_filenames(directory):
  # 确保目录存在
  if not os.path.exists(directory):
      print(f"目录 '{directory}' 不存在")
      return []
  # 列出目录下的所有文件（包括子文件夹中的文件）
  filenames = set()
  for _, _, files in os.walk(directory):
    for file in files:
      filenames.add(Path(file).stem)
  return filenames


folder_thms = get_all_filenames(folder_path)

print(folder_path, len(folder_thms))

def extract_names_from_file(filepath):
    pattern = r"\(C (\w+)\)"
    names = []
    with open(filepath, 'r', encoding='utf-8') as file:
        for line in file:
            names.extend(re.findall(pattern, line))
    return names


deps = set() # 证明依赖的常量 
for thm_file in tqdm(folder_thms):
  names = extract_names_from_file(os.path.join(folder_path, f"{thm_file}.txt"))
  for name in names:
    if name not in thm_file:
      deps.add(name)

depslist = list(deps)
depslist.sort()
print("开始写入thms_dep1...")
with open("thms_dep1.txt", "w") as f:
  f.writelines([line + '\n' for line in depslist])
print("成功写入thms_dep1")
