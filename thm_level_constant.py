from huggingface_hub import list_repo_files, hf_hub_download
import re
from dotenv import load_dotenv
import zipfile
import os
from pathlib import Path
import shutil


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
  pattern = r"output-(\d+)-(\d+)\.zip"
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

def load_hashed_consts_map():
  print("开始加载hashed_consts_map...")
  repo_id = "colorlessboy/mathlib4-thms"
  hashed_consts_filename = "hashed_consts.txt"
  hashed_consts_filepath = os.path.join("output", hashed_consts_filename)
  if not os.path.exists(hashed_consts_filepath):
    tmp = hf_hub_download(repo_id=repo_id, repo_type="dataset", filename=hashed_consts_filename)
    shutil.copy(tmp, hashed_consts_filepath)
  hashed_consts_map = {}
  with open(hashed_consts_filepath, 'r') as f:
    for line in f.readlines():
      k, v = line.strip().split('\t')
      hashed_consts_map[k] = v
  print("成功加载hashed_consts_map")
  return hashed_consts_map

hashed_consts_map = load_hashed_consts_map()

def load_zip_file(filename: str): 
  print(f"开始下载{filename}...")
  extract_path = os.path.join("output", Path(filename).stem)
  os.makedirs(extract_path, exist_ok=True)
  repo_id = "colorlessboy/mathlib4-thms"
  filepath = hf_hub_download(repo_id=repo_id, repo_type="dataset", filename=filename)
  with zipfile.ZipFile(filepath, 'r') as zip_ref:
    zip_ref.extractall(extract_path)
  print(f"成功下载{filename}")
  return extract_path

folder_path = load_zip_file(zip_files[0])  

def load_thm_list():
  print("开始加载thms.txt...")
  with open("output/hashed_consts.txt", "r") as f:
    thms = {}
    for line in f.readlines():
      k, v = line.strip().split('\t')
      thms[k] = v
  print("成功加载thms.txt")
  return thms

thms = load_thm_list()
print(len(thms))
k = "Ad1041480902"
print(k, thms[k])
