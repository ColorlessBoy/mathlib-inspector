import argparse
import os
import zipfile

from huggingface_hub import HfApi
from huggingface_hub.utils import RepositoryNotFoundError
from tqdm import tqdm

import subprocess
import sys

def run_lean_script(thmsfile_path: str, output_dir: str, start_thm_idx: int|None = None, end_thm_idx: int|None = None):
  try:
    if start_thm_idx is None:
      start_thm_idx = 0
    if end_thm_idx is None:
      with open(thmsfile_path, 'r') as f:
        end_thm_idx = len(f.readlines())

    # 启动 Lean 子进程
    process = subprocess.Popen(
      ["lake", "env", "lean", "--run", "MathlibInspector.lean", thmsfile_path, output_dir, start_thm_idx, end_thm_idx],
        stdout=sys.stdout,  # 子进程的 stdout 重定向到父进程
        stderr=sys.stderr,  # 子进程的 stderr 重定向到父进程
        text=True
    )
    
    process.wait()
    # 检查退出码
    if process.returncode != 0:
      print(f"Process exited with return code {process.returncode}")
    else:
      print("Process completed successfully.")
  
  except FileNotFoundError as e:
    print("Error: Could not find 'lake' command. Ensure it is installed and in your PATH.", e)
  except Exception as e:
    print(f"An unexpected error occurred: {e}")

def hash_string(s: str) -> str:
  modulus = 4294967311 
  rst = 5381
  multiplier = 131
  for ch in s:
    rst = (rst * multiplier + ord(ch)) % modulus
  return str(rst)  # 转换为16进制字符串，去掉 '0x' 前缀

def extractPrefix(s: str) -> str :
  if s.startswith("Lean."):
    return s[5:7]
  return s[:2]

def zip_dataset(dataset_dir, output_zip):
  file_list = []  # 创建文件列表
  for root, dirs, files in os.walk(dataset_dir):
    for file in files:
      file_path = os.path.join(root, file)
      file_list.append(file_path)  # 收集文件路径

  with zipfile.ZipFile(output_zip, "w", zipfile.ZIP_DEFLATED) as zipf:
    for file_path in tqdm(file_list, desc="压缩中", unit="文件"):  # 添加进度条
      zipf.write(file_path, os.path.relpath(file_path, dataset_dir))

if __name__ == "__main__":
  parser = argparse.ArgumentParser(description="Upload dataset")
  parser.add_argument(
    "-t",
    "--thmsfile",
    dest="thmsfile",
    type=str,
    help="Theorems file path",
  )
  parser.add_argument(
    "-o",
    "--output",
    dest="output",
    type=str,
    help="Output folder",
  )
  parser.add_argument(
    "-d",
    "--repo-id",
    dest="repo_id",
    type=str,
    help="Hugging Face repo ID",
  )
  parser.add_argument(
    "-s",
    "--start",
    dest="start",
    type=int,
    help="Start theorem index",
    default=None,
  )
  parser.add_argument(
    "-e",
    "--end",
    dest="end",
    type=int,
    help="End theorem index",
    default=None,
  )
  parser.add_argument(
    "-g",
    "--generate",
    dest="generate",
    type=bool,
    help="Enable generator of lean4 script",
    default=False,
  )

  args = parser.parse_args()

  thmsfile_path = args.thmsfile
  output_dir = args.output
  start_of_index = args.start
  end_of_index = args.end

  if args.generate:
    run_lean_script(thmsfile_path, output_dir, start_of_index, end_of_index)
  
  with open("thms.txt", 'r') as f:
    thms_total_num = len(f.readlines())
  
  if end_of_index is None or end_of_index <= start_of_index:
    end_of_index = thms_total_num

  # zip output_dir
  output_zip = output_dir + '-' + str(start_of_index) + '-' + str(end_of_index) + ".zip"
  zip_dataset(output_dir, output_zip)

  # 上传数据集到 Hugging Face
  api = HfApi()
  repo_id = args.repo_id
  path_in_repo = output_zip

  try:
    api.dataset_info(repo_id)
    print(f"数据集 {repo_id} 已存在。")
  except RepositoryNotFoundError:
    print(f"数据集 {repo_id} 不存在，正在创建...")
    api.create_repo(repo_id, repo_type="dataset")

  # 通过 upload_with_progress 进行直接上传
  with open(output_zip, "rb") as f:  # 以二进制模式打开文件
    # 进行上传
    try:
      api.upload_file(
        path_or_fileobj=f,  # 传递文件对象
        path_in_repo=path_in_repo,
        repo_id=repo_id,
        repo_type="dataset",
      )
      print(output_zip, "上传成功")  # 上传成功提示
    except Exception as e:
      print(f"上传失败: {e}")

  """
  const_hash_list: list[str] = []

  with open("consts.txt", "r") as f:
    for line in tqdm(f.readlines()):
      line = line.strip()
      head = extractPrefix(line)
      body = hash_string(line)
      code = head + body
      const_hash_list.append(f"{code}\t{line}\n")
  
  with open("hashed_consts.txt", "w") as f:
    f.writelines(const_hash_list)

  words_path = "hashed_consts.txt"
  api.upload_file(
    path_or_fileobj=words_path,
    path_in_repo=words_path,
    repo_id=repo_id,
    repo_type="dataset",
  )
  print(words_path, "上传成功") 
  """