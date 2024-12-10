
from huggingface_hub import list_repo_files, hf_hub_download
from huggingface_hub import HfApi
from huggingface_hub.utils import RepositoryNotFoundError
import os
import re 
from pathlib import Path
from tqdm import tqdm
from concurrent.futures import ProcessPoolExecutor, as_completed
import sys
import zipfile

def extract_names_from_file(filepath):
    pattern = r"\(C (\w+)\)"
    names = []
    with open(filepath, "r", encoding="utf-8") as file:
        for line in file:
            names.extend(re.findall(pattern, line))
    return names

def get_huggingface_thms():
  repo_id = "colorlessboy/mathlib4-thms"
  # 获取文件名列表
  file_names = list_repo_files(repo_id=repo_id, repo_type="dataset")
  # 正则表达式匹配模式
  pattern = r"thms(\w*)\.txt"
  # 用于存放解析后的结果
  parsed_files = [name for name in file_names if re.match(pattern, name)]
  parsed_files.sort(key=lambda x: int(x[len("thms_dep"):]) if x.startswith("thms_dep") else 0)
  filepaths: list[str] = []
  for name in parsed_files:
    if os.path.exists(name):
        os.remove(name)
    filepath = hf_hub_download(repo_id=repo_id, repo_type="dataset", filename=name)
    print(f"download {name}")
    filepaths.append(filepath)
  return parsed_files, filepaths

def load_previous_thms(target_file: str = None):
    thms = []
    hf_thms, hf_filepaths = get_huggingface_thms()
    print("hf_thms", hf_thms)
    os.system("ls")
    all_thmtxts = [name[:-len(".txt")] for name in hf_thms]
    for idx, thmfile in enumerate(hf_filepaths):
        if target_file is not None and thmfile.startswith(target_file):
            all_thmtxts = all_thmtxts[:idx]
            break
        with open(thmfile, "r") as f:
            thms.extend([line.strip() for line in f.readlines()])
    all_thmtxts.sort(key=lambda x: int(x[len("thms_dep"):]) if x.startswith("thms_dep") else 0)
    return thms, all_thmtxts

def process_file(file_path, previousThms):
    """处理单个文件，提取不在 previousThms 中的依赖。"""
    names = extract_names_from_file(file_path)
    return {name for name in names if name not in previousThms}

def get_huggingface_zip(filename: str):
  print("开始查找zip文件")
  # 你的 Hugging Face 仓库 ID
  repo_id = "colorlessboy/mathlib4-thms"
  # 获取文件名列表
  file_names = list_repo_files(repo_id=repo_id, repo_type="dataset")
  print('file_names', file_names)
  # 用于存放解析后的结果
  # 正则表达式匹配模式
  pattern = filename + r"-\d+-\d+\.zip"
  print('pattern', pattern)
  # 遍历文件名并解析
  for file_name in file_names:
    match = re.match(pattern, file_name)
    if match:
      print("找到文件", file_name)
      return file_name

def load_zip_file(filename: str): 
  extract_path = os.path.join("output", Path(filename).stem)
  # 检查 extract_path 是否非空
  if os.path.exists(extract_path) and any(os.scandir(extract_path)):
    print(f"{extract_path} 已存在且非空，跳过下载和解压。")
    return extract_path
  hf_zips = get_huggingface_zip(filename)
  print(f"开始下载{hf_zips}...")
  repo_id = "colorlessboy/mathlib4-thms"
  filepath = hf_hub_download(repo_id=repo_id, repo_type="dataset", filename=hf_zips)
  with zipfile.ZipFile(filepath, 'r') as zip_ref:
    zip_ref.extractall(extract_path)
  print(f"成功下载{filename}")
  return extract_path


def get_ext_depth(previousThms: set[str], folder: str, max_workers=8, start=None, end=None):
    deps = set()
    folder = load_zip_file(folder)
    thmsfiles = [Path(folder) / file for file in os.listdir(folder) if file.endswith(".txt")]

    if end is not None:
      thmsfiles = thmsfiles[:end]
    if start is not None:
      thmsfiles = thmsfiles[start:]

    with ProcessPoolExecutor(max_workers=max_workers) as executor:
        futures = []
        for file in tqdm(thmsfiles):
            futures.append(executor.submit(process_file, file, previousThms))
            # 控制提交任务的数量，防止内存占用过高
            if len(futures) >= max_workers * 2:
                for future in as_completed(futures):
                    deps.update(future.result())
                futures.clear()

        # 处理剩余的任务
        for future in as_completed(futures):
            deps.update(future.result())

    depslist = sorted(deps)
    return depslist

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


if __name__ == "__main__":
    # 生成起始
    start = int(sys.argv[1]) if len(sys.argv) >= 2 else None
    # 生成结束 
    end = int(sys.argv[2]) if len(sys.argv) >= 3 else None
    # 生成的依赖的等级 
    level = int(sys.argv[3]) if len(sys.argv) >= 4 else None
    # 并行数量 
    max_workers = int(sys.argv[4]) if len(sys.argv) >= 5 else 32

    target = f"thms_dep{level}" if level is not None and level > 0 else None
    previousThms, all_thmtxts = load_previous_thms(target)
    previous_thmsfile = all_thmtxts[-1]
    next_thmsfile = f"thms_dep{len(all_thmtxts)}"
    deps = get_ext_depth(previousThms, previous_thmsfile, max_workers=max_workers, start=start, end=end)
    output_file = next_thmsfile
    if start is not None:
      output_file += "-" + str(start)
    if end is not None:
      output_file += "-" + str(end)
    output_file += ".txt"
    if len(deps) > 0:
      print(f"开始写入{output_file}={len(deps)}...")
      with open({output_file}, "w") as f:
        f.writelines([line + "\n" for line in deps])
      print(f"成功写入{output_file}")
      upload_file({output_file})
        
