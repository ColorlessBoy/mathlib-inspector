
from huggingface_hub import list_repo_files, hf_hub_download
from huggingface_hub import HfApi
from huggingface_hub.utils import RepositoryNotFoundError
import os
import re 
from pathlib import Path
from tqdm import tqdm
import shutil

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
  for name in parsed_files:
    if os.path.exists(name):
        os.remove(name)
    filepath = hf_hub_download(repo_id=repo_id, repo_type="dataset", filename=name)
    shutil.move(filepath, name)
  return parsed_files

def load_previous_thms():
    thms = []
    all_thmtxts = [name[:-len(".txt")] for name in get_huggingface_thms()]
    for thmfile in all_thmtxts:
        with open(f"{thmfile}.txt", "r") as f:
            thms.extend([line.strip() for line in f.readlines()])
    all_thmtxts.sort(key=lambda x: int(x[len("thms_dep")]) if x.startswith("thms_dep") else 0)
    return thms, all_thmtxts

def get_ext_depth(previousThms: set[str], folder: str):
    deps = set()  # 证明依赖的常量
    thmsfiles = [Path(file).stem for file in os.listdir(folder)]
    for thm_file in tqdm(thmsfiles):
        names = extract_names_from_file(os.path.join(folder, f"{thm_file}.txt"))
        for name in names:
            if name not in previousThms:
                deps.add(name)
    depslist = list(deps)
    depslist.sort()
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
    previousThms, all_thmtxts = load_previous_thms()
    previous_thmsfile = all_thmtxts[-1]
    next_thmsfile = f"thms_dep{len(all_thmtxts)}"
    deps = get_ext_depth(previousThms, previous_thmsfile)
    if len(deps) > 0:
        print(f"开始写入{next_thmsfile}={len(deps)}...")
        with open(f"{next_thmsfile}.txt", "r") as f:
            f.writelines([line + "\n" for line in deps])
        print(f"成功写入{next_thmsfile}")
        upload_file(f"{next_thmsfile}.txt")
        
