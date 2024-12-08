import argparse
import os
import zipfile
import shutil

from huggingface_hub import HfApi
from huggingface_hub.utils import RepositoryNotFoundError
from tqdm import tqdm

import subprocess
import sys
import re


def run_lean_script(
    thmsfile: str,
    start_thm_idx: int | None = None,
    end_thm_idx: int | None = None,
    max_prop_size=2048,
    max_proof_size=10000,
    generate_new_words=0,
):
    try:
        if start_thm_idx is None:
            start_thm_idx = 0
        if end_thm_idx is None:
            with open(f"{thmsfile}.txt", "r") as f:
                end_thm_idx = len(f.readlines())

        # 启动 Lean 子进程
        process = subprocess.Popen(
            [
                "lake",
                "env",
                "lean",
                "--run",
                "MathlibInspector.lean",
                f"{thmsfile}.txt",
                thmsfile,
                str(start_thm_idx),
                str(end_thm_idx),
                str(generate_new_words),
                str(max_prop_size),
                str(max_proof_size)
            ],
            stdout=sys.stdout,  # 子进程的 stdout 重定向到父进程
            stderr=sys.stderr,  # 子进程的 stderr 重定向到父进程
            text=True,
        )

        process.wait()
        # 检查退出码
        if process.returncode != 0:
            print(f"Process exited with return code {process.returncode}")
        else:
            print("Process completed successfully.")

    except FileNotFoundError as e:
        print(
            "Error: Could not find 'lake' command. Ensure it is installed and in your PATH.",
            e,
        )
    except Exception as e:
        print(f"An unexpected error occurred: {e}")


def zip_dataset(dataset_dir, output_zip):
    file_list = []  # 创建文件列表
    for root, dirs, files in os.walk(dataset_dir):
        for file in files:
            file_path = os.path.join(root, file)
            file_list.append(file_path)  # 收集文件路径

    with zipfile.ZipFile(output_zip, "w", zipfile.ZIP_DEFLATED) as zipf:
        for file_path in tqdm(file_list, desc="压缩中", unit="文件"):  # 添加进度条
            zipf.write(file_path, os.path.relpath(file_path, dataset_dir))


def upload(thmsfile: str, end_of_index: int):
    with open(f"{thmsfile}.txt", "r") as f:
        thms_total_num = len(f.readlines())

    if end_of_index is None or end_of_index <= start_of_index:
        end_of_index = thms_total_num

    # zip output_dir
    output_zip = thmsfile + "-" + str(start_of_index) + "-" + str(end_of_index) + ".zip"
    zip_dataset(thmsfile, output_zip)

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


def extract_names_from_file(filepath):
    pattern = r"\(C (\w+)\)"
    names = []
    with open(filepath, "r", encoding="utf-8") as file:
        for line in file:
            names.extend(re.findall(pattern, line))
    return names


def load_thms(thmfile):
    thms = []
    with open(f"{thmfile}.txt", "r") as f:
        thms = [line.strip() for line in f.readlines()]
    return thms


def get_ext_depth(previousThms: set[str], thmsfile: str):
    deps = set()  # 证明依赖的常量
    for thm_file in tqdm(thmsfile):
        names = extract_names_from_file(os.path.join(thmsfile, f"{thm_file}.txt"))
        for name in names:
            if name not in previousThms:
                deps.add(name)
    depslist = list(deps)
    depslist.sort()
    return depslist


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
        help="Enable generator of lean4 script",
        default=False,
        action="store_true",
    )
    parser.add_argument(
        "--max-prop-size",
        dest="max_prop_size",
        type=int,
        help="Max Prop Size",
        default=2048,
    )
    parser.add_argument(
        "--max-proof-size",
        dest="max_proof_size",
        type=int,
        help="Max Proof Size",
        default=100000,
    )
    parser.add_argument("--depth", dest="depth", type=int, help="Depth", default=0)

    args = parser.parse_args()

    thmsfile = args.thmsfile
    start_of_index = args.start
    end_of_index = args.end
    max_prop_size = args.max_prop_size
    max_proof_size = args.max_proof_size

    print(f"Generate flag: {args.generate}")

    if args.generate:
        run_lean_script(
            thmsfile,
            start_of_index,
            end_of_index,
            max_prop_size,
            max_proof_size,
            generate_new_words=1,
        )
        os.system(f"git add {thmsfile}.txt")
        os.system("git add consts.txt")
        os.system(f'git commit -m "new {thmsfile}.txt"')
        os.system("git push origin main")

    upload(thmsfile, end_of_index)

    depth = args.depth
    if depth == 0 or args.generate:
        exit(0)

    previousThms = load_thms(thmsfile)
    for idx in range(depth):
        previous_thmsfile = f"{thmsfile}_dep{idx}" if idx > 0 else thmsfile
        next_thmsfile = f"{thmsfile}_dep{idx+1}"
        deps = get_ext_depth(previousThms, previous_thmsfile)
        if len(deps) == 0:
            break
        shutil.rmtree(previous_thmsfile)
        print(f"开始写入{next_thmsfile}={len(deps)}...")
        with open(f"{next_thmsfile}.txt", "r") as f:
            f.writelines([line + "\n" for line in deps])
        print(f"成功写入{next_thmsfile}")
        os.system(f"git add {next_thmsfile}.txt")
        os.system(f'git commit -m "add {next_thmsfile}.txt"')
        os.system("git push origin main")
        run_lean_script(next_thmsfile, 0, None, max_prop_size, max_proof_size)
        upload(next_thmsfile, None)
        previousThms.extend(load_thms(next_thmsfile))
