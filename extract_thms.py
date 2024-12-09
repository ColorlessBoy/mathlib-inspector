import argparse
import os
import zipfile

from huggingface_hub import HfApi
from huggingface_hub.utils import RepositoryNotFoundError
from tqdm import tqdm

import subprocess
import sys


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
            end_thm_idx = 0

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

def upload_file(file: str):
    # 上传数据集到 Hugging Face
    api = HfApi()
    repo_id = args.repo_id

    try:
        api.dataset_info(repo_id)
        print(f"数据集 {repo_id} 已存在。")
    except RepositoryNotFoundError:
        print(f"数据集 {repo_id} 不存在，正在创建...")
        api.create_repo(repo_id, repo_type="dataset")
    with open(file, "r") as f:
        api.upload_file(
            path_or_fileobj=f,  # 传递文件对象
            path_in_repo=file,
            repo_id=repo_id,
            repo_type="dataset",
        )
    print(file, "上传成功")  # 上传成功提示

def upload(thmsfile: str, start_of_index: int, end_of_index: int):
    with open(f"{thmsfile}.txt", "r") as f:
        thms_total_num = len(f.readlines())
    
    if start_of_index is None:
        start_of_index = 0

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
    return output_zip

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
        default=10000,
    )

    args = parser.parse_args()

    thmsfile = args.thmsfile
    start_of_index = args.start
    end_of_index = args.end
    max_prop_size = args.max_prop_size
    max_proof_size = args.max_proof_size

    print(f"Generate flag: {args.generate}")

    if args.generate:
        generate_new_words = 1 if thmsfile=="thms" else 0
        run_lean_script(
            thmsfile,
            start_of_index,
            end_of_index,
            max_prop_size,
            max_proof_size,
            generate_new_words=generate_new_words
        )
        if generate_new_words > 0:
            os.system("ls")
            upload_file(f"{thmsfile}.txt")
            upload_file("consts.txt")

    zip_file = upload(thmsfile, start_of_index, end_of_index)
