
import os
import re 
from pathlib import Path
from tqdm import tqdm

def extract_names_from_file(filepath):
    pattern = r"\(C (\w+)\)"
    names = []
    with open(filepath, "r", encoding="utf-8") as file:
        for line in file:
            names.extend(re.findall(pattern, line))
    return names

def load_previous_thms():
    thms = []
    all_thmtxtx = [Path(file).stem for file in os.listdir('.') if file.startswith('thms') and file.endswith('.txt')]
    for thmfile in all_thmtxtx:
        with open(f"{thmfile}.txt", "r") as f:
            thms.extend([line.strip() for line in f.readlines()])
    all_thmtxts.sort(key=lambda x: int(x[len("thms_dep")]) if x.startswith("thms_dep") else 0)
    return thms, all_thmtxtx

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
        os.system(f"git add {next_thmsfile}.txt")
        os.system(f'git commit -m "add {next_thmsfile}.txt"')
        os.system("git push -f origin workflow:workflow")
