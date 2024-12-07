
from collections import defaultdict
from tqdm import tqdm 

def hash_string(s: str) -> str:
  modulus = 4294967311 
  rst = 5381
  multiplier = 131
  for ch in s:
    rst = (rst * multiplier + ord(ch)) % modulus
  return str(rst)

def extractPrefix(s: str) -> str :
  if s.startswith("Lean."):
    return s[5:7]
  return s[:2]

def hashConst(s: str) -> str:
  head = extractPrefix(s)
  body = hash_string(s)
  code = head + body
  return code

const_map: dict[str, list[str]] = defaultdict(list)

with open("consts.txt", "r") as f:
  for line in tqdm(f.readlines()):
    line = line.strip()
    code = hashConst(line)
    const_map[code].append(line)

cnt = 0
max_length = 0
for key, arr in tqdm(const_map.items()):
  max_length = max(max_length, len(key))
  if len(arr) > 1:
    print(arr)
    cnt += 1
print(cnt)
print(max_length)

t = "Algebra.PreSubmersivePresentation.mk.sizeOf_spec"
print(hashConst(t), t)
