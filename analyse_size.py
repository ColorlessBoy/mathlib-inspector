import sys 

def count_theorems_below_threshold(data, threshold1, threshold2):
  count1 = 0
  count2 = 0
  for name, prop_length, proof_length in data:
    if prop_length <= threshold1:
      count1 += 1
      if proof_length <= threshold2:
        count2 += 1
  return count1, count2

with open('constAndSize.txt', 'r') as f:
  data = []
  for line in f.readlines():
    name, prop_length, proof_length = line.split(' ')
    data.append((name, int(prop_length), int(proof_length)))

# 设置阈值 n

n1 = 10000
n2 = 10000
if len(sys.argv) >= 2:
  n1 = int(sys.argv[1])
if len(sys.argv) >= 3:
  n2 = int(sys.argv[2])

# 执行分析
c1, c2 = count_theorems_below_threshold(data, n1, n2)
print(f"Total: {len(data)}")
print(f"Number of theorems with proposition length <= {n1}: {c1}")
print(f"Number of theorems with proof length <= {n2}: {c2}")
