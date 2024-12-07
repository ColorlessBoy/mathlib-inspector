
with open("thms.txt", "r") as f:
  lines = [line.strip() for line in f.readlines()]
lines.sort()
with open("thms.txt", "w") as f:
  f.writelines([line + '\n' for line in lines])

with open("consts.txt", "r") as f:
  lines = [line.strip() for line in f.readlines()]
lines.sort()
with open("consts.txt", "w") as f:
  f.writelines([line + '\n' for line in lines])
