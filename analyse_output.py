
import os
from tqdm import tqdm

folder = 'output/thms-0-309448'
files = os.listdir(folder)

thms = 0
axioms = 0
for file in tqdm(files):
    with open(os.path.join(folder, file), 'r') as f:
        line = len(f.readlines())
        if line == 2:
            axioms += 1
        else:
            thms += 1
print('axioms =', axioms)
print('thms =', thms)
