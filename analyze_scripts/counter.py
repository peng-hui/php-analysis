#!/usr/bin/env python3

import os
resultdir = '/data/cpu_dos_data/results'
counter = 0
for folder in os.listdir(resultdir):
    for f in os.listdir(resultdir + '/' + folder):
        if 'constraint.txt' in f:
            counter += 1
print(counter)

