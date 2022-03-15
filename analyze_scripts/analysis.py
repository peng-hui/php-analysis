#!/usr/bin/env python3
import os
resultdir = '/data/cpu_dos_data/results/'
files = os.listdir(resultdir)
counter1 = 0
counter2 = 0
counter3 = 0
def countfolder(folder):
    global counter1
    global counter2
    global counter3
    files = os.listdir(folder)
    for f in files:
        if 'loop' in f and f[-7:] == '.result':
            fp = open(folder + f)
            contents = fp.read()
            if '[1, 1]' in contents:
                counter1 += 1 
            counter2 += 1
            if '[1,' in contents:
                counter3 += 1
        elif os.path.isdir(folder + f):
            countfolder(folder + f + '/')
countfolder(resultdir)
"""
for f in files:
    fp = open(resultdir + '/' + f)
    contents = fp.read()

    if f[-7:] == '.result':
        counter3 += 1
        if '[1, 1]' in contents:
            counter1 += 1
    else:
        if '[1, 1]' in contents:
            counter2 += 1
"""
print('counters', counter1, counter2, counter3)


