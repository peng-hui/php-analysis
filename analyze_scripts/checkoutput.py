#!/usr/bin/env python3

import os, sys

def checkempty(folder):
    subfolders = os.listdir(folder)
    apps = []
    for subfolder in subfolders:
        files = os.listdir(folder + '/' + subfolder)
        if(len(files) > 0):
            apps.append(subfolder)

    return apps

if __name__ == '__main__':
    if(len(sys.argv) > 1):
        r = checkempty(sys.argv[1])
    else:
        r = checkempty('/home/users/phli/cpu_dos/output')

    r = sorted(r)
    f = open('notemptyoutput.txt', 'w+')
    for i in r:
        f.write(str(i) + '\n')
    f.write(str(len(r)))
    f.close()
    
    



