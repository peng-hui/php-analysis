#!/usr/bin/env python3
import os, sys
from mkdirs import mkdirs

tar = 'tar -zcvf output.tar.gz ../output/  ../loops/'
os.system(tar)
clearoutput = 'rm -r /home/users/phli/cpu_dos/output/*  /home/users/phli/cpu_dos/loops/*'
if os.path.isfile('/home/users/phli/cpu_dos/tdata/output.tar.gz') :
    os.system(clearoutput)
    mkdirs('app', 0, 1000)


else:
    print("why not tar file")


