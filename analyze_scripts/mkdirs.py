#!/usr/bin/env python3

import os, sys


def mkdirs(filename, start, end):
    for i in range(start, end):
        command = 'mkdir ' + '../loops/' + filename  + str(i)
        print(command)
        os.system(command)
        command = 'mkdir ' + '../output/' + filename + str(i)
        print(command)
        os.system(command)


if __name__ =='__main__':
    mkdirs('app', 0, 1000)
