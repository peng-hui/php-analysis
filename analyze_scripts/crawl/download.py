#!/usr/bin/env python3
import os
from multiprocessing import Process


def download(urls, idx):
    for url in urls:
        command = 'git clone ' + url.rstrip('\n') + ' /data/cpu_dos_data/phpapps/26_/' + str(idx)
        print(command)
        os.system(command)
        #filename = url.split('/')[-1]
        #mvcommand = 'mv ' + filename + '  f' + str(idx)
        #print(filename, mvcommand)
        idx += 1
    return


if __name__ == '__main__':
    filename = '26.txt'
    f = open(filename, 'r')
    urls = f.readlines()
    numofprocess = 20
    process = {}
    for num in range(numofprocess):
        process[num] = Process(target=download, args=(urls[num*40: num*40 + 40], num * 40 + 100))
        process[num].start()

    for num in range(numofprocess):
        process[num].join()

