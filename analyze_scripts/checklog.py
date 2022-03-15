#!/usr/bin/env python3

import os, sys

def checklog(log):
    f = open(log, 'r')
    with f:
        lines = f.readlines()
        apps = {}
        for line in lines:
            line = line.split('/')
            catagory = line[0]
            app = line[1]
            #print(catagory, app)
            if int(app) not in apps:
                apps[int(app)]  = 0
            apps[int(app)] += 1
        f.close()
        return apps
            

            


if __name__ == '__main__':
    if(len(sys.argv) > 1):
        log = sys.argv[1]
    else:

        log = 'last100_get.log'
    apps = checklog(log)
    f = open('sum_' + log, 'w+')
    for app in apps:
        time = apps[app]
        f.write(str(app) + ":" + str(time) + '\n')
    f.write('===' + str(len(apps)) + '\n')

    f.close()
