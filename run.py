#!/usr/bin/env python3
import os, sys
from multiprocessing import Process, Lock
import subprocess

#startapp = {0: 0, 1: 5, 2: 10, 3: 15, 4: 20, 5: 25, 6: 30, 7: 35, 8: 40, 9: 45, 10: 50,
#        11: 55, 12: 60, 13: 65, 14: 70, 15: 75, 16: 80, 17: 85, 18: 90, 19: 95, 20: 100
#        }

def visitdir(dirname):# should be abspath
    if os.path.isdir(dirname):
        files = os.listdir(dirname)
        for filename in files:
            if os.path.isdir(dirname+ '/' + filename):
                visitdir(dirname + '/' + filename)
            else:
                if '.php' in filename:
                    os.system("php main.php " + dirname + '/' + filename)
    else:
        if '.php' in dirname:
            os.system("php main.php " + dirname)


def runlast(startapp, endapp):# startapp <= x < endapp
    for i in range(startapp, endapp):
        appname = findappdir(i)
        print("appname", appname)
        command = 'php main_analysis.php ' + os.path.abspath('/data/cpu_dos_data/phpapps/' + appname) 
        #subprocess.call(command)
        #subprocess.run(command)
        subprocess.run(['php', 'main_analysis.php', arg], stdout=subprocess.PIPE, check=True)
        #os.system('php main_analysis.php ' + os.path.abspath('/data/cpu_dos_data/phpapps/' + appname) ) 

def runselect(appnames):
    for appname in appnames:
        arg = os.path.abspath('/data/cpu_dos_data/phpapps/selected/' + str(appname)) 
        command = 'php main_analysis.php ' + arg
        print(command)
        #subprocess.call(command)
        #subprocess.run(['php', 'main_analysis.php', arg], stdout=subprocess.PIPE, check=True)
        os.system(command)
    return



def findappdir(app):
    directory = str(int(app / 100)) + '00/'
    return directory + str(app)


def usage():

    print('Option1 ./run.py selected numofprocess')
    print('Option2 ./run.py all numofprocess start end')


def main1(argv):

    f = open('selected_appname', 'r+')
    apps = f.readlines()
    apps = [app.strip('\n') for app in apps]
    f.close()

    numofprocess = int(argv[1])
    start = 0
    end = len(apps)

    startapp = {}

    total = end - start
    eachprocess = int(total / numofprocess)
    
    print('numofprocess', numofprocess, 'total', total, start, end)
    for app in apps:
        print(app)

    for i in range(numofprocess):
        startapp[i] = eachprocess * i + start
    startapp[numofprocess] = end # finished first 120
    process = {}

    for i in range(numofprocess):
        process[i] = Process(target=runselect, args=(apps[startapp[i] : startapp[i + 1] ], ))
        process[i].start()

    for i in range(numofprocess):
        process[i].join()
    print('finally finished')



def main(argv):
    
    if(len(argv) != 4):
        usage()
        sys.exit(1)

    numofprocess = int(argv[1])
    start = int(argv[2])
    end = int(argv[3])
    startapp = {}

    total = end - start
    eachprocess = int(total / numofprocess)
    
    for i in range(numofprocess):
        startapp[i] = eachprocess * i + start
    startapp[numofprocess] = end # finished first 120
    process = {}

    for i in range(numofprocess):
        process[i] = Process(target=runlast, args=(startapp[i], startapp[i + 1], ))
        process[i].start()

    for i in range(numofprocess):
        process[i].join()
    print('finally finished')


if __name__ == '__main__':
    if(len(sys.argv) > 1):
        if(sys.argv[1] == 'selected'):
            main1(sys.argv[1: ])
        else:
            main(sys.argv[1: ])
    else:
        usage()


