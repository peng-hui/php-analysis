#!/usr/bin/env python
import os, sys, subprocess

def countfiles(dirname):# should be abspath
    if os.path.isdir(dirname):
        count = 0
        lines = 0
        files = os.listdir(dirname)
        for filename in files:
            subcount = countfiles(dirname + '/' + filename)
            count += subcount[0]
            lines += subcount[1]
        return [count, lines]
    else:
        if dirname.endswith('.php'):
            dirname = dirname.replace(' ', '\\ ')
            command = 'wc -l ' + dirname
            try:
                lines = int(subprocess.check_output('wc -l ' + dirname,  shell=True).decode('ascii').split(' ')[0])
            #except subprocess.CalledProcessError as e:
            #    return [1, 0]
            #except UnicodeDecodeError as e:
            #    return [1, 0]
            except:
                return [1, 0]

            return [1, lines]
    return [0, 0]

def usage():
    print('Usage:  ./countfiles.py dirname ')
    print('\tExample: =>  ./councountfiles.py example/wordpress/ ')


if __name__ == '__main__':
    if len(sys.argv) > 1:
        re = countfiles(sys.argv[1])
        print("Number of files: ", re[0])
        print("Number of lines: ", re[1])
    else:
        usage()


