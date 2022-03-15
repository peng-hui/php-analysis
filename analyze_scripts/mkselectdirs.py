import os
f = open('sum_', 'r+')
lines = f.readlines()
f.close()
lines = [line.split(':')[0] for line in lines]
for line in lines:
    command = 'mkdir loops/app' + line
    os.system(command)
    print(command)
    command = 'mkdir output/app' + line
    print(command)
    os.system(command)


