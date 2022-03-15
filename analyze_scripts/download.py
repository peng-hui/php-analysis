import os, multiprocessing


def download(urls):
    idx = 0
    for url in urls:
        command = 'git clone ' + url.rstrip('\n') + ' /data/phpapp/last10/' + str(idx)
        print(command)
        os.system(command)
        #filename = url.split('/')[-1]
        #mvcommand = 'mv ' + filename + '  f' + str(idx)
        #print(filename, mvcommand)
        idx += 1


if __name__ == '__main__':
    filename = 'last10.txt'
    f = open(filename, 'r')
    urls = f.readlines()
    download(urls)
