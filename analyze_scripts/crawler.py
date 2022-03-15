#!/usr/bin/env python3
from bs4 import BeautifulSoup
import urllib2
import re, time, os
from multiprocessing import Process, Lock


def geturl(searchurl, filename):
    try:
        html_page = urllib2.urlopen(searchurl)
    except urllib2.HTTPError as e:
        if e.code == 429:
            time.sleep(5)
            geturl(searchurl,filename)
            return 
        else:
            pass
            return
    soup = BeautifulSoup(html_page, "html.parser")
    repo_list =  soup.findAll('a', attrs={'class': 'v-align-middle'})
    f = open(filename, 'a+')
    for repo in repo_list:
        url = 'https://github.com' + repo['href']
        f.write(url + '\n')
        print(url)
    f.close()

def crawlpage(url, startpage, endpage):
    for i in range(startpage, endpage):
        turl = url + '&p=' + str(i+1)
        print('page %d', i + 1)
        geturl(turl, str(startpage) + '.txt')

def last10(url):
    os.system('mv last10.txt last10.txt.old')
    for i in range(90,100):
        turl = url + '&p=' + str(i+1)
        print('page %d', i + 1)
        geturl(turl, '.txt')

if __name__ == '__main__':
    url = 'https://github.com/search?l=PHP&o=desc&q=php&s=stars&type=Repositories'
    
    numofprocess = 1
    startpage = {0: 10, 1: 20, 2: 70, 3: 80}
    process = {}
    for num in range(numofprocess):
        process[num] = Process(target=crawlpage, args=(url, startpage[num], startpage[num] + 10 ))
        process[num].start()

    for num in range(numofprocess):
        process[num].join()


