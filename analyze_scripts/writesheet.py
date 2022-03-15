#!/usr/bin/env python3
import os, xlwt, sys
from countfiles import countfiles

def writesheet(workbook, urls, sheetname):
    sheet = workbook.add_sheet(sheetname, cell_overwrite_ok = True)
    sheet.write(0, 0, 'app #')
    sheet.write(0, 1, 'repo name')
    sheet.write(0, 2, 'repo link')
    sheet.write(0, 3, 'line of code')
    sheet.write(0, 4, 'num of files')

    idx = 1
    for url in urls:
        url = url.rstrip('\n')
        repo_name = url.split('/')[-1] # the last item
        sheet.write(idx, 0, str(idx - 1))
        sheet.write(idx, 1, repo_name)
        sheet.write(idx, 2, url)
        idx += 1
    parent_dirname =  sheetname + '/'

    for i in range(100):
        dirname = parent_dirname + str(i)
        counter = countfiles(dirname)
        print(dirname, counter[1])
        sheet.write(i + 1, 3, counter[1])
        sheet.write(i + 1, 4, counter[0])

    return workbook
if __name__ =='__main__':
    workbook = xlwt.Workbook()
    f = open('last100.txt')
    urls = f.readlines()
    workbook = writesheet(workbook, urls, 'last100')

    

    
    f = open('top100.txt')
    urls = f.readlines()
    workbook = writesheet(workbook, urls, 'top100')

    workbook.save('result.xls')


