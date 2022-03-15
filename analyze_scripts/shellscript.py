#from func_caller_parser import *
import json, os, sys
'''
FORMAT:
    [
        funcname:xxx,
        caller:[
        callername1: tainted args1
        callername2: tainted args1
        ],
        funcname:xxx
        ...
    ]
'''
#resultpath = 'output/result.txt'
def funcname_caller_json(path, resultpath):# ended with '/'
    files = os.listdir(path)
    funcs = {}
    caller2callee = {}
    funcargnum = {}
    times = {}
    for eachfile in files:
        if 'SINK' in eachfile:
            fp = open(path + eachfile)
            lines = fp.readlines()
            for eachline in lines:
                split = eachline.split(':')
                key = split[0]
                rejson = json.loads(eachline[len(key) + 1:])
                caller = rejson['Caller']
                args = rejson['args']
                paramdetermined = rejson['paramdetermined']
                if key not in funcs:
                    funcs[key] = {}
                if key not in times:
                    times[key] = 0
                if key not in funcargnum:
                    funcargnum[key] = 0
                funcs[key][caller] = True
                times[key] += 1
                funcargnum[key] = max(funcargnum[key], len(args))


                '''
                    funcs[key][caller]['args'] = [args]
                    funcs[key][caller]['paramdetermined'] =[paramdetermined]
                    #else:
                    #length = min(len(args), len(funcs[key][caller]['args']))
                    #for i in range(length):
                    #    funcs[key][caller]['args'][i]  = funcs[key][caller]['args'][i] or args[i]
                    #if length < len(args):
                    #    funcs[key][caller]['args'].extend(args[length: ])
                    if args not in funcs[key][caller]['args']:
                        funcs[key][caller]['args'].append(args)
                    if paramdetermined not in funcs[key][caller]['paramdetermined']:

                        funcs[key][caller]['paramdetermined'].append(paramdetermined)
                '''

                # start new from caller->callee instead of callee->caller
                callee = key
                if caller not in caller2callee:
                    caller2callee[caller] = {}
                if callee not in caller2callee[caller]:
                    caller2callee[caller][callee] = {}
                    caller2callee[caller][callee] = [paramdetermined]
                else:
                    if paramdetermined not in caller2callee[caller][callee]:
                        caller2callee[caller][callee].append(paramdetermined)
            #os.remove(path + eachfile)
    return [caller2callee, funcs, funcargnum, times]

'''
use the json file funcs above as the param
'''
def getstartfuncs(funcs):
    table = {}
    for func in funcs:
        callers = funcs[func]
        table[func] = True
        for caller in callers:
            if caller not in table:
                table[caller] = False
    result = []
    for func in table:
        if table[func] == False:
            result.append(func)
    #print(result)
    return result



class traverse:

    def __init__(self, caller2callee, funcargnum):
        self.caller2callee = caller2callee
        self.funcargnum = funcargnum
        self.functaintedparams = {}

    def start(self, startfuncs):
        print('start analysis here')
        for startfunc in startfuncs:
            self.funcargnum[startfunc] = 10
        for startfunc in startfuncs:
            if startfunc in self.caller2callee:
                args = [1] * self.funcargnum[startfunc]
                self.functaintedparams[startfunc] = [args] # tainted all params
                visited = {}
                visited[startfunc] = True
                self.start_traverse(startfunc, args, visited)
        return 

    def start_traverse(self, funcname, params,visited):
        if funcname not in self.caller2callee:
            return 
        #print('funcname', funcname)
        for callee in self.caller2callee[funcname]:
            if callee in visited and visited[callee] == True:
                continue
            else:
                #print('callee', callee)
                visited[callee] = True
                if callee not in self.functaintedparams:
                    self.functaintedparams[callee] = []
                eachtimes = self.caller2callee[funcname][callee]
                #print('callee ', eachtimes)
                for each in eachtimes:
                    #print('each', each)
                    re = []
                    for param in each:
                        tre = 0
                        #print('param', param, each[param])
                        for  i in range( min(len(each[param]),len(params) )):
                            tre += each[param][i]*params[i]
                        re.append(1 if tre > 0 else 0)
                    if re not in self.functaintedparams[callee]:
                        self.functaintedparams[callee].append(re)
                        self.start_traverse(callee, re, visited)
                visited[callee] = False
        return

    def writedowntaint(self, filename):
        dump = json.dumps(self.functaintedparams)
        with open(filename, 'w') as fp:
            fp.write(dump)
            fp.close()
        return dump






if __name__ == '__main__':

    path = os.path.dirname(os.path.realpath(__file__))
    #print(path)
    caller2callee, funcs, funcargnum, times = funcname_caller_json( path + '/output/', path + '/tdata/result_func_caller.txt') 
    startfuncs = getstartfuncs(funcs) # get start funcs

    newtimes = sorted(times.items(), key=lambda x: x[1])
    for tu in newtimes:
        print(tu[0], tu[1])

    # traverse from the start funcs 
    Traver = traverse(caller2callee, funcargnum)
    Traver.start(startfuncs)
    Traver.writedowntaint(path + '/tdata/result_taintfuncs.txt')
    


    allfiles = os.listdir(path + "/output/")
    '''
    for one in allfiles:
        if 'txt' in one:
            os.remove(path + "/output/"+one);
    '''

    with open(path + '/tdata/startfuncs.txt', 'w+') as fp:
        for i in startfuncs:
            fp.write(i + '\n')
        fp.close()
    print('finish shellscirpt.py')

