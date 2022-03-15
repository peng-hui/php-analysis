#!/usr/bin/env python3
# coding: utf-8
import os, sys, json, random, string
import subprocess
from z3 import *
from multiprocessing import Process

sys.setrecursionlimit(100000)
# this depends on the length of constraints
maxvalue = 100

def convertbool(left):
    if type(left) != bool and type(left) != BoolRef:
        if type(left) == String:
            left = left != StringVal('')
        elif is_arith(left):
            left = left != 0
        else:
            print("type  ", type(left))
            return True
    return left

def getrandint():
    return random.randint(- maxvalue, maxvalue)

def getrandstr(num = 0):
    letters = string.ascii_letters
    if num <= 0 or type(num) != int:
        randlen = random.randint(0, maxvalue)
        return ''.join(random.choice(letters) for i in range(randlen))
    else:
        return ''.join(random.choice(letters) for i in range(num))

def getvardict():
    varname = getrandstr(10)
    vardict = {}
    vardict['nodeType'] = 'Expr_Varible'
    vardict['name'] = varname
    vardict['attributes'] = {'startLine':0, 'endLine':0}
    return vardict

#Declare Sorts here, and it follows below process
class parse2smt:
    def __init__(self):
        '''
        types are like following: Bool, int, real, string, [int, real, string]
        it can also be the combination of more than one kind, regardless 
        of the usage '>' => number/string work. 
        '''
        self.Vars = {} # get var type if possible. 
        self.UnSupportExprs = []
        # Assume there is no conflict on var types.
        
        self.Var2Container = {} # x => 1, y => 1, z => 2
        self.Container2Var = {} # dict for variables whose types are realted to each other.
        self.ContainerType = {}
        # 1 => x,y, 2=>z
        self.ContainerIndex = 0 # current index containers using
        self.MaxContainerIndex = 0 # record max/next index
        self.Container2Var[0] = []
        self.Funcs = {} # same as Vars, record the type of return value
        self.Arg2Vars = {} # when infering types, mapping arguments to varaibles. e.g. 
        '''
        Arrays should be converted into variables as Arrays in Z3 should be same type key
        values points to same type values. which is differenct with PHP.
        '''
        self.Arrays = {}

        self.SVars = {} #/symbolic variables
        self.SFuncs = {} # symbolic functions
        self.NumofArgFuncs = {} # mapping funcname to number of arguments

        # a dict to may types, currently do not include Int, BitVectors
        self.TypeDefine = {
                0: 'None',
                1: 'Bool',
                2: 'Real',
                4: 'String',
                3: 'Bool&Real',
                5: 'Bool&String',
                6: 'Real&String',
                7: 'Bool&Real&String'
                }
        return
    
    def increaseContainerIndex(self): 
        # container index is the current index
        self.ContainerIndex = self.MaxContainerIndex
        self.Container2Var[self.ContainerIndex] = []
        self.MaxContainerIndex += 1

    
    # Input with expected types and return with possible types
    def scanvartypes(self, cst, ExType): # inherited Type: Array
        '''
        This is firstly used to scan for variable types 
        before converting them into Z3 representations.
        Information is in self.vars
        '''
        typeofcst = cst.get('nodeType')
        print(typeofcst)
        if typeofcst:
            if typeofcst == 'Stmt_Expression':
                return self.scanvartypes(cst['expr'], 1)

            elif 'Expr_BinaryOp_Logical' in typeofcst:# Act on Logical Operations, including and,xor,or.
                return self.scanExpr_BinaryOp_Boolean(cst)

            elif 'Expr_BinaryOp_Boolean' in typeofcst:
                return self.scanExpr_BinaryOp_Boolean(cst) # this should be the same thing with logical ones

            elif typeofcst == 'Expr_BinaryOp_Plus':
                return self.scanExpr_BinaryOp_Plus(cst)

            elif typeofcst == 'Expr_BinaryOp_Pow':
                return self.scanExpr_BinaryOp_Pow(cst)

            elif typeofcst == 'Expr_BinaryOp_ShiftLeft':
                return self.scanExpr_BinaryOp_ShiftLeft(cst)

            elif typeofcst == 'Expr_BinaryOp_ShiftRight':
                return self.scanExpr_BinaryOp_ShiftRight(cst)

            elif typeofcst == 'Expr_BinaryOp_Mod':
                return self.scanExpr_BinaryOp_Mod(cst)

            elif typeofcst == 'Expr_BinaryOp_Mul':
                return self.scanExpr_BinaryOp_Mul(cst)

            elif typeofcst == 'Expr_BinaryOp_Div':
                return self.scanExpr_BinaryOp_Mul(cst)
            
            elif typeofcst == 'Expr_BinaryOp_Minus':
                return self.scanExpr_BinaryOp_Minus(cst)

            elif typeofcst == 'Expr_BinaryOp_Greater' or typeofcst == 'Expr_BinaryOp_GreaterOrEqual' or\
                typeofcst == 'Expr_BinaryOp_Smaller' or typeofcst == 'Expr_BinaryOp_SmallerOrEqual' or \
                typeofcst == 'Expr_BinaryOp_Equal' or  typeofcst == 'Expr_BinaryOp_NotEqual' or\
                typeofcst == 'Expr_BinaryOp_Identical' or typeofcst == 'Expr_BinaryOp_NotIdentical':
                return self.scanExpr_BinaryOp_CMP(cst)

            elif typeofcst == 'Expr_Empty':
                return self.scanvartypes(cst['expr'], ExType)

            elif typeofcst == 'Expr_Variable':
                varname = cst['name']
                if(type(varname) != str):
                    newvarname = self.convert2str(str(varname))#str(dim).replace('\n', "").replace(' ', '') # getrandstr(10)
                    cst['name'] = newvarname
                    varname = newvarname

                print(varname)
                print(self.ContainerIndex)
                vartype = self.Vars.get(varname)
                # add to current container
                if varname not in self.Container2Var[self.ContainerIndex]:
                    self.Container2Var[self.ContainerIndex].append(varname)
                if varname not in self.Var2Container:
                    self.Var2Container[varname] = []
                if self.ContainerIndex not in self.Var2Container[varname]:
                    self.Var2Container[varname].append(self.ContainerIndex)
                if vartype and vartype != ExType:
                    print('MinCover in Expr_Variable')
                    self.Vars[varname] = self.MinCover(ExType, vartype)  
                    # assume that each variable can only have one type
                    # in each constraint
                else:
                    self.Vars[varname] = ExType

                if varname == 'maxValueLength':
                    if varname in self.Vars:
                        print(len(self.Vars))
                return self.Vars[varname]

            elif typeofcst == 'Expr_ArrayDimFetch': # the var/dim should be string already!!!
                var = cst['var']
                dim = cst['dim']

                if dim['nodeType'] != 'Expr_String':
                    dimname = self.convert2str(str(dim))#str(dim).replace('\n', "").replace(' ', '') # getrandstr(10)
                    dimdict = {}
                    dimdict['nodeType'] = 'Expr_String'
                    dimdict['value'] = dimname
                    dimdict['attributes'] = {'startLine': 0, 'endLine': 0,'kind':1}
                    dim = cst['dim'] = dimdict
                    self.Vars[dimname] = 4 # add

                if var['nodeType'] != 'Expr_Variable':
                    varname = self.convert2str(str(var)) #str(var).replace('\n', "").replace(' ', '') # getrandstr(10)
                    #varname = getrandstr(10)
                    vardict = {}
                    vardict['nodeType'] = 'Expr_Varible'
                    vardict['name'] = varname
                    vardict['attributes'] = {'startLine':0, 'endLine':0}
                    var = cst['var'] = vardict
                    self.Vars[varname] = 7

                varname = "ARRAY_" + var['name'] + "_" + dim['value'] # rename arraydimfetch 
                vartype = self.Vars.get(varname)
                if varname not in self.Container2Var[self.ContainerIndex]:
                    self.Container2Var[self.ContainerIndex].append(varname)
                if varname not in self.Var2Container:
                    self.Var2Container[varname] = []
                if self.ContainerIndex not in self.Var2Container[varname]:
                    self.Var2Container[varname].append(self.ContainerIndex)
                if vartype and vartype != ExType:
                    print('MinCover in Array_dimfetch')
                    print("type ", self.MinCover(ExType, vartype))
                    self.Vars[varname] = self.MinCover(ExType, vartype)
                else:
                    self.Vars[varname] = ExType
                return self.Vars[varname]


            elif 'Scalar' in typeofcst: # Act on Scalars, including numbers and strings.
                if typeofcst == 'Scalar_LNumber':
                    return 2 # todo
                elif typeofcst == 'Scalar_DNumber':
                    return 2
                elif typeofcst == 'Scalar_Bool':
                    return 1
                elif typeofcst == 'Scalar_String':
                    return 4
                else:
                    print("ERROR: Uncatched Scalar Tpye :", typeofcst )
                    return 7
            
            elif typeofcst == 'Expr_FuncCall':
                return self.scanfunc(cst, ExType) # pass all info: name, args...
                # what to do for func


            elif typeofcst == 'Expr_ConstFetch':
                #print(cst['name'])
                namepart = cst['name']
                if namepart['nodeType'] == 'Name':
                    constname = namepart['parts'][0]
                    if constname == 'null' or constname == "NULL":
                        return 0
                    elif constname == 'True' or constname == 'false':
                        return 1
                    elif constname == 'False' or constname == 'false':
                        return 1
                else:
                    print("ConstFetch is not standard")
                return 1
            elif typeofcst == 'Expr_BooleanNot':
                return self.scanvartypes(cst['expr'], 1) # bool
            elif typeofcst == 'Expr_Cast_String':
                self.scanvartypes(cst['expr'], 4)
                return 4
            elif typeofcst == 'Expr_Isset':
                self.scanvartypes(cst['vars'][-1], 7) # Not sure why here is an array, but temperary get first time
                return 1
            else:
                print('===== Unsupported type', typeofcst)
                varname = self.convert2str(str(cst)) #str(cst).replace('\n', "").replace(' ', '') # getrandstr(10)
                #varname = getrandstr(10)
                cst['nodeType'] = 'Expr_Variable'
                cst['name'] = varname
                cst['attributes'] = {'startLine':0, 'endLine':0}
                self.Vars[varname] = ExType
                #self.Vars[varname] = 7
                return self.scanvartypes(cst, ExType)
        else:
            print('---- typenode not exists??', typeofcst)
            return 7
        return 7

    def convert2str(self, expr):
        t =  expr.replace('\n', '').replace(' ', '').replace('[', '').replace(']', '').replace('{', '').replace('}', '').replace(':', '').replace('\'', '').replace(',', '')[0:15]
        # this might need to change.
        # some of them are built-in functions that has some arguments
        return t

    def scanExpr_MethodCall(self, expr, ExType):
        var = expr['var']
        name = expr['name']
        # actually it should not come into this function
        # if it is well handled in function intepretion.
        return 7
    
    def scanfunc(self, expr, ExType):
        '''
        name:{
            "nodeType":"Name"
            "parts":[
                    "f"
                    ]
            "args":[
            { // arg 1
                "nodeType":"Arg"
                "value":{
        '''

        #print('come into scanfunc ', ExType)
        name = expr['name']
        if name['nodeType'] == 'Identifier':
            funcname = name['name']
        else:
            funcname = expr['name']['parts'][0]
        tt = self.Funcs.get(funcname)
        if not tt:
            self.Funcs[funcname] = []
        if ExType not in self.Funcs[funcname]:
            self.Funcs[funcname].append(ExType)

        t = self.NumofArgFuncs.get(funcname)
        if not t:
            self.NumofArgFuncs[funcname] = len(expr['args'])
        else:
            self.NumofArgFuncs[funcname] = max(t, len(expr['args']))
        i = 0
        saveIndex = self.ContainerIndex
        for arg in expr['args']:
            argname = 'Function_' + funcname + '_arg' + str(i)
            # save context of container
            self.increaseContainerIndex()
            argtype = self.scanvartypes(arg['value'], 7) 
            if arg['value']['nodeType'] == 'Expr_Variable': # if it is only variable
                if not self.Arg2Vars.get(argname):
                    self.Arg2Vars[argname] = []
                t = self.Arg2Vars[argname]
                t.append(arg['value']['name'])
            elif arg['value']['nodeType'] == 'Expr_ArrayDimFetch':
                if not self.Arg2Vars.get(argname):
                    self.Arg2Vars[argname] = []
                t = self.Arg2Vars[argname]
                var = arg['value']['var']
                dim = arg['value']['dim']
                varname = "ARRAY_" + var['name'] + "_" + dim['value'] # rename arraydimfetch
                t.append('ARRAY_' + var['name'] + '_' + dim['value'])
#             else:
#                 self.Funcs_Args[funcname][i] = argtype
            self.Vars[argname] = argtype
            i += 1
        self.ContainerIndex = saveIndex
        return ExType
    
    def scanExpr_BinaryOp_Boolean(self, expr): ## todo 
        print('come into scan binaryop_boolean')
        if expr.get('nodeType'):
            self.scanvartypes(expr['left'], 1)
            self.scanvartypes(expr['right'], 1)
            return 1 #only type not the value
        return 1
        
    
    ### Below part focus on Binary Operations.
    ## Comparasion
    def scanExpr_BinaryOp_CMP(self, expr):
        print("scanExpr_BinaryOp_CMP")
        self.increaseContainerIndex()
        ltype = self.scanvartypes(expr['left'], 7) 
        rtype = self.scanvartypes(expr['right'], ltype)
        if ltype != rtype:
            # need update
            #print('In scanExpr_BinaryOp_CMP', ltype, rtype)
            Type = self.MinCover(ltype, rtype)
            self.scanvartypes(expr['left'], Type)
            self.scanvartypes(expr['right'], Type)
            return Type
        return 1
    
    def MinCover(self, type1, type2):
        result = type1 & type2 # bitwise and
        print('MinCover', type1, type2, result)
        return result % 8 
    
    def MaxCover(self, type1, type2):
        # similar thing as minColver
        return (type1 | type2)%8
    
    ## Arithmetic Operations 
    ## Bitwise Operators should make lhs&rhs into BitVectors, however, currently, we only focus on int/real
    def scanExpr_BinaryOp_Bitwise(self, expr): # todo
        self.scanvartypes(expr['left'], 2) 
        self.scanvartypes(expr['right'], 2)
        return 2
    
    def scanExpr_BinaryOp_Coalesce(self, expr): # todo
        self.scanvartypes(expr['left'], 7) 
        self.scanvartypes(expr['right'], 7)
        return 7
    
    def scanExpr_BinaryOp_Concat(self, expr): # should ensure lhs&rhs are in string type
        self.scanvartypes(expr['left'], 4) 
        self.scanvartypes(expr['right'], 4)
        return 4
    
    def scanExpr_BinaryOp_Div(self, expr): # should ensure non-zero
        self.scanvartypes(expr['left'], 2) 
        self.scanvartypes(expr['right'], 2)
        return 2
    
    def scanExpr_BinaryOp_Identical(self, expr): # should consider the type.
        ltype = self.scanvartypes(expr['left'], 7) 
        rtype = self.scanvartypes(expr['right'], 7)
        if ltype != rtype:
            Type = self.MinCover(ltype, rtype)
            self.scanvartypes(expr['left'], Type) 
            self.scanvartypes(expr['right'], Type)
            return Type
        return ltype
    
    def scanExpr_BinaryOp_Minus(self, expr): 
        self.scanvartypes(expr['left'], 2) 
        self.scanvartypes(expr['right'], 2)
        return 2
    
    def scanExpr_BinaryOp_Mod(self, expr):
        self.scanvartypes(expr['left'], 2)
        self.scanvartypes(expr['right'], 2)
        return 2
    
    def scanExpr_BinaryOp_Mul(self, expr):
        self.scanvartypes(expr['left'], 2) 
        self.scanvartypes(expr['right'], 2)
        return 2
    
    def scanExpr_BinaryOp_Plus(self, expr):
        self.scanvartypes(expr['left'], 2) 
        self.scanvartypes(expr['right'], 2)
        return 2
    
    def scanExpr_BinaryOp_Pow(self, expr):
        self.scanvartypes(expr['left'], 2) 
        self.scanvartypes(expr['right'], 2)
        return 2
    
    def scanExpr_BinaryOp_ShiftLeft(self, expr):
        self.scanvartypes(expr['left'],2)
        self.scanvartypes(expr['right'], 2)
        return 2
    
    def scanExpr_BinaryOp_ShiftRight(self, expr):
        self.scanvartypes(expr['left'], 2)
        self.scanvartypes(expr['right'], 2)
        return 2
    
    def scanExpr_BinaryOp_Spaceship(self, expr): # @todo
        self.scanvartypes(expr['left'], 7)
        self.scanvartypes(expr['right'], 7)
        return 7
    
    def printvartypes(self):
        print('=====================')
        print("Start printing Vars :")
        for var in self.Vars:
            print("    " + var,':', self.Vars[var],'->', self.TypeDefine[self.Vars[var]])
        print("Start print Funcs :")
        #for func in self.SFuncs:
            #print("    " + func, ':', self.Funcs[func], '->', self.TypeDefine[self.Funcs[func]])
#             for i in self.Funcs_Args[func]:
#                 print("         ", self.Funcs_Args[func][i],  '->', self.TypeDefine[self.Funcs_Args[func][i]])
    
        print("Start print unsupported Expr")
        for use in self.UnSupportExprs:
            print("    " + use)
    # Here starts with convert
    
    
    def convert2smt(self, cst, ExType):
        '''
        Assume the length of the input JSON file is one.
        data: type is formated in JSON.
        '''
        typeofcst = cst.get('nodeType')
        print("-->>>>>" + typeofcst)
        if typeofcst:
            if typeofcst == 'Stmt_Expression':
                # go see whether it's function
                return self.convert2smt(cst['expr'], 1)

            elif 'Expr_BinaryOp_Logical' in typeofcst:# Act on Logical Operations, including and,xor,or.
                return self.convertExpr_BinaryOp_Boolean(cst)

            elif 'Expr_BinaryOp_Boolean' in typeofcst:
                return self.convertExpr_BinaryOp_Boolean(cst) # this should be the same thing with logical ones

            elif typeofcst == 'Expr_BinaryOp_Plus':
                return self.convertExpr_BinaryOp_Plus(cst)

            elif typeofcst == 'Expr_BinaryOp_Pow':
                return self.convertExpr_BinaryOp_Pow(cst)

            elif typeofcst == 'Expr_BinaryOp_ShiftLeft':
                return self.convertExpr_BinaryOp_ShiftLeft(cst)

            elif typeofcst == 'Expr_BinaryOp_ShiftRight':
                return self.convertExpr_BinaryOp_ShiftRight(cst)

            elif typeofcst == 'Expr_BinaryOp_Mod':
                return self.convertExpr_BinaryOp_Mod(cst)

            elif typeofcst == 'Expr_BinaryOp_Mul':
                return self.convertExpr_BinaryOp_Mul(cst)

            elif typeofcst == 'Expr_BinaryOp_Div':
                return self.convertExpr_BinaryOp_Mul(cst)
            elif typeofcst == 'Expr_BinaryOp_Minus':
                return self.convertExpr_BinaryOp_Minus(cst)

            elif typeofcst == 'Expr_BinaryOp_Greater':
                return self.convertExpr_BinaryOp_Greater(cst)
            
            elif typeofcst == 'Expr_BinaryOp_GreaterOrEqual':
                return self.convertExpr_BinaryOp_GreaterOrEqual(cst)
            
            elif typeofcst == 'Expr_BinaryOp_Smaller':
                return self.convertExpr_BinaryOp_Greater(cst)
            
            elif typeofcst == 'Expr_BinaryOp_SmallerOrEqual':
                return self.convertExpr_BinaryOp_SmallerOrEqual(cst)

            elif typeofcst == 'Expr_BinaryOp_Equal':
                return self.convertExpr_BinaryOp_Equal(cst)
            
            elif typeofcst == 'Expr_BinaryOp_NotEqual':
                return self.convertExpr_BinaryOp_NotEqual(cst)

            elif typeofcst == 'Expr_BinaryOp_Identical':
                return self.convertExpr_BinaryOp_NotIdentical(cst)
            elif typeofcst == 'Expr_BinaryOp_NotIdentical':
                return self.convertExpr_BinaryOp_NotIdentical(cst)

            elif typeofcst == 'Expr_Variable': # mark1
                if cst['name'] in self.SVars:
                    return self.SVars[cst['name']]
                else:
                    if type(cst['name']) == str:
                        #print(cst['name'], self.Vars[cst['name']])
                        t = self.getvar(cst['name'], self.Vars[cst['name']])# should specify a type
                        #print(type(t))
                        self.SVars[cst['name']] = t
                        return t

            elif 'Scalar' in typeofcst: # Act on Scalars, including numbers and strings.
                return self.convertScalar(cst)
            
            elif typeofcst == 'Expr_FuncCall':
                return self.getfunc(cst, ExType) # pass all info: name, args...


            elif typeofcst == 'Expr_ConstFetch':
                #print(cst['name'])
                namepart = cst['name']
                if namepart['nodeType'] == 'Name':
                    constname = namepart['parts'][0]
                    if constname == 'null' or constname == "NULL":
                        return None
                    elif constname == 'True' or constname == 'false':
                        return True
                    elif constname == 'False' or constname == 'false':
                        return False
                else:
                    print("ConstFetch is not standard")
                return True
            elif typeofcst == 'Expr_Cast_String':
                return self.convert2smt(cst['expr'], 7)
            elif typeofcst == 'Expr_BooleanNot':
                t = self.convert2smt(cst['expr'], 1)
                return Not(convertbool(t))

                return Not(self.convert2smt(cst['expr'], 1))

            elif typeofcst == 'Expr_ArrayDimFetch': # the var/dim should be string already!!!
                var = cst['var']
                dim = cst['dim']
                varname = "ARRAY_" + var['name'] + "_" + dim['value'] # rename arraydimfetch
                vartype = self.Vars.get(varname)
                if varname not in self.SVars:
                    self.SVars[varname] = self.getvar(varname, vartype)
                return self.getvar(varname, vartype)
            elif typeofcst == 'Expr_Empty':
                return self.convert2smt(cst['expr'], 7)

            else:
                print('-----Unsupported type', typeofcst) #mark2
                return True
        else:
            print('typenode not exists??')
            return True
    
    
    '''
    def convertExpr_BinaryOp_Logical(self, expr):
        print('come into logical and')
        typeofexpr = expr.get('nodeType')
        if typeofexpr == 'Expr_BinaryOp_LogicalAnd':
            return  And(self.convert2smt(expr['left']), self.convert2smt(expr['right']))
        elif typeofexpr == 'Expr_BinaryOp_LogicalOr':
            return Or(self.convert2smt(expr['left']), self.convert2smt(expr['right']))
        elif typeofexpr == 'Expr_BinaryOp_LogicalXor':
            return Xor(self.convert2smt(expr['left']), self.convert2smt(expr['right']))
        else:
            pass
        return
    '''


    def convertExpr_BinaryOp_Boolean(self, expr): ## todo 
        print('come into lboolean and')
        typeofexpr = expr.get('nodeType')
        left = self.convert2smt(expr['left'], 1)

        right = self.convert2smt(expr['right'], 1)
        left = convertbool(left)
        right = convertbool(right)
        # type check of left and which
        if typeofexpr == 'Expr_BinaryOp_LogicalAnd' or typeofexpr == 'Expr_BinaryOp_BooleanAnd':
            #print (expr['left'], expr['right'])
            return And(left, right)
            #return  And(self.convert2smt(expr['left']), self.convert2smt(expr['right']))
        elif typeofexpr == 'Expr_BinaryOp_LogicalOr' or typeofexpr == 'Expr_BinaryOp_BooleanOr':
            return Or(left, 
                    right)
            #return Or(self.convert2smt(expr['left']), self.convert2smt(expr['right']))
        elif typeofexpr == 'Expr_BinaryOp_LogicalXor':
            return Xor(left, right)
            #return Xor(self.convert2smt(expr['left']), self.convert2smt(expr['right']))
        else:
            print("UNSUPPORT  convertBinaryOp_Boolean " + typeofexpr)
            pass
        return
    
    ## define some necessary functions for type ensure
    def my_is_arith(self, expr1, expr2 = None):
        #  if not(is_arith(expr1) or type(expr1) == BoolRef or type(expr1) == bool or type(expr1) == int or type(expr1) == float):
        if not(is_arith(expr1) or type(expr1) == bool or type(expr1) == int or type(expr1) == float):
            return False
        #print(type(expr2), is_arith(expr2))
        if(expr2 != None and not(is_arith(expr2) or type(expr2) == bool or \
             type(expr2) == int or type(expr2) == float)):
            return False
        return True

    def my_is_bitvec(self, expr1, expr2 = None):
        if(not(is_bv(expr1))):
            return False
        if(expr2 != None and not(is_bv(expr2))):
            return False
        return True

    def my_is_string(self, expr1, expr2 = None):
        if not(is_string(expr1) or type(expr1) == str):
            return False
        if(expr2 != None and not(is_string(expr2) or 
            type(expr2)  == str)):
            return False
        return True

    ### Below part focuses on Binary Operations.
    ## Comparasion
    def convertExpr_BinaryOp_Greater(self, expr):
        left, right = self.funchandler(expr)

        if self.my_is_arith(left, right) or (type(left) == str and type(right) == str): #or self.my_is_string(left, right):
            return left > right
        return False

    
    def convertExpr_BinaryOp_Smaller(self, expr):
        left, right = self.funchandler(expr)
        if self.my_is_arith(left, right) or (type(left) == str and type(right) == str): #or self.my_is_string(left, right):
            return left < right
        return False
    
    def convertExpr_BinaryOp_GreaterOrEqual(self, expr):
        left, right = self.funchandler(expr)
        #print('come into greater')
        if self.my_is_arith(left, right) or (type(left) == str and type(right) == str): #or self.my_is_string(left, right):
            return left >= right
        return False

    def convertExpr_BinaryOp_SmallerOrEqual(self, expr):
        left, right = self.funchandler(expr)

        if self.my_is_arith(left, right) or (type(left) == str and type(right) == str): #or self.my_is_string(left, right):
            return left <= right
        return False
    

    def convertExpr_BinaryOp_Equal(self, expr):
        left, right = self.funchandler(expr)

        #print('equal===  ', type(left), type(right))
        if self.my_is_arith(left, right) or self.my_is_string(left, right) :
        #     print('equal', left, right)
            return left == right
        return False
    
    def convertExpr_BinaryOp_NotEqual(self, expr):
        left, right = self.funchandler(expr)

        if self.my_is_arith(left, right) or self.my_is_string(left, right):
            return left != right
        return True
    
    def convertExpr_BinaryOp_Minus(self, expr): 
        left = self.convert2smt(expr['left'], 2) 
        right = self.convert2smt(expr['right'], 2)

        if(self.my_is_arith(left, right)):
            return left - right
        return IntVal(getrandint())
    
    def convertExpr_BinaryOp_Mod(self, expr):
        left = self.convert2smt(expr['left'], 2) 
        right = self.convert2smt(expr['right'], 2)
        if(self.my_is_arith(left, right)):
            return left % right
        return IntVal(getrandint())
    

    def convertExpr_BinaryOp_Mul(self, expr):
        left = self.convert2smt(expr['left'], 2)
        right = self.convert2smt(expr['right'], 2)

        if(self.my_is_arith(left, right)):
            return left * right
        return IntVal(getrandint())
    
    def convertExpr_BinaryOp_Plus(self, expr):
        left = self.convert2smt(expr['left'], 2) 
        right = self.convert2smt(expr['right'], 2)

        if(self.my_is_arith(left, right)):
            return left + right
        return IntVal(getrandint())
    
    def convertExpr_BinaryOp_Pow(self, expr):
        left = self.convert2smt(expr['left'], 2) 
        right = self.convert2smt(expr['right'], 2)

        if(self.my_is_arith(left, right)):
            return left ** right
        return IntVal(getrandint())
    
    def convertExpr_BinaryOp_ShiftLeft(self, expr): # bitvec
        left = self.convert2smt(expr['left'], 2) 
        right = self.convert2smt(expr['right'], 2)

        if is_arith(left):
            leftbv = Int2BV(ToInt(left), 32)
        elif is_bv(left):
            leftbv = left
        else:
            leftbv = BitVecVal(getrandint(), 32)
        if is_arith(right):
            rightvb = Int2BV(ToInt(right), 32)
        elif is_bv(right):
            rightbv = right
        else:
            rightbv = BitVecVal(getrandint(), 32)

        return leftbv << rightbv
    
    def convertExpr_BinaryOp_ShiftRight(self, expr):
        left = self.convert2smt(expr['left'], 2) 
        right = self.convert2smt(expr['right'], 2)

        if is_arith(left):
            leftbv = Int2BV(ToInt(left), 32)
        elif is_bv(left):
            leftbv = left
        else:
            leftbv =  BitVecVal(getrandint(), 32)
        if is_arith(right):
            rightvb = Int2BV(ToInt(right), 32)
        elif is_bv(right):
            rightbv = right
        else:
            rightbv = BitVecVal(getrandint(), 32)
        return leftbv >> rightbv
    
    ## Arithmetic Operations 
    ## Bitwise Operators should make lhs&rhs into BitVectors, however, currently, we only focus on int/real
    def convertExpr_BinaryOp_BitwiseAnd(self, expr): # todo
        left = self.convert2smt(expr['left'], 2) 
        right = self.convert2smt(expr['right'], 2)
 
        if is_arith(left):
            leftbv = Int2BV(ToInt(left), 32)
        elif is_bv(left):
            leftbv = left
        else:
            leftbv = BitVecVal(getrandint(), 32)
        if is_arith(right):
            rightvb = Int2BV(ToInt(right), 32)
        elif is_bv(right):
            rightbv = right
        else:
            rightbv = BitVecVal(getrandint(), 32)
        return leftbv & rightbv
    
    def convertExpr_BinaryOp_BitwiseOr(self, expr): # todo
        left = self.convert2smt(expr['left'], 2) 
        right = self.convert2smt(expr['right'], 2)

        if is_arith(left):
            leftbv = Int2BV(ToInt(left), 32)
        elif is_bv(left):
            leftbv = left
        else:
            leftbv = BitVecVal(getrandint(), 32)
        if is_arith(right):
            rightvb = Int2BV(ToInt(right), 32)
        elif is_bv(right):
            rightbv = right
        else:
            rightbv = BitVecVal(getrandint(), 32)

        return leftbv | rightbv
    
    def convertExpr_BinaryOp_BitwiseXor(self, expr): # todo
        left = self.convert2smt(expr['left'], 2) 
        right = self.convert2smt(expr['right'], 2)

        if is_arith(left):
            leftbv = Int2BV(ToInt(left), 32)
        elif is_bv(left):
            leftbv = left
        else:
            leftbv = BitVecVal(getrandint(), 32)
        if is_arith(right):
            rightvb = Int2BV(ToInt(right), 32)
        elif is_bv(right):
            rightbv = right
        else:
            rightbv = BitVecVal(getrandint(), 32)

        return leftbv ^ rightbv
    
    def convertExpr_BinaryOp_Coalesce(self, expr): # todo
        print("there must be a bug as z3 does not support COALESCE")
        left = self.convert2smt(expr['left'], 7) 
        right = self.convert2smt(expr['right'], 7)
        return right
    
    def convertExpr_BinaryOp_Concat(self, expr): # should ensure lhs&rhs are in string type
        left = self.convert2smt(expr['left'], 4) 
        right = self.convert2smt(expr['right'], 4)
        if(self.my_is_arithm(left)):
            leftstr = IntToStr(ToInt(left))
        elif(self.my_is_string(left)):
            leftstr = left
        else:
            leftstr = StringVal(getrandstr())

        if(self.my_is_arithm(right)):
            rightstr = IntToStr(ToInt(right))
        elif(self.my_is_string(right)):
            rightstr = right
        else:
            rightstr = StringVal(getrandstr())


        return leftstr + rightstr
    
    def convertExpr_BinaryOp_Div(self, expr): # should ensure non-zero
        left = self.convert2smt(expr['left'], 2) 
        right = self.convert2smt(expr['right'], 2)

        if is_arith(left) and is_arith(right):
            return left / right
        return IntVal(getrandint())
    
    def convertExpr_BinaryOp_Identical(self, expr): # should consider the type.
        left, right = self.funchandler(expr)
        if self.gettype(left) == self.gettype(right):
            return left ==  right
        return False

    def convertExpr_BinaryOp_NotIdentical(self, expr): # should consider the type.
        left, right = self.funchandler(expr)
        if self.gettype(left) == self.gettype(right):
            return left != right
        return True
    

    
    def convertExpr_BinaryOp_Spaceship(self, expr): # @todo
        '''
        eturn 0 if values on either side are equal
        Return 1 if value on the left is greater
        Return -1 if the value on the right is greater
        '''
        return IntVal(1) #not true
    
    
    def convertScalar(self, expr):
        typeofexpr = expr.get('nodeType')
        if typeofexpr == 'Scalar_LNumber':
            return expr['value']
        elif typeofexpr == 'Scalar_DNumber':
            return Real(expr['value'])
        elif typeofexpr == 'Scalar_String':
            return StringVal(expr['value'])
        else:
            print("Unknown Scalar")
            return True
        return True
    
    def getfunc1(self, expr, ExType):
        print('come into getfuncfunc11 ')
        #### change expr from func to variable @todo
        '''
        varname = getrandstr(10)
        expr['nodeType'] = 'Expr_Varible'
        expr['name'] = varname
        expr['attributes'] = {'startLine':0, 'endLine':0}
        
        return self.convert2smt(expr, ExType)
        '''
        
        

        # codes below not used currently
        funcname = ''.join(expr['name']['parts']) #[0] #bugnumber1

        ####  get arguments first
        args = []
        typeofargs = []
        idx = 0
        while(idx < len(expr['args'])):
            arg = expr['args'][idx]['value']
            t = self.convert2smt(arg, 7)
            args.append(t)
            typeofargs.append(self.gettype(t))
            idx += 1
        return [typeofargs, args]


    def getfunc(self, expr, ExType):
        '''
        name:{
            "nodeType":"Name"
            "parts":{
                    "f"
            }
            "args":[
            { // arg 1
                "nodeType":"Arg"
                "value":{
                ...
                }
            },
            
            { // arg 2
                "nodeType":"Arg"
                "value":{
                    "nodeType":"Scalar_LNumber"
                    
                }
            }
            ]
        }
        '''
        # add dynamic declare here

        print('come into getfunc ')
        name = expr['name']
        if name['nodeType'] == 'Identifier':
            funcname = name['name']
        else:
            funcname = expr['name']['parts'][0] #bugnumber1
        if funcname == 'isset':
            return True
            


        ####  get arguments first
        args = []
        typeofargs = []
        strtypeofargs = []
        idx = 0
        while(idx < len(expr['args'])):
            arg = expr['args'][idx]['value']
            t = self.convert2smt(arg, 7)
            strtypeofargs.append(str(self.gettype(t)))
            args.append(t)
            typeofargs.append(self.gettype(t))
            idx += 1


        funckey = 'Return' + str(ExType) + '_' +  '_'.join(strtypeofargs)
        if funcname not in self.SFuncs:
            self.SFuncs[funcname] = {}

        if funckey not in self.SFuncs[funcname]:
            self.SFuncs[funcname][funckey] = self.declarefunc1(funcname, funckey, ExType, typeofargs)

        #print(funcname, funckey, ExType)
        func = self.SFuncs[funcname][funckey]
        # however, the arguments can be other functions, so the return 
        # read and store into SFuncs

        #for arg in args:
            #print(type(arg))
        #print(type(func))
        return func(args)

        '''
        if self.NumofArgFuncs[funcname] == 0:
            return func()
        elif self.NumofArgFuncs[funcname] == 1:
            print(expr['args'])
            print(funcname, type(func), type(args[0]))
            #print(type(func(args[0])))
            return func(args[0])
        elif self.NumofArgFuncs[funcname] == 2:
            print(expr['args'][1])
            print(funcname, type(func), type(args[0]), type(args[1]))
            return func(args[0], args[1])
        elif self.NumofArgFuncs[funcname] == 3:
            return func(args[0], args[1], args[2])
        elif self.NumofArgFuncs[funcname] == 4:
            return func(args[0], args[1], args[2], args[3])
        else:
            print("Other number of arguments\n")
            return None
        '''

    def declarefunc1(self, funcname, funckey, returntype, argtypes):
        functionname = funcname + '_' + funckey
        sortlist = []
        for argtype in argtypes:
            sortlist.append(self.getsortbynum(argtype))
        sortlist.append(self.getsortbynum(returntype))
        return Function(functionname, sortlist)

    '''
    def declarefunc(self, expr):
        funcname = expr['name']['parts'][0] # bugnumber1
        numberofarguments = self.NumofArgFuncs.get(funcname)
        idx = 0
        args = []
        while idx < numberofarguments:
            # get type of each arguments 
            argname = 'Function_' + funcname + '_arg' + str(idx)
            t = self.Vars.get(argname)
            if not t:
                t = 7
            sort = self.getsortbynum(t)
            args.append(sort)
            idx += 1

        returnsort = self.getsortbynum(self.Funcs.get(funcname))

        if self.NumofArgFuncs[funcname] == 0:
            self.SFuncs[funcname] = Function(funcname, returnsort)
        elif self.NumofArgFuncs[funcname] == 1:
            self.SFuncs[funcname] = Function(funcname, args[0], returnsort)
        elif self.NumofArgFuncs[funcname] == 2:
            self.SFuncs[funcname] = Function(funcname, args[0], args[1], returnsort)
        elif self.NumofArgFuncs[funcname] == 3:
            self.SFuncs[funcname] = Function(funcname, args[0], args[1], args[2], returnsort)
        elif self.NumofArgFuncs[funcname] == 4:
            self.SFuncs[funcname] = Function(funcname, args[0], args[1], args[2], args[3], returnsort)
        else:
            print("Other number of arguments\n")
        return None
    '''

    def getsortbynum(self, num):
        if num == None:
            return NewSort
        if num == 1:
            return BoolSort()
        elif num == 2:
            return RealSort()
        elif num == 4:
            return StringSort()
        else:
            return StringSort() #add
            return NewSort
    
    def getvar(self, name, Type):
        #print('in get var?')
        #print(name, Type)
        if Type == 2:
            return Real(name)
        elif Type == 4:
            return String(name)
        elif Type == 1:
            return Bool(name)
        else:
            print('ERROR: Type: ', Type, 'Undefined')
            return String(name) #add
            return Const(name, NewSort)
        

    def unite(self, visitcon, visitvar):
        for var in self.Vars:
            if self.Vars[var] in [1,2,4] and var not in visitvar and var in self.Var2Container:
                visitvar.append(var)
                # propagate to other containers
                for con in self.Var2Container[var]:
                    if con not in visitcon:
                        visitcon.append(con)
                        for ivar in self.Container2Var[con]:
                            self.Vars[ivar] = self.Vars[var]
                            if ivar not in visitvar:
                                self.unite(visitcon, visitvar)


    # Other left should be assigned with type 7, and then use the default type
    def unitearg(self):
        for arg in self.Arg2Vars:
            Vars = self.Arg2Vars[arg]
            mintype = min(7, self.Vars[arg])
            for var in Vars:
                if var in self.Vars:
                    tmp = self.Vars[var]
                    mintype = min(mintype, tmp)
            self.Vars[arg] = mintype


        
    def gettype(self, cst):
        if type(cst) == bool or type(cst) == BoolRef:
            return 1
        elif type(cst) == int or is_arith(cst) == True:
            return 2
        elif type(cst) == str or is_string(cst) == True:
            return 4 
        elif type(cst) == ArithRef:
            return 2
        elif type(cst) == ExprRef:
            return 7
        elif cst == None:
            return 7

        typeofcst = cst['nodeType']
        if typeofcst == 'Stmt_Expression':
            return 1

        elif 'Expr_BinaryOp_Logical' in typeofcst:# Act on Logical Operations, including and,xor,or.
            return 1

        elif 'Expr_BinaryOp_Boolean' in typeofcst:
            return 1

        elif typeofcst == 'Expr_BinaryOp_Plus':
            return 2

        elif typeofcst == 'Expr_BinaryOp_Pow':
            return 2

        elif typeofcst == 'Expr_BinaryOp_ShiftLeft':
            return 2

        elif typeofcst == 'Expr_BinaryOp_ShiftRight':
            return 2

        elif typeofcst == 'Expr_BinaryOp_Mod':
            return 2

        elif typeofcst == 'Expr_BinaryOp_Mul':
            return 2

        elif typeofcst == 'Expr_BinaryOp_Div':
            return 2
        
        elif typeofcst == 'Expr_BinaryOp_Minus':
            return 2

        elif typeofcst == 'Expr_BinaryOp_Greater' or typeofcst == 'Expr_BinaryOp_GreaterOrEqual' or\
            typeofcst == 'Expr_BinaryOp_Smaller' or typeofcst == 'Expr_BinaryOp_SmallerOrEqual' or \
            typeofcst == 'Expr_BinaryOp_Equal' or  typeofcst == 'Expr_BinaryOp_NotEqual' or\
            typeofcst == 'Expr_BinaryOp_Identical' or typeofcst == 'Expr_BinaryOp_NotIdentical':
            return 1
        elif typeofcst == 'Expr_Empty' :
            return self.gettype(cst['expr'])

        elif typeofcst == 'Expr_Variable':
            varname = cst['name']
            vartype = self.Vars.get(varname)
            if not vartype:
                return 7
            return vartype
        elif typeofcst == 'Expr_ArrayDimFetch': # the var/dim should be string already!!!
            var = cst['var']
            dim = cst['dim']
            varname = "ARRAY_" + var['name'] + "_" + dim['value'] # rename arraydimfetch 
            vartype = self.Vars.get(varname)
            if not vartype:
                return 7
            return vartype

        elif 'Scalar' in typeofcst: # Act on Scalars, including numbers and strings.
            if typeofcst == 'Scalar_LNumber':
                return 2 # todo
            elif typeofcst == 'Scalar_DNumber':
                return 2
            elif typeofcst == 'Scalar_Bool':
                return 1
            elif typeofcst == 'Scalar_String':
                return 4
            else:
                print("ERROR: Uncatched Scalar Tpye :", typeofcst )
                return 7
        
        elif typeofcst == 'Expr_FuncCall':
            return 7 # for function call now 
        elif typeofcst == 'Expr_ConstFetch':
            #print(cst['name'])
            namepart = cst['name']
            if namepart['nodeType'] == 'Name':
                constname = namepart['parts'][0]
                if constname == 'null' or constname == "NULL":
                    return 0
                elif constname == 'True' or constname == 'false':
                    return 1
                elif constname == 'False' or constname == 'false':
                    return 1
            else:
                print("ConstFetch is not standard")
            return 1 # assume bool  type for true or false

        elif typeofcst == 'Expr_BooleanNot':
            return 1
        elif typeofcst == 'Expr_Cast_String':
            return 4
        elif typeofcst == 'Expr_Isset':
            return 1
        else:
            print('=====gettype-> Unsupported type', typeofcst)
            return 7
        return 7

    # return function 
    def funchandler(self, expr):
        print("come into funchandler")
        lfuncinfo = None
        rfuncinfo = None
        if expr['left']['nodeType'] == 'Expr_FuncCall':
            lfuncinfo = self.getfunc1(expr['left'], 7)
        else:
            left = self.convert2smt(expr['left'], 7)

        if expr['right']['nodeType'] == 'Expr_FuncCall':
            rfuncinfo = self.getfunc1(expr['right'], 7)
        else:
            right = self.convert2smt(expr['right'], 7)

        if not lfuncinfo and not rfuncinfo:
            return [left, right]
        elif not lfuncinfo and rfuncinfo != None: # right hand is function
            ltype = self.gettype(left)
            # declare in ltype
            #rfuncinfo is array of argtypes
            typeofargs = rfuncinfo[0]
            args = rfuncinfo[1]
            name = expr['right']['name']
            if name['nodeType'] == 'Identifier':
                funcname = name['name']
            else:
                funcname = expr['right']['name']['parts'][0] 

            funckey = 'Return' + str(ltype) + '_' +  '_'.join([str(i) for i in typeofargs])
            if funcname not in self.SFuncs:
                self.SFuncs[funcname] = {}

            if funckey not in self.SFuncs[funcname]:
                self.SFuncs[funcname][funckey] = self.declarefunc1(funcname, funckey, ltype, typeofargs)

            func = self.SFuncs[funcname][funckey]
            return [left, func(args)]

        elif not rfuncinfo and lfuncinfo != None: # left hand is function
            rtype = self.gettype(right)
            typeofargs = lfuncinfo[0]
            args = lfuncinfo[1]
            name = expr['left']['name']
            if name['nodeType'] == 'Identifier':
                funcname = name['name']
            else:
                funcname = expr['left']['name']['parts'][0] 
            funckey = 'Return' + str(rtype) + '_' +  '_'.join([str(i) for i in typeofargs])
            if funcname not in self.SFuncs:
                self.SFuncs[funcname] = {}

            if funckey not in self.SFuncs[funcname]:
                print("declare function with funckey",funckey)
                self.SFuncs[funcname][funckey] = self.declarefunc1(funcname, funckey, rtype, typeofargs)

            func = self.SFuncs[funcname][funckey]
            print(type(args[0]))
            return[func(args), right]
        else: # both functions ,then set them to 7
            rtype = ltype = 7
            typeofargs = lfuncinfo[0]
            args = lfuncinfo[1]

            name = expr['left']['name']
            if name['nodeType'] == 'Identifier':
                funcname = name['name']
            else:
                funcname = expr['left']['name']['parts'][0] 
            funckey = 'Return' + str(rtype) + '_' +  '_'.join([str(i) for i in typeofargs])
            if funcname not in self.SFuncs:
                self.SFuncs[funcname] = {}

            if funckey not in self.SFuncs[funcname]:
                print("declare function with funckey",funckey)
                self.SFuncs[funcname][funckey] = self.declarefunc1(funcname, funckey, rtype, typeofargs)
            lfunc = self.SFuncs[funcname][funckey]

            typeofargs = rfuncinfo[0]
            args = rfuncinfo[1]
            name = expr['right']['name']
            if name['nodeType'] == 'Identifier':
                funcname = name['name']
            else:
                funcname = expr['right']['name']['parts'][0] 
            funckey = 'Return' + str(ltype) + '_' +  '_'.join([str(i) for i in typeofargs])
            if funcname not in self.SFuncs:
                self.SFuncs[funcname] = {}

            if funckey not in self.SFuncs[funcname]:
                self.SFuncs[funcname][funckey] = self.declarefunc1(funcname, funckey, ltype, typeofargs)
            rfunc = self.SFuncs[funcname][funckey]

            return [lfunc, rfunc]

    def test1(self, data, solution):
        tester = testall()
        tester.Vars = self.Vars
        tester.UnSupportExprs = self.UnSupportExprs
        tester.Var2Container = self.Var2Container
        tester.Container2Var = self.Container2Var
        tester.ContainerType = self.ContainerType
        tester.ContainerIndex = self.ContainerIndex
        tester.MaxContainerIndex = self.MaxContainerIndex
        tester.Container2Var = self.Container2Var
        tester.Funcs = self.Funcs
        tester.Arg2Vars = self.Arg2Vars
        tester.Arrays = self.Arrays
        tester.Svars = self.SVars
        tester.SFuncs = self.SFuncs
        tester.NumofArgFuncs = self.NumofArgFuncs
        tester.solution = solution
        return tester.testallsmt(data, 7)



#Declare Sorts here, and it follows below process
class testall:
    def __init__(self):
        '''
        types are like following: Bool, int, real, string, [int, real, string]
        it can also be the combination of more than one kind, regardless 
        of the usage '>' => number/string work. 
        '''
        self.solution = {}
        self.Vars = {} # get var type if possible. 
        self.UnSupportExprs = []
        # Assume there is no conflict on var types.
        
        self.Var2Container = {} # x => 1, y => 1, z => 2
        self.Container2Var = {} # dict for variables whose types are realted to each other.
        self.ContainerType = {}
        # 1 => x,y, 2=>z
        self.ContainerIndex = 0 # current index containers using
        self.MaxContainerIndex = 0 # record max/next index
        self.Container2Var[0] = []
        self.Funcs = {} # same as Vars, record the type of return value
        self.Arg2Vars = {} # when infering types, mapping arguments to varaibles. e.g. 
        '''
        Arrays should be tested into variables as Arrays in Z3 should be same type key
        values points to same type values. which is differenct with PHP.
        '''
        self.Arrays = {}

        self.SVars = {} # symbolic variables
        self.SFuncs = {} # symbolic functions
        self.NumofArgFuncs = {} # mapping funcname to number of arguments

        # a dict to may types, currently do not include Int, BitVectors
        self.TypeDefine = {
                0: 'None',
                1: 'Bool',
                2: 'Real',
                4: 'String',
                3: 'Bool&Real',
                5: 'Bool&String',
                6: 'Real&String',
                7: 'Bool&Real&String'
                }
        return
    
    def increaseContainerIndex(self): 
        # container index is the current index
        self.ContainerIndex = self.MaxContainerIndex
        self.Container2Var[self.ContainerIndex] = []
        self.MaxContainerIndex += 1


    
    def printvartypes(self):
        print('=====================')
        print("Start printing Vars :")
        for var in self.Vars:
            print("    " + var,':', self.Vars[var],'->', self.TypeDefine[self.Vars[var]])
        print("Start print Funcs :")
        #for func in self.SFuncs:
            #print("    " + func, ':', self.Funcs[func], '->', self.TypeDefine[self.Funcs[func]])
#             for i in self.Funcs_Args[func]:
#                 print("         ", self.Funcs_Args[func][i],  '->', self.TypeDefine[self.Funcs_Args[func][i]])
    
        print("Start print unsupported Expr")
        for use in self.UnSupportExprs:
            print("    " + use)
    # Here starts with test
    
    def testallsmt(self, cst, ExType):
        '''
        Assume the length of the input JSON file is one.
        data: type is formated in JSON.
        '''
        typeofcst = cst.get('nodeType')
        print("-->>>>>" + typeofcst)
        if typeofcst:
            if typeofcst == 'Stmt_Expression':
                # go see whether it's function
                return self.testallsmt(cst['expr'], 1)

            elif 'Expr_BinaryOp_Logical' in typeofcst:# Act on Logical Operations, including and,xor,or.
                return self.testExpr_BinaryOp_Boolean(cst)

            elif 'Expr_BinaryOp_Boolean' in typeofcst:
                return self.testExpr_BinaryOp_Boolean(cst) # this should be the same thing with logical ones

            elif typeofcst == 'Expr_BinaryOp_Plus':
                return self.testExpr_BinaryOp_Plus(cst)

            elif typeofcst == 'Expr_BinaryOp_Pow':
                return self.testExpr_BinaryOp_Pow(cst)

            elif typeofcst == 'Expr_BinaryOp_ShiftLeft':
                return self.testExpr_BinaryOp_ShiftLeft(cst)

            elif typeofcst == 'Expr_BinaryOp_ShiftRight':
                return self.testExpr_BinaryOp_ShiftRight(cst)

            elif typeofcst == 'Expr_BinaryOp_Mod':
                return self.testExpr_BinaryOp_Mod(cst)

            elif typeofcst == 'Expr_BinaryOp_Mul':
                return self.testExpr_BinaryOp_Mul(cst)

            elif typeofcst == 'Expr_BinaryOp_Div':
                return self.testExpr_BinaryOp_Mul(cst)
            elif typeofcst == 'Expr_BinaryOp_Minus':
                return self.testExpr_BinaryOp_Minus(cst)

            elif typeofcst == 'Expr_BinaryOp_Greater':
                return self.testExpr_BinaryOp_Greater(cst)
            
            elif typeofcst == 'Expr_BinaryOp_GreaterOrEqual':
                return self.testExpr_BinaryOp_GreaterOrEqual(cst)
            
            elif typeofcst == 'Expr_BinaryOp_Smaller':
                return self.testExpr_BinaryOp_Greater(cst)
            
            elif typeofcst == 'Expr_BinaryOp_SmallerOrEqual':
                return self.testExpr_BinaryOp_SmallerOrEqual(cst)

            elif typeofcst == 'Expr_BinaryOp_Equal':
                return self.testExpr_BinaryOp_Equal(cst)
            
            elif typeofcst == 'Expr_BinaryOp_NotEqual':
                return self.testExpr_BinaryOp_NotEqual(cst)

            elif typeofcst == 'Expr_BinaryOp_Identical':
                return self.testExpr_BinaryOp_NotIdentical(cst)
            elif typeofcst == 'Expr_BinaryOp_NotIdentical':
                return self.testExpr_BinaryOp_NotIdentical(cst)

            elif typeofcst == 'Expr_Variable': # mark1
                if cst['name'] in self.solution:
                    print('get solution')
                    print('type ', type(self.solution[cst['name']]))
                    return self.solution[cst['name']]
                else:
                    if type(cst['name']) == str:
                        #print(cst['name'], self.Vars[cst['name']])
                        #type_ = self.Vars.get(cst['name'])
                        if cst['name'] == 'maxValueLength':
                            if 'maxValueLength' not in self.Vars:
                                print(len(self.Vars))
                                for i in self.Vars:
                                    print(i)
                                print("not exit?")
                        t = self.getvar(cst['name'],
                               self.Vars[cst['name']])
                        #print(type(t))
                        self.SVars[cst['name']] = t
                        return t

            elif 'Scalar' in typeofcst: # Act on Scalars, including numbers and strings.
                return self.testScalar(cst)
            
            elif typeofcst == 'Expr_FuncCall':
                return self.testfunc(cst, ExType) # pass all info: name, args...


            elif typeofcst == 'Expr_ConstFetch':
                #print(cst['name'])
                namepart = cst['name']
                if namepart['nodeType'] == 'Name':
                    constname = namepart['parts'][0]
                    if constname == 'null' or constname == "NULL":
                        return False
                    elif constname == 'True' or constname == 'false':
                        return True
                    elif constname == 'False' or constname == 'false':
                        return False
                else:
                    print("ConstFetch is not standard")
                return True
            elif typeofcst == 'Expr_Cast_String':
                return self.testallsmt(cst['expr'], 7)
            elif typeofcst == 'Expr_BooleanNot':
                t = self.testallsmt(cst['expr'], 1)

                print('type t', type(t))
                return Not(convertbool(t))
                return Not(self.testallsmt(cst['expr'], 1))


            elif typeofcst == 'Expr_ArrayDimFetch': # the var/dim should be string already!!!
                var = cst['var']
                dim = cst['dim']
                varname = "ARRAY_" + var['name'] + "_" + dim['value'] # rename arraydimfetch
                vartype = self.Vars.get(varname)
                if varname not in self.solution: 
                    self.SVars[varname] = self.getvar(varname, vartype)
                return self.getvar(varname, vartype)
            elif typeofcst == 'Expr_Empty':
                return self.testallsmt(cst['expr'], 7)

            else:
                #print(typeofcst)
                print('-----Unsupported type', typeofcst) #mark2
                return True
            return False
        else:
            print('typenode not exists??')
            return True
        return False
    
    def testExpr_BinaryOp_Boolean(self, expr): ## todo 
        print('come into lboolean and')
        typeofexpr = expr.get('nodeType')
        left = self.testallsmt(expr['left'], 1)
        right = self.testallsmt(expr['right'], 1)
        left = convertbool(left)
        right = convertbool(right)


        if typeofexpr == 'Expr_BinaryOp_LogicalAnd' or typeofexpr == 'Expr_BinaryOp_BooleanAnd':
            #print (expr['left'], expr['right'])
            return And(left, right)
            #return  And(self.testallsmt(expr['left']), self.testallsmt(expr['right']))
        elif typeofexpr == 'Expr_BinaryOp_LogicalOr' or typeofexpr == 'Expr_BinaryOp_BooleanOr':
            return Or(left, right)
            #return Or(self.testallsmt(expr['left']), self.testallsmt(expr['right']))
        elif typeofexpr == 'Expr_BinaryOp_LogicalXor':
            return Xor(left, right)
            #return Xor(self.testallsmt(expr['left']), self.testallsmt(expr['right']))
        else:
            print("UNSUPPORT  testBinaryOp_Boolean " + typeofexpr)
            pass
        return
    
    ## define some necessary functions for type ensure
    def my_is_arith(self, expr1, expr2 = None):
        if not(is_arith(expr1) or type(expr1) == BoolRef or type(expr1) == bool or type(expr1) == int or type(expr1) == float):
            return False
        #print(type(expr2), is_arith(expr2))
        if(expr2 != None and not(is_arith(expr2) or type(expr2) == BoolRef or type(expr2) == bool or \
             type(expr2) == int or type(expr2) == float)):
            return False
        return True

    def my_is_bitvec(self, expr1, expr2 = None):
        if(not(is_bv(expr1))):
            return False
        if(expr2 != None and not(is_bv(expr2))):
            return False
        return True

    def my_is_string(self, expr1, expr2 = None):
        if not(is_string(expr1) or type(expr1) == str):
            return False
        if(expr2 != None and not(is_string(expr2) or 
            type(expr2)  == str)):
            return False
        return True

    ### Below part focuses on Binary Operations.
    ## Comparasion
    def testExpr_BinaryOp_Greater(self, expr):
        left, right = self.funchandler(expr)

        if self.my_is_arith(left, right) or self.my_is_string(left, right):
            return left > right
        return False

    
    def testExpr_BinaryOp_Smaller(self, expr):
        left, right = self.funchandler(expr)
        if self.my_is_arith(left, right) or self.my_is_string(left, right):
            return left < right
        return False
    
    def testExpr_BinaryOp_GreaterOrEqual(self, expr):
        left, right = self.funchandler(expr)
        #print('come into greater')
        if self.my_is_arith(left, right) or self.my_is_string(left, right):
            return left >= right
        return False

    def testExpr_BinaryOp_SmallerOrEqual(self, expr):
        left, right = self.funchandler(expr)

        if self.my_is_arith(left, right) or self.my_is_string(left, right):
            return left <= right
        return False
    

    def testExpr_BinaryOp_Equal(self, expr):
        left, right = self.funchandler(expr)

        print('equal===  ', type(left), type(right))
        if self.my_is_arith(left, right) or self.my_is_string(left, right) :
            print('equal', left, right)
            return left == right
        return False
    
    def testExpr_BinaryOp_NotEqual(self, expr):
        left, right = self.funchandler(expr)

        if self.my_is_arith(left, right) or self.my_is_string(left, right):
            return left != right
        return True
    
    def testExpr_BinaryOp_Minus(self, expr): 
        left = self.testallsmt(expr['left'], 2) 
        right = self.testallsmt(expr['right'], 2)

        if(self.my_is_arith(left, right)):
            return left - right
        return IntVal(getrandint())
    
    def testExpr_BinaryOp_Mod(self, expr):
        left = self.testallsmt(expr['left'], 2) 
        right = self.testallsmt(expr['right'], 2)

        if(self.my_is_arith(left, right)):
            return left % right
        return IntVal(getrandint())
    

    def testExpr_BinaryOp_Mul(self, expr):
        left = self.testallsmt(expr['left'], 2)
        right = self.testallsmt(expr['right'], 2)

        if(self.my_is_arith(left, right)):
            return left * right
        return IntVal(getrandint())
    
    def testExpr_BinaryOp_Plus(self, expr):
        left = self.testallsmt(expr['left'], 2) 
        right = self.testallsmt(expr['right'], 2)

        if(self.my_is_arith(left, right)):
            return left + right
        return IntVal(getrandint())
    
    def testExpr_BinaryOp_Pow(self, expr):
        left = self.testallsmt(expr['left'], 2) 
        right = self.testallsmt(expr['right'], 2)

        if(self.my_is_arith(left, right)):
            return left ** right
        return IntVal(getrandint())
    
    def testExpr_BinaryOp_ShiftLeft(self, expr): # bitvec
        left = self.testallsmt(expr['left'], 2) 
        right = self.testallsmt(expr['right'], 2)

        if is_arith(left):
            leftbv = Int2BV(ToInt(left), 32)
        elif is_bv(left):
            leftbv = left
        else:
            leftbv = BitVecVal(getrandint(), 32)
        if is_arith(right):
            rightvb = Int2BV(ToInt(right), 32)
        elif is_bv(right):
            rightbv = right
        else:
            rightbv = BitVecVal(getrandint(), 32)

        return leftbv << rightbv
    
    def testExpr_BinaryOp_ShiftRight(self, expr):
        left = self.testallsmt(expr['left'], 2) 
        right = self.testallsmt(expr['right'], 2)

        if is_arith(left):
            leftbv = Int2BV(ToInt(left), 32)
        elif is_bv(left):
            leftbv = left
        else:
            leftbv =  BitVecVal(getrandint(), 32)
        if is_arith(right):
            rightvb = Int2BV(ToInt(right), 32)
        elif is_bv(right):
            rightbv = right
        else:
            rightbv = BitVecVal(getrandint(), 32)
        return leftbv >> rightbv
    
    ## Arithmetic Operations 
    ## Bitwise Operators should make lhs&rhs into BitVectors, however, currently, we only focus on int/real
    def testExpr_BinaryOp_BitwiseAnd(self, expr): # todo
        left = self.testallsmt(expr['left'], 2) 
        right = self.testallsmt(expr['right'], 2)
 
        if is_arith(left):
            leftbv = Int2BV(ToInt(left), 32)
        elif is_bv(left):
            leftbv = left
        else:
            leftbv = BitVecVal(getrandint(), 32)
        if is_arith(right):
            rightvb = Int2BV(ToInt(right), 32)
        elif is_bv(right):
            rightbv = right
        else:
            rightbv = BitVecVal(getrandint(), 32)
        return leftbv & rightbv
    
    def testExpr_BinaryOp_BitwiseOr(self, expr): # todo
        left = self.testallsmt(expr['left'], 2) 
        right = self.testallsmt(expr['right'], 2)

        if is_arith(left):
            leftbv = Int2BV(ToInt(left), 32)
        elif is_bv(left):
            leftbv = left
        else:
            leftbv = BitVecVal(getrandint(), 32)
        if is_arith(right):
            rightvb = Int2BV(ToInt(right), 32)
        elif is_bv(right):
            rightbv = right
        else:
            rightbv = BitVecVal(getrandint(), 32)

        return leftbv | rightbv
    
    def testExpr_BinaryOp_BitwiseXor(self, expr): # todo
        left = self.testallsmt(expr['left'], 2) 
        right = self.testallsmt(expr['right'], 2)

        if is_arith(left):
            leftbv = Int2BV(ToInt(left), 32)
        elif is_bv(left):
            leftbv = left
        else:
            leftbv = BitVecVal(getrandint(), 32)
        if is_arith(right):
            rightvb = Int2BV(ToInt(right), 32)
        elif is_bv(right):
            rightbv = right
        else:
            rightbv = BitVecVal(getrandint(), 32)

        return leftbv ^ rightbv
    
    def testExpr_BinaryOp_Coalesce(self, expr): # todo
        print("there must be a bug as z3 does not support COALESCE")
        left = self.testallsmt(expr['left'], 7) 
        right = self.testallsmt(expr['right'], 7)
        return right
    
    def testExpr_BinaryOp_Concat(self, expr): # should ensure lhs&rhs are in string type
        left = self.testallsmt(expr['left'], 4) 
        right = self.testallsmt(expr['right'], 4)
        if(self.my_is_arithm(left)):
            leftstr = IntToStr(ToInt(left))
        elif(self.my_is_string(left)):
            leftstr = left
        else:
            leftstr = StringVal(getrandstr())

        if(self.my_is_arithm(right)):
            rightstr = IntToStr(ToInt(right))
        elif(self.my_is_string(right)):
            rightstr = right
        else:
            rightstr = StringVal(getrandstr())


        return leftstr + rightstr
    
    def testExpr_BinaryOp_Div(self, expr): # should ensure non-zero
        left = self.testallsmt(expr['left'], 2) 
        right = self.testallsmt(expr['right'], 2)

        if is_arith(left) and is_arith(right):
            return left / right
        return IntVal(getrandint())
    
    def testExpr_BinaryOp_Identical(self, expr): # should consider the type.
        left, right = self.funchandler(expr)
        if self.gettype(left) == self.gettype(right):
            return left ==  right
        return False

    def testExpr_BinaryOp_NotIdentical(self, expr): # should consider the type.
        left, right = self.funchandler(expr)
        if self.gettype(left) == self.gettype(right):
            return left != right
        return True
    

    
    def testExpr_BinaryOp_Spaceship(self, expr): # @todo
        '''
        eturn 0 if values on either side are equal
        Return 1 if value on the left is greater
        Return -1 if the value on the right is greater
        '''
        return IntVal(1) #not true
    
    
    def testScalar(self, expr):
        typeofexpr = expr.get('nodeType')
        if typeofexpr == 'Scalar_LNumber':
            return expr['value']
        elif typeofexpr == 'Scalar_DNumber':
            return Real(expr['value'])
        elif typeofexpr == 'Scalar_String':
            return StringVal(expr['value'])
        else:
            print("Unknown Scalar")
            return True
        return True
    
    def testfunc1(self, expr, ExType): # test
        print('come into testfunc func11 ')
        #### change expr from func to variable @todo
        '''
        varname = getrandstr(10)
        expr['nodeType'] = 'Expr_Varible'
        expr['name'] = varname
        expr['attributes'] = {'startLine':0, 'endLine':0}
        
        return self.testallsmt(expr, ExType)
        '''
        
        

        # codes below not used currently
        name = expr['name']
        if name['nodeType'] == 'Identifier':
            funcname = name['name']
        else:
            funcname = ''.join(expr['name']['parts']) #[0] #bugnumber1

        ####  get arguments first
        args = []
        typeofargs = []
        idx = 0
        while(idx < len(expr['args'])):
            arg = expr['args'][idx]['value']
            t = self.testallsmt(arg, 7)
            args.append(t)
            typeofargs.append(self.gettype(arg))
            idx += 1
        return [typeofargs, args]


    def testfunc(self, expr, ExType): # test
        '''
        name:{
            "nodeType":"Name"
            "parts":{
                    "f"
            }
            "args":[
            { // arg 1
                "nodeType":"Arg"
                "value":{
                ...
                }
            },
            
            { // arg 2
                "nodeType":"Arg"
                "value":{
                    "nodeType":"Scalar_LNumber"
                    
                }
            }
            ]
        }
        '''
        # add dynamic declare here

        print('come into testfuncfunc ')
        name = expr['name']
        if name['nodeType'] == 'Identifier':
            funcname = name['name']
        else:
            funcname = expr['name']['parts'][0] #bugnumber1

        ####  get arguments first
        args = []
        typeofargs = []
        strtypeofargs = []
        idx = 0
        while(idx < len(expr['args'])):
            arg = expr['args'][idx]['value']
            t = self.testallsmt(arg, 7)
            strtypeofargs.append(str(self.gettype(arg)))
            args.append(t)
            typeofargs.append(self.gettype(arg))
            idx += 1


        funckey = 'Return' + str(ExType) + '_' +  '_'.join(strtypeofargs)
        if funcname not in self.SFuncs:
            self.SFuncs[funcname] = {}

        if funckey not in self.SFuncs[funcname]:
            self.SFuncs[funcname][funckey] = self.declarefunc1(funcname, funckey, ExType, typeofargs)

        #print(funcname, funckey, ExType)
        
        func = self.SFuncs[funcname][funckey]
        return self.runphp(funcname, funckey, args, typeofargs) # run php to get the values

        # however, the arguments can be other functions, so the return 
        # read and store into SFuncs

        #for arg in args:
            #print(type(arg))
        #print(type(func))
        return func(args)

        '''
        if self.NumofArgFuncs[funcname] == 0:
            return func()
        elif self.NumofArgFuncs[funcname] == 1:
            print(expr['args'])
            print(funcname, type(func), type(args[0]))
            #print(type(func(args[0])))
            return func(args[0])
        elif self.NumofArgFuncs[funcname] == 2:
            print(expr['args'][1])
            print(funcname, type(func), type(args[0]), type(args[1]))
            return func(args[0], args[1])
        elif self.NumofArgFuncs[funcname] == 3:
            return func(args[0], args[1], args[2])
        elif self.NumofArgFuncs[funcname] == 4:
            return func(args[0], args[1], args[2], args[3])
        else:
            print("Other number of arguments\n")
            return None
        '''

    def declarefunc1(self, funcname, funckey, returntype, argtypes):
        functionname = funcname + '_' + funckey
        sortlist = []
        for argtype in argtypes:
            sortlist.append(self.getsortbynum(argtype))
        sortlist.append(self.getsortbynum(returntype))
        return Function(functionname, sortlist)

    def getsortbynum(self, num):
        if num == None:
            return NewSort
        if num == 1:
            return BoolSort()
        elif num == 2:
            return RealSort()
        elif num == 4:
            return StringSort()
        else:
            return StringSort() #add
            return NewSort
    
    def getvar(self, name, Type):
        print('in get var?')
        print(name, Type)
        if Type == 2:
            return Real(name)
        elif Type == 4:
            return String(name)
        elif Type == 1:
            return Bool(name)
        else:
            print('ERROR: Type: ', Type, 'Undefined')
            return String(name) #add
            return Const(name, NewSort)
        

    def unite(self, visitcon, visitvar):
        for var in self.Vars:
            if self.Vars[var] in [1,2,4] and var not in visitvar and var in self.Var2Container:
                visitvar.append(var)
                # propagate to other containers
                for con in self.Var2Container[var]:
                    if con not in visitcon:
                        visitcon.append(con)
                        for ivar in self.Container2Var[con]:
                            self.Vars[ivar] = self.Vars[var]
                            if ivar not in visitvar:
                                self.unite(visitcon, visitvar)


    # Other left should be assigned with type 7, and then use the default type
    def unitearg(self):
        for arg in self.Arg2Vars:
            Vars = self.Arg2Vars[arg]
            mintype = min(7, self.Vars[arg])
            for var in Vars:
                if var in self.Vars:
                    tmp = self.Vars[var]
                    mintype = min(mintype, tmp)
            self.Vars[arg] = mintype


        
    def gettype(self, cst):
        if type(cst) == bool or type(cst) == BoolRef:
            return 1
        elif type(cst) == int or is_arith(cst) == True:
            return 2
        elif type(cst) == str or is_string(cst) == True:
            return 4 
        elif type(cst) == ArithRef:
            return 2
        elif type(cst) == ExprRef:
            return 7
        elif cst == None:
            return 7

        typeofcst = cst['nodeType']
        if typeofcst == 'Stmt_Expression':
            return 1

        elif 'Expr_BinaryOp_Logical' in typeofcst:# Act on Logical Operations, including and,xor,or.
            return 1

        elif 'Expr_BinaryOp_Boolean' in typeofcst:
            return 1

        elif typeofcst == 'Expr_BinaryOp_Plus':
            return 2

        elif typeofcst == 'Expr_BinaryOp_Pow':
            return 2

        elif typeofcst == 'Expr_BinaryOp_ShiftLeft':
            return 2

        elif typeofcst == 'Expr_BinaryOp_ShiftRight':
            return 2

        elif typeofcst == 'Expr_BinaryOp_Mod':
            return 2

        elif typeofcst == 'Expr_BinaryOp_Mul':
            return 2

        elif typeofcst == 'Expr_BinaryOp_Div':
            return 2
        
        elif typeofcst == 'Expr_BinaryOp_Minus':
            return 2

        elif typeofcst == 'Expr_BinaryOp_Greater' or typeofcst == 'Expr_BinaryOp_GreaterOrEqual' or\
            typeofcst == 'Expr_BinaryOp_Smaller' or typeofcst == 'Expr_BinaryOp_SmallerOrEqual' or \
            typeofcst == 'Expr_BinaryOp_Equal' or  typeofcst == 'Expr_BinaryOp_NotEqual' or\
            typeofcst == 'Expr_BinaryOp_Identical' or typeofcst == 'Expr_BinaryOp_NotIdentical':
            return 1
        elif typeofcst == 'Expr_Empty' :
            return self.gettype(cst['expr'])

        elif typeofcst == 'Expr_Variable':
            varname = cst['name']
            vartype = self.Vars.get(varname)
            if not vartype:
                return 7
            return vartype
        elif typeofcst == 'Expr_ArrayDimFetch': # the var/dim should be string already!!!
            var = cst['var']
            dim = cst['dim']
            varname = "ARRAY_" + var['name'] + "_" + dim['value'] # rename arraydimfetch 
            vartype = self.Vars.get(varname)
            if not vartype:
                return 7
            return vartype

        elif 'Scalar' in typeofcst: # Act on Scalars, including numbers and strings.
            if typeofcst == 'Scalar_LNumber':
                return 2 # todo
            elif typeofcst == 'Scalar_DNumber':
                return 2
            elif typeofcst == 'Scalar_Bool':
                return 1
            elif typeofcst == 'Scalar_String':
                return 4
            else:
                print("ERROR: Uncatched Scalar Tpye :", typeofcst )
                return 7
        
        elif typeofcst == 'Expr_FuncCall':
            return 7 # for function call now 
        elif typeofcst == 'Expr_ConstFetch':
            #print(cst['name'])
            namepart = cst['name']
            if namepart['nodeType'] == 'Name':
                constname = namepart['parts'][0]
                if constname == 'null' or constname == "NULL":
                    return 0
                elif constname == 'True' or constname == 'false':
                    return 1
                elif constname == 'False' or constname == 'false':
                    return 1
            else:
                print("ConstFetch is not standard")
            return 1 # assume bool  type for true or false

        elif typeofcst == 'Expr_BooleanNot':
            return 1
        elif typeofcst == 'Expr_Cast_String':
            return 4
        elif typeofcst == 'Expr_Isset':
            return 1
        else:
            print('=====gettype-> Unsupported type', typeofcst)
            return 7
        return 7

    # return function 
    def funchandler(self, expr):
        print("come into funchandler")
        lfuncinfo = None
        rfuncinfo = None
        if expr['left']['nodeType'] == 'Expr_FuncCall':
            lfuncinfo = self.testfunc1(expr['left'], 7)
        else:
            left = self.testallsmt(expr['left'], 7)

        if expr['right']['nodeType'] == 'Expr_FuncCall':
            rfuncinfo = self.testfunc1(expr['right'], 7)
        else:
            right = self.testallsmt(expr['right'], 7)

        if not lfuncinfo and not rfuncinfo:
            return [left, right]
        elif not lfuncinfo and rfuncinfo != None: # right hand is function
            ltype = self.gettype(left)
            # declare in ltype
            #rfuncinfo is array of argtypes
            typeofargs = rfuncinfo[0]
            args = rfuncinfo[1]
            funcname = expr['right']['name']['parts'][0] 
            funckey = 'Return' + str(ltype) + '_' +  '_'.join([str(i) for i in typeofargs])
            if funcname not in self.SFuncs:
                self.SFuncs[funcname] = {}

            if funckey not in self.SFuncs[funcname]:
                self.SFuncs[funcname][funckey] = self.declarefunc1(funcname, funckey, ltype, typeofargs)

            r = self.runphp(funcname, funckey, args, typeofargs)
            return [left, r]

            func = self.SFuncs[funcname][funckey]
            return [left, func(args)]

        elif not rfuncinfo and lfuncinfo != None: # left hand is function
            rtype = self.gettype(right)
            typeofargs = lfuncinfo[0]
            args = lfuncinfo[1]
            funcname = expr['left']['name']['parts'][0] 
            funckey = 'Return' + str(rtype) + '_' +  '_'.join([str(i) for i in typeofargs])
            if funcname not in self.SFuncs:
                self.SFuncs[funcname] = {}

            if funckey not in self.SFuncs[funcname]:
                print("declare function with funckey",funckey)
                self.SFuncs[funcname][funckey] = self.declarefunc1(funcname, funckey, rtype, typeofargs)
            l = self.runphp(funcname, funckey, args, typeofargs)
            #print('run php')
            #print(l)
            return [l, right]

            func = self.SFuncs[funcname][funckey]
            return[func(args), right]
        else: # both functions ,then set them to 7
            rtype = ltype = 7
            typeofargs = lfuncinfo[0]
            args = lfuncinfo[1]
            funcname = expr['left']['name']['parts'][0] 
            funckey = 'Return' + str(rtype) + '_' +  '_'.join([str(i) for i in typeofargs])
            if funcname not in self.SFuncs:
                self.SFuncs[funcname] = {}

            if funckey not in self.SFuncs[funcname]:
                print("declare function with funckey",funckey)
                self.SFuncs[funcname][funckey] = self.declarefunc1(funcname, funckey, rtype, typeofargs)
            lfunc = self.SFuncs[funcname][funckey]
            l = self.runphp(funcname, funckey, args, typeofargs)

            typeofargs = rfuncinfo[0]
            args = rfuncinfo[1]
            funcname = expr['right']['name']['parts'][0] 
            funckey = 'Return' + str(ltype) + '_' +  '_'.join([str(i) for i in typeofargs])
            if funcname not in self.SFuncs:
                self.SFuncs[funcname] = {}

            if funckey not in self.SFuncs[funcname]:
                self.SFuncs[funcname][funckey] = self.declarefunc1(funcname, funckey, ltype, typeofargs)
            rfunc = self.SFuncs[funcname][funckey]
            r = self.runphp(funcname, funckey, args, typeofargs)
            return [l, r]


            return [lfunc, rfunc]

    def runphp(self, funcname, funckey, args, types):
        # coming to declarefunc1 with
        # funcname, funckey, extype, typeofargs
        types = [str(t) for t in types]
        targs = []
        l = len(args)
        params = {}
        for i in range(l):
            v = translatesinglevalue(args[i])
            t = types[i]
            t = {'type': t, 'val': str(v)}
            params[i] = t
        param_dump = json.dumps(params).replace(' ', '')
        #print(param_dump)
        f = open('args/' + funcname + 'args' , 'w+')
        f.write(param_dump)
        f.close()


        #args = [str(translatesinglevalue(a)) for a in args]
        jointypes = ' '.join(types)
        joinargs = ' '.join(targs)

        command = ['php', 'phpfunc.php', funcname, str(len(args)), param_dump]
        joincommand = ' '.join(command)

        #os.system(joincommand)
        output = subprocess.check_output(joincommand, stderr=subprocess.STDOUT, shell=True)
        output = output.decode('utf-8')
        output = output.rstrip('\n')
        #print(output)
        return parseoutput(output)



def parseoutput(expr):
    if expr[0:3] == 'int':
        l = expr.find('(')
        r = expr.find(')')
        return IntVal(int(expr[l + 1:r]))
    if expr[0:4] == 'bool':
        l = expr.find('(')
        r = expr.find(')')
        val = expr[l + 1: r]
        if val.lower() == 'false'.lower() or val.lower() == '' or val.lower() == '0':
            return False
        else:
            return True

def translatesinglevalue(value):
    if is_true(value):
        return True
    elif is_false(value):
        return False
    elif is_int_value(value):
        return value.as_long()
    elif is_rational_value(value):
        return float(value.numerator_as_long()) / float(value.denominator_as_long())
    elif is_string_value(value):
        return value.as_string() 
    else:
        return False



    return True

def translatesolution(solution):
    keys = list(solution)
    sol = {}
    for key in keys:
        value = translatesinglevalue(solution[key])
        sol[str(key)] = value
    return sol

def manultest():
    s = Solver()
    #print(data)
    try:
        reader = json.loads(data)
    except:
        return [0,0] 
    if type(reader) == list:
        reader = reader[0]
    #print(reader)
    parser = parse2smt()
    parser.scanvartypes(reader, 1)
    #print(reader)
    parser.unite([],[])
    parser.unitearg()

    parser.printvartypes()

    parser.ContainerIndex = 0
    #parser.scanvartypes(reader[0]['expr'], 1)
    r = parser.convert2smt(reader, 7) # haven't declare uninterpreted functions.
    s.add(r)
    Vars = {}

    ############## define two varaibles
    alphabet = string.printable
    SIZEOF_ALPHABET = len(alphabet)

    if s.check() == sat:
        solution = s.model()
        print(solution)
        keys = list(solution)
        sol = translatesolution(solution) # sol is a dict
        result = json.dumps(sol)
        f = open('results.txt', 'w+')
        f.write(result)
        f.close()
        tsol = {}
        for k in keys:
            tsol[str(k)] = solution[k]
        tr = parser.test1(reader, tsol)
        #print(tr)
        ts = Solver()
        ts.add(tr)
        if ts.check() == sat:
            print("really??? sat ??? ====")
            tsolution = ts.model()
            tsol = translatesolution(tsolution)
            result = json.dumps(tsol)
            f = open('result1.txt', 'w+')
            f.write(result)
            f.close()
            reutrn [1, 1]
        else:
            return [1, 0]

    else:
        print('not sat')
        return [0, 0]

resultdir = '/data/cpu_dos_data/results_cs'
NewSort = DeclareSort('NewSort')

def start_eachsink(filename):
    #filename = 'cst1.txt'
    try:
        #f = open('../output/csts_0.txt', 'r')
        #os.system('php dump.php')
        #f = open('constraints.txt', 'r')

        #data = f.read()
        print(filename)
        f = open(filename, 'r')
        data = f.read()
    except IOError:
        print("Could not read file ")
        sys.exit()
    with f:
        paths = data.split('----------')
        r = []
        for data in paths:
            if data != '' and data != '\n' and data != '\n\n':
                t = tmpfunc(data)
                r.append(t)
        #f = open(resultdir + '/' + filename.replace('/', ''), 'w+')
        #f.write(str(r))
        #f.close()
        return str(r)
    
def tmpfunc(data):
    eachnode = data.split('==========')
    nodes = []
    for n in eachnode:
        if n != '' and n != '\n' and n != '\n\n' and n != '\n\n\n':
            nodes.append(n)
    s = Solver()
    storereader = []
    parser = parse2smt()
    for data in nodes:
        #print(data)
        try:
            reader = json.loads(data)
        except:
            return [0,0]
        if type(reader) == list:
            reader = reader[0]
        #print(reader)
        parser.scanvartypes(reader, 1)
        #print(reader)
        parser.unite([],[])
        parser.unitearg()

        parser.printvartypes()

        parser.ContainerIndex = 0
        #parser.scanvartypes(reader[0]['expr'], 1)
        r = parser.convert2smt(reader, 7) # haven't declare uninterpreted functions.
        storereader.append(reader)
        print(type(r))
        if(is_bool(r)):
            s.add(r)
    Vars = {}

    ############## define two varaibles
    alphabet = string.printable
    SIZEOF_ALPHABET = len(alphabet)
    ##############
    if s.check() == sat:
        #return True
        print("=================================")
        solution = s.model()
        print(solution)
        keys = list(solution)
        sol = translatesolution(solution) # sol is a dict
        result = json.dumps(sol)
        tsol = {}
        for k in keys:
            tsol[str(k)] = solution[k]

        ts = Solver()
        for reader in storereader:
            tr = parser.test1(reader, tsol)
            print("finisheed")
            print(tr)
            print(type(tr))
            if(is_bool(tr)):
                ts.add(tr)

        if ts.check() == sat:
            print("really??? sat ??? ====")
            tsolution = ts.model()
            tsol = translatesolution(tsolution)
            result = json.dumps(tsol)
            #f = open('result1.txt', 'w+')
            #f.write(result)
            #f.close()
            return [1, 1]
        return [1, 0]

    else:
        print('not sat')
        return [0, 0]

constraints_dir = '/data/cpu_dos_data/results' 

def start_init(folderlist):
    for folder in folderlist:
        files = os.listdir(constraints_dir + '/' + folder)
        for f in files:
            if '.txt' in f and '.txt.hr' not in f and ('loop-' in f or 'callsite-' in f):
                print(f)
                try:
                    start_eachsink(constraints_dir  + '/' + folder  + '/' + f)
                except:
                    continue
def writecst(loc, contents):
    f = open(loc, "w+")
    f.write(contents)
    f.close()

def start_rec(folder): # folder is already in abs path
    files = os.listdir(folder)
    for f in files: # source, paths, log
        if f[-7: ]  == '.result':
            os.remove(folder + f)
            continue
        #if os.path.exists(folder + f + '-'):#means it has a callsite and its corresponding folder
        if f + '-' in files:#means it has a callsite and its corresponding folder
            t = "visited foler" +  folder + f + '-\n'
            #with open('resultvisit', "a+") as myfile:
            #    myfile.write(t)
            
            # solve f, and then see if
            re = start_eachsink(folder + f)
            writecst(folder + f + '.result', re)

            start_rec(folder + f + '-' + '/')
        elif 'loop' in f and '.hr' not in f and '.php' not in f: # it is a loop file
            t = "visited " +  folder + f + '\n'
            #with open('resultvisit', "a+") as myfile:
            #    myfile.write(t)
            re = start_eachsink(folder + f) # still analyze it
            writecst(folder + f + '.result', re)

        elif f[-1:]  == '-' or f[-3: ] == '.hr' or f[-4: ] == '.php':
            continue
        else:
            re = start_eachsink(folder + f)
            writecst(folder + f + '.b.result', re) # write builtin functions
            # callsite without folder, terminating callsite/builtin folder



    return

def startall_rec(folderlist):
    for folder in folderlist:
        start_rec(constraints_dir + '/' + folder + '/')

if __name__ == '__main__':
    #os.system('php dump.php > constraints.txt') # execute dump.php into constraints.txt
    #dirs = os.listdir('/data/cpu_dos_data/results/')
    dirs = os.listdir(constraints_dir)
    np = int(sys.argv[1])
    eachps =  int(len(dirs) / np)
    starts = {}
    for i in range(np):
        starts[i] = eachps * i
    starts[np] = len(dirs)

    processes = {}
    for i in range(np):
        processes[i] = Process(target=startall_rec, args=(dirs[starts[i]: starts[i + 1]], ))
        processes[i].start()

    for i in range(np):
        processes[i].join()
