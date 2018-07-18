from classes import WORD
import copy
import re

from var import VAR
mypattern = re.compile("^[A-Z0-9]+$")
count = 0

def myscan(nlist, mylist = None):
    if mylist == None:
        mylist = copy.deepcopy(nlist)
    for i, num in enumerate(nlist):
        if isinstance(nlist[i], WORD):
            #mylist[i] = nlist[i].form
            #This version will find the VAR
            if matchpattern(nlist[i].form):
                global count
                count = count+1
                form = nlist[i].form
                mylist[i] = VAR("%s%s"%(form,count)) #VAR("%s%s"%(nlist[i].form,count))
            else:
                mylist[i] = nlist[i].form
        if isinstance(nlist[i], list):
            myscan(nlist[i], mylist[i])
    return mylist 

def matchpattern(s):
    result = mypattern.match(s)
    return result

#nl = ['a', 'b',['c','dc',['d']],'a',['c',['g']]], ['b']],'a',['a']]
