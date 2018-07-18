
# X loves Y ==> Y loves X" split it into "X loves Y" and "Y loves X"
# Just for a single lhs
from nestedlist import myscan
from readrules import readTerm
#myparser():get the dependency tree, elements are WORD()
#myscan()  :change the dependency tree to word, element are words
#myRead()  :change a rule to two part (right, left), each part is a nestedlist


def myRead(parser, rule):
    vtable = {}
    try:
        lhs, rhs = rule.split("==>")
        lhs = [myscan(myparser(parser,l)) for l in lhs.split("&")]
        #lhs = [readTerm(myscan(mypraser(parser,l)),vtable) for l in  lhs.split("&")]
    except:
        lhs = []
        rhs = rule
    rhs = myscan(myparser(parser, rhs))
    return (rhs, lhs)

def myparser(parser, sentence):
    t = parser(sentence)
    return t.dtree

