"""
INFERENCE.PY

This is an extended version of the match.py that we were looking at
last week. It includes a matcher which is very similar to the one we
were looking at and also a version of the inference engine, to
illustrate how we manage the fact that we have two components each of
which may need to do backtracking. There's a fairly complicated bit
for reading rules which have been written in a nice readable format
and converting them into instances of the class RULE which you don't
really want to look at. I've exported that to a separate file,
readrules.py, which is imported by this one, to make it easy to
ignore. The properties of RULEs are important, how we read them is not
(because when we start working with dependency trees we will get them
by a different mechanism anyway: this file for now is just to show the
principles of the inference engine).

We use continuations to manage backtracking, and yield to get results,
as before:

  Using continuations: the continuation is an encapsulation of "what I
  want you to do once you've finished your immediate task". *Returning*
  from a function means you haven't got any new ways of working out how
  to do the immediate task.

  Using yield turns your function into a generator, in other words into
  something which you can iterate over or get the "next" element of. We
  make make match and prove into generators, i.e. into tings that
  generate successive solutions. The important thing about a generator
  is that it remembers the state of the computation when it last yielded
  an answer, so we can resume it from exactly where we were.

"""

"""
We want to write rules in a reasonably standard reasonably readable
format. Something like "p(X, Y) ==> q(X, Y)". But we need them
represented as datastructures of type RULE, where a RULE has a
consequent (the "then"-part) and an antecedent (the "if"-part), where
each of these is a nested list containing VARiables where
necessary. So we need something which will turn a string like "f(b,
c(X, p(Y)))" into a list like ['f', 'b', ['c', #X, ['p', #Y]]]. This
is complicated without being terribly interesting, so I've put it into
a separate file: it is important to know why we want to do this, and
to know what the lists that are produced are like, but not necessarily
to know how.
"""

from nltk.corpus import wordnet
from var import VAR
from readrules import readRule, readTerm, VCOUNT
from myreadRule import myRead

def myreadRules(parser, rules):
    return [RULE(myRead(parser, r)) for r in rules.split(";")]

def readRules(s):
    return [RULE(readRule(r)) for r in s.split(";")]


def hashRules(strrules):
#    rules = readRules(strrules)
    rules = strrules
    dic = dict()
    for r in rules:
        #for the hypernyms of the consequent of the rule
        for h in supersets(r.consequent[0]):
            consequent1 = [h]+r.consequent[1:]
            r1 = RULE((consequent1, r.antecedent))
            h = "%s-%s"%(h, len(r.consequent)-1)
            if h in dic.keys():
                #if h in the hashtable and have no antecedent, it is a fact.
                if r1 not in dic[h]:
                    dic[h].append(r1)
            else:
                dic[h] = [r1]
    return dic

def supersets(w, seen=None, words=None, indent=''):
    if seen is None:
        seen = set()
        words = set([w])
        w = wordnet.synsets(w)
    for s in w:
        if not s in seen:
            seen.add(s)
            for l in s.lemmas():
                l = l.name()
                if not l in words:
                    words.add(l)
            supersets(s.hypernyms(), seen=seen, words=words, indent=indent+' ')
    return words

class RULE:
    """
    We want a representation of rules, for which we introduce a class
    called RULE.  You write a rule as something like RULE("p(X) & q(X, Y) & r(Y) ==>
    s(X)").

    The constructor splits this at ==>, splits the left-hand side at &
    and turns all the expressions into nested lists, and finally
    produces an object of type RULE with an antecedent and a
    consequent
    """

    def __init__(self, (consequent, antecedent)):
        self.consequent = consequent
        self.antecedent = antecedent

    def __repr__(self):
        return "%s ==> %s"%(self.antecedent, self.consequent)

"""
This is a little function that we use to set up the initial
continuation: when you've finished what you're doing, yield whatever
you were given as an argument. This will typically be a copy of the
original goal.

Why is that a sensible thing to yield as the result? Because the goal
will generally contain variables, which will be bound during the
course of a match or a proof, and seeing what they are bound to is a
significant part of why we asked to do the proof or match in the first
place.
"""
def done(s):
    yield "DONE %s"%(s)

"""
match has an extra argument, indent, which we use for indenting the
output nicely to try make what's going on clearer

The interesting bits are

- if they're variables, we dereference them before we do anything
  else. If either of them is still a variable after that then we know
  it's unbound, so we bind it to the other. If we subsequently run out
  of solutions in the continuation we then *unbind* it, since this
  attempted solution has failed and we don't want to continue with the
  assumption this variable should be bound to whatever we just bound
  it to

- if they're both non-empty lists: we try to match their heads and set
  "matching the tails and do the old continuation" of this call of
  match.

The matcher is not yet non-deterministic (i.e. doesn't need to be able
to do backtracking), so we don't actually need to use continuations
yet; but it's going to be once we start looking at dependency trees,
so we build in the capacity for backtracking now. Easier to include it
before we need it than to rewrite everything later to accommodate it.
"""

def match(x, y, indent, contn):
    print "%smatching %s and %s"%(indent, x, y)
    """
    doing dereferencing inside a try ... except ... does the test to
    see whether it's a variable and actually does the dereferencing
    all in one go. Python encourages yoy to use try ... except ... in
    this kind of way. It is actually *more* efficient than asking
    whether x is a VAR and then dereferencing it if it is
    """
    try:
        x = x.deref()
        print "%sdereferenced X to %s"%(indent, x)
    except:
        pass
    try:
        y = y.deref()
        print "%sdereferenced Y to %s"%(indent, y)
    except:
        pass
    if x == y:
        """
        Are they the same thing: in that case ask the continuation for
        all the solutions it can find
        """
        print "%s%s and %s are the same thing/equal"%(indent, x, y)
        for s in contn():
            yield s
    elif isinstance(x, VAR):
        print "%sbinding %s (X) to %s"%(indent, x, y)
        x.bind(y)
        print "%safter binding %s"%(indent, x)
        for s in contn():
            yield s
        x.unbind()
    elif isinstance(y, VAR):
        print "%sbinding %s (Y) to %s"%(indent, y, x)
        y.bind(x)
        print "%safter binding %s"%(indent, y)
        for s in contn():
            yield s
        y.unbind()
    elif isinstance(x, list) and isinstance(y, list) and len(x) == len(y):
        """
        Are they lists of the same length? If so, try to match the
        heads and set matching the tails as the continuation. Ask for
        all solutions and *yield* them.
        """
        for s in match(x[0], y[0], indent+" ", lambda: match(x[1:], y[1:], indent+" ", contn)):
            yield s
        """
        We get to here if we've seen all the solutions that arise from
        matching the head and then matching the tails and then trying
        the continuation.
        """
    """
    Get to here if there are no more ways to match X and Y. In simple
    cases, that means that we get to here if X and Y don't match, but
    there will be more interesting extensions.
    """
    print "%sfinished trying to match %s and %s"%(indent, x, y)

"""
Small program for testing the matcher. The important thing to note is
that it sets the initial continuation to be a function which just
prints something out. The thing it prints out looks really obvious,
but if variables have been bound during the match then it can be more
interesting than you expect.
"""

def testMatcher(x, y):
    for s in match(x, y, "", lambda: done("Solution '%s'='%s'"%(x, y))):
        print s

"""
prove works by looking through the set of rules to find one whose
consequent matches the goal (remember: matching is likely to involve
binding variables) and then trying to prove every element of the
antecedent. We deal with facts by making them into rules with emopty
antecedents. Then "trying to prove every element of the antecedent"
doesn't actually require us to to anything, i.e. a rule with an empty
antecedent can be used at any time without doing any work, i.e. it's a
fact.

prove is necessarily non-deterministic, because we may have several
rules whose consequents match our goal, but not all of them will have
provable antecendents. Consider the following example:

[] ==> a
[] ==> c
[a, b] ==> p
[a, c] ==> p

If I want to try to prove p, the first thing I will do is to try the
first rules. That will lead me to try to prove [a, b]. I try to find a
proof of a, which I can do because I've got [] ==> a, but then I'm
stuck, because I don't have anything that will let me prove. So I have
to *backtrack* to the point where I chose to use [a, b] ==> p and look
for another rule. This can happen quite deeply into a proof, so it's
tricky to manage it properly.

Again indent is just there to lay out the printing nicely
"""
def myprove(goal):
    F = "%s-%s"%(goal[0], len(goal)-1)
    return F


def prove(goal, rules, indent, contn):
    print "%sprove(goal=%s, rules=%s)"%(indent, goal, rules)
    print "%slook through rules %s to see if there's one that leads to %s"%(indent, rules, goal)
    F = "%s-%s"%(goal[0], len(goal)-1)
    '''
    for s in subsets(F):
    '''
    if F in rules.keys():

        for rule in rules[F]:
                print "%strying %s"%(indent, rule)
                """
                remember: every rule has an antecedent, but for ones that we
have thought of as "facts" the antecdent is
                empty, so the call of proveAll doesn't have a huge amount of
                work to do
                """
                for s in match(goal, rule.consequent, indent+" ", lambda: proveAll(rule.antecedent, rules, indent+" ", contn)):
                    yield s
    print "%stried every rule for %s (there may not have been any)"%(indent, goal)

def proveAll(goals, rules, indent, contn):
    if goals == []:
        for s in contn():
            yield s
    else:
        for s in prove(goals[0], rules, indent+" ", lambda: proveAll(goals[1:], rules, indent+" ", contn)):
            yield s

def testProve(goal, rules):
    global VCOUNT
    VCOUNT = 0
   # goal = readTerm(goal, {})
    #print(goal)
    for s in prove(goal, hashRules(rules), "", lambda: done(goal)):
        print s

"""
A couple of test sets: do

>>> testProve(goal0, rules0)

and

>>> testProve(goal1, rules1)

With any luck, examining the trace of what these do will help clarify
how everything works, and it will also make you think "That's doing a
lot of unnecessary work, I wonder if there are ways we could make it
all more efficient.
"""

rules0 = "a; c; a & b ==> p; a & c ==> p"
goal0 = "p"

rules1 = "f(b); f(c); h(0); f(X) ==> g(X); h(X) ==> g(X)"
goal1 = "g(X)"

"""
Task 1a: take the set of rules that arises from doing readRules(rules0)
or readRules(rules1) and turn them into a dictionary like

{"a0": [[] ==> a],
 "p0": [[a, b] ==> p, [a, c] ==> p]}


{"g1": [[f[X]] ==> g[X], [h[X]] ==> g[X]],
 ...}

Use this table in prove rather than a list of rules.

Task 1b: make prove use this table when we want to find the rules for
a specific goal.

Task 2: write a generator for getting all the synsets that correspond
to a given word or its subsets. (the things below a synset are its hyponyms:

>>> wordnet.synsets("man")[0].hyponyms()
wordnet.synsets("man")[0].hyponyms()
[Synset('adonis.n.01'), Synset('babu.n.01'), Synset('bachelor.n.01'), Synset('bey.n.01'), Synset('black_man.n.01'), Synset('boy.n.02'), Synset('boyfriend.n.01'), Synset('bull.n.02'), Synset('dandy.n.01'), Synset('ejaculator.n.01'), Synset('esquire.n.02'), Synset('eunuch.n.01'), ...

Task 3:

3a, 3b, 3c: take subsets and fix it so we've got things for calculating subsets *and* suoersets, and use one of them (almost certainly supersets) for calculating whether one word is a subset/superset of another

We have an indexed set of rules like

{"mortal": [[person(X)] ==> mortal(X)],
 "volunteer": [[] ==> volunteer(John)]}

If these had looked like 

{"mortal": [[person(X)] ==> mortal(X)],
 "person": [[] ==> person(John)]}

then we would know how to use the index to get the right rule quickly.

We want to think about the indexing scheme so that when we want to prove person(John) we get to the [[] ==> volunteer(John)] rule quickly.

.

Task 4:
Either train a parser with

>>> parser = NLP.train()

or recover one with

>>> parser = NLP.load("parser.pck")

and do things like 

>>> parser.tagger.lexicon["X"] = {"PR":1}

for words we are very interested in that it gets wrong

4a: write something to convert the .dtree of the result of the parser into a nested list where the laves are words

>>> t = parser("the cat sat on the mat")
>>> t.dtree
[WORD(sat, VB, position=2), [WORD(cat, NN, position=1), [WORD(the, DT, position=0)]], [WORD(mat, NN, position=5), [WORD(on, IN, position=3)], [WORD(the, DT, position=4)]]]
>>> NLP.pretty(t.dtree)
[WORD(sat, VB, position=2), 
 [WORD(cat, NN, position=1), 
  [WORD(the, DT, position=0)]], 
 [WORD(mat, NN, position=5), 
  [WORD(on, IN, position=3)], 
  [WORD(the, DT, position=4)]]]

Turn this into

[sit, 
 [cat, 
  [the]], 
 [mat, 
  [on], 
  [the]]]

4b: given a string like "X loves Y ==> Y loves X" split it into "X loves Y" and "Y loves X" and parse both of them.

4c: try to to use what you got from 4b to make rules.

"""

"""
rule = "man(John); man(X) ==> handsome(X)"
goal = "handsome(John)"
"""
