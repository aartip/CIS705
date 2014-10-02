
### INTERPRETER FOR OBJECT-ORIENTED LANGUAGE

"""The interpreter processes parse trees of this format:

PTREE ::=  DLIST CLIST
DLIST ::=  [ DTREE* ]
DTREE ::=  ["int", ID, ETREE]  |  ["proc", ID, ILIST, DLIST, CLIST]  |  ["ob", ID, ETREE]  |  ["class", ID, TTREE]
CLIST ::=  [ CTREE* ]
CTREE ::=  ["=", LTREE, ETREE]  |  ["if", ETREE, CLIST, CLIST]
        |  ["print", ETREE]  |  ["call", LTREE, ELIST]
ELIST ::=  [ ETREE* ]
ETREE ::=  NUM  |  [OP, ETREE, ETREE] |  ["deref", LTREE]  |  "nil"  |  ["new", TTREE]
      where  OP ::= "+" | "-"
TTREE ::=  ["struct", DLIST]  |  ["call", LTREE]
LTREE ::=  ID  |  ["dot", LTREE, ID]

NUM   ::=  a nonempty string of digits
IDLIST ::=  [ ID+ ]
ID    ::=  a nonempty string of letters

The interpreter computes the meaning of the parse tree, which is
a sequence of updates to heap storage.

You will extend the above to include declarations and calls of parameterized
procedures.
"""


from heapmodule import *   # import the contents of the  heapmodule.py  module 


### INTERPRETER FUNCTIONS, one for each class of parse tree listed above.
#   See the end of program for the driver function,  interpretPTREE


def interpretPTREE(tree) :
    """interprets a complete program tree
       pre: tree is a  PTREE ::= [ DLIST, CLIST ]
       post: heap holds all updates commanded by the  tree
    """
    initializeHeap()
    interpretDLIST(tree[0])
    interpretCLIST(tree[1])
    print "Successful termination."
    printHeap()


def interpretDLIST(dlist) :
    """pre: dlist  is a list of declarations,  DLIST ::=  [ DTREE+ ]
       post:  memory  holds all the declarations in  dlist
    """
    for dec in dlist :
        interpretDTREE(dec)


def interpretDTREE(d) :
    """pre: d  is a declaration represented as a DTREE:
       DTREE ::=  ["int", ID, ETREE]  |  ["proc", ID, ILIST, DLIST, CLIST]  |  ["ob", ID, ETREE]  |  ["class", ID, TTREE]
       post:  heap is updated with  d
    """
    # pass
    if not d :
        pass
    else : 
        operator = d[0]
        if operator == "int" : 
            # compute the value of E in the active namespace
            # bind I to E's value in the active namespace
            declare(activeNS(), d[1], interpretETREE(d[2]))
        elif operator == "proc" :
            if isLValid(activeNS(), d[1]) :
                crash(d, "redeclaration error")
            else :
                newNS = allocateNS()
                # bind I to the handle of a newly allocated closure
                declare(activeNS(), d[1], newNS)
                declare(newNS, "params", d[2])
                declare(newNS, "locals", d[3])
                declare(newNS, "body", d[4])
                declare(newNS, "type", "proc")
                declare(newNS, "link", activeNS())
        elif operator == "ob" :
        	# computes the meaning of E
        	rval = interpretETREE(d[2])
        	# validate that E is either a handle to an object or is nil
        	if isLValid(heap, rval) or (rval == nil) :         		
        		# binds I to the meaning in the active namespace (provided that I is not declared there)
        		if isLValid(activeNS(), rval) : 
        			crash (d, "redeclare object")
        		else :
        			declare(activeNS(), d[1], rval)
        	else :
        		crash (d, "invalid obj declaration")
        elif operator == "class" :
            # I is bound to a closure containing T and its link to global variables
            newNS = allocateNS()
            declare(activeNS(), d[1], newNS)
            declare(newNS, "body", d[2])
            declare(newNS, "type", "class")

        else :
            crash(d, "invalid declaration")

def interpretCLIST(clist) :
    """pre: clist  is a list of commands,  CLIST ::=  [ CTREE+ ]
                  where  CTREE+  means  one or more CTREEs
       post:  memory  holds all the updates commanded by program  p
    """
    for command in clist :
        interpretCTREE(command)


def interpretCTREE(c) :
    """pre: c  is a command represented as a CTREE:
       CTREE ::=  ["=", LTREE, ETREE]  |  ["if", ETREE, CLIST, CLIST2] 
        |  ["print", LTREE] | LTREE, ETREE |
       post:  heap  holds the updates commanded by  c
    """
    operator = c[0]
    if operator == "=" :   # , ["=", LTREE, ETREE]
        handle, field = interpretLTREE(c[1])  # returns (handle,field) pair
        rval = interpretETREE(c[2])
        update(handle, field, rval)
    elif operator == "print" :   # ["print", LTREE]
        print interpretETREE(c[1])
        printHeap()
    elif operator == "if" :   # ["if", ETREE, CLIST1, CLIST2]
        test = interpretETREE(c[1])
        if test != 0 :
            interpretCLIST(c[2])
        else :
            interpretCLIST(c[3])

    elif operator == "call" :   # call command, ["call", L, EL]
        # Compute the meaning of L, verify that the meaning is the handle to a procedure closure
        handle, field = interpretLTREE(c[1])
        procedureHandle = lookup(handle, field)
        # extract from that closure these parts: IL, DL, CL, and parentns link
        paramsList = lookup(procedureHandle, "params")
        localvars = lookup(procedureHandle, "locals")
        body = lookup(procedureHandle, "body")
        link = lookup(procedureHandle, "link")
        # evaluate EL to a list of values
        inputList = []
        for expression in c[2] :
        	inputList.append(interpretETREE(expression))

        # Allocate a new namespace
        newNS = allocateNS()

        # Within the new namespace, bind parentns to the handle extracted from the closure
        declare(newNS, "parentns", link)

        # Make certain that the number of arguments in EL equals the number of parameters in IL
        if len(inputList) == len(paramsList) : 
            # bind the values from EL to the corresponding names in IL
            iteration = 0
            while iteration < len(inputList) :
                    declare(newNS, paramsList[iteration], inputList[iteration])
                    iteration = iteration + 1

        # Otherwise, it's an error that prints a message and stops execution
        else : 
            crash(c, "Parameter error")

        # Push the new namespace's handle onto the activation stack
        push(newNS)

        # execute DL
        interpretDLIST(localvars)
        # execute CL
        interpretCLIST(body)
        # pop the activation stack
        pop()



    else :  crash(c, "invalid command")

def interpretETREE(etree) :
    """interpretETREE computes the meaning of an expression operator tree.
         ETREE ::=  NUM  |  [OP, ETREE, ETREE] |  ["deref", LTREE]  |  "nil"  |  ["new", TTREE] 
         OP ::= "+" | "-"
        post: updates the heap as needed and returns the  etree's value
    """
    if isinstance(etree, str) and etree.isdigit() :  # NUM  -- string of digits
      ans = int(etree) 
    elif  etree[0] in ("+", "-") :    # [OP, ETREE, ETREE]
        ans1 = interpretETREE(etree[1])
        ans2 = interpretETREE(etree[2])
        if isinstance(ans1,int) and isinstance(ans2, int) :
            if etree[0] == "+" :
                ans = ans1 + ans2
            elif etree[0] == "-" :
                ans = ans1 - ans2
        else : crash(etree, "addition error --- nonint value used")
    elif  etree[0] == "deref" :    # ["deref", LTREE]
        handle, field = interpretLTREE(etree[1])
        ans = lookup(handle,field)
    # implement "nil" to have itself as its value
    elif etree[0] == "nil" :
        ans = "nil"
    # implement ["new", T] to call interpretTTREE(T), whose job is to allocate an object, fill it with T, and return the object's handle
    elif etree[0] == "new" :
        ans = interpretTTREE(etree[1])
    else :  crash(etree, "invalid expression form")
    return ans

def interpretTTREE(ttree) :
	"""interpretTTREE computes the meaning of a template tree
		 TTREE ::=  ["struct", DLIST]  
	   post: returns the popped handle as its value
	"""
	# allocates a new namespace and pushes the namespace's handle on the activation stack
	newNS = allocateNS
	push(newNS)

	# evaluate DLIST
	interpretDLIST(ttree[1])

	# pops the activation stack and returns the popped handle as its answer
	return pop();



def interpretLTREE(ltree) :
    """interpretLTREE computes the meaning of a lefthandside operator tree.
          LTREE ::=  ID  |  ["dot", LTREE, ID]
       post: returns a pair,  (handle,varname),  the L-value of  ltree
    """
    # compute the handle name by L, call it h
    if ltree[0] == "dot" :
    	h = interpretLTREE(ltree[1])
    	if isLValid(h, ltree[2]) :
    		ans = (h, ltree[2])
    	else :
    		crash(ltree, "cannot find variable in object")
    elif isinstance(ltree, str) and  ltree[0].isalpha()  :  #  ID 
        
        # uses a loop to follow the parentns links to locate nonlocal variables
        currentNS = activeNS()
        while not isLValid(currentNS, ltree) : 
            currentNS = lookup(currentNS, "parentns")
        ans = (currentNS, ltree)

    else :
        crash(ltree, "illegal L-value")
    return ans

def crash(tree, message) :
    """pre: tree is a parse tree,  and  message is a string
       post: tree and message are printed and interpreter stopped
    """
    print "Error evaluating tree:", tree
    print message
    print "Crash!"
    printHeap()
    raise Exception   # stops the interpreter




