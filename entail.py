# AI project 4. Logic inference agent 
# Author: Joshua Wang
# date: 11/29  2013 started 
import sys
from collections import defaultdict
import re
import os

def ReadKB(filename):
	result=[]
	try:
		KBfile=open(filename, "r")
		l=KBfile.readline().strip()

		while l:
			result.append(l)
			l=KBfile.readline().strip()
		KBfile.close()
	except IOError:
		print ("error, no such file as "+filename)
		sys.exit(1) 

	return result

def parsehornform(formula):
	fields=filter(None, formula.strip().split(" "))
	result=[[],"_NULL_"]

	if "=>" in fields:  #Implication form
		inconclusion=False
		for element in fields:
			if element=="^":
				pass
			elif element=="v" or element == "<=>" or element =="~":
				print ("error, input is not in horn form: v or ~ in Implication form or <=> exists" )
			elif element == "=>" and inconclusion ==False:
				inconclusion=True
			elif inconclusion==False:
				result[0].append(element)
			elif inconclusion==True:
				if result[1]=="_NULL_":
					result[1]=element
				else:
					print ("error, more than one variable in conclusion")
	else: #presumably Disjunction form, or fact
		for element in fields:
			if element=="v":
				pass
			elif element=="^" or element == "<=>" or element == "=>":
				print ("error, input is not in horn form: ^ or => in disjunctive form or <=> exists")
			elif "~" in element: # premise
				result[0].append(element[1:])
			else:
				if not result[1]== "_NULL_":
					print "error, more than two positive variable"
				else:
					result[1]=element  #fact will go here
	result=(tuple(result[0]), result[1])
	return result

def parseCNF(formula):
	all_clauses=filter(None, formula.strip().split("^"))
	result=[]
	for clause in all_clauses:
		clause=clause.strip()
		if clause[0]=="(" and clause[-1]==")": #a disjunction with ( )
			clause=clause[1:-1]
			literals=filter(None, clause.strip().split("v"))
			result+=[tuple([x.strip() for x in literals])]
		elif not re.search("^|V|=>|<=>", clause)==None: #an clause with one literal
			#print (clause)
			result+=[tuple([clause.strip()])]
		else:
			print "CNF input format error: ", clause
	return result









def forwardchaining(raw_KB, query):
	#declaration
	count=defaultdict(int)
	inferred=defaultdict(bool)
	printingresult=[]
	agenda=[]
	
	KBlist=[parsehornform(text) for text in raw_KB]
	#print KBlist
	#if query is false, KB can not entail unless it is in fact:
	if query[0]=="~":
		for clause in KBlist:
			if clause[0]==tuple([query[1:]]) and clause[1]=="_NULL_": # negative fact:
				printingresult+=["~"+clause[0][0]]
				return [True, printingresult]
		return [False, "_NEG_"]

	#initialization
	for clause in KBlist:
		count[clause]+=len(clause[0]) # set count
		for symbol in clause[0]:  # set inferred 
			inferred[symbol]=False
		inferred[clause[1]]=False #  inferred used for referring , so "_NULL_" does not matter

		if len(clause[0])==0 and not clause[1]=="_NULL_":  # for facts  
			agenda.append(clause[1])
			printingresult+=[clause[1]]  # start constructing printing result
		# set agenda
	#forward chaining
	while not len(agenda)==0:
		p=agenda.pop()
		if not inferred[p]:
			inferred[p]=True
			for c in [x for x in KBlist if p in x[0]]:
				count[c]-=1
				if count[c]==0: # all premise encountered
					printingresult+=[raw_KB[KBlist.index(c)]]
					
					if c[1]=="_NULL_":
						print "Note: KB is not consistent, thus it entails anything"
						return [True, printingresult]
					
					elif c[1]==query and not tuple([query]) in [ x[0] for x in KBlist if x[1]=="_NULL_"]:  # =_NULL_: contradiction in KB
						return [True, printingresult]

					agenda.append(c[1])
	return [False, "_UNSAT_"]

class backwardchaining(object):
	def __init__(self, rawlist, KBlist): # in constructor, initialize KB representation. record raw representation for output
		self.facts={}
		self.rules={}
		self.rawlist=rawlist # the raw representation for printing 
		self.printablefacts=set([]) # the facts that can be printed: inputed facts. remove once printed
		for i, clause in enumerate(KBlist):
			if len(clause[0])==0:
				self.facts[clause[1]]=i
				self.printablefacts.add(clause[1])
			else:
				self.rules[clause]=i
	
	def backward(self, query):
		
		inconsistentcheck=self.queryistrue("_NULL_", set())
		if inconsistentcheck[0]:
			print "Note: KB is not consistent, thus it entails anything"
			return inconsistentcheck
		
		elif query[0]=="~":
			for clause in self.rules:
				if clause[0]==tuple([query[1:]]) and clause[1]=="_NULL_": # negative fact:
					return [True, ["~"+clause[0][0]]]

		else:
			return self.queryistrue(query, set())


	def queryistrue(self, query, seen):

		if query in self.facts:
			if query in self.printablefacts:
				printingfact=query
				self.printablefacts.discard(query)
				return [True,[query]]
			else: # not in self.printable deduced fact or printed before
				return [True,[]]
	
		elif query in seen: # detect a loop, this branch cannot entail query
			return [False, "_LOOP_"]

		elif query in [x[1] for x in self.rules]: # query is the conclusion of a rule
			
			rulelist=[x for x in self.rules if x[1]==query] #rules whose conslusion is query. [0] premise : a frozen set ;[1] conclusion 		
			for rule in rulelist: # test all satisfying rules 
				allpremisetrue=True
				rulestoprint=[]
				for symbol in rule[0]:  # each symbol in premise (a set)
					[premisevalue, premiserule]=self.queryistrue(symbol, seen.union([query]) )
					allpremisetrue=allpremisetrue and premisevalue 
					rulestoprint+=premiserule
				
				if allpremisetrue: 
					# memoization
					self.rawlist+=[query]
					self.facts[query]=len(self.rawlist)-1 # last index 
				
					#print self.facts
					index=self.rules[rule]
					return [True, [self.rawlist[index]]+rulestoprint]
					# if not allpremisetrue, continue (check next possible rule)
					
			# no rule whose premises are all true, or no circle:
			return [False, "_UNSAT_"]
				
			# other cases, false (should not go here normally)
			return [False, "_ERROR_"]
		
		else: # query not in any rule's conclusion
			return [False, "ERROR"]


class resolutiondoer(object): # the class that dose resolution
	def resolve(self, cl1, cl2):  # resolve two clauses
		resultset=set()
		for literal1 in cl1:
			for literal2 in cl2:  # for each literal pair if can be resolved:
				if literal1[1:]== literal2 or literal1 ==literal2[1:]:  
					resolvelist=[]
					for l1 in cl1: #  input the element
						if not l1==literal1 : 
							resolvelist.append(l1)
					for l2 in cl2:
						if not l2==literal2 and not l2 in [x for x in cl1 if x != literal1] : # add the latter condition for factoring
							resolvelist.append(l2)
					if resolvelist==[]:
						pass 
						#print "Detect contradiction!!"
					resultset.add(tuple(resolvelist))
		
		return resultset 
	
	def resolution(self, KB, query ):  # KB :the list of clauses, query: a clause of query
		ne_query="~"+query if query[0]!="~" else query[1:]  # get the negation of query 
		newliteral=tuple([ne_query])
		KBset=set(KB).union([newliteral])
		#print KBset
		new=set()
		bp=defaultdict(list)
		for groundrules in KBset:
			bp[groundrules].append("_GROUND_")

		while True:
			checklist=list(KBset)
			for i, c1 in enumerate(checklist[:-1]):
				for c2 in checklist[i+1:]:
					resolvents=self.resolve(c1,c2)
					for newc in resolvents:
						bp[newc].append((c1,c2))
					#print resolvents
					if () in resolvents:
						bp["NULL"].append((c1,c2))
						return [True, self.resolutionorder(bp, "NULL")]
					new=new.union(resolvents)

			if new.issubset(KBset):
				return [False, ["DUMMY"]]
			KBset=KBset.union(new)


	def resolutionorder(self, bp, me):  # bp[me]=(my two parents (closer to ground))
		if bp[me]==["_GROUND_"]:
			return []
		else:
			resolver=bp[me].pop()
			return self.resolutionorder(bp, resolver[0])+self.resolutionorder(bp, resolver[1])+[("resolve: ",resolver[0], resolver[1],me)]
	def showresult(self, tuples):
		result=tuples[0]
		result=result+"( "
		for element in tuples[1]:
			result=result+element+"v "
		result=result[:-2]
		result=result+" )  and "
		
		result=result+"( "
		for element in tuples[2]:
			result=result+element+"v "
		result=result[:-2]
		result=result+" )  --> "

		
		if tuples[3]=="NULL":
			result=result+"NULL"
		else:
			result=result+"( "
			for element in tuples[3]:
				result=result+element+"v "
			result=result[:-2]
			result=result+" )"
		
		return result







if len(sys.argv)!=4:
	print "Input format error. format: <type> <KB> <query>"
	sys.exit(0)


qtype=sys.argv[1] # querytype : forward , backward, resolution
rawlist=ReadKB(sys.argv[2])
query=sys.argv[3]

#print rawlist
if qtype=="forward":  # Forwardchainging
	[value, resultlist]=forwardchaining(rawlist,query)
	if value: # true
		for rules in resultlist:
			print(rules)
		print "--> true"
	else:
		print "--> false"

elif qtype=="backward": #Backwardchainging
	bc=backwardchaining(rawlist, [parsehornform(x) for x in rawlist]) # KB representation 
	[value, resultlist]=bc.backward(query)
	if value: # true
		for rules in resultlist:
			print(rules)
		print "--> true"
	else:
		print "--> false"


elif qtype=="CNF":  # resolution
	clauses=set()
	for cnf in rawlist:  # conjunct all CNF
		clauses=clauses.union(parseCNF(cnf))  
	resolutiondoer= resolutiondoer()
	[value, resultlist]=resolutiondoer.resolution(clauses, query)
	if value: # true
		for rules in resultlist:
			print(resolutiondoer.showresult(rules))
		print "--> true"
	else:
		print "--> false"


