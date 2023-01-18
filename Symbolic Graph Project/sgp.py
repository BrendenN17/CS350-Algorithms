#symbolic Graph Search Project for cs350
#Created by Brenden Nelson spring 2020

"""
I Have implemented steps 3.1, 3.2, 3.3, 3.4, and 3.5
The result of Statement A on Graph G is False!

I Also Implemented BONUS step 4 as a test function at the end of the program
The Test demonstrates that 3.4 was implemented correctly with a total of 6 successful cases
Users can enter two numbers to test whether they satisfy BDD PE from step 3.4
Testing begins on line 245
"""

from pyeda.inter import *

ran_ge = range(32)  #generates range 0-31
#print(ran_ge)
xcount = []
ycount = []
xbcount = []
ybcount = []

#R is the set of all connected edges in graph G
R = [(i, j) for i in ran_ge for j in ran_ge if (i + 3) % 32 == j % 32 or (i + 8) % 32 == j % 32]
for i in ran_ge:
     for j in ran_ge:
          if (i + 3) % 32 == j % 32 or (i + 8) % 32 == j % 32:
              xcount.append(i)
              ycount.append(j)

#print("R (set of connected edges)")
#print(R)
#print("\n")

ss = range(len(xcount))
for i in ss:
    xbcount.append('{0:05b}'.format(xcount[i]))
    ybcount.append('{0:05b}'.format(ycount[i]))
    R[i] = (xbcount[i], ybcount[i])

#print("R list in binary")
#print(R)
#print("\n")

#even is the set of all even nodes in G
even = [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30]
#print("even set")
#print(even)
#print("\n")

se = range(len(even))
for i in se:
    even[i] = '{0:05b}'.format(even[i])
#print("even list in binary")
#print(even)
#print("\n")

#prime is the set of all prime nodes in G
prime = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
#print("prime set")
#print(prime)
#print("\n")

sp = range(len(prime))
for i in sp:
    prime[i] = '{0:05b}'.format(prime[i])
#print("prime in binary")
#print(prime)
#print("\n")

#AS OF NOW I HAVE R, EVEN, PRIME ALL AS BOOLEAN SETS
#I WILL NOW CONVERT THEM INTO BOOLEAN EXPRESSIONS
a = [0, 0, 0, 0, 0]  #will track x bits in R 
b = [0, 0, 0, 0, 0]  #will track y bits in R
a0, a1, a2, a3, a4 = bddvars('a', 5)
b0, b1, b2, b3, b4 = bddvars('b', 5)

num1 = 0 #x number in R
num2 = 0  #y number in R

Rexp = ''  #string expression for set R
for k in ss:  #loop list
    num1 = xbcount[k]
    num2 = ybcount[k]

    #below loops to get individual bits from the set and into a boolean expression
    bits = [(int(num1) >> bit) & 1 for bit in range(5 - 1, -1, -1)]
    for position, bit in enumerate(bits):
        a[position] = bit
        #setting string expressions for R, r1, r2
        #print("in bit loop")
        if a[position] == 1:
            Rexp = Rexp + ' a' + str(position) + ' &'
          
        if a[position] == 0:
            Rexp = Rexp + ' ~a' + str(position) + ' &'
           

    bits = [(int(num2) >> bit) & 1 for bit in range(5 - 1, -1, -1)]
    for position, bit in enumerate(bits):
        b[position] = bit
         #print("in bit loop")
        if b[position] == 1:
            Rexp = Rexp + ' b' + str(position) + ' &'
         
        if b[position] == 0:
            Rexp = Rexp + ' ~b' + str(position) + ' &'
            

    Rexp = Rexp[:-1]  #remove extra &
    Rexp = Rexp + ' |'  #add or for next pair
  

print("boolean exp for R: ")
Rexp = Rexp[:-1]
REXP = expr(Rexp)  #creating boolean expression
print(REXP)

evennum = 0
EVENxp = ''  #string expression for set even
for k in se:
    evennum = even[k]

    bits = [(int(evennum) >> bit) & 1 for bit in range(5 - 1, -1, -1)]
    for position, bit in enumerate(bits):
        b[position] = bit

        if b[position] == 1:
            EVENxp = EVENxp + ' b' + str(position) + ' &'
        if b[position] == 0:
            EVENxp = EVENxp + ' ~b' + str(position) + ' &'

    EVENxp = EVENxp[:-1]
    EVENxp = EVENxp + ' |'

print("boolean exp for Even: ")
EVENxp = EVENxp[:-1]
EVENXP = expr(EVENxp)#creating a boolean expression
print(EVENXP)

primenum = 0
PRIMExp = ''  #string expression for set prime
for k in sp:
    primenum = prime[k]

    bits = [(int(primenum) >> bit) & 1 for bit in range(5 - 1, -1, -1)]
    for position, bit in enumerate(bits):
        a[position] = bit

        if a[position] == 1:
            PRIMExp = PRIMExp + ' a' + str(position) + ' &'
        if a[position] == 0:
            PRIMExp = PRIMExp + ' ~a' + str(position) + ' &'

    PRIMExp = PRIMExp[:-1]
    PRIMExp = PRIMExp + ' |'

print("boolean exp for Prime: ")
PRIMExp = PRIMExp[:-1]
PRIMEXP = expr(PRIMExp)#creating boolean expression
print(PRIMEXP)

#NOW I HAVE 3 BOOLEAN EXPRESSIONS

#STEP 3.1
#I WILL CONVERT THESE INTO BDDS BELOW

RR = expr2bdd(REXP) #BDD for R
EVEN = expr2bdd(EVENXP) #BDD for [even]
PRIME = expr2bdd(PRIMEXP)  #BDD for [prime]


#STEP 3.2
#COMPUTE BDD RR2 for RoR from BDD RR
#set of node pairs that reach each other in 2 steps

e0, e1, e2, e3, e4 = bddvars('e', 5)

R_R = RR
RRR = RR
#finding relations for 2 step reachability
r1 = R_R.compose({b0:e0, b1:e1, b2:e2, b3:e3, b4:e4})
r2 = RRR.compose({a0:e0, a1:e1, a2:e2, a3:e3, a4:e4})
RR2 = r1 & r2
#removing helper e var from new BDD
RR2 = RR2.smoothing((e0, e1, e2, e3, e4))

#STEP 3.3
#COMPUTE TRANSITIVE CLOSURE RR2* OF RR2
#one node can reach the other in an even number of steps

H = RR #initialize like from notes
loop = True #loop variable
while loop == True:
    Hp = H
    #print("in loop")
    #checking reachability
    r1 = Hp.compose({b0:e0, b1:e1, b2:e2, b3:e3, b4:e4})
    r2 = RR.compose({a0: e0, a1: e1, a2: e2, a3: e3, a4: e4})
    #composing like in notes
    f = r1 & r2
    #adding to new BDD
    H = Hp | f
    #removing e (helper for reachability)
    H = H.smoothing((e0, e1, e2, e3, e4))
    if H.equivalent(Hp):
        loop = False

#print("out of the while loop\n")

RR2star = H & RR2 #BDD for all nodes can reach each other in even number of steps

#STEP 3.4
#COMPUTE BDD PE FROM PRIME, EVEN, RR2STAR
#set of all node pairs(u, v) where u is prime and v is even
#and u can reach v in even number of steps
PE = PRIME & EVEN & RR2star
pe = bdd2expr(PE)


#STEP 3.5
#formulate Statement A in terms of BDD operations on PE
#Statement A: for each node u in [prime], there is a node
#v in [even] such that u can reach v in an even num of steps
StatA = PE
StatA = StatA.consensus((a0, a1, a2, a3, a4))#consensus to implement the "for each" quantifier
StatA = StatA.smoothing((b0, b1, b2, b3, b4))#smoothing to implement the "there is" quantifier
StattA = bdd2expr(StatA)
#convert to expression for output
print("Statement A as a boolean expression: ")
print(StattA)
print("\n")

#results displayed below
if StatA is True:
    print("*******************************")
    print("Statement A is true on Graph G")
    print("*******************************")
else:
    print("***********************************")
    print("Statement A is NOT true on Graph G")
    print("***********************************")

print("\n")


#BONUS PART 4
#Testing part 3.4
#pick prime number u = 5. Find an even statement in A!
#using that v, verify that the (u,v) does satisfy PE in 3.4
#if u = 5 then there are two edges satisfying #2 which have u as 5
#(5, 8) and (5, 13), however 13 is a prime number, so v = 8
#write test code to check whether (u,v) satisfies my PE from 3.4
#write the test for generic u and v
testexp = ''
testu = 5  #can enter any number here to test u
testv = 8  #can enter any number here to test v
ub = '{0:05b}'.format(testu)
vb = '{0:05b}'.format(testv)
print("numbers chosen for this test run are:")
print(testu, testv)
print(ub, vb)
print("\n")

#below loops to get individual bits from the set and into a boolean expression
bits = [(int(ub) >> bit) & 1 for bit in range(5 - 1, -1, -1)]
for position, bit in enumerate(bits):
    a[position] = bit
    #print("in bit loop")
    if a[position] == 1:
        testexp = testexp + ' a' + str(position) + ' &'
      
    if a[position] == 0:
        testexp = testexp + ' ~a' + str(position) + ' &'
           

bits = [(int(vb) >> bit) & 1 for bit in range(5 - 1, -1, -1)]
for position, bit in enumerate(bits):
    b[position] = bit
    #print("in bit loop")
    if b[position] == 1:
        testexp = testexp + ' b' + str(position) + ' &'
         
    if b[position] == 0:
        testexp = testexp + ' ~b' + str(position) + ' &'
            

testexp = testexp[:-1]  #remove extra &
TESTEX = expr(testexp)
print("Our Test Expression is")
print(TESTEX)
print("\n")
print("Our PE Expression from 3.4 is")
print(pe)
print("\n")
TESTBDD = expr2bdd(TESTEX)

if PE & TESTBDD:
    print("test passes")
else:
    print("test fails")

#TEST PASSES WITH (5,8) and (17,20) and (7, 10)
#TEST FAILS WITH (5,13) and (15, 20) and (0, 3)
# I believe 6 tests with expected results is enough to conclude that my PE from step 3.4 is correct