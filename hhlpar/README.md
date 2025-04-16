# hhlpar
## Test cases
There is a list of test cases in function 'testSyncPostBoth' in class 'AssnTest' in 'assn_test.py'.<br> 
We can see the results of these cases by running:
```
>>>python -m unittest hhlpar.assn_test.AssnTest.testSyncPostBoth
```
## CCS Case Introduction
line 311-333 represents the case of CCS
* D is dict type:
  1. "chset": the set of communications in synchronization
  2. "init": the initial conditionn default to be True
  3. "recinv": the recursion condition default to be True
* C1(or C2) is dict type if c1(or c2) is a sequential process:
  1. "pn": the parallel name usually use "A,B,C..."
  2. "P": the HCSP process c1(or c2) in text form
* C1(or C2) is tuple type (C11,D1,C12) if c1(or c2) is a parallel process c11||c12
