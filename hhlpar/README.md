# hhlpar
## Test cases
There is a list of test cases in function 'testSyncPostBoth' in class 'AssnTest' in 'assn_test.py'.<br> 
We can see the results of these cases by running:
```
>>>python -m unittest hhlpar.assn_test.AssnTest.testSyncPostBoth
```
## Introduction of the case CCS 
The dictionary in line 311-333 from 'assn_test.py' shows the case of CCS:
* "PA" records the parallel process in the form of a triple:
  1. The first part is the plant process: "pn" gives a name "A" and "P" records the sequential HCSP
  2. The second part uses "chset" to record the set of communicating channels
  3. The third part is the control process: "pn" gives a name "B" and "P" records the sequential HCSP
* "Pre" records the condition on the initial state
* "Post" records the condition on the end state to be proved
* "Postr" records the condition on all the continuous intervals to be proved
* "RI" records the loop invariant we provide
