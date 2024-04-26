# hhlpar
## Test cases
There is a list of test cases in function 'testSyncAssn' in class 'AssnTest' in 'assn_test.py'.<br> 
We can see the results of these cases by running:
```
>>>python -m unittest hhlpar.assn_test.AssnTest.testSyncAssn
```
## Case format
Users can add cases in the format of a tuple type (C1,D,C2) to verify c1||c2:
* D is dict type:
  1. "chset": the set of communications in synchronization
  2. "init": the initial conditionn default to be True
  3. "recinv": the recursion condition default to be True
* C1(or C2) is dict type if c1(or c2) is a sequential process:
  1. "pn": the parallel name usually use "A,B,C..."
  2. "P": the HCSP process c1(or c2) in text form
* C1(or C2) is tuple type (C11,D1,C12) if c1(or c2) is a parallel process c11||c12


For example ({"pn":"A","P":"ch1?x;"}, {"chset":{"ch1"}}, {"pn":"B","P":"ch1!3;"}) and apply function sync_mult on it
```
t = ({"pn":"A","P":"ch1?x;"}, {"chset":{"ch1"}}, {"pn":"B","P":"ch1!3;"})
print(sync_mult(t))
```
