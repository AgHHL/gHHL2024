# lics2023-case1
## usage
   1. Install Isabelle2021-1   
   2. Make AFP available to Isabelle  
   3. Change logic session to "Ordinary_Differential_Equations" (change requires restart)
   4. Open these ".thy" files in this package in Isabelle2021-1


## simple intrudction of theories
### Analysis_more.thy
  * some results about derivatives   
  * some lemmas in real functions like MVT and IVT  
  * definitions of state, ode and ode solution
      
### BigStepSimple.thy
  * Big-step semantics 
  * definition of valid
  * Hoare rules for discrete process
      
### BigStepContinuous.thy
  * Hoare rules for ode and ode interrupt
      
### BigStepParallel.thy
  * combination of traces
  * Hoare rules for parallel hcsp
      
### ContinuousInv.thy and Complementlemma.thy
  * Diffinv rule, Dbx rule and Dbarrier rule and their variants

### Lander1.thy and Lander2.thy
  * Lander1: the example of lander with no parallel
  * Lander2: the example of lander with as described in article
  * "sorry" in the proof correspond to properties of "inv" which have been verified in Mathematica
      
   
