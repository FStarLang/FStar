module RewriteEqualityImplications
#reset-options "--log_queries"
//Look at the queries-rewriteEqualityImplications.smt2 file 
//     -- the query presented to Z3 is just (0 = 0)
//     -- still need to do the final step of proving (0 = 0) within the tactic language
let test = assert (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y))
