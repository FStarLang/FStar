module RewriteEqualityImplications
#reset-options "--log_queries"
//Look at the queries-rewriteEqualityImplications.smt2 file
let test_1 = assert (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y))
let test_2 = assert (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z))
let test_3 () = assert (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z))

let good (x:int) = true
let test_4 () = assert (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z) /\ good x) //(good x) goes to SMT

unfold let good_2 (x:int) = True
let test_5 () = assert (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z) /\ good_2 x) //gets normalized

unfold let good_3 (x:int) = true
let test_6 () = assert (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z) /\ good_3 x) //b2t true, goes to SMT (fix)

let test_7 =
  let x = 10 in
  assert (x + 0 == 10) //this one fails because of mk_eq and the whole query goes to SMT
