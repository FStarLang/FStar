module RST.Effect.Test

open Steel.Resource
open Steel.RST

open RST.Effect

#set-options "--max_fuel 0 --max_ifuel 0 --using_facts_from '* \
  -FStar.Seq \
  -FStar.ST \
  -FStar.HyperStack \
  -FStar.Monotonic.HyperStack
  -FStar.Heap
  -FStar.Monotonic.Heap \
  -FStar.Tactics \
  -FStar.Reflection \
  -LowStar \
  -FStar.ModifiesGen'"

let test1 ()
: RST nat emp (fun _ -> emp) (fun _ -> True) (fun _ r _ -> r == 2)
= 2


assume val r1 : r:resource{r.t == nat}
assume val r2 : r:resource{r.t == nat}
assume val r3 : r:resource{r.t == nat}


assume val f1
: x:nat ->
  RST unit r1 (fun _ -> r2)
  (fun (rm:rmem r1) -> rm r1 == 2)
  (fun (rm_in:rmem r1) _ (rm_out:rmem r2) -> rm_out r2 == rm_in r1 + x)

assume val f2
: x:nat ->
  RST unit r2 (fun _ -> r3)
  (fun rm -> rm r2 == 2)
  (fun rm_in _ rm_out -> rm_out r3 == rm_in r2 + x)

assume val f3
: x:nat ->
  RST unit r3 (fun _ -> r3)
  (fun rm -> rm r3 == 2)
  (fun rm_in _ rm_out -> rm_out r3 == rm_in r3 + x)

let test2 ()
: RST unit r1 (fun _ -> r3)
  (fun rm -> rm r1 == 2)
  (fun rm_in x rm_out -> rm_out r3 > 2)
= f1 0; f2 0; f3 3

assume Can_be_split_into_emp:
  forall (r:resource). r `can_be_split_into` (r, emp) /\ r `can_be_split_into` (emp, r)

let test3 ()
: RST nat r1 (fun _ -> r3)
  (fun rm -> rm r1 == 2)
  (fun rm_in x rm_out -> True) //rm_out r3 > 2)
= f1 0; f2 0; f3 3;
  rst_frame r3 (fun _ -> r3) r3 test1

let test4 ()
: RST nat r1 (fun _ -> r3)
  (fun rm -> rm r1 == 2)
  (fun rm_in x rm_out -> x == 2 /\ rm_out r3 > 0)
= f1 0; f2 0; f3 3;
  rst_frame r3 (fun _ -> r3) r3 test1
