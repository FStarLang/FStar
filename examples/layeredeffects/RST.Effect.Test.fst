module RST.Effect.Test

open Steel.Resource
open Steel.RST

open RST.Effect

#set-options "--max_fuel 0 --max_ifuel 0"

let test1 ()
: RST int emp (fun _ -> emp) (fun _ -> True) (fun _ r _ -> r > 1)
= 2


assume val r1 : r:resource{r.t == nat}
assume val r2 : r:resource{r.t == nat}
assume val r3 : r:resource{r.t == nat}


assume val f1
: x:nat ->
  RST unit r1 (fun _ -> r2)
  (fun (rm:rmem r1) -> rm r1 > 2)
  (fun (rm_in:rmem r1) _ (rm_out:rmem r2) -> x == rm_in r1 /\ rm_out r2 == rm_in r1 + x)

assume val f2
: x:nat ->
  RST unit r2 (fun _ -> r3)
  (fun rm -> rm r2 > 2)
  (fun rm_in _ rm_out -> rm_out r3 == rm_in r2 + x)

let test2 ()
: RST unit r1 (fun _ -> r3)
  (fun rm -> rm r1 > 3)
  (fun rm_in _ rm_out -> rm_out r3 > 3)
= f1 0; f2 0
