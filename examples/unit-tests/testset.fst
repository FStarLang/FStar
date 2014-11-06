(* Expect 3 intentional failures *)
module TestSet
assume type elt
assume logic val A : elt
assume logic val B : elt
assume logic val C : elt
assume AB_distinct: A=!=B

val should_succeed: unit -> Tot unit
let should_succeed u =
  assert (InSet B (Union (Singleton A) (Singleton B)));
  assert (InSet A (Union (Singleton A) (Singleton B)));
  assert (Subset (Singleton A) (Union (Singleton A) (Singleton B)));
  assert (Subset (Singleton B) (Union (Singleton A) (Singleton B)));
  assert (SetEqual (Union (Singleton A) (Singleton B))
                   (Union (Singleton B) (Singleton A)))

val should_fail1: unit -> Tot unit
let should_fail1 u =
  assert (InSet B (Singleton A))

val should_fail2: unit -> Tot unit
let should_fail2 u = 
  assert (Subset (Union (Singleton A) (Singleton B)) (Singleton A))

val should_fail3: unit -> Tot unit
let should_fail3 u =
  assert (InSet C (Union (Singleton A) (Singleton B)))
            
