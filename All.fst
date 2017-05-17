module All

// Weird things in F*

let _ = assert_norm (True /\ True)

let _ = assert (c_and True True)

let _ = assert (c_and c_True c_True)


val l1 : (a : Type) -> Lemma (a ==> squash a)
let l1 a = assert_norm (a ==> squash a)

val l2 : (a : Type) -> Lemma (squash a ==> a)
let l2 a = assert_norm (squash a ==> a)

let _ = assert_norm (c_and c_True c_True)


// These work after the patch
val l3 : unit -> Lemma (u:unit{True})
let l3 () = ()

assume type phi
assume val proof : phi

val l2 : (x:int) -> (l : unit -> Lemma (requires phi) (ensures x > 0)) ->
                    Lemma (y:int{y == x /\ y > 0})
let l2 x l = let p = proof in l (); ()


