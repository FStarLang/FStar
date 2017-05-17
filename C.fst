module C

// These now work

val l1 : unit -> Lemma (u:unit{True})
let l1 () = ()

assume type phi
assume val proof : phi

val l2 : (x:int) -> (l : unit -> Lemma (requires phi) (ensures x > 0)) ->
                    Lemma (y:int{y == x /\ y > 0})
let l2 x l = let p = proof in l (); ()
