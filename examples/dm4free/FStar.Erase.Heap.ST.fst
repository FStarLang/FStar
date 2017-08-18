module FStar.Erase.Heap.ST

open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST


let inductive_inv = p:(heap -> Type0){ p emp }

let invariant (#a #b:Type)
  (p:inductive_inv) (pre_pure:a -> pure_pre) (post_pure:a -> pure_post b)
  (#pre:a -> st_pre) (#post:a -> st_post b) (f: x:a -> ST b (pre x) (post x)) =
  (* The pre- and post-condition split between state-invariant and pure component *)
  (forall x s. (p s /\ pre_pure x) ==> pre x s) /\
  (forall x s1 s2 y. (p s1 /\ post x s1 y s2) ==> (p s2 /\ post_pure x y)) /\
  (* The result of f does not depend on the initial state as long as it satisfies the invariant *)
  (forall s1 s2. p s1 /\ p s2 ==> (forall x. pre_pure x ==> fst (reify (f x) s1) == fst (reify (f x) s2)))

let erase_st (#a #b:Type)
    (p:inductive_inv) (pre_pure:a -> pure_pre) (post_pure:a -> pure_post b)
    (#pre:a -> st_pre) (#post:a -> st_post b) (f: x:a -> ST b (pre x) (post x))
  : Pure (x:a -> Pure b (pre_pure x) (post_pure x))
    (requires (invariant p pre_pure post_pure #pre #post f))
      (ensures (fun g -> (invariant p pre_pure post_pure #pre #post f) /\
                      (forall x. pre_pure x ==> g x == fst (reify (f x) emp))))
= fun (x:a) -> fst (reify (f x) emp)
