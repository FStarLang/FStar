(*--build-config
    options:--admit_fsi OrdSet;
    other-files:ordset.fsi
 --*)
module OrdSetProps
 
open OrdSet
 
val fold: #a:Type -> #b:Type -> f:cmp a -> (a -> b -> Tot b) -> s:ordset a f -> b
          -> Tot b (decreases (size f s))
let rec fold f g s a =
  if s = empty f then a
  else
    let Some e = choose f s in
    fold f g (remove f e s) (g e a)

(**********)

val union':#a:Type -> f:cmp a -> ordset a f -> ordset a f -> Tot (ordset a f)
let union' f s1 s2 = fold f (fun e s -> insert f e s) s1 s2

val union_lemma: #a:Type -> f:cmp a -> s1:ordset a f -> s2:ordset a f
                 -> Lemma (requires (True))
                    (ensures (forall x. mem f x (union f s1 s2) = mem f x (union' f s1 s2)))
                    (decreases (size f s1))
let rec union_lemma f s1 s2 =
  if s1 = empty f then ()
  else
    let Some e = choose f s1 in
    union_lemma f (remove f e s1) (insert f e s2)

val union_lemma': #a:Type -> f:cmp a -> s1:ordset a f -> s2:ordset a f
                  -> Lemma (requires (True))
                     (ensures (union f s1 s2 = union' f s1 s2))
let rec union_lemma' f s1 s2 =
  union_lemma f s1 s2;
  eq_lemma f (union f s1 s2) (union' f s1 s2)

