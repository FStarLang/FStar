(*--build-config
    options:--admit_fsi FStar.OrdSet;
    other-files:ordset.fsi
 --*)
module FStar.OrdSetProps
 
open FStar.OrdSet
 
val fold: #a:Type -> #b:Type -> #f:cmp a -> (a -> b -> Tot b) -> s:ordset a f -> b
          -> Tot b (decreases (size s))
let rec fold (#a:Type) (#b:Type) #f g s a =
  if s = empty then a
  else
    let Some e = choose s in
    let a_rest = fold g (remove e s) a in
    g e a_rest

(**********)

let insert (#a:Type) (#f:cmp a) (x:a) (s:ordset a f) = union #a #f (singleton #a #f x) s

val union':#a:Type -> #f:cmp a -> ordset a f -> ordset a f -> Tot (ordset a f)
let union' (#a:Type) #f s1 s2 = fold (fun e (s:ordset a f) -> insert e s) s1 s2

val union_lemma: #a:Type -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
                 -> Lemma (requires (True))
                    (ensures (forall x. mem x (union s1 s2) = mem x (union' s1 s2)))
                    (decreases (size s1))
let rec union_lemma (#a:Type) #f s1 s2 =
  if s1 = empty then ()
  else
    union_lemma (remove (Some.v (choose s1)) s1) s2

val union_lemma': #a:Type -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
                  -> Lemma (requires (True))
                     (ensures (union s1 s2 = union' s1 s2))
let union_lemma' (#a:Type) #f s1 s2 =
  union_lemma s1 s2;
  eq_lemma (union s1 s2) (union' s1 s2)

