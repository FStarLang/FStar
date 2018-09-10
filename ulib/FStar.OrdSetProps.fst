module FStar.OrdSetProps

open FStar.OrdSet

val fold: #a: eqtype -> #b: Type -> #f: cmp a -> (a -> b -> Tot b) -> s: ordset a f -> b ->
  Tot b (decreases (size s))
let rec fold (#a: eqtype) (#b: Type) #f g s x =
  if s = empty
  then x
  else
    let Some e = choose s in
    let a_rest = fold g (remove e s) x in
    g e a_rest


let insert (#a: eqtype) (#f: cmp a) (x: a) (s: ordset a f) = union #a #f (singleton #a #f x) s

val union': #a: eqtype -> #f: cmp a -> ordset a f -> ordset a f -> Tot (ordset a f)
let union' (#a: eqtype) #f s1 s2 = fold (fun e (s: ordset a f) -> insert e s) s1 s2

val union_lemma: #a: eqtype -> #f: cmp a -> s1: ordset a f -> s2: ordset a f ->
  Lemma (requires (True))
    (ensures (forall x. mem x (union s1 s2) = mem x (union' s1 s2)))
    (decreases (size s1))
let rec union_lemma (#a: eqtype) #f s1 s2 =
  if s1 = empty then () else union_lemma (remove (Some?.v (choose s1)) s1) s2

val union_lemma': #a: eqtype -> #f: cmp a -> s1: ordset a f -> s2: ordset a f ->
  Lemma (requires (True)) (ensures (union s1 s2 = union' s1 s2))
let union_lemma' (#a: eqtype) #f s1 s2 = union_lemma s1 s2; eq_lemma (union s1 s2) (union' s1 s2)

