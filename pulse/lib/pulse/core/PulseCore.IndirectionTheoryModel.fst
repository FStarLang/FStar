module PulseCore.IndirectionTheoryModel
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
let compose #a #b #c (f:b -> c) (g:a -> b) : (a ^-> c) = F.on_dom a (fun x -> f (g x))
let id #a : (a ^-> a) = F.on_dom a (fun x -> x)
#push-options "--print_implicits --print_universes"
class functor (f: Type u#a -> Type u#a) = {
  fmap: (
    #a:Type ->
    #b:Type ->
    (a -> b) ->
    f a ->
    f b
  );
  fmap_id: (
    a:Type ->
    x:f a ->
    squash (fmap (id #a) == id #(f a))
  );
  fmap_comp: (
      a:Type ->
      b:Type ->
      c:Type ->
      b2c:(b -> c) ->
      a2b:(a -> b) ->
      squash (compose (fmap b2c) (fmap a2b ) ==
              fmap (compose b2c a2b))
  );
  tt : Type u#b;
  t_bot: tt;
}

class pre_knot (k:Type u#a) = {
  f:Type u#a -> Type u#a;
  ff: functor f;
  down: (nat & f (k -> ff.tt)) -> k;
  up: k -> (nat & f (k -> ff.tt));
}
instance pk_functor #k {| pk: pre_knot k |} : functor pk.f = pk.ff
let predicate (k:Type) {| pk:pre_knot k |} = k -> pk.ff.tt
let level (#k:Type) {| pk:pre_knot k |} (x:k) = fst (pk.up x)
let approx (#k:Type) {| pk:pre_knot k |} (n:nat) (p:predicate k)
: predicate k
= fun (w:k) -> if level w >= n then pk.ff.t_bot else p w

class knot (k:Type u#a) = {
  pk: pre_knot k;
  down_up: (
    x:k ->
    squash (down #k (up #k x) == x)
  );
  up_down: (
    n:nat ->
    x:(pk.f (k -> pk.ff.tt)) ->
    squash (up (down (n, x)) == (n, fmap (approx n) x))
  )
}
instance pre_knot_of_knot #k {| kk: knot k |} : pre_knot k = kk.pk

let test #k {| kk:knot k |} (x:k) = level x
let test2 #k {| kk:knot k |} (n:nat) (p:predicate k) = approx n p

module U = FStar.Universe
type pnat =
  | Z
  | S of pnat
let rec ipred (f:Type u#a -> Type u#a) {| ff: functor f |} (n:pnat)
: Tot (Type u#a) (decreases %[n; 0])
= match n with
  | Z -> U.raise_t unit
  | S n' -> ipred_alt f n' & (f (ipred_alt f n') -> ff.tt)
and ipred_alt (f:Type u#a -> Type u#a) {| ff: functor f |} (n:pnat)
: Tot (Type u#a) (decreases %[n; 1]) =
  ipred f n
module T = FStar.Tactics
let fold_ipred_z
     (#f:Type u#a -> Type u#a)
     {| ff: functor f |}
: ipred f Z
= coerce_eq  
  ( _ by (
    T.trefl())
  )
  (U.raise_val ())

let fold_ipred_succ 
     (#f:Type u#a -> Type u#a)
     {| ff: functor f |}
     (n:pnat)
     (fst:ipred f n)
     (snd:(f (ipred f n) -> ff.tt))
: ipred f (S n)
= coerce_eq  
  ( _ by (
    T.trefl())
  )
  (fst, snd)

let unfold_ipred_succ 
     (#f:Type u#a -> Type u#a)
     {| ff: functor f |}
     (n:pnat)
     (pp:ipred f (S n))
: ipred_alt f n &
  (f (ipred_alt f n) -> ff.tt)
= coerce_eq  
  ( _ by (
    T.dump "A";
    T.norm [delta_only [`%ipred]; zeta; iota];
    T.trefl()
    )
  )
  pp

let tknot (f:Type u#a -> Type u#a) {| ff: functor f |}
: Type u#a
= n:nat & ipred f n
let klevel (#f:Type -> Type) {| ff:functor f |} (x:tknot f) = dfst x
let pred (f:Type -> Type) {| ff:functor f |} = tknot f -> ff.tt
let rec strat (f:Type u#a -> Type u#a) {| ff:functor f |} (n:nat) (p:pred f)
: ipred f n
= if n = 0 then U.raise_val ()
  else 
    let fst : ipred f (n - 1) = strat f (n - 1) p in
    let snd : f (ipred f (n - 1) -> ff.tt) = magic () in
    coerce_eq () (fst, snd)
   
      // p (| n - 1, fst |) in
      //     (fun g -> p (| n - 1, g |)) |)