module PulseCore.IndirectionTheory
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
  other : Type u#a;
}

let pred (k:Type u#a) (other:Type u#a) (tt:Type u#a) = (k & other) -> tt

class pre_knot (k:Type u#a) = {
  f:Type u#a -> Type u#a;
  ff: functor f;
  down: (nat & f (pred k ff.other ff.tt)) -> k;
  up: k -> (nat & f (pred k ff.other ff.tt));
}
instance pk_functor #k {| pk: pre_knot k |} : functor pk.f = pk.ff
let predicate (k:Type) {| pk:pre_knot k |} = pred k pk.ff.other pk.ff.tt
let level (#k:Type) {| pk:pre_knot k |} (x:k) = fst (pk.up x)
let approx (#k:Type) {| pk:pre_knot k |} (n:nat) (p:predicate k)
: predicate k
= fun (w:(k & pk.ff.other)) -> if level (fst w) >= n then pk.ff.t_bot else p w

class knot (k:Type u#a) = {
  pk: pre_knot k;
  down_up: (
    x:k ->
    squash (down #k (up #k x) == x)
  );
  up_down: (
    n:nat ->
    x:(pk.f <| pred k pk.ff.other pk.ff.tt) ->
    squash (up (down (n, x)) == (n, fmap (approx n) x))
  )
}
instance pre_knot_of_knot #k {| kk: knot k |} : pre_knot k = kk.pk

val mk_knot (#f:Type -> Type) (ff:functor f) : (k:Type & knot k)

let test #k {| kk:knot k |} (x:k) = level x
let test2 #k {| kk:knot k |} (n:nat) (p:predicate k) = approx n p