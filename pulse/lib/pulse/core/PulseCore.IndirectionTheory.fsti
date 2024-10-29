module PulseCore.IndirectionTheory
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
let compose #a #b #c (f:b -> c) (g:a -> b) : (a ^-> c) = F.on_dom a (fun x -> f (g x))
let id #a : (a ^-> a) = F.on_dom a (fun x -> x)
#push-options "--print_implicits --print_universes"
class functor (f: Type u#(a+1) -> Type u#(a+1)) = {
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
      squash (compose (fmap b2c) (fmap a2b) ==
              fmap (compose b2c a2b))
  );
  tt : Type u#1;
  t_bot: tt;
  other : Type u#(a+1);
}

let pred (k:Type u#(a+1)) (other:Type u#(a+1)) (tt:Type u#1) = (k & other) ^-> tt

val knot_t #f (ff: functor u#a f) : Type u#(a+1)
val down #f (#ff: functor f) : (nat & f (pred (knot_t ff) ff.other ff.tt)) -> knot_t ff
val up #f (#ff: functor f) : knot_t ff -> (nat & f (pred (knot_t ff) ff.other ff.tt))

let predicate #f (ff: functor f) = pred (knot_t ff) ff.other ff.tt
let level #f (#ff: functor f) (x:knot_t ff) = fst (up x)
let approx #f {| ff: functor f |} (n:nat) : (predicate ff ^-> predicate ff)
= F.on_dom (predicate ff) fun p -> F.on_dom _ fun (w:(knot_t ff & ff.other)) -> if level (fst w) >= n then ff.t_bot else p w

val down_up #f (#ff: functor f) : x:knot_t ff -> squash (down (up x) == x)
val up_down #f (#ff: functor f) (n:nat) (x: f (predicate ff)) :
  squash (up #f (down (n, x)) == (n, fmap #f (approx #f n) x))
