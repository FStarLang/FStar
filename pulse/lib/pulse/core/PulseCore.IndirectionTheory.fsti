module PulseCore.IndirectionTheory
open FStar.FunctionalExtensionality

let compose #a #b #c (f:b -> c) (g:a -> b) : (a ^-> c) = on_dom a (fun x -> f (g x))
let id #a : (a ^-> a) = on_dom a (fun x -> x)

class functor (f: Type u#(a+1) -> Type u#(a+1)) = {
  fmap: (#a:Type -> #b:Type -> (a -> b) -> f a -> f b);
  fmap_id: (a:Type -> x:f a -> squash (fmap (id #a) == id #(f a)));
  fmap_comp: (a:Type -> b:Type -> c:Type -> b2c:(b -> c) -> a2b:(a -> b) ->
    squash (compose (fmap b2c) (fmap a2b) == fmap (compose b2c a2b)));
}

val knot_t #f (ff: functor u#a f) : Type u#(a+1)
let predicate #f (ff: functor u#a f) = knot_t ff ^-> prop
val level #f (#ff: functor f) (x:knot_t ff) : GTot nat
val pack #f (#ff: functor f) (n: Ghost.erased nat) : f (predicate ff) -> knot_t ff
val unpack #f (#ff: functor f) : knot_t ff -> f (predicate ff)

let approx #f (#ff: functor u#a f) (n:nat) : (predicate ff ^-> predicate ff) =
  on_dom (predicate ff) #(fun _ -> predicate ff) fun p ->
    on_dom _ #(fun _ -> prop) fun w -> if level w >= n then False else p w

val pack_unpack #f (#ff: functor f) : x:knot_t ff -> squash (pack (level x) (unpack x) == x)
val unpack_pack #f (#ff: functor f) (n:nat) (x: f (predicate ff)) :
  squash (level (pack n x) == n /\ unpack #f (pack n x) == fmap #f (approx #f n) x)
