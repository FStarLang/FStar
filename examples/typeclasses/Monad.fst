module Monad

open FStar.Tactics.Typeclasses

(* Fails... due to unification? check it out *)
// noeq type monad (m:Type0 -> Type0) : Type = {
//   return : #a:_ -> a -> m a;
//   bind   : #a:_ -> #b:_ -> m a -> (a -> m b) -> m b;
//   idL    : #a:_ -> #b:_ -> x:a -> f:(a -> m b) -> Lemma (__fname__bind (__fname__return x) f == f x);
//   idR    : #a:_ -> x:m a -> Lemma (__fname__bind x __fname__return == x);
//   assoc  : #a:_ -> #b:_ -> #c:_ -> x:m a -> f:(a -> m b) -> g:(b -> m c) ->
// 			 Lemma (__fname__bind (__fname__bind x f) g ==
// 			        __fname__bind x (fun y -> __fname__bind (f y) g));
// }

noeq
type monad_laws (m:Type0 -> Type0) (return : (#a:_ -> a -> m a)) (bind : (#a:_ -> #b:_ -> m a -> (a -> m b) -> m b)) = {
  idL    : #a:_ -> #b:_ -> x:a -> f:(a -> m b) -> Lemma (bind (return x) f == f x);
  idR    : #a:_ -> x:m a -> Lemma (bind x return == x);
  assoc  : #a:_ -> #b:_ -> #c:_ -> x:m a -> f:(a -> m b) -> g:(b -> m c) ->
			 Lemma (bind (bind x f) g ==
			        bind x (fun y -> bind (f y) g));
}

class monad (m : Type0 -> Type0) = {
  return : #a:_ -> a -> m a;
  bind   : #a:_ -> #b:_ -> m a -> (a -> m b) -> m b;
  laws   : monad_laws m __fname__return __fname__bind;
}


let f #a #b #m [|monad m|] (x : m (a -> b)) (y : m a) : m b =
  bind #_ #_ #m x (fun x ->
  bind #_ #_ #m y (fun y ->
  return #_ #m (x y)))

let g #a #b #m [|d : monad m|] (x : m a) =
  d.laws.idL () (fun () -> x);
  d.laws.idR x;
  assert (bind #_ #_ #m x (return #_ #m) == bind #_ #_ #m (return #_ #m ()) (fun () -> x))

(* Same bug as EnumEq, I think, requiring the #d in for laws *)
let g' #a #b #m [|d : monad m|] (x : m a) =
  (laws #m #d).idL () (fun () -> x);
  (laws #m #d).idR x;
  assert (bind #_ #_ #m x (return #_ #m) == bind #_ #_ #m (return #_ #m ()) (fun () -> x))

open Functor

instance monad_functor #m (d : monad m) : functor m =
  { fmap = (fun #_ #_ f x -> bind #_ #_ #m x (fun xx -> return #_ #m (f xx))); }
