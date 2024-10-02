module MonadFull.Class

(* The mk_projs tactic does not yet work with the rest
of typeclasses, but at least we can generate projectors for
all these already. *)

open FStar.Tactics.Typeclasses

[@@no_auto_projectors_decls]
noeq
type monad (m:Type0 -> Type0) : Type = {
  return : #a:_ -> a -> m a;
  bind   : #a:_ -> #b:_ -> m a -> (a -> m b) -> m b;
  idL    : #a:_ -> #b:_ -> x:a -> f:(a -> m b) -> Lemma (bind (return x) f == f x);
  idR    : #a:_ -> x:m a -> Lemma (bind x return == x);
  assoc  : #a:_ -> #b:_ -> #c:_ -> x:m a -> f:(a -> m b) -> g:(b -> m c) ->
			 Lemma (bind (bind x f) g ==
			        bind x (fun y -> bind (f y) g));
}
%splice[return; bind; idL] (Tactics.MkProjectors.mk_projs true (`%monad))

let test #m {| monad m |} (x : 'a) (f g : 'a -> 'a) =
  idL #m x (fun y -> bind (return (f y)) (fun z -> return (g z)));
  idL #m (f x) (fun z -> return (g z));
  assert (bind #m (return x) (fun y -> bind (return (f y)) (fun z -> return (g z)))
            == return (g (f x)))