module MonadFull

(* The mk_projs tactic does not yet work with the rest
of typeclasses, but at least we can generate projectors for
all these already. *)

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
%splice[] (Tactics.MkProjectors.mk_projs false (`%monad))

[@@no_auto_projectors_decls]
noeq
type monad_laws (m:Type0 -> Type0) (return : (#a:_ -> a -> m a)) (bind : (#a:_ -> #b:_ -> m a -> (a -> m b) -> m b)) = {
  idL    : #a:_ -> #b:_ -> x:a -> f:(a -> m b) -> Lemma (bind (return x) f == f x);
  idR    : #a:_ -> x:m a -> Lemma (bind x return == x);
  assoc  : #a:_ -> #b:_ -> #c:_ -> x:m a -> f:(a -> m b) -> g:(b -> m c) ->
			 Lemma (bind (bind x f) g ==
			        bind x (fun y -> bind (f y) g));
}
%splice[] (Tactics.MkProjectors.mk_projs false (`%monad_laws))

[@@no_auto_projectors_decls]
noeq
type monad2 (m : Type0 -> Type0) = {
  return : #a:_ -> a -> m a;
  bind   : #a:_ -> #b:_ -> m a -> (a -> m b) -> m b;
  laws   : monad_laws m return bind;
}
%splice[] (Tactics.MkProjectors.mk_projs false (`%monad2))