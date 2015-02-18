module Extensionality

type arr (a:Type) (b:(a->Type)) = x:a -> Tot (b x)

assume type Eq : #a:Type -> #b:(a -> Type) -> arr a b -> arr a b -> Type

assume EqDef : forall (a:Type) (b:(a->Type)) (f:arr a b) (g:arr a b).
              {:pattern Eq f g} (Eq f g) <==> (forall x. f x = g x)
(*
WARNING: '=' cannot be used in patterns.
WARNING: '=' cannot be used in patterns.
WARNING: 'and' cannot be used in patterns.
WARNING: '=>' cannot be used in patterns.
WARNING: '=' cannot be used in patterns.
WARNING: '=>' cannot be used in patterns.
WARNING: 'and' cannot be used in patterns.
*)

assume Extensionality : forall (a:Type) (b:(a->Type)) (f: arr a b) (g: arr a b).
                        {:pattern Eq f g} Eq f g <==> f=g
