module FunctionalExtensionality
type efun (a:Type) (b:Type) = a -> Tot b

opaque logic type FEq : #a:Type -> #b:Type -> efun a b -> efun a b -> Type =
           fun (a:Type) (b:Type) (f:efun a b) (g:efun a b) -> (forall x. f x = g x)

assume Extensionality : forall (a:Type) (b:Type) (f: efun a b) (g: efun a b).
                        {:pattern FEq #a #b f g} FEq #a #b f g <==> f=g
