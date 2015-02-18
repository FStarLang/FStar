module Extensionality
type arr (a:Type) (b:Type) = a -> Tot b

opaque logic type Eq : #a:Type -> #b:Type -> arr a b -> arr a b -> Type =
           fun (a:Type) (b:Type) (f:arr a b) (g:arr a b) -> (forall x. f x = g x)

assume Extensionality : forall (a:Type) (b:Type) (f: arr a b) (g: arr a b).
                        {:pattern Eq #a #b f g} Eq #a #b f g <==> f=g
