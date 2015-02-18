module Extensionality

type arr (a:Type) (b:(a->Type)) = x:a -> Tot (b x)

opaque type Eq : #a:Type -> #b:(a -> Type) -> arr a b -> arr a b -> Type = 
           fun (a:Type) (b:(a->Type)) (f:arr a b) (g:arr a b) -> (forall x. f x = g x)

assume Extensionality : forall (a:Type) (b:(a->Type)) (f: arr a b) (g: arr a b).
                        {:pattern Eq #a #b f g} Eq #a #b f g <==> f=g
