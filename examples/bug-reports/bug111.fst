module Bug111
kind Post (a:Type) = a -> Type
assume type Recv: a:Type -> (a -> Type) -> Type
assume val recv: unit -> PURE 'a (fun (p:Post 'a) -> Recv 'a p) (fun (p:Post 'a) -> Recv 'a p)
