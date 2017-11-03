module Bug111

type post (a:Type) = a -> Type
assume type recv_t: a:Type -> (a -> Type) -> Type
assume val recv: unit -> PURE 'a (fun (p:post 'a) -> recv_t 'a p)
