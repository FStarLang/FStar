module Bug111

type post (a:Type) = a -> prop
assume type recv_t: a:Type -> (a -> prop) -> prop
assume val recv: unit -> PURE 'a (fun (p:post 'a) -> recv_t 'a p)
