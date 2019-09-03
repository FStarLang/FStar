module Bug1841

let reader (r:Type) (a:Type) = r -> M a

let return (r:Type) (a:Type) (x:a)
: reader r a
= fun _ -> x

let bind (r:Type) (a:Type) (b:Type) (x:reader r a) (f:a -> reader r b)
: reader r b
= fun env ->
  let z = x env in
  f z env

let get (r:Type) () : reader r r = fun env -> env

total reifiable reflectable new_effect {
  READER (r:Type) : a:Type -> Effect
  with repr   = reader r
     ; return = return r
     ; bind   = bind r
     ; get    = get r
}

[@expect_failure [147]]
effect Reader (r:Type) (a:Type) (pre:READER?.pre r) (post:r -> a -> GTot Type0) =
  READER r a (fun (l0:r) (p:a -> Type0) -> pre l0 /\ (forall x. pre l0 /\ post l0 x ==> p x))
