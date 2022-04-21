module MonadFunctorInference

class functor (m:Type -> Type) =
{
  fmap: (#a:Type -> #b:Type -> (a -> b) -> m a -> m b)
}

let id (a:Type) = a

instance id_functor : functor id =
{
  fmap = fun #a #b f -> f
}

let test_id (a:Type) (f:a -> a) (x:id a) = fmap f x

instance option_functor : functor option =
{
  fmap = (fun #a #b (f:a -> b) (x:option a) ->
            match x with
            | None -> None
            | Some y -> Some (f y))
}

let test_option (f:int -> bool) (x:option int) = fmap f x

class monad (m:Type -> Type) =
{
   return : (#a:Type -> a -> m a);
   bind   : (#a:Type -> #b:Type -> (f:m a) -> (g:(a -> m b)) -> m b)
}

(* Now, with bind and return in scope, we have monad-polymorphic
   do notation *)

instance monad_functor #m (d:monad m) : functor m =
{
  fmap = (fun #a #b (f:a -> b) (c:m a) ->
             x <-- c;
             return (f x))
}

let st (a:Type) = int -> a & int

instance st_monad : monad st =
{
   return = (fun #a (x:a) -> (fun s -> x, s));
   bind   = (fun #a #b (f: st a) (g: a -> st b) (s0:int) ->
               let x, s1 = f s0 in
               g x s1)
}

let get
  : st int
  = fun s -> s, s

let put (x:int)
  : st unit
  = fun _ -> (), x

let get_inc =
  x <-- get;
  return (x + 1)

let test_st2 () =
  y <-- get;
  x <-- get_inc;
  if x > 17
  then put (x + y)
  else put y

instance opt_monad : monad option =
{
   return = (fun #a (x:a) -> Some x);
   bind = (fun #a #b (x:option a) (y: a -> option b) ->
             match x with
             | None -> None
             | Some a -> y a)
}

let raise #a : option a = None
let div (n m:int) =
  if m = 0 then raise
  else return (n / m)

let test_opt_monad (n m:nat) =
  x <-- div n m;
  y <-- div x m;
  return (x + y)
