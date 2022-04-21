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

let st (s:Type) (a:Type) = s -> a & s

instance st_monad s : monad (st s) =
{
   return = (fun #a (x:a) -> (fun s -> x, s));
   bind   = (fun #a #b (f: st s a) (g: a -> st s b) (s0:s) ->
               let x, s1 = f s0 in
               g x s1)
}

let get #s
  : st s s
  = fun s -> s, s

let put #s (x:s)
  : st s unit
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

let get_put #s =
  x <-- get #s;
  put x

let noop #s : st s unit = return ()

open FStar.FunctionalExtensionality

let get_put_identity (s:Type)
  : Lemma (get_put #s `feq` noop #s)
  = ()

module T = FStar.Tactics

let get_put_identity_alt (s:Type)
  : Tot (squash (get_put #s == noop #s))
    by (T.dump "A"; 
        T.norm [delta_only [`%get_put; `%return; `%bind; `%get; `%put; `%Mkmonad?.bind; `%Mkmonad?.return;`%st_monad; `%noop]; iota];
        T.smt()) //trefl fails here because there's an ascription on one side : (
  = ()

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
