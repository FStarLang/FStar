module Part3.MonadsAndFunctors

//SNIPPET_START: monad$
class monad (m:Type -> Type) =
{
   return : (#a:Type -> a -> m a);
   bind   : (#a:Type -> #b:Type -> (f:m a) -> (g:(a -> m b)) -> m b);
}
//SNIPPET_END: monad$

//SNIPPET_START: st$
let st (s:Type) (a:Type) = s -> a & s

instance st_monad s : monad (st s) =
{
   return = (fun #a (x:a) -> (fun s -> x, s));
   bind   = (fun #a #b (f: st s a) (g: a -> st s b) (s0:s) ->
               let x, s1 = f s0 in
               g x s1);
}
//SNIPPET_END: st$

//SNIPPET_START: get_inc$
let get #s
  : st s s
  = fun s -> s, s

let put #s (x:s)
  : st s unit
  = fun _ -> (), x

let get_inc =
  x <-- get;
  return (x + 1)
//SNIPPET_END: get_inc$

let test_st2 () =
  y <-- get;
  x <-- get_inc;
  if x > 17
  then put (x + y)
  else put y

//SNIPPET_START: get_put$
let get_put #s =
  x <-- get #s;
  put x

let noop #s : st s unit = return ()

let get_put_identity (s:Type)
  : Lemma (get_put #s `FStar.FunctionalExtensionality.feq` noop #s)
  = ()
//SNIPPET_END: get_put$

//SNIPPET_START: opt_monad$
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

let test_opt_monad (i j k:nat) =
  x <-- div i j;
  y <-- div i k;
  return (x + y)
//SNIPPET_END: opt_monad$

