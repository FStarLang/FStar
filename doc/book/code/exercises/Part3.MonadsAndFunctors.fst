module Part3.MonadsAndFunctors

class monad (m:Type -> Type) =
{
   return : (#a:Type -> a -> m a);
   ( let! ) : (#a:Type -> #b:Type -> (f:m a) -> (g:(a -> m b)) -> m b);
}

let st (s:Type) (a:Type) = s -> a & s

instance st_monad s : monad (st s) =
{
   return = (fun #a (x:a) -> (fun s -> x, s));
    ( let! )   = (fun #a #b (f: st s a) (g: a -> st s b) (s0:s) ->
               let x, s1 = f s0 in
               g x s1);
}

let get #s
  : st s s
  = fun s -> s, s

let put #s (x:s)
  : st s unit
  = fun _ -> (), x

let get_inc =
  let! x = get in
  return (x + 1)

let test_st2 () =
  let! y = get in
  let! x = get_inc in
  if x > 17
  then put (x + y)
  else put y

let get_put #s =
  let! x = get #s in
  put x

let noop #s : st s unit = return ()

let get_put_identity (s:Type)
  : Lemma (get_put #s `FStar.FunctionalExtensionality.feq` noop #s)
  = ()

instance opt_monad : monad option =
{
   return = (fun #a (x:a) -> Some x);
   ( let! ) = (fun #a #b (x:option a) (y: a -> option b) ->
             match x with
             | None -> None
             | Some a -> y a)
}

let raise #a : option a = None

let div (n m:int) =
  if m = 0 then raise
  else return (n / m)

let test_opt_monad (i j k:nat) =
  let! x = div i j in
  let! y = div i k in
  return (x + y)

