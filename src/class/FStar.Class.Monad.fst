module FStar.Class.Monad

open FStar.Compiler
open FStar.Compiler.Effect

instance monad_option : monad option = {
  return = (fun x -> Some x); // FIXME: without the we gell ill-typed ML
  ( let! ) = Util.bind_opt;
}

instance monad_list : monad list = {
  return = (fun x -> [x]);
  ( let! ) = (fun x f -> List.concatMap f x)
}

let rec mapM f l =
  match l with
   | [] -> return []
   | x::xs ->
      let! y = f x in
      let! ys = mapM f xs in
      return (y::ys)

let rec foldM_left f e xs =
  match xs with
  | [] -> return e
  | x::xs ->
    let! e' = f e x in
    foldM_left f e' xs

let rec foldM_right f xs e =
  match xs with
  | [] -> return e
  | x::xs ->
    let! e' = foldM_right f xs e in
    f x e'

let (<$>) f x =
  let! v = x in
  return (f v)

let (<*>) ff x =
  let! f = ff in
  let! v = x in
  return (f v)

let fmap f m =
  let! v = m in
  return (f v)
