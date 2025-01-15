module FStarC.Class.Monad

open FStarC
open FStarC.Effect

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

let mapMi #m #_ #a #b f l =
  (* FIXME: need to annotate the return type, why? *)
  let rec mapMi_go i f l : m (list b) =
    match l with
    | [] -> return []
    | x::xs ->
      let! y = f i x in
      let! ys = mapMi_go (i+1) f xs in
      return (y::ys)
  in
  mapMi_go 0 f l

let map_optM f l =
  match l with
  | None -> return None
  | Some x ->
    let! x = f x in
    return (Some x)

let rec iterM f l =
  match l with
   | [] -> return ()
   | x::xs ->
      f x;!
      iterM f xs

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
