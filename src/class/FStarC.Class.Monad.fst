module FStarC.Class.Monad

open FStarC
open FStarC.Effect

instance monad_option : monad option = {
  return = (fun x -> Some x); // FIXME: without the we gell ill-typed ML
  bind   = (fun o f -> match o with | None -> None | Some v -> f v);
}

(* Aliases. Need to declare a very precise type for them. *)
instance monad_list : monad list = {
  return = (fun x -> [x]);
  bind   = (fun l f -> List.concatMap f l)
}

let rec mapM f l =
  match l with
  | [] -> return []
  | x::xs ->
    let! y = f x in
    let! ys = mapM f xs in
    return (y::ys)

let mapMi #m #_ #a #b (f : int -> a -> ML (m b)) l =
  let rec mapMi_go i l : ML (m (list b)) =
    match l with
    | [] -> return []
    | x::xs ->
      let! y = f i x in
      let! ys = mapMi_go (i+1) xs in
      return (y::ys)
  in
  mapMi_go 0 l

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
  let r = f v in
  return r

let (<*>) ff x =
  let! f = ff in
  let! v = x in
  return (f v)

let fmap f m =
  let! v = m in
  let r = f v in
  return r
