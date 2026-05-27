module Pulse.Simplify

open Pulse.Show
open FStar.Reflection.V2
module T = FStar.Tactics.V2

let thua_t = term & option (fv & universes & list argv)
let thua x = x, T.hua x
let hua (x:thua_t) = snd x

let is_Cons (t:thua_t) : T.Tac (option (term & term)) =
  match hua t with
  | Some (h, us, args) ->
    if implode_qn (T.inspect_fv h) = `%Prims.Cons
    then
      match args with
      | [(_, Q_Implicit); (h, Q_Explicit); (t, Q_Explicit)] -> Some (h,t)
      | _ -> None
    else
    None
  | _ -> None

let is_List_Tot_hd (t:thua_t) : T.Tac (option term) =
  match hua t with
  | Some (h, us, args) ->
    if implode_qn (T.inspect_fv h) = `%List.Tot.hd
    || implode_qn (T.inspect_fv h) = `%Cons?.hd
    then
      match args with
      | [(_, Q_Implicit); (t, Q_Explicit)] -> Some t
      | _ -> None
    else
    None
  | _ -> None

let is_List_Tot_tl (t:thua_t) : T.Tac (option term) =
  match hua t with
  | Some (h, us, args) ->
    if implode_qn (T.inspect_fv h) = `%List.Tot.tl
    || implode_qn (T.inspect_fv h) = `%Cons?.tl
    then
      match args with
      | [(_, Q_Implicit); (t, Q_Explicit)] -> Some t
      | _ -> None
    else
    None
  | _ -> None

let simpl_list (t:thua_t) : T.Tac thua_t =
  match is_List_Tot_hd t with
  | Some x ->
    begin match is_Cons (thua x) with
    | Some (h, t) -> thua h
    | None -> t
    end
  | None ->
    match is_List_Tot_tl t with
    | Some x ->
      begin match is_Cons (thua x) with
      | Some (_, t) -> thua t
      | None -> t
      end
    | None -> t

let is_Some (t:thua_t) : T.Tac (option term) =
  match hua t with
  | Some (h, us, args) ->
    if implode_qn (T.inspect_fv h) = `%Some
    then
      match args with
      | [(_, Q_Implicit); (t, Q_Explicit)] -> Some t
      | _ -> None
    else
    None
  | _ -> None

let is_Some_v (t:thua_t) : T.Tac (option term) =
  match hua t with
  | Some (h, us, args) ->
    if implode_qn (T.inspect_fv h) = `%Some?.v
    then
      match args with
      | [(_, Q_Implicit); (t, Q_Explicit)] -> Some t
      | _ -> None
    else
    None
  | _ -> None

let simpl_option (t:thua_t) : T.Tac thua_t =
  match is_Some_v t with
  | Some o ->
    (match is_Some (thua o) with
    | Some x -> thua x
    | None -> t)
  | None -> t

let is_tuple2__1 (t:thua_t) : T.Tac (option term) =
  match hua t with
  | Some (h, us, args) ->
    if implode_qn (T.inspect_fv h) = `%Mktuple2?._1
    || implode_qn (T.inspect_fv h) = `%fst
    then
      match args with
      | [(_, Q_Implicit); (_, Q_Implicit); (t, Q_Explicit)] -> Some t
      | _ -> None
    else
    None
  | _ -> None

let is_tuple2__2 (t:thua_t) : T.Tac (option term) =
  match hua t with
  | Some (h, us, args) ->
    if implode_qn (T.inspect_fv h) = `%Mktuple2?._2
    || implode_qn (T.inspect_fv h) = `%snd
    then
      match args with
      | [(_, Q_Implicit); (_, Q_Implicit); (t, Q_Explicit)] -> Some t
      | _ -> None
    else
    None
  | _ -> None

let is_tuple2 (t:thua_t) : T.Tac (option (term & term)) =
  match hua t with
  | Some (h, us, args) ->
    (* T.print <| "h = " ^ show (T.inspect_fv h); *)
    if implode_qn (T.inspect_fv h) = `%Mktuple2 then (
      (* T.print <| "found Mktuple2"; *)
      match args with
      | [(_, Q_Implicit); (_, Q_Implicit); (x, Q_Explicit); (y, Q_Explicit)] ->
        Some (x, y)
      | _ -> None
    ) else
      None
  | _ -> None

let omap (f : 'a -> 'b) (x : option 'a) : option 'b =
  match x with
  | None -> None
  | Some x -> Some (f x)

(* This is a huge hack to work around the lack of reduction of projectors in F*.
Note that we cannot simply unfold the projects willy-nilly, we only want to do so
when they are applied to a constructed value. *)
let _simpl_proj (t:thua_t) : T.Tac (option term) =
  match is_tuple2__1 t with
  | Some t -> omap fst (is_tuple2 (thua t))
  | None ->
    match is_tuple2__2 t with
    | Some t -> omap snd (is_tuple2 (thua t))
    | None -> None

let simpl_proj (t:thua_t) : T.Tac thua_t =
  match _simpl_proj t with
  | Some t -> thua t
  | None -> t

let is_reveal (t:thua_t) : T.Tac (option (typ & term)) =
  match hua t with
  | Some (h, us, args) ->
    if implode_qn (T.inspect_fv h) = `%Ghost.reveal
    then
      match args with
      | [(typ, Q_Implicit); (t, Q_Explicit)] -> Some (typ, t)
      | _ -> None
    else
    None
  | _ -> None

let is_hide (t:thua_t) : T.Tac (option (typ & term)) =
  match hua t with
  | Some (h, us, args) ->
    if implode_qn (T.inspect_fv h) = `%Ghost.hide
    then
      match args with
      | [(typ, Q_Implicit); (t, Q_Explicit)] -> Some (typ, t)
      | _ -> None
    else
    None
  | _ -> None

let simpl_reveal_hide (t:thua_t) : T.Tac thua_t =
  match is_reveal t with
  | Some (_, x) ->
    begin match is_hide (thua x) with
    | Some (_, x) -> thua x
    | None -> t
    end
  | None -> t

let simpl_hide_reveal (t:thua_t) : T.Tac thua_t =
  match is_hide t with
  | Some (t1, x) ->
    begin match is_reveal (thua x) with
    | Some (t2, x) ->
      (* hide #nat (reveal #int x) is == to x *)
      if FStar.Reflection.TermEq.term_eq t1 t2
      then thua x
      else t
    | None -> t
    end
  | None -> t

let rec simplify (t0:term) : T.Tac term =
  let t = thua t0  in
  let t = simpl_proj t in
  let t = simpl_option t in
  let t = simpl_list t in
  let t = simpl_hide_reveal t in
  let t = simpl_reveal_hide t in
  let t =
    match hua t with
    | Some (h, us, args) ->
      let args = T.map (fun (t, q) -> simplify t, q) args in
      T.mk_app (T.Tv_UInst h us) args
    | _ -> fst t
  in
  // T.print <| "simplified " ^ show t0 ^ " to " ^ show t;
  t
