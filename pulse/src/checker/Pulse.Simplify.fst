module Pulse.Simplify

open Pulse.Show
open FStar.Reflection.V2
module T       = FStar.Tactics.V2

let is_tuple2__1 (t:term) : T.Tac (option term) =
  match T.hua t with
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

let is_tuple2__2 (t:term) : T.Tac (option term) =
  match T.hua t with
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

let is_tuple2 (t:term) : T.Tac (option (term & term)) =
  match T.hua t with
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
let _simpl_proj (t:term) : T.Tac (option term) =
  match is_tuple2__1 t with
  | Some t -> omap fst (is_tuple2 t)
  | None ->
    match is_tuple2__2 t with
    | Some t -> omap snd (is_tuple2 t)
    | None -> None

let simpl_proj (t:term) : T.Tac term =
  match _simpl_proj t with
  | Some t -> t
  | None -> t

let is_reveal (t:term) : T.Tac (option (typ & term)) =
  match T.hua t with
  | Some (h, us, args) ->
    if implode_qn (T.inspect_fv h) = `%Ghost.reveal
    then
      match args with
      | [(typ, Q_Implicit); (t, Q_Explicit)] -> Some (typ, t)
      | _ -> None
    else
    None
  | _ -> None

let is_hide (t:term) : T.Tac (option (typ & term)) =
  match T.hua t with
  | Some (h, us, args) ->
    if implode_qn (T.inspect_fv h) = `%Ghost.hide
    then
      match args with
      | [(typ, Q_Implicit); (t, Q_Explicit)] -> Some (typ, t)
      | _ -> None
    else
    None
  | _ -> None

let simpl_reveal_hide (t:term) : T.Tac term =
  match is_reveal t with
  | Some (_, x) ->
    begin match is_hide x with
    | Some (_, x) -> x
    | None -> t
    end
  | None -> t

let simpl_hide_reveal (t:term) : T.Tac term =
  match is_hide t with
  | Some (t1, x) ->
    begin match is_reveal x with
    | Some (t2, x) ->
      (* hide #nat (reveal #int x) is == to x *)
      if FStar.Reflection.TermEq.term_eq t1 t2
      then x
      else t
    | None -> t
    end
  | None -> t

let rec simplify (t0:term) : T.Tac term =
  let t = t0 in
  let t = simpl_proj t in
  let t = simpl_hide_reveal t in
  let t = simpl_reveal_hide t in
  let t =
    match T.hua t with
    | Some (h, us, args) ->
      let args = T.map (fun (t, q) -> simplify t, q) args in
      T.mk_app (T.Tv_UInst h us) args
    | _ -> t
  in
  // T.print <| "simplified " ^ show t0 ^ " to " ^ show t;
  t
