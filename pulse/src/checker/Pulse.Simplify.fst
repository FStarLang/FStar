module Pulse.Simplify

open Pulse.Show
open FStar.Reflection.V2
module T = FStar.Tactics.V2

(* Additional simplifications, gated behind `--ext pulse:extra_simplify`
since they change which slprops the prover can match syntactically, and
hence which programs verify. *)
let extra_simplify_enabled () : T.Tac bool =
  T.ext_enabled "pulse:extra_simplify"

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

let _simpl_list (t:thua_t) : T.Tac (option term) =
  match is_List_Tot_hd t with
  | Some x ->
    begin match is_Cons (thua x) with
    | Some (h, _) -> Some h
    | None -> None
    end
  | None ->
    match is_List_Tot_tl t with
    | Some x ->
      begin match is_Cons (thua x) with
      | Some (_, tl) -> Some tl
      | None -> None
      end
    | None -> None

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

let _simpl_option (t:thua_t) : T.Tac (option term) =
  match is_Some_v t with
  | Some o ->
    (match is_Some (thua o) with
    | Some x -> Some x
    | None -> None)
  | None -> None

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

let _simpl_reveal_hide (t:thua_t) : T.Tac (option term) =
  match is_reveal t with
  | Some (_, x) ->
    begin match is_hide (thua x) with
    | Some (_, x) -> Some x
    | None -> None
    end
  | None -> None

let _simpl_hide_reveal (t:thua_t) : T.Tac (option term) =
  match is_hide t with
  | Some (t1, x) ->
    begin match is_reveal (thua x) with
    | Some (t2, x) ->
      (* hide #nat (reveal #int x) is == to x *)
      if FStar.Reflection.TermEq.term_eq t1 t2
      then Some x
      else None
    | None -> None
    end
  | None -> None

(* A precondition is a trailing implicit [squash] argument now, so an
   application of a partial operation such as [FStar.SizeT.add] carries one
   more argument than the source writes.  Match on the explicit ones. *)
let explicit_args (args : list argv) : list argv =
  FStar.List.Tot.filter (fun (_, q) -> Q_Explicit? q) args

let is_size_t_v (t:thua_t) : T.Tac (option term) =
  match hua t with
  | Some (h, us, args) ->
    if implode_qn (T.inspect_fv h) = `%FStar.SizeT.v
    then
      match args with
      | [(t, Q_Explicit)] -> Some t
      | _ -> None
    else
    None
  | _ -> None

let _simpl_sizet_literal (t:thua_t) : T.Tac (option term) =
  match is_size_t_v t with
  | Some e -> (
    match hua (thua e) with
    | Some (h, us, args) ->
      if implode_qn (T.inspect_fv h) = `%FStar.SizeT.uint_to_t
      then
        match explicit_args args with
        | [(t, Q_Explicit)] -> Some t
        | _ -> None
      else
      None
    | None -> None
    )
  | None -> None

type op =
  | Add
  | Sub
  | Mul
  | Div
  | Rem

let is_size_t_op (fv : fv) : option op =
  match implode_qn (T.inspect_fv fv) with
  | `%FStar.SizeT.add -> Some Add
  | `%FStar.SizeT.sub -> Some Sub
  | `%FStar.SizeT.mul -> Some Mul
  | `%FStar.SizeT.div -> Some Div
  | `%FStar.SizeT.rem -> Some Rem
  | _ -> None

let math_opfv (o : op) : string =
  match o with
  | Add -> `%(+)
  | Sub -> `%(-)
  | Mul -> `%( * )
  | Div -> `%(/)
  | Rem -> `%(%)

let is_size_t_applied_op (t:thua_t) : T.Tac (option (op & term & term)) =
  match hua t with
  | Some (h, us, args) -> (
    match is_size_t_op h, explicit_args args with
    | Some op, [(l, Q_Explicit); (r, Q_Explicit)] ->
      Some (op, l, r)
    | _ -> None
  )
  | _ -> None

// Rewrites SZ.v (SZ.mul x y) to SZ.v x * SZ.v y, and similar
let _simpl_sizet_op (t:thua_t) : T.Tac (option term) =
  match is_size_t_v t with
  | Some e -> (
    match is_size_t_applied_op (thua e) with
    | Some (h, l, r) ->
      let f : fv = pack_fv <| explode_qn (math_opfv h) in
      let l' = `(FStar.SizeT.v (`#l)) in
      let r' = `(FStar.SizeT.v (`#r)) in
      Some (T.mk_app (T.Tv_UInst f []) [(l', Q_Explicit); (r', Q_Explicit)])
    | None -> None
    )
  | None -> None

(* Try each rule in turn, returning the rewritten term if one of them fires.
The rules guarded by `extra` are only tried when `--ext pulse:extra_simplify`
is set.
Note that we cannot detect "did anything change?" by comparing terms:
`FStar.Reflection.TermEq.term_eq` is conservative and returns false for equal
terms that are not faithful, e.g. any term containing a uvar. *)
let try_rules (extra:bool) (t:thua_t) : T.Tac (option thua_t) =
  match _simpl_proj t with
  | Some t -> Some (thua t)
  | None ->
  match _simpl_option t with
  | Some t -> Some (thua t)
  | None ->
  match _simpl_list t with
  | Some t -> Some (thua t)
  | None ->
  match _simpl_hide_reveal t with
  | Some t -> Some (thua t)
  | None ->
  match _simpl_reveal_hide t with
  | Some t -> Some (thua t)
  | None ->
  if not extra then None else
  match _simpl_sizet_op t with
  | Some t -> Some (thua t)
  | None ->
  match _simpl_sizet_literal t with
  | Some t -> Some (thua t)
  | None ->
  None

(* Apply the rules at the root until none of them fires. Every rule replaces the
term by one of its own subterms, so this terminates. *)
let rec apply_rules_fix (extra:bool) (t:thua_t) : T.Tac thua_t =
  match try_rules extra t with
  | Some t' -> apply_rules_fix extra t'
  | None -> t

(* The rules are applied at a node both before and after its arguments are
simplified.

Applying them before is what keeps this cheap: a rule discards whole branches
(`fst (a, b)` becomes `a`), and those branches are then never traversed.

Applying them again afterwards is what makes the pass complete: simplifying an
argument can expose a redex at a node that has already been visited, e.g. the
outer projection of `fst (fst ((c, ()), ()))` only becomes reducible once its
argument has been rewritten to `(c, ())`. A rule firing at that point returns a
subterm of an already-simplified argument, so no further traversal is needed. *)
let rec simplify' (extra:bool) (t0:term) : T.Tac term =
  let t = apply_rules_fix extra (thua t0) in
  let t =
    match hua t with
    | Some (h, us, args) ->
      let args = T.map (fun (t, q) -> simplify' extra t, q) args in
      fst (apply_rules_fix extra (thua (T.mk_app (T.Tv_UInst h us) args)))
    | _ -> fst t
  in
  // T.print <| "simplified " ^ show t0 ^ " to " ^ show t;
  t

let simplify (t0:term) : T.Tac term =
  simplify' (extra_simplify_enabled ()) t0
