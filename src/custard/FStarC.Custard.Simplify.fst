(*
   Copyright 2008-2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module FStarC.Custard.Simplify

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Show
open FStarC.Custard.Syntax

module SMap   = FStarC.SMap
module GenSym = FStarC.GenSym

(* Does [v] occur free in [e]?  Custard's variable names come from F* bound
   variables and so already carry a unique index, but this deliberately does
   not track shadowing: an over-count keeps a binding that could have been
   dropped, which is the safe direction. *)
let rec occurs (v:string) (x:expr) : ML bool =
  match x.e with
  | EVar w -> w = v
  | EConst _ | EQual _ -> false
  | ELet (_, _, e1, e2) -> occurs v e1 || occurs v e2
  | EApp (h, es) -> occurs v h || occurs_list v es
  | EFun (_, b) -> occurs v b
  | EMatch (s, brs) -> occurs v s || occurs_branches v brs
  | EIf (c, a, b) -> occurs v c || occurs v a || occurs v b
  | EAny | EAbort _ -> false
  | ESeq (a, b) -> occurs v a || occurs v b
  | ECtor (_, es) | ETuple es | EOp (_, es) | ERaise (_, es) -> occurs_list v es
  | ERecord (_, fs) -> occurs_list v (fs |> List.map snd)
  | EProj (e1, _, _) | EDiscrim (e1, _) | ECast (e1, _) -> occurs v e1
  | EWhile (a, b) -> occurs v a || occurs v b
  | ETry (a, brs) -> occurs v a || occurs_branches v brs

and occurs_list (v:string) (es:list expr) : ML bool =
  es |> List.existsb (occurs v)

and occurs_branches (v:string) (brs:list branch) : ML bool =
  brs |> List.existsb (fun (_, g, b) ->
    (match g with None -> false | Some g -> occurs v g) || occurs v b)

let rec simpl (x:expr) : ML expr =
  match x.e with
  | ELet (v, ty, e1, e2) ->
    let e1 = simpl e1 in
    let e2 = simpl e2 in
    (* [let x = e in x] is just [e], whatever [e]'s effect: nothing moves. *)
    if (match e2.e with EVar w -> w = v | _ -> false) then e1
    else if occurs v e2 then { x with e = ELet (v, ty, e1, e2) }
    (* Section 7.3: an unused binding may only be deleted if evaluating it is
       unobservable; otherwise it becomes a statement, which keeps its effect
       and its position. *)
    else if is_pure e1.eff then e2
    else { x with e = ESeq (e1, e2) }

  | ESeq (e1, e2) ->
    let e1 = simpl e1 in
    let e2 = simpl e2 in
    if is_pure e1.eff then e2 else { x with e = ESeq (e1, e2) }

  | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> x
  | EApp (h, es) -> { x with e = EApp (simpl h, es |> List.map simpl) }
  | EFun (bs, b) -> { x with e = EFun (bs, simpl b) }
  | EMatch (s, brs) -> { x with e = EMatch (simpl s, brs |> List.map simpl_branch) }
  | EIf (c, a, b) -> { x with e = EIf (simpl c, simpl a, simpl b) }
  | ECtor (n, es) -> { x with e = ECtor (n, es |> List.map simpl) }
  | ETuple es -> { x with e = ETuple (es |> List.map simpl) }
  | EOp (o, es) -> { x with e = EOp (o, es |> List.map simpl) }
  | ERaise (n, es) -> { x with e = ERaise (n, es |> List.map simpl) }
  | ERecord (n, fs) -> { x with e = ERecord (n, fs |> List.map (fun (f, e) -> (f, simpl e))) }
  | EProj (e1, n, f) -> { x with e = EProj (simpl e1, n, f) }
  | EDiscrim (e1, n) -> { x with e = EDiscrim (simpl e1, n) }
  | ECast (e1, c) -> { x with e = ECast (simpl e1, c) }
  | EWhile (a, b) -> { x with e = EWhile (simpl a, simpl b) }
  | ETry (a, brs) -> { x with e = ETry (simpl a, brs |> List.map simpl_branch) }

and simpl_branch (br:branch) : ML branch =
  let p, g, b = br in
  (p, (match g with None -> None | Some g -> Some (simpl g)), simpl b)

(* -------------------------------------------------------------------- *)
(* Inlining                                                             *)
(* -------------------------------------------------------------------- *)

(* A substitution of expressions for variables, plus the renaming that keeps
   the copy's own bound variables distinct from the ones at the call site.
   Both are string maps because Custard variable names are already unique per
   definition; only *copying* a definition can break that. *)
let subst = SMap.t expr

let rename (x:string) : ML string = x ^ "_i" ^ show (GenSym.next_id ())

let rec sub (sm:subst) (x:expr) : ML expr =
  let g = sub sm in
  match x.e with
  | EVar v ->
    (match SMap.try_find sm v with
     | Some e -> e
     | None -> x)
  | EConst _ | EQual _ | EAny | EAbort _ -> x
  | ELet (v, ty, e1, e2) ->
    let v' = rename v in
    let e1 = g e1 in
    SMap.add sm v { x with e = EVar v'; ty; eff = E_Pure };
    let e2 = sub sm e2 in
    { x with e = ELet (v', ty, e1, e2) }
  | EApp (h, es) -> { x with e = EApp (g h, es |> List.map g) }
  | EFun (bs, b) ->
    let bs = bs |> List.map (fun b ->
      let n = rename b.b_name in
      SMap.add sm b.b_name { e = EVar n; ty = b.b_ty; eff = E_Pure };
      { b with b_name = n }) in
    { x with e = EFun (bs, sub sm b) }
  | EMatch (s, brs) -> { x with e = EMatch (g s, brs |> List.map (sub_branch sm)) }
  | EIf (c, a, b) -> { x with e = EIf (g c, g a, g b) }
  | ESeq (a, b) -> { x with e = ESeq (g a, g b) }
  | ECtor (n, es) -> { x with e = ECtor (n, es |> List.map g) }
  | ETuple es -> { x with e = ETuple (es |> List.map g) }
  | EOp (o, es) -> { x with e = EOp (o, es |> List.map g) }
  | ERaise (n, es) -> { x with e = ERaise (n, es |> List.map g) }
  | ERecord (n, fs) -> { x with e = ERecord (n, fs |> List.map (fun (f, e) -> (f, g e))) }
  | EProj (e1, n, f) -> { x with e = EProj (g e1, n, f) }
  | EDiscrim (e1, n) -> { x with e = EDiscrim (g e1, n) }
  | ECast (e1, c) -> { x with e = ECast (g e1, c) }
  | EWhile (a, b) -> { x with e = EWhile (g a, g b) }
  | ETry (a, brs) -> { x with e = ETry (g a, brs |> List.map (sub_branch sm)) }

and sub_branch (sm:subst) (br:branch) : ML branch =
  let p, guard, b = br in
  let p = sub_pat sm p in
  (p, (match guard with None -> None | Some e -> Some (sub sm e)), sub sm b)

and sub_pat (sm:subst) (p:pat) : ML pat =
  match p with
  | PWild | PConst _ -> p
  | PVar v ->
    let v' = rename v in
    (* The type is unknown here, and nothing downstream reads it off a
       pattern variable's occurrence. *)
    SMap.add sm v { e = EVar v'; ty = TAny; eff = E_Pure };
    PVar v'
  | PCtor (n, ps) -> PCtor (n, ps |> List.map (sub_pat sm))
  | PTuple ps -> PTuple (ps |> List.map (sub_pat sm))
  | POr ps -> POr (ps |> List.map (sub_pat sm))

let imax (a b : int) : int = if a >= b then a else b
let imin (a b : int) : int = if a <= b then a else b

(* How many times does [v] occur in [x]?  Capped at 2, which is all the
   decision below needs. *)
let rec count (v:string) (x:expr) : ML int =
  if occurs v x then (match x.e with
    | EVar _ -> 1
    | ELet (_, _, e1, e2) -> imin 2 (count v e1 + count v e2)
    | EApp (h, es) -> imin 2 (count v h + count_list v es)
    | EFun (_, b) -> count v b
    | EMatch (s, brs) ->
      (* The branches are alternatives, so the worst one is the count. *)
      imin 2 (count v s + (brs |> List.fold_left (fun acc (_, g, b) ->
               imax acc (count v b + (match g with None -> 0 | Some g -> count v g))) 0))
    | EIf (c, a, b) -> imin 2 (count v c + imax (count v a) (count v b))
    | EAny | EAbort _ -> 0
    | ESeq (a, b) -> imin 2 (count v a + count v b)
    | ECtor (_, es) | ETuple es | EOp (_, es) | ERaise (_, es) -> count_list v es
    | ERecord (_, fs) -> count_list v (fs |> List.map snd)
    | EProj (e1, _, _) | EDiscrim (e1, _) | ECast (e1, _) -> count v e1
    | EWhile (a, b) -> imin 2 (count v a + count v b)
    | ETry (a, brs) -> imin 2 (count v a + (brs |> List.fold_left (fun acc (_, _, b) ->
                                imax acc (count v b)) 0))
    | _ -> 1)
  else 0

and count_list (v:string) (es:list expr) : ML int =
  es |> List.fold_left (fun acc e -> imin 2 (acc + count v e)) 0

(* Duplicating an argument is only sound when evaluating it is unobservable,
   and only desirable when it is trivial; otherwise it gets a [let], which the
   simplifier will drop again if the parameter turns out to be unused. *)
let is_atomic (e:expr) : bool =
  match e.e with
  | EVar _ | EConst _ | EQual _ -> true
  | _ -> false

let inline_call (bs : list binder) (body:expr) (args:list expr) (at:expr) : ML expr =
  let sm : subst = SMap.create 10 in
  let lets = List.zip bs args |> List.collect (fun (b, a) ->
    if is_atomic a || (is_pure a.eff && count b.b_name body <= 1)
    then (SMap.add sm b.b_name a; [])
    else
      let v = rename b.b_name in
      SMap.add sm b.b_name { a with e = EVar v };
      [(v, b.b_ty, a)]) in
  let r = sub sm body in
  let r = { r with ty = at.ty; eff = at.eff } in
  List.fold_right (fun (v, ty, a) acc ->
    { acc with e = ELet (v, ty, a, acc) }) lets r

(* [Inline] declarations are substituted at their fully applied uses.  A use
   that is *not* fully applied keeps the declaration alive, so it is emitted
   after all; that is rare enough not to be worth eta-expanding. *)
let rec inline_expr (tbl : SMap.t (list binder & expr)) (used : SMap.t bool) (x:expr)
  : ML expr =
  (* [used] records the [Inline] declarations that had to be kept after all,
     either because a use was not fully applied or because it came before the
     definition (which a mutually recursive group can do). *)
  let g = inline_expr tbl used in
  match x.e with
  | EApp ({e = EQual (n, tys)}, args) ->
    let args = args |> List.map g in
    (match SMap.try_find tbl (string_of_name n) with
     | Some (bs, body) when List.length bs = List.length args ->
       inline_call bs body args x
     | _ -> SMap.add used (string_of_name n) true;
            { x with e = EApp ({ x with e = EQual (n, tys) }, args) })
  | EQual (n, _) ->
    (match SMap.try_find tbl (string_of_name n) with
     | Some ([], body) -> inline_call [] body [] x
     | _ -> SMap.add used (string_of_name n) true; x)
  | EConst _ | EVar _ | EAny | EAbort _ -> x
  | ELet (v, ty, e1, e2) -> { x with e = ELet (v, ty, g e1, g e2) }
  | EApp (h, es) -> { x with e = EApp (g h, es |> List.map g) }
  | EFun (bs, b) -> { x with e = EFun (bs, g b) }
  | EMatch (s, brs) -> { x with e = EMatch (g s, brs |> List.map (inline_branch tbl used)) }
  | EIf (c, a, b) -> { x with e = EIf (g c, g a, g b) }
  | ESeq (a, b) -> { x with e = ESeq (g a, g b) }
  | ECtor (n, es) -> { x with e = ECtor (n, es |> List.map g) }
  | ETuple es -> { x with e = ETuple (es |> List.map g) }
  | EOp (o, es) -> { x with e = EOp (o, es |> List.map g) }
  | ERaise (n, es) -> { x with e = ERaise (n, es |> List.map g) }
  | ERecord (n, fs) -> { x with e = ERecord (n, fs |> List.map (fun (f, e) -> (f, g e))) }
  | EProj (e1, n, f) -> { x with e = EProj (g e1, n, f) }
  | EDiscrim (e1, n) -> { x with e = EDiscrim (g e1, n) }
  | ECast (e1, c) -> { x with e = ECast (g e1, c) }
  | EWhile (a, b) -> { x with e = EWhile (g a, g b) }
  | ETry (a, brs) -> { x with e = ETry (g a, brs |> List.map (inline_branch tbl used)) }

and inline_branch (tbl : SMap.t (list binder & expr)) (used : SMap.t bool) (br:branch)
  : ML branch =
  let p, guard, b = br in
  (p, (match guard with None -> None | Some e -> Some (inline_expr tbl used e)),
   inline_expr tbl used b)

(* -------------------------------------------------------------------- *)
(* Eta reduction                                                        *)
(* -------------------------------------------------------------------- *)

(* F* stores the projector of a field whose type is an arrow eta-expanded:
   [let __proj__Mkht_t__item__hashf projectee x = (match projectee with ... ) x].
   Extraction faithfully reproduces that, and the extra binder then defeats
   both projector inlining (which needs an exactly saturated use) and the C
   backend (which sees a call with too few arguments).  Dropping a trailing
   binder that is applied to a pure head, and to nothing else, is always sound;
   the arrow it used to consume moves into the result type. *)

let rec split_last (es:list 'a) : ML (option (list 'a & 'a)) =
  match es with
  | [] -> None
  | [e] -> Some ([], e)
  | e :: es -> (match split_last es with
                | Some (pre, last) -> Some (e :: pre, last)
                | None -> None)

let rec eta_reduce (bs:list binder) (body:expr) (ret:cty) (ef:eff)
  : ML (list binder & expr & cty & eff) =
  match split_last bs, body.e with
  | Some (bs', b), EApp (f, args) when Cons? bs' ->
    (match split_last args with
     | Some (args', { e = EVar v }) when v = b.b_name
                                      && is_pure f.eff
                                      && not (occurs v f)
                                      && not (args' |> List.existsb (occurs v)) ->
       let ret' = TArrow (b.b_ty, ef, ret) in
       let body' = match args' with
                   | [] -> { f with ty = ret' }
                   | _ -> { body with e = EApp (f, args'); ty = ret'; eff = E_Pure } in
       eta_reduce bs' body' ret' E_Pure
     | _ -> (bs, body, ret, ef))
  | _ -> (bs, body, ret, ef)

let eta_reduce_decls (prog:program) : ML program =
  prog |> List.map (fun d ->
    match d with
    | DLet l ->
      let bs, body, ret, ef = eta_reduce l.dl_binders l.dl_body l.dl_ret l.dl_eff in
      DLet { l with dl_binders = bs; dl_body = body; dl_ret = ret; dl_eff = ef }
    | d -> d)

(* One left-to-right pass: the program is topologically sorted, so by the time
   an [Inline] body is stored it has already had its own callees inlined. *)
let inline_decls (prog:program) : ML program =
  let tbl : SMap.t (list binder & expr) = SMap.create 50 in
  let used : SMap.t bool = SMap.create 50 in
  let prog = prog |> List.map (fun d ->
    match d with
    | DLet dl ->
      let body = inline_expr tbl used dl.dl_body in
      if dl.dl_flags |> List.existsb Inline?
      then SMap.add tbl (string_of_name dl.dl_name) (dl.dl_binders, body);
      DLet { dl with dl_body = body }
    | d -> d) in
  prog |> List.filter (fun d ->
    match d with
    | DLet dl -> not (dl.dl_flags |> List.existsb Inline?)
              || Some? (SMap.try_find used (string_of_name dl.dl_name))
    | _ -> true)

(* -------------------------------------------------------------------- *)
(* Dead-declaration elimination                                         *)
(* -------------------------------------------------------------------- *)

(* Extraction requests a definition as soon as it meets one, including from
   positions that the layout analysis later erases -- the ghost model of a data
   structure, say.  What is left behind is a specification-only declaration
   that nothing reachable calls: harmless in OCaml, but karamel rejects it
   ("not Low*", because specifications use mathematical integers), so it has to
   go.  Reachability is computed after inlining, when the call graph is final. *)

let rec cty_deps (c:cty) : ML (list string) =
  match c with
  | TApp (n, args) -> string_of_name n :: List.collect cty_deps args
  | TArrow (a, _, b) -> cty_deps a @ cty_deps b
  | TTuple cs -> List.collect cty_deps cs
  | TBuf c -> cty_deps c
  | _ -> []

let rec pat_deps (p:pat) : ML (list string) =
  match p with
  | PCtor (n, ps) -> string_of_name n :: List.collect pat_deps ps
  | PTuple ps
  | POr ps -> List.collect pat_deps ps
  | _ -> []

let rec expr_deps (x:expr) : ML (list string) =
  let ds = cty_deps x.ty in
  let sub (es:list expr) : ML (list string) = List.collect expr_deps es in
  ds @ (match x.e with
        | EQual (n, tys) -> string_of_name n :: List.collect cty_deps tys
        | ECtor (n, es) | ERaise (n, es) -> string_of_name n :: sub es
        | ERecord (n, fs) -> string_of_name n :: sub (List.map snd fs)
        | EDiscrim (e, n) -> string_of_name n :: expr_deps e
        | EProj (e, n, _) -> string_of_name n :: expr_deps e
        | EConst _ | EVar _ | EAny | EAbort _ -> []
        | ELet (_, t, e1, e2) -> cty_deps t @ sub [e1; e2]
        | EApp (h, es) -> sub (h :: es)
        | EFun (bs, b) -> List.collect (fun (b:binder) -> cty_deps b.b_ty) bs @ expr_deps b
        | EMatch (sc, brs) ->
          expr_deps sc @ (brs |> List.collect (fun (p, g, b) ->
            pat_deps p @ (match g with Some g -> expr_deps g | None -> []) @ expr_deps b))
        | EIf (c, a, b) -> sub [c; a; b]
        | ESeq (a, b) -> sub [a; b]
        | ETuple es | EOp (_, es) -> sub es
        | ECast (e, t) -> cty_deps t @ expr_deps e
        | EWhile (c, b) -> sub [c; b]
        | ETry (e, brs) ->
          expr_deps e @ (brs |> List.collect (fun (p, g, b) ->
            pat_deps p @ (match g with Some g -> expr_deps g | None -> []) @ expr_deps b)))

let decl_deps (d:decl) : ML (list string) =
  match d with
  | DLet l ->
    List.collect (fun (b:binder) -> cty_deps b.b_ty) l.dl_binders
    @ cty_deps l.dl_ret @ expr_deps l.dl_body
  | DType t ->
    (match t.dt_body with
     | TAbbrev c -> cty_deps c
     | TRecord fs -> List.collect (fun (_, c) -> cty_deps c) fs
     | TVariant cs -> cs |> List.collect (fun (_, fs) ->
                        List.collect (fun (_, c) -> cty_deps c) fs)
     | TAbstract -> [])
  | DExternal x -> cty_deps x.dx_ty
  | DExn e -> List.collect cty_deps e.de_args

(* A constructor or field name refers to its declaration, not to itself. *)
let owners (prog:program) : ML (SMap.t string) =
  let m : SMap.t string = SMap.create 50 in
  prog |> List.iter (fun d ->
    match d with
    | DType t ->
      let owner = string_of_name t.dt_name in
      (match t.dt_body with
       | TVariant cs -> cs |> List.iter (fun (cn, _) -> SMap.add m (string_of_name cn) owner)
       | _ -> ())
    | _ -> ());
  m

let dce (prog:program) : ML program =
  let own = owners prog in
  let resolve (n:string) : ML string =
    match SMap.try_find own n with Some o -> o | None -> n in
  let defs : SMap.t decl = SMap.create 50 in
  prog |> List.iter (fun d -> SMap.add defs (string_of_name (name_of_decl d)) d);
  let live : SMap.t bool = SMap.create 50 in
  let rec visit (n:string) : ML unit =
    let n = resolve n in
    if None? (SMap.try_find live n) then begin
      SMap.add live n true;
      match SMap.try_find defs n with
      | Some d -> decl_deps d |> List.iter visit
      | None -> ()
    end in
  prog |> List.iter (fun d ->
    if decl_flags d |> List.existsb (fun f -> Root? f || Entrypoint? f)
    then visit (string_of_name (name_of_decl d)));
  prog |> List.filter (fun d ->
    Some? (SMap.try_find live (string_of_name (name_of_decl d))))

let run (prog:program) : ML program =
  let prog = eta_reduce_decls prog in
  let prog = inline_decls prog in
  let prog = prog |> List.map (fun d ->
    match d with
    | DLet dl -> DLet { dl with dl_body = simpl dl.dl_body }
    | d -> d) in
  dce prog
