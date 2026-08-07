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

module FStarC.Custard.Rename

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Show
open FStarC.Custard.Syntax

module SMap   = FStarC.SMap
module String = FStarC.String

(* Everything a local name may need to be looked up against: the renaming in
   force, and the names already taken in the enclosing scope. *)
type scope = {
  sub:  list (string & string);
  used: list string;
}

let empty_scope : scope = { sub = []; used = [] }

(* The name a binder should ideally get.  [Syntax.base_name] removes the
   uniquifying suffix that extraction added; what is left is the [ppname] the
   programmer wrote, except for the [uu____NNN] that F* invents for a binder
   the programmer wrote as [_], whose digits are just as volatile as the
   suffix we are removing and are collapsed too. *)
let preferred (x:string) : ML string =
  let b = base_name x in
  let b = if String.length b >= 4 && String.substring b 0 4 = "uu__" then "tmp" else b in
  if b = "" then "x" else b

let taken (s:scope) (x:string) : ML bool =
  List.existsb (fun u -> u = x) s.used

let rec pick (s:scope) (b:string) (i:int) : ML string =
  let cand = if i = 0 then b else b ^ show i in
  if taken s cand then pick s b (i + 1) else cand

(* Bind [x], returning the name it gets and the scope its body sees. *)
let bind (s:scope) (x:string) : ML (string & scope) =
  let n = pick s (preferred x) 0 in
  (n, { sub = (x, n) :: s.sub; used = n :: s.used })

let lookup (s:scope) (x:string) : ML string =
  match List.tryFind (fun (a, _) -> a = x) s.sub with
  | Some (_, n) -> n
  (* Not bound here: either a type variable used inside a value scope, or --
     if this ever fires -- a bug.  Falling back on the preferred name keeps
     the output free of uniquifying suffixes either way. *)
  | None -> preferred x

let rec bind_all (s:scope) (xs:list string) : ML (list string & scope) =
  match xs with
  | [] -> ([], s)
  | x :: xs ->
    let n, s = bind s x in
    let ns, s = bind_all s xs in
    (n :: ns, s)

(* -------------------------------------------------------------------- *)
(* Types                                                                *)
(* -------------------------------------------------------------------- *)

let rec rn_cty (ts:scope) (c:cty) : ML cty =
  match c with
  | TVar x -> TVar (lookup ts x)
  | TArrow (a, e, b) -> TArrow (rn_cty ts a, e, rn_cty ts b)
  | TApp (n, args) -> TApp (n, args |> List.map (rn_cty ts))
  | TBuf t -> TBuf (rn_cty ts t)
  | TRef t -> TRef (rn_cty ts t)
  | TTuple cs -> TTuple (cs |> List.map (rn_cty ts))
  | c -> c

(* -------------------------------------------------------------------- *)
(* Expressions                                                          *)
(* -------------------------------------------------------------------- *)

(* Field names live in their constructor's namespace, not the enclosing term's,
   so they are renamed once per declaration and the result recorded here for
   the [ERecord]/[EProj] nodes that mention them. *)
let field_key (n:name) (f:string) : ML string = string_of_name n ^ "." ^ f

let rn_field (fields:SMap.t string) (n:name) (f:string) : ML string =
  match SMap.try_find fields (field_key n f) with
  | Some f' -> f'
  | None -> preferred f

let rec rn_pat (fields:SMap.t string) (s:scope) (p:pat) : ML (pat & scope) =
  match p with
  | PWild
  | PConst _ -> (p, s)
  | PVar x ->
    let n, s = bind s x in
    (PVar n, s)
  | PCtor (n, ps) ->
    let ps, s = rn_pats fields s ps in
    (PCtor (n, ps), s)
  | PTuple ps ->
    let ps, s = rn_pats fields s ps in
    (PTuple ps, s)
  (* The alternatives of an or-pattern bind the same names, so threading the
     scope through them is the same as renaming each separately. *)
  | POr ps ->
    let ps, s = rn_pats fields s ps in
    (POr ps, s)

and rn_pats (fields:SMap.t string) (s:scope) (ps:list pat) : ML (list pat & scope) =
  match ps with
  | [] -> ([], s)
  | p :: ps ->
    let p, s = rn_pat fields s p in
    let ps, s = rn_pats fields s ps in
    (p :: ps, s)

let rec rn_expr (fields:SMap.t string) (ts:scope) (s:scope) (x:expr) : ML expr =
  let go = rn_expr fields ts s in
  let ty = rn_cty ts x.ty in
  let e =
    match x.e with
    | EConst _
    | EAny
    | EAbort _ -> x.e

    | EVar v -> EVar (lookup s v)
    | EQual (n, args) -> EQual (n, args |> List.map (rn_cty ts))

    | ELet (v, t, e1, e2) ->
      let t = rn_cty ts t in
      let e1 = go e1 in
      let v', s' = bind s v in
      ELet (v', t, e1, rn_expr fields ts s' e2)

    | EFun (bs, body) ->
      let bs, s' = rn_binders ts s bs in
      EFun (bs, rn_expr fields ts s' body)

    | EApp (h, args) -> EApp (go h, args |> List.map go)
    | EMatch (scrut, brs) ->
      EMatch (go scrut, brs |> List.map (rn_branch fields ts s))
    | EIf (c, t1, t2) -> EIf (go c, go t1, go t2)
    | ESeq (e1, e2) -> ESeq (go e1, go e2)
    | ECtor (n, es) -> ECtor (n, es |> List.map go)
    | ETuple es -> ETuple (es |> List.map go)
    | ERecord (n, fs) ->
      ERecord (n, fs |> List.map (fun (f, e) -> (rn_field fields n f, go e)))
    | EProj (e1, n, f) -> EProj (go e1, n, rn_field fields n f)
    | EDiscrim (e1, n) -> EDiscrim (go e1, n)
    | ECast (e1, t) -> ECast (go e1, rn_cty ts t)
    | EOp (o, es) -> EOp (o, es |> List.map go)
    | EWhile (c, b) -> EWhile (go c, go b)
    | ERaise (n, es) -> ERaise (n, es |> List.map go)
    | ETry (e1, brs) -> ETry (go e1, brs |> List.map (rn_branch fields ts s))
  in
  { x with e = e; ty = ty }

and rn_branch (fields:SMap.t string) (ts:scope) (s:scope) (br:branch) : ML branch =
  let p, g, b = br in
  let p, s = rn_pat fields s p in
  (p, (match g with None -> None | Some g -> Some (rn_expr fields ts s g)),
   rn_expr fields ts s b)

and rn_binders (ts:scope) (s:scope) (bs:list binder) : ML (list binder & scope) =
  match bs with
  | [] -> ([], s)
  | b :: bs ->
    let t = rn_cty ts b.b_ty in
    let n, s = bind s b.b_name in
    let bs, s = rn_binders ts s bs in
    ({ b_name = n; b_ty = t } :: bs, s)

(* -------------------------------------------------------------------- *)
(* Declarations                                                         *)
(* -------------------------------------------------------------------- *)

(* A constructor's fields are a scope of their own, so they are renamed in one
   pass over the declaration and the result is published in [fields] for the
   accessors elsewhere in the program to find. *)
let rn_fields (fields:SMap.t string) (n:name) (ts:scope)
              (fs:list (string & cty)) : ML (list (string & cty)) =
  let rec go (s:scope) (fs:list (string & cty)) : ML (list (string & cty)) =
    match fs with
    | [] -> []
    | (f, c) :: fs ->
      let f', s = bind s f in
      SMap.add fields (field_key n f) f';
      (f', rn_cty ts c) :: go s fs in
  go empty_scope fs

let rn_tydef (fields:SMap.t string) (self:name) (ts:scope) (b:tydef) : ML tydef =
  match b with
  | TAbbrev c -> TAbbrev (rn_cty ts c)
  | TRecord fs -> TRecord (rn_fields fields self ts fs)
  | TVariant cs -> TVariant (cs |> List.map (fun (cn, fs) -> (cn, rn_fields fields cn ts fs)))
  | TAbstract -> TAbstract

(* Types have to be renamed before terms: a term that reads a field needs the
   field's new name, and the declaration it belongs to may come later in the
   program order. *)
let rn_types (fields:SMap.t string) (d:decl) : ML decl =
  match d with
  | DType t ->
    let params, ts = bind_all empty_scope t.dt_params in
    DType { t with dt_params = params; dt_body = rn_tydef fields t.dt_name ts t.dt_body }
  | d -> d

let rn_terms (fields:SMap.t string) (d:decl) : ML decl =
  match d with
  | DType _ -> d
  | DLet l ->
    let typars, ts = bind_all empty_scope l.dl_typars in
    (* Type and value names share a namespace in neither backend, so a value
       binder is free to reuse a type variable's name. *)
    let binders, s = rn_binders ts empty_scope l.dl_binders in
    DLet { l with dl_typars = typars;
                  dl_binders = binders;
                  dl_ret = rn_cty ts l.dl_ret;
                  dl_body = rn_expr fields ts s l.dl_body }
  | DExternal x -> DExternal { x with dx_ty = rn_cty empty_scope x.dx_ty }
  | DExn e -> DExn { e with de_args = e.de_args |> List.map (rn_cty empty_scope) }

let run (prog:program) : ML program =
  let fields : SMap.t string = SMap.create 50 in
  let prog = prog |> List.map (rn_types fields) in
  prog |> List.map (rn_terms fields)
