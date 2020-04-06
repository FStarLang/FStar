(*
   Copyright 2008-2020 Microsoft Research

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
#light "off"
module FStar.Extraction.ML.UEnv

(** This module provides a typing environment used for extracting
    programs to ML. It addresses the following main concerns:

    It distinguishes between several kinds of names:
        - local type variable ('a, 'b, ...)
        - type definition (list, option, ...)
        - local variable (x, y, ...)
        - top-level names (List.map, ...)
        - record field names
        - module names

    For each kind, it supports generating an OCaml/F# compatible name
    respecting the naming and keyword conventions of those languages.

    Further, for each F* name of a given kind (except for module
    names), it generates a unique name in a scope for that kind.

    See tests/bug-reports/Bug310.fst for several examples of the
    kinds of concerns this addresses.
 *)

open FStar.ST
open FStar.All
open FStar
open FStar.Util
open FStar.Ident
open FStar.Extraction.ML.Syntax
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.TypeChecker
module U  = FStar.Syntax.Util
module BU = FStar.Util
module Const = FStar.Parser.Const


(** An ML identifier corresponding to an identifier in F* that binds a
    type, e.g., [a:Type].

    In the common case, [ty_b_name] is a type variable (e.g., ['a]),
    and [ty_b_ty] is just an [(MLTY_Var 'a)]

    However, there are cases where the F* identifier cannot be
    translated to a type-identifier in OCaml, e.g., if [a:Type] does
    not appear prenex quantified. In such cases, [ty_b_name] is a
    ML term identifer (e.g., [a]) and [ty_b_ty] is [MLTY_Top].
  *)
type ty_binding = {
    ty_b_name: mlident;
    ty_b_ty: mlty
}

(** A term identifier in ML
      -- [exp_b_name] is the short name

      -- [exp_b_expr] is usually the long name, although in some cases
         it could be the long name applied to a unit, in case extraction
         needed to add a thunk to respect ML's value restriction.

      -- [exp_b_tscheme] the polymorphic ML type

      -- [exp_b_inst_ok] a flag that tells whether its okay for this
         identifier to be instantiated
 *)
type exp_binding = {
    exp_b_name: mlident;
    exp_b_expr: mlexpr;
    exp_b_tscheme: mltyscheme;
    exp_b_inst_ok: bool
}

type ty_or_exp_b = either<ty_binding, exp_binding>

(**
    [Bv]: An F* local binding [bv] can either correspond to an ML
          type or term binding.

    [Fv]: An F* top-level fv is associated with an ML term binding.
          Type definitions are maintained separately, see [tydef].
  *)
type binding =
    | Bv  of bv * ty_or_exp_b
    | Fv  of fv * exp_binding

(** A top-level F* type definition, i.e., a type abbreviation,
    corresponds to a [tydef] in ML.

    Note, inductive types (e.g., list, option etc.) are separately
    tracked as [tyname], see below.

    - [fv] The source F* identifier
    - [tydef_mlmodule_name, tydef_name] An mlpath for [fv]
    - [tydef_def]: The definition of the abbreviation
 *)
type tydef = {
    tydef_fv:fv;
    tydef_mlmodule_name:list<mlsymbol>;
    tydef_name:mlsymbol;
    tydef_def:mltyscheme
}

(** tydef is abstract:  Some accessors *)
let tydef_fv (td : tydef) = td.tydef_fv
let tydef_def (td : tydef) = td.tydef_def
let tydef_mlpath (td: tydef) : mlpath = td.tydef_mlmodule_name, td.tydef_name

(** The main type of this module; it's abstract

    - [env_tcenv]: The underlying typechecker environment
    - [env_bindings]: names in scope
    - [env_mlident_map]: The set of names currently in scope
    - [mlpath_of_lid]: A map from a full F* lident to its corresponding mlpath
    - [env_fieldname_map]: The set of record field names current in scope
    - [mlpath_of_fieldname]: A map from a full F* record field identifier to its corresponding mlpath
    - [tydefs]: Type abbreviations in scope
    - [type_names]: Inductive type constructors in scope
    - [currentModule]: ML name of the current module being extracted
 *)
type uenv = {
    env_tcenv: TypeChecker.Env.env;
    env_bindings:list<binding>;
    env_mlident_map:psmap<mlident>;
    mlpath_of_lid:psmap<mlpath>;
    env_fieldname_map:psmap<mlident>;
    mlpath_of_fieldname:psmap<mlpath>;
    tydefs:list<tydef>;
    type_names:list<(fv*mlpath)>;
    currentModule: mlpath // needed to properly translate the definitions in the current file
}

let tcenv_of_uenv (u:uenv) : TypeChecker.Env.env = u.env_tcenv
let set_tcenv (u:uenv) (t:TypeChecker.Env.env) = { u with env_tcenv=t}

let current_module_of_uenv (u:uenv) : mlpath = u.currentModule
let set_current_module (u:uenv) (m:mlpath) : uenv = { u with currentModule = m }

(* Only for printing in Modul.fs *)
let bindings_of_uenv u = u.env_bindings

let debug g f =
    let c = string_of_mlpath g.currentModule in
    if Options.debug_at_level c (Options.Other "Extraction")
    then f ()


(* TODO : need to make sure that the result of this name change does not collide with a variable already in the context. That might cause a change in semantics.
   E.g. , consider the following in F*
   let mkPair (a:Type) ('a:Type) (ta : a) (ta' : a') = (ta, ta')

   Perhaps this function also needs to look at env.Gamma*)

(* TODO : if there is a single quote in the name of the type variable, the
 * additional tick in the beginning causes issues with the lexer/parser of OCaml
 * (syntax error).
  Perhaps the type variable is interpreted as a string literal.  For an example,
  see
  https://github.com/FStarLang/FStar/blob/f53844512c76bd67b21b4cf68d774393391eac75/lib/FStar.Heap.fst#L49

   Coq seems to add a space after the tick in such cases. Always adding a space for now
  *)

let rec lookup_ty_local (gamma:list<binding>) (b:bv) : mlty =
    match gamma with
        | (Bv (b', Inl ty_b)) :: tl -> if (bv_eq b b') then ty_b.ty_b_ty else lookup_ty_local tl b
        | (Bv (b', Inr _)) :: tl -> if (bv_eq b b') then failwith ("Type/Expr clash: "^(b.ppname.idText)) else lookup_ty_local tl b
        | _::tl -> lookup_ty_local tl b
        | [] -> failwith ("extraction: unbound type var "^(b.ppname.idText))

let tyscheme_of_td (_, _, _, vars, _, body_opt) : option<mltyscheme> =
    match body_opt with
    | Some (MLTD_Abbrev t) -> Some (vars, t)
    | _ -> None

//TODO: this two-level search is pretty inefficient: we should optimize it
let lookup_ty_const (env:uenv) ((module_name, ty_name):mlpath) : option<mltyscheme> =
    BU.find_map env.tydefs  (fun tydef ->
        if ty_name = tydef.tydef_name
        && module_name = tydef.tydef_mlmodule_name
        then Some tydef.tydef_def
        else None)

let module_name_of_fv fv = fv.fv_name.v.ns |> List.map (fun (i:ident) -> i.idText)

let try_lookup_fv (g:uenv) (fv:fv) : option<exp_binding> =
    BU.find_map g.env_bindings (function
        | Fv (fv', t) when fv_eq fv fv' -> Some t
        | _ -> None)

let lookup_fv (g:uenv) (fv:fv) : exp_binding =
    match try_lookup_fv g fv with
    | None -> failwith (BU.format2 "(%s) free Variable %s not found\n" (Range.string_of_range fv.fv_name.p) (Print.lid_to_string fv.fv_name.v))
    | Some y -> y

let lookup_bv (g:uenv) (bv:bv) : ty_or_exp_b =
    let x = BU.find_map g.env_bindings (function
        | Bv (bv', r) when bv_eq bv bv' -> Some (r)
        | _ -> None) in
    match x with
        | None -> failwith (BU.format2 "(%s) bound Variable %s not found\n" (Range.string_of_range bv.ppname.idRange) (Print.bv_to_string bv))
        | Some y -> y


let lookup  (g:uenv) (x:either<bv,fv>) : ty_or_exp_b * option<fv_qual> =
    match x with
    | Inl x -> lookup_bv g x, None
    | Inr x -> Inr (lookup_fv g x), x.fv_qual

let lookup_term g (t:term) = match t.n with
    | Tm_name x -> lookup g (Inl x)
    | Tm_fvar x -> lookup g (Inr x)
    | _ -> failwith "Impossible: lookup_term for a non-name"

(* do we really need to keep gamma uptodate with hidden binders? For using F* utils, we just need to keep tcenv update.
 An alternative solution is to remove these binders from the type of the inductive constructors

let extend_hidden_ty (g:env) (a:btvar) (mapped_to:mlty) : env =
    let ml_a = as_mlident a.v in
    let tcenv = Env.push_local_binding g.tcenv (Env.Binding_typ(a.v, a.sort)) in
    {g with tcenv=tcenv}
*)


let sanitize (s:string) (is_type:bool) : string =
  let cs = FStar.String.list_of_string s in
  let sanitize_typ () =
    let valid_rest c = BU.is_letter_or_digit c in
    let aux cs = List.map (fun x -> if valid_rest x then x else 'u') cs in
    if List.hd cs = '\'' then List.hd cs :: aux (List.tail cs)
    else '\'' :: aux cs
  in
  let sanitize_term () =
    let valid c = BU.is_letter_or_digit c || c = '_' || c = '\'' in
    let cs' = List.fold_right (fun c cs -> (if valid c then [c] else ['_';'_'])@cs) cs [] in
    match cs' with
    | (c::cs) when BU.is_digit c || c = '\'' ->
       '_'::c::cs
    | _ -> cs
  in
  FStar.String.string_of_list
    (if is_type then sanitize_typ() else sanitize_term())


// (* 20161021, JP: trying to make sense of this code...
//  * - the second field of the [mlident] was meant, I assume, to disambiguate
//  *   variables; however, many places provide a placeholder value (0)
//  * - my assumption is thus that the code extraction never generates code that
//  *   needs to refer to a shadowed variable; since the scoping rules
//  *   of both F* and OCaml are lexical, then this probably works out somehow
//  *   (sic);
//  * - however, since this function is not parameterized over the environment, now
//  *   that I avoid generating names that are OCaml keywords, it is no longer
//  *   injective, because of the following F* example:
//  *     let land_15 = 0 in
//  *     let land = () in
//  *     print_int land_15
//  * It's slightly tricky to get into this case, but... not impossible. There's a
//  * similar problem for top-level bindings. For instance, this will be a problem:
//  *   let land_ = 0
//  *   let land = ()
//  * One solution is to carry the environment; for a pair of names (original,
//  * destination), compute the set of original names shadowed by the original
//  * name; make sure that the destination name does not shadow more than the
//  * destination names of these original names; otherwise, keep generating fresh
//  * destination names.
//  *)
// let avoid_keyword s =
//   if is_reserved s then
//     s ^ "_"
//   else
//     s

let bv_as_mlident (x:bv): mlident =
  if BU.starts_with x.ppname.idText Ident.reserved_prefix
  || is_null_bv x
  then x.ppname.idText ^ "_" ^ (string_of_int x.index)
  else x.ppname.idText

// Need to avoid shadowing an existing identifier (see comment about ty_or_exp_b)
let find_uniq ml_ident_map mlident is_type =
  let rec aux i mlident =
    let target_mlident = if i = 0 then mlident else mlident ^ (string_of_int i) in
    match BU.psmap_try_find ml_ident_map target_mlident with
      | Some x -> aux (i+1) mlident
      | None ->
        let map = BU.psmap_add ml_ident_map target_mlident "" in
        target_mlident, map
  in
  let mlident = sanitize mlident is_type in
  if is_type
  then let nm, map = aux 0 (BU.substring_from mlident 1) in
       "'" ^ nm, map
  else aux 0 mlident

(* -------------------------------------------------------------------- *)
let mlns_of_lid (x:lident) = List.map (fun x -> x.idText) x.ns

let new_mlpath_of_lident (g:uenv) (x : lident) : mlpath * uenv =
  let mlp, g =
    if Ident.lid_equals x FStar.Parser.Const.failwith_lid
    then ([], x.ident.idText), g
    else let name, map = find_uniq g.env_mlident_map x.ident.idText false in
         let g = { g with env_mlident_map = map } in
         (mlns_of_lid x, name), g
  in
  let g = { g with
    mlpath_of_lid = BU.psmap_add g.mlpath_of_lid x.str mlp
  } in
  mlp, g

let print_mlpath_map (g:uenv) =
  let string_of_mlpath mlp =
    (String.concat "." (fst mlp) ^ "." ^ (snd mlp))
  in
  let entries =
    BU.psmap_fold g.mlpath_of_lid (fun key value entries ->
      BU.format2 "%s -> %s" key (string_of_mlpath value) :: entries) []
  in
  String.concat "\n" entries

let mlpath_of_lident (g:uenv) (x:lident) : mlpath =
  match BU.psmap_try_find g.mlpath_of_lid x.str with
  | None ->
    debug g (fun _ ->
      BU.print1 "Identifier not found: %s" x.str;
      BU.print1 "Env is \n%s\n" (print_mlpath_map g));
    failwith ("Identifier not found: " ^ x.str)
  | Some mlp -> mlp

let extend_ty (g:uenv) (a:bv) (map_to_top:bool) : uenv =
    let is_type = not map_to_top in
    let ml_a, mlident_map = find_uniq g.env_mlident_map (bv_as_mlident a) is_type in
    let mapped_to =
      if map_to_top
      then MLTY_Top
      else MLTY_Var ml_a
    in
    let gamma = Bv(a, Inl ({ty_b_name=ml_a; ty_b_ty=mapped_to}))::g.env_bindings in
    let tcenv = TypeChecker.Env.push_bv g.env_tcenv a in
    {g with env_bindings=gamma; env_mlident_map=mlident_map; env_tcenv=tcenv}

let lookup_ty (g:uenv) (x:bv) : ty_binding =
  match lookup_bv g x with
  | Inl ty -> ty
  | _ -> failwith "Expected a type name"

let extend_bv (g:uenv) (x:bv) (t_x:mltyscheme) (add_unit:bool) (is_rec:bool)
              (mk_unit:bool (*some pattern terms become unit while extracting*))
    : uenv
    * mlident
    * exp_binding =
    let ml_ty = match t_x with
        | ([], t) -> t
        | _ -> MLTY_Top in
    let mlident, mlident_map = find_uniq g.env_mlident_map (bv_as_mlident x) false in
    let mlx = MLE_Var mlident in
    let mlx = if mk_unit
              then ml_unit
              else if add_unit
              then with_ty MLTY_Top <| MLE_App(with_ty MLTY_Top mlx, [ml_unit])
              else with_ty ml_ty mlx in
    let t_x = if add_unit then pop_unit t_x else t_x in
    let exp_binding = {exp_b_name=mlident; exp_b_expr=mlx; exp_b_tscheme=t_x; exp_b_inst_ok=is_rec} in
    let gamma = Bv(x, Inr exp_binding)::g.env_bindings in
    let tcenv = TypeChecker.Env.push_binders g.env_tcenv (binders_of_list [x]) in
    {g with env_bindings=gamma; env_mlident_map = mlident_map; env_tcenv=tcenv}, mlident, exp_binding

let new_mlident (g:uenv)
  : uenv * mlident
  = let ml_ty = MLTY_Top in
    let x = FStar.Syntax.Syntax.new_bv None FStar.Syntax.Syntax.tun in
    let g, id, _ = extend_bv g x ([], MLTY_Top) false false false in
    g, id

let rec mltyFvars (t: mlty) : list<mlident>  =
    match t with
    | MLTY_Var  x -> [x]
    | MLTY_Fun (t1, f, t2) -> List.append (mltyFvars t1) (mltyFvars t2)
    | MLTY_Named(args, path) -> List.collect mltyFvars args
    | MLTY_Tuple ts -> List.collect mltyFvars ts
    | MLTY_Top
    | MLTY_Erased -> []

let rec subsetMlidents (la : list<mlident>) (lb : list<mlident>)  : bool =
    match la with
    | h::tla -> List.contains h lb && subsetMlidents tla lb
    | [] -> true

let tySchemeIsClosed (tys : mltyscheme) : bool =
    subsetMlidents  (mltyFvars (snd tys)) (fst tys)

let extend_fv (g:uenv) (x:fv) (t_x:mltyscheme) (add_unit:bool) (is_rec:bool)
    : uenv
    * mlident
    * exp_binding =
    if tySchemeIsClosed t_x
    then
        let ml_ty = match t_x with
            | ([], t) -> t
            | _ -> MLTY_Top in
        let mlpath, g = new_mlpath_of_lident g x.fv_name.v in
        // the mlpath cannot be determined here. it can be determined at use site, depending on the name of the module where it is used
        // so this conversion should be moved to lookup_fv
        let mlsymbol = snd mlpath in
        let mly = MLE_Name mlpath in
        let mly = if add_unit then with_ty MLTY_Top <| MLE_App(with_ty MLTY_Top mly, [ml_unit]) else with_ty ml_ty mly in
        let t_x = if add_unit then pop_unit t_x else t_x in
        let exp_binding = {exp_b_name=mlsymbol; exp_b_expr=mly; exp_b_tscheme=t_x; exp_b_inst_ok=is_rec} in
        let gamma = Fv(x, exp_binding)::g.env_bindings in
        let mlident_map = BU.psmap_add g.env_mlident_map mlsymbol "" in
        {g with env_bindings=gamma; env_mlident_map=mlident_map}, mlsymbol, exp_binding
    else failwith "freevars found"

let extend_lb (g:uenv) (l:lbname) (t:typ) (t_x:mltyscheme) (add_unit:bool) (is_rec:bool)
    : uenv
    * mlident
    * exp_binding =
    match l with
    | Inl x ->
        // FIXME missing in lib; NS: what does ths mean??
        extend_bv g x t_x add_unit is_rec false
    | Inr f ->
        extend_fv g f t_x add_unit is_rec

let extend_tydef (g:uenv) (fv:fv) (ts:mltyscheme) : tydef * mlpath * uenv =
    let name, g = new_mlpath_of_lident g fv.fv_name.v in
    let tydef = {
        tydef_fv = fv;
        tydef_mlmodule_name=fst name;
        tydef_name = snd name;
        tydef_def = ts;
    } in
    tydef,
    name,
    {g with tydefs=tydef::g.tydefs; type_names=(fv, name)::g.type_names}

let extend_type_name (g:uenv) (fv:fv) : mlpath * uenv =
  let name, g = new_mlpath_of_lident g fv.fv_name.v in
  name,
  {g with type_names=(fv,name)::g.type_names}

let is_type_name g fv = g.type_names |> BU.for_some (fun (x, _) -> fv_eq fv x)

let is_fv_type g fv =
    is_type_name g fv ||
    g.tydefs |> BU.for_some (fun tydef -> fv_eq fv tydef.tydef_fv)

let initial_mlident_map =
  let map = BU.mk_ref None in
  fun () ->
    match !map with
    | Some m -> m
    | None ->
      let m =
        List.fold_right
          (fun x m -> BU.psmap_add m x "")
          (if Options.codegen() = Some Options.FSharp
           then fsharpkeywords
           else ocamlkeywords)
        (BU.psmap_empty())
      in
      map := Some m;
      m

let mkContext (e:TypeChecker.Env.env) : uenv =
   let env = {
     env_tcenv = e;
     env_bindings =[];
     env_mlident_map=initial_mlident_map ();
     mlpath_of_lid = BU.psmap_empty();
     env_fieldname_map=initial_mlident_map ();
     mlpath_of_fieldname = BU.psmap_empty();
     tydefs =[];
     type_names=[];
     currentModule = ([], "");
   } in
   let a = "'a" in
   let failwith_ty = ([a], MLTY_Fun(MLTY_Named([], (["Prims"], "string")), E_IMPURE, MLTY_Var a)) in
   let g, _, _ =
       extend_lb env (Inr (lid_as_fv Const.failwith_lid delta_constant None)) tun failwith_ty false false
   in
   g

let extend_with_monad_op_name g (ed:Syntax.eff_decl) nm ts =
    (* Extract bind and return of effects as (unqualified) projectors of that effect, *)
    (* same as for actions. However, extracted code should not make explicit use of them. *)
    let lid = U.mk_field_projector_name_from_ident ed.mname (id_of_text nm) in
    let g, mlid, exp_b = extend_fv g (lid_as_fv lid delta_constant None) ts false false in
    let mlp = mlns_of_lid lid, mlid in
    mlp, lid, exp_b, g


let extend_with_action_name g (ed:Syntax.eff_decl) (a:Syntax.action) ts =
    let nm = a.action_name.ident.idText in
    let module_name = ed.mname.ns in
    let lid = Ident.lid_of_ids (module_name@[Ident.id_of_text nm]) in
    let g, mlid, exp_b = extend_fv g (lid_as_fv lid delta_constant None) ts false false in
    let mlp = mlns_of_lid lid, mlid in
    mlp, lid, exp_b, g

let extend_record_field_name g (type_name, fn) =
    let key = Ident.lid_of_ids (type_name.ns@[fn]) in
    let name, fieldname_map = find_uniq g.env_fieldname_map fn.idText false in
    let ns = mlns_of_lid key in
    let mlp = ns, name in
    let g = { g with env_fieldname_map = fieldname_map;
                     mlpath_of_fieldname = BU.psmap_add g.mlpath_of_fieldname key.str mlp }
    in
    mlp, g

let lookup_record_field_name g (type_name, fn) =
  let key = Ident.lid_of_ids (type_name.ns@[fn]) in
  match BU.psmap_try_find g.mlpath_of_fieldname key.str with
  | None -> failwith ("Field name not found: " ^ key.str)
  | Some mlp -> mlp

(* Module names are in a different namespace in OCaml
   and cannot clash with keywords (since they are uppercase in F* )
   or with other identifiers *)
let extend_with_module_name (g:uenv) (m:lid) =
  let ns = mlns_of_lid m in
  let p = m.ident.idText in
  (ns, p), g

let exit_module g =
  { g with env_mlident_map=initial_mlident_map();
           env_fieldname_map=initial_mlident_map()}
