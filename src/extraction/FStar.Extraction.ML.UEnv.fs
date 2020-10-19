﻿(*
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

(**** Type definitions *)

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
 *)
type exp_binding = {
  exp_b_name: mlident;
  exp_b_expr: mlexpr;
  exp_b_tscheme: mltyscheme
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
let tydef_mlpath (td : tydef) : mlpath = td.tydef_mlmodule_name, td.tydef_name

(** The main type of this module; it's abstract

    - [env_tcenv]: The underlying typechecker environment
    - [env_bindings]: names in scope associated with their types
    - [env_mlident_map]: The set of names used in the current scope (for freshness)
    - [mlpath_of_lid]: A map from a full F* lident to its corresponding mlpath
    - [env_fieldname_map]: The set of record field names used in the current in scope (for freshness)
    - [mlpath_of_fieldname]: A map from a full F* record field identifier to its corresponding mlpath
    - [tydefs]: Type abbreviations in scope
    - [type_names]: Inductive type constructors in scope
    - [currentModule]: ML name of the current module being extracted
 *)
type uenv = {
  env_tcenv:TypeChecker.Env.env;
  env_bindings:list<binding>;
  env_mlident_map:psmap<mlident>;
  mlpath_of_lid:psmap<mlpath>;
  env_fieldname_map:psmap<mlident>;
  mlpath_of_fieldname:psmap<mlpath>;
  tydefs:list<tydef>;
  type_names:list<(fv*mlpath)>;
  currentModule: mlpath // needed to properly translate the definitions in the current file
}

(**** Getters and Setters *)

let tcenv_of_uenv (u:uenv) : TypeChecker.Env.env = u.env_tcenv
let set_tcenv (u:uenv) (t:TypeChecker.Env.env) = { u with env_tcenv=t}
let current_module_of_uenv (u:uenv) : mlpath = u.currentModule
let set_current_module (u:uenv) (m:mlpath) : uenv = { u with currentModule = m }

(**** Debugging *)

// Only for debug printing in Modul.fs
let bindings_of_uenv u = u.env_bindings

let debug g f =
    let c = string_of_mlpath g.currentModule in
    if Options.debug_at_level c (Options.Other "Extraction")
    then f ()

let print_mlpath_map (g:uenv) =
    let string_of_mlpath mlp =
      String.concat "." (fst mlp) ^ "." ^ (snd mlp)
    in
    let entries =
      BU.psmap_fold g.mlpath_of_lid (fun key value entries ->
        BU.format2 "%s -> %s" key (string_of_mlpath value) :: entries) []
    in
    String.concat "\n" entries

(**** Constructors *)


(**** Looking up identifiers *)

(** Scans the list of bindings for an fv:
    - it's always mapped to an ML expression
  *)
let try_lookup_fv (g:uenv) (fv:fv) : option<exp_binding> =
    BU.find_map
      g.env_bindings
      (function
        | Fv (fv', t) when fv_eq fv fv' -> Some t
        | _ -> None)

(** Fatal failure version of try_lookup_fv *)
let lookup_fv (g:uenv) (fv:fv) : exp_binding =
    match try_lookup_fv g fv with
    | None ->
      failwith (BU.format2 "(%s) free Variable %s not found\n"
                           (Range.string_of_range fv.fv_name.p)
                           (Print.lid_to_string fv.fv_name.v))
    | Some y -> y

(** An F* local variable (bv) can be mapped either to
    a ML type variable or a term variable *)
let lookup_bv (g:uenv) (bv:bv) : ty_or_exp_b =
    let x =
      BU.find_map g.env_bindings
        (function
          | Bv (bv', r) when bv_eq bv bv' -> Some r
          | _ -> None)
    in
    match x with
    | None ->
      failwith (BU.format2 "(%s) bound Variable %s not found\n"
                           (Range.string_of_range (range_of_id bv.ppname))
                           (Print.bv_to_string bv))
    | Some y -> y

(** Lookup either a local variable or a top-level name *)
let lookup_term g (t:term) =
    match t.n with
    | Tm_name x -> lookup_bv g x, None
    | Tm_fvar x -> Inr (lookup_fv g x), x.fv_qual
    | _ -> failwith "Impossible: lookup_term for a non-name"

(** Lookup an local variable mapped to a ML type variable *)
let lookup_ty (g:uenv) (x:bv) : ty_binding =
    match lookup_bv g x with
    | Inl ty -> ty
    | _ -> failwith "Expected a type name"

(** Lookup a type abbreviation *)
let lookup_tydef (env:uenv) ((module_name, ty_name):mlpath)
  : option<mltyscheme>
  = BU.find_map env.tydefs  (fun tydef ->
        if ty_name = tydef.tydef_name
        && module_name = tydef.tydef_mlmodule_name
        then Some tydef.tydef_def
        else None)

(** Given an F* qualified name, find its ML counterpart *)
let mlpath_of_lident (g:uenv) (x:lident) : mlpath =
    match BU.psmap_try_find g.mlpath_of_lid (string_of_lid x) with
    | None ->
      debug g (fun _ ->
        BU.print1 "Identifier not found: %s" (string_of_lid x);
        BU.print1 "Env is \n%s\n" (print_mlpath_map g));
      failwith ("Identifier not found: " ^ string_of_lid x)
    | Some mlp -> mlp

(** Is [fv] the name of an F* inductive type? *)
let is_type_name g fv =
    g.type_names |>
    BU.for_some (fun (x, _) -> fv_eq fv x)

(** Is [fv] the name of an F* inductive type or type abbreviation? *)
let is_fv_type g fv =
    is_type_name g fv ||
    g.tydefs |> BU.for_some (fun tydef -> fv_eq fv tydef.tydef_fv)

(** Find the ML counterpart of an F* record field identifier

    - F* Record field names are pairs of a fully qualified *type* name
      and the short field name

    - In ML, the record field name is unique for a given namespace
      (i.e., unique per F* module)

    In extend_record_field_name we associate a module-level unique ML
    fieldname with the [(type_name, fn)] pair.
 *)
let lookup_record_field_name g (type_name, fn) =
    let key = Ident.lid_of_ids (ids_of_lid type_name @ [fn]) in
    match BU.psmap_try_find g.mlpath_of_fieldname (string_of_lid key) with
    | None -> failwith ("Field name not found: " ^ string_of_lid key)
    | Some mlp -> mlp

(**** Naming conventions and freshness (internal) *)

(** The initial map of used identifiers is populated
    with the keyword list of the target language.

    That ensures that any name we generate doesn't clash
    with those keywords
  *)
let initial_mlident_map =
    let map = BU.mk_ref None in
    fun () ->
      match !map with
      | Some m -> m
      | None ->
        let m =
          List.fold_right
            (fun x m -> BU.psmap_add m x "")
            (match Options.codegen() with
              | Some Options.FSharp -> fsharpkeywords
              | Some Options.OCaml
              | Some Options.Plugin -> ocamlkeywords
              | Some Options.Kremlin -> kremlin_keywords
              | None -> [])
          (BU.psmap_empty())
        in
        map := Some m;
        m

(** Enforces naming conventions for indentifiers of term and (local)
    type variables:

    - Term variables
      - must be sequences of letters, digits, _ and ',
      - must beginning with letter or _
      - any other invalid character is replaced with __

    - Type variables
      - must begin with a '
      - their second character cannot be "_" (since that's a weak type variable in OCaml)
      - rest of their characters are letter or digit or underscore (no further ' allowed)
      - any other invalid character is replaced with 'u' (not _, since
        that could introduce a weak type variable)
  *)
let rename_conventional (s:string) (is_local_type_variable:bool) : string =
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
    (if is_local_type_variable then sanitize_typ() else sanitize_term())

(** The root name of a F* local variable, adapted for conventions, is
    a prefix of this name in ML,

    It is either the [ppname] (pretty-printing name)
    Or, in case the [ppname] is unset, it's the unique name in F* *)
let root_name_of_bv (x:bv): mlident =
  if BU.starts_with (string_of_id x.ppname) Ident.reserved_prefix
  || is_null_bv x
  then Ident.reserved_prefix
  else string_of_id x.ppname

(** Given a candidate root_name, generate an ML identifier
    for it that is unique in the current scope.

    By,
    - rewriting it to enforce naming conventions

    - and then appending a numeric suffix in case it clashes with
      some variable in scope
 *)
let find_uniq ml_ident_map root_name is_local_type_variable =
  let rec aux i root_name =
    let target_mlident = if i = 0 then root_name else root_name ^ (string_of_int i) in
    match BU.psmap_try_find ml_ident_map target_mlident with
      | Some x -> aux (i+1) root_name
      | None ->
        let map = BU.psmap_add ml_ident_map target_mlident "" in
        target_mlident, map
  in
  let mlident = rename_conventional root_name is_local_type_variable in
  if is_local_type_variable
  then let nm, map = aux 0 (BU.substring_from mlident 1) in
       "'" ^ nm, map
  else aux 0 mlident

(** The ML namespace corresponding to an F* qualified name
    is just all the identifiers in the F* namespace (as strings) *)
let mlns_of_lid (x:lident) = List.map string_of_id (ns_of_lid x)

(**** Extending context with identifiers *)

(** A new [mlpath] for an F* qualified name [x]:

    It's short name (i.e., the last element of [x]) is unique for the
    current scope and subsequent names in the scope will not clash
    with it.

    E.g.,  given
    {[
      module A
      let id = 0
      let foo (id:int) = id
    ]}

    we'll generate [id] for the top-level name
    and then [id1] for the local variable
*)
let new_mlpath_of_lident (g:uenv) (x : lident) : mlpath * uenv =
  let mlp, g =
    if Ident.lid_equals x FStar.Parser.Const.failwith_lid
    then ([], string_of_id (ident_of_lid x)), g
    else let name, map = find_uniq g.env_mlident_map (string_of_id (ident_of_lid x)) false in
         let g = { g with env_mlident_map = map } in
         (mlns_of_lid x, name), g
  in
  let g = { g with
    mlpath_of_lid = BU.psmap_add g.mlpath_of_lid (string_of_lid x) mlp
  } in
  mlp, g

(** Extending the context with an F* type variable

      - If [map_to_top] is set, then this variable gets mapped to unit in
        ML, so it is not always a type variable in ML
  *)
let extend_ty (g:uenv) (a:bv) (map_to_top:bool) : uenv =
    let is_local_type_variable = not map_to_top in
    let ml_a, mlident_map = find_uniq g.env_mlident_map (root_name_of_bv a) is_local_type_variable in
    let mapped_to =
      if map_to_top
      then MLTY_Top
      else MLTY_Var ml_a
    in
    let gamma = Bv(a, Inl ({ty_b_name=ml_a; ty_b_ty=mapped_to}))::g.env_bindings in
    let tcenv = TypeChecker.Env.push_bv g.env_tcenv a in
    {g with env_bindings=gamma; env_mlident_map=mlident_map; env_tcenv=tcenv}

(** Extending the context with a local term variable
    - [add_unit] is set if the variable should be forced on each use
    - [is_rec] if the variable is bound to a local recursive definition
    - [mk_unit] if every use of the variable to be erased to [()]
  *)
let extend_bv (g:uenv) (x:bv) (t_x:mltyscheme) (add_unit:bool)
              (mk_unit:bool (*some pattern terms become unit while extracting*))
    : uenv
    * mlident
    * exp_binding =
    let ml_ty = match t_x with
        | ([], t) -> t
        | _ -> MLTY_Top in
    let mlident, mlident_map = find_uniq g.env_mlident_map (root_name_of_bv x) false in
    let mlx = MLE_Var mlident in
    let mlx = if mk_unit
              then ml_unit
              else if add_unit
              then with_ty MLTY_Top <| MLE_App(with_ty MLTY_Top mlx, [ml_unit])
              else with_ty ml_ty mlx in
    let t_x = if add_unit then pop_unit t_x else t_x in
    let exp_binding = {exp_b_name=mlident; exp_b_expr=mlx; exp_b_tscheme=t_x } in
    let gamma = Bv(x, Inr exp_binding)::g.env_bindings in
    let tcenv = TypeChecker.Env.push_binders g.env_tcenv (binders_of_list [x]) in
    {g with env_bindings=gamma; env_mlident_map = mlident_map; env_tcenv=tcenv}, mlident, exp_binding

let burn_name (g:uenv) (i:mlident) : uenv =
  { g with env_mlident_map = BU.psmap_add g.env_mlident_map i "" }

(** Generating a fresh local term variable *)
let new_mlident (g:uenv)
  : uenv * mlident
  = let ml_ty = MLTY_Top in
    let x = FStar.Syntax.Syntax.new_bv None FStar.Syntax.Syntax.tun in
    let g, id, _ = extend_bv g x ([], MLTY_Top) false false in
    g, id

(** Similar to [extend_bv], except for top-level term identifiers *)
let extend_fv (g:uenv) (x:fv) (t_x:mltyscheme) (add_unit:bool)
    : uenv
    * mlident
    * exp_binding =
    let rec mltyFvars (t: mlty) : list<mlident>  =
      match t with
      | MLTY_Var  x -> [x]
      | MLTY_Fun (t1, f, t2) -> List.append (mltyFvars t1) (mltyFvars t2)
      | MLTY_Named(args, path) -> List.collect mltyFvars args
      | MLTY_Tuple ts -> List.collect mltyFvars ts
      | MLTY_Top
      | MLTY_Erased -> []
    in
    let rec subsetMlidents (la : list<mlident>) (lb : list<mlident>)  : bool =
      match la with
      | h::tla -> List.contains h lb && subsetMlidents tla lb
      | [] -> true
    in
    let tySchemeIsClosed (tys : mltyscheme) : bool =
      subsetMlidents  (mltyFvars (snd tys)) (fst tys)
    in
    if tySchemeIsClosed t_x
    then
        let ml_ty = match t_x with
            | ([], t) -> t
            | _ -> MLTY_Top in
        let mlpath, g = new_mlpath_of_lident g x.fv_name.v in
        let mlsymbol = snd mlpath in
        let mly = MLE_Name mlpath in
        let mly = if add_unit then with_ty MLTY_Top <| MLE_App(with_ty MLTY_Top mly, [ml_unit]) else with_ty ml_ty mly in
        let t_x = if add_unit then pop_unit t_x else t_x in
        let exp_binding = {exp_b_name=mlsymbol; exp_b_expr=mly; exp_b_tscheme=t_x } in
        let gamma = Fv(x, exp_binding)::g.env_bindings in
        let mlident_map = BU.psmap_add g.env_mlident_map mlsymbol "" in
        {g with env_bindings=gamma; env_mlident_map=mlident_map}, mlsymbol, exp_binding
    else failwith "freevars found"

(** Extend with a let binding, either local or top-level *)
let extend_lb (g:uenv) (l:lbname) (t:typ) (t_x:mltyscheme) (add_unit:bool)
    : uenv
    * mlident
    * exp_binding =
    match l with
    | Inl x ->
        // FIXME missing in lib; NS: what does this mean??
        extend_bv g x t_x add_unit false
    | Inr f ->
        extend_fv g f t_x add_unit

(** Extend with an abbreviation [fv] for the type scheme [ts] *)
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

(** Extend with [fv], the identifer for an F* inductive type *)
let extend_type_name (g:uenv) (fv:fv) : mlpath * uenv =
  let name, g = new_mlpath_of_lident g fv.fv_name.v in
  name,
  {g with type_names=(fv,name)::g.type_names}


(** The [bind] and [return] of an effect declaration
    are names like field projectors *)
let extend_with_monad_op_name g (ed:Syntax.eff_decl) nm ts =
    (* Extract bind and return of effects as (unqualified) projectors of that effect, *)
    (* same as for actions. However, extracted code should not make explicit use of them. *)
    let lid = U.mk_field_projector_name_from_ident ed.mname (id_of_text nm) in
    let g, mlid, exp_b = extend_fv g (lid_as_fv lid delta_constant None) ts false in
    let mlp = mlns_of_lid lid, mlid in
    mlp, lid, exp_b, g

(** The actions of an effect declaration are qualified to the module
    name in which they are defined. *)
let extend_with_action_name g (ed:Syntax.eff_decl) (a:Syntax.action) ts =
    let nm = string_of_id (ident_of_lid a.action_name) in
    let module_name = ns_of_lid ed.mname in
    let lid = Ident.lid_of_ids (module_name@[Ident.id_of_text nm]) in
    let g, mlid, exp_b = extend_fv g (lid_as_fv lid delta_constant None) ts false in
    let mlp = mlns_of_lid lid, mlid in
    mlp, lid, exp_b, g

(** Record field names are in a separate namespace in ML and cannot
    clash with type names, top-level names, local identifiers etc.

    So, we maintain then in a separate map.

    We generate a unique field name associated with just the
    [fn]---the generated [name] is a unique field name for the current
    module.

    However, we associate this generated name with the [(type_name,
    fn)] pair, and retrieve the unique ML fieldname [name] using this
    pair as a key.

    This is important to avoid name clashes among record in the same
    module whose fields have overlapping names. See Bug 2058 and
    tests/Bug2058.fst
 *)
let extend_record_field_name g (type_name, fn) =
    let key = Ident.lid_of_ids (ids_of_lid type_name @ [fn]) in
    let name, fieldname_map = find_uniq g.env_fieldname_map (string_of_id fn) false in
    let ns = mlns_of_lid type_name in
    let mlp = ns, name in
    let g = { g with env_fieldname_map = fieldname_map;
                     mlpath_of_fieldname = BU.psmap_add g.mlpath_of_fieldname (string_of_lid key) mlp }
    in
    name, g


(** Module names are in a different namespace in OCaml
    and cannot clash with keywords (since they are uppercase in F* )
    or with other identifiers.

    An F* module name is mapped as is to OCaml.
    When printed, instead of A.B.C, we get A_B_C *)
let extend_with_module_name (g:uenv) (m:lid) =
  let ns = mlns_of_lid m in
  let p = string_of_id (ident_of_lid m) in
  (ns, p), g

(** After completing the extraction of a module
    we reset its uses sets so that name generation for the next module
    needn't be bothered with names that were generated for prior modules
    which are in a different namespace *)
let exit_module g =
  { g with env_mlident_map=initial_mlident_map();
           env_fieldname_map=initial_mlident_map()}


(**** Constructor for a uenv *)

let new_uenv (e:TypeChecker.Env.env)
  : uenv
  = let env = {
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
    (* We handle [failwith] specially, extracting it to OCaml's 'failwith'
       rather than FStar_All.failwith. Not sure this is necessary *)
    let a = "'a" in
    let failwith_ty = ([a], MLTY_Fun(MLTY_Named([], (["Prims"], "string")), E_IMPURE, MLTY_Var a)) in
    let g, _, _ =
        extend_lb env (Inr (lid_as_fv Const.failwith_lid delta_constant None)) tun failwith_ty false
    in
    g
