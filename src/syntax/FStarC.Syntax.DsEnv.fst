(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

module FStarC.Syntax.DsEnv
open FStarC.Effect
open FStarC.List
open FStarC
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Syntax.Util
open FStarC.Parser
open FStarC.Ident
open FStarC.Errors

open FStarC.Class.Show
open FStarC.Class.Monad
open FStarC.Class.Setlike

let rec takeWhileMax (n : int) (f : 'a -> bool) (xs : list 'a) : list 'a =
  if n <= 0
  then []
  else
    match xs with
    | [] -> []
    | x::xs' ->
      if f x
      then x :: takeWhileMax (n - 1) f xs'
      else []

(* The functions for typo suggestions can be SLOW. They should only be called
when we are actually logging an error, which is not very frequent. *)

(* User wrote 'x', which wasn't found in the list 'xs'. Give some suggestions. *)
let typo_candidates (x : string) (xs : list string) : list string =
  let cands = xs |> List.map (fun y -> (EditDist.edit_distance x y, y)) in
  let cands = Class.Ord.sort cands |> Class.Ord.dedup in
  (* Don't suggest anything with a big distance (>= 3), and return at most 5 suggestions. *)
  let cands = takeWhileMax 5 (fun (d, _) -> d < 3) cands in
  List.map snd cands

let rec list_sep2 #a (s1 s2 : a) (xs : list a) : list a =
  match xs with
  | [] -> []
  | [x] -> [x]
  | [x;y] -> [x; s2; y]
  | x::y::xs -> x :: s1 :: list_sep2 s1 s2 (y::xs)

let typo_msg (x : string) (xs : list string) : Pprint.document =
  let open FStarC.Pprint in
  let cands = typo_candidates x xs in
  if List.length cands = 0
  then empty
  else
    nest 2 <| text "Hint: Did you mean" ^/^
      flow empty
        (list_sep2
          (comma ^^ break_ 1)
          (break_ 1 ^^ doc_of_string "or" ^^ break_ 1)
          (List.map doc_of_string cands))
        ^^ doc_of_string "?"

module BU = FStarC.Util

let ugly_sigelt_to_string_hook : ref (sigelt -> string) = mk_ref (fun _ -> "")
let ugly_sigelt_to_string (se:sigelt) : string = !ugly_sigelt_to_string_hook se

module S = FStarC.Syntax.Syntax
module U = FStarC.Syntax.Util
module BU = FStarC.Util
module Const = FStarC.Parser.Const

type local_binding = (ident & bv & used_marker)           (* local name binding for name resolution, paired with an env-generated unique name *)
type rec_binding   = (ident & lid &                       (* name bound by recursive type and top-level let-bindings definitions only *)
                      used_marker)                        (* this ref marks whether it was used, so we can warn if not *)

type scope_mod =
| Local_bindings           of PSMap.t local_binding (* a map local bindings in a scope; a map to avoid a linear scan *) 
| Rec_binding              of rec_binding
| Module_abbrev            of module_abbrev
| Open_module_or_namespace of open_module_or_namespace
| Top_level_defs           of PSMap.t unit
  (* ^ A map (to avoid a linear scan) recording that a top-level definition
     for an unqualified identifier x is in scope and should be resolved
     as curmodule.x. *)
| Record_or_dc             of record_or_dc    (* to honor interleavings of "open" and record definitions *)

instance _ : showable scope_mod = {
  show = function
    | Local_bindings lbs -> "Local_bindings"
    | Rec_binding (id, lid, _) -> "Rec_binding " ^ (string_of_id id) ^ " " ^ (string_of_lid lid)
    | Module_abbrev (id, lid) -> "Module_abbrev " ^ (string_of_id id) ^ " " ^ (string_of_lid lid)
    | Open_module_or_namespace (lid, _, _) -> "Open_module_or_namespace " ^ (string_of_lid lid)
    | Top_level_defs lbs -> "Top_level_defs"
    | Record_or_dc r -> "Record_or_dc " ^ (string_of_lid r.typename)
}

type string_set = RBSet.t string

type exported_id_kind = (* kinds of identifiers exported by a module *)
| Exported_id_term_type (* term and type identifiers *)
| Exported_id_field     (* field identifiers *)

instance _: showable exported_id_kind = {
  show = (function | Exported_id_field -> "Exported_id_field"
                   | Exported_id_term_type -> "Exported_id_term_type")
}

type exported_id_set = exported_id_kind -> ref string_set

type env = {
  curmodule:            option lident;                   (* name of the module being desugared *)
  curmonad:             option ident;                    (* current monad being desugared *)
  modules:              list (lident & modul);           (* previously desugared modules *)
  scope_mods:           list scope_mod;                  (* a STACK of toplevel or definition-local scope modifiers *)
  exported_ids:         SMap.t exported_id_set;         (* identifiers (stored as strings for efficiency)
                                                             reachable in a module, not shadowed by "include"
                                                             declarations. Used only to handle such shadowings,
                                                             not "private"/"abstract" definitions which it is
                                                             enough to just remove from the sigmap. Formally,
                                                             iden is in exported_ids[ModulA] if, and only if,
                                                             there is no 'include ModulB' (with ModulB.iden
                                                             defined or reachable) after iden in ModulA. *)
  trans_exported_ids:   SMap.t exported_id_set;         (* transitive version of exported_ids along the
                                                             "include" relation: an identifier is in this set
                                                             for a module if and only if it is defined either
                                                             in this module or in one of its included modules. *)
  includes:             SMap.t (ref (list (lident & restriction)));   (* list of "includes" declarations for each module. *)
  sigaccum:             sigelts;                          (* type declarations being accumulated for the current module *)
  sigmap:               SMap.t (sigelt & bool);         (* bool indicates that this was declared in an interface file *)
  iface:                bool;                             (* whether or not we're desugaring an interface; different scoping rules apply *)
  admitted_iface:       bool;                             (* is it an admitted interface; different scoping rules apply *)
  expect_typ:           bool;                             (* syntactically, expect a type at this position in the term *)
  remaining_iface_decls:list (lident&list Parser.AST.decl);  (* A map from interface names to their stil-to-be-processed top-level decls *)
  syntax_only:          bool;                             (* Whether next push should skip type-checking *)
  ds_hooks:             dsenv_hooks;                       (* hooks that the interactive more relies onto for symbol tracking *)
  dep_graph:            FStarC.Parser.Dep.deps;
  no_prelude:           bool;                             (* whether the module was marked no_prelude *)
}
and dsenv_hooks =
  { ds_push_open_hook : env -> open_module_or_namespace -> unit;
    ds_push_include_hook : env -> lident -> unit;
    ds_push_module_abbrev_hook : env -> ident -> lident -> unit }

(* For typo suggestions *)
let all_local_names (env:env) : list string =
  List.fold_right (fun scope acc ->
    match scope with
    | Local_bindings lbs -> PSMap.keys lbs @ acc
    | Rec_binding (x, _, _) -> string_of_id x :: acc
    | Module_abbrev (x, _) -> acc
    | Open_module_or_namespace _ -> acc
    | Top_level_defs lbs -> PSMap.keys lbs @ acc
    | Record_or_dc r -> string_of_lid r.typename :: acc
  ) env.scope_mods []

let all_mod_names (env:env) : list string =
  (List.map (fun (l, _) -> Ident.string_of_lid l) env.modules) @
  List.fold_right (fun scope acc ->
    match scope with
    | Local_bindings lbs -> acc
    | Rec_binding (x, _, _) -> acc
    | Module_abbrev (x, _) -> string_of_id x :: acc
    | Open_module_or_namespace (m, _, _) -> Ident.string_of_lid m :: acc
    | Top_level_defs lbs -> acc
    | Record_or_dc r -> acc
  ) env.scope_mods []

let mk_dsenv_hooks open_hook include_hook module_abbrev_hook =
  { ds_push_open_hook = open_hook;
    ds_push_include_hook = include_hook;
    ds_push_module_abbrev_hook = module_abbrev_hook }

let default_ds_hooks =
  { ds_push_open_hook = (fun _ _ -> ());
    ds_push_include_hook = (fun _ _ -> ());
    ds_push_module_abbrev_hook = (fun _ _ _ -> ()) }

let set_iface env b = {env with iface=b}
let iface e = e.iface
let set_admitted_iface e b = {e with admitted_iface=b}
let admitted_iface e = e.admitted_iface
let set_expect_typ e b = {e with expect_typ=b}
let expect_typ e = e.expect_typ
let all_exported_id_kinds: list exported_id_kind = [ Exported_id_field; Exported_id_term_type ]
let transitive_exported_ids env lid =
    let module_name = Ident.string_of_lid lid in
    match SMap.try_find env.trans_exported_ids module_name with
    | None -> []
    | Some exported_id_set -> !(exported_id_set Exported_id_term_type) |> elems
let opens_and_abbrevs env : list (either open_module_or_namespace module_abbrev) =
    List.collect
       (function
        | Open_module_or_namespace payload -> [Inl payload]
        | Module_abbrev (id, lid) -> [Inr (id, lid)]
        | _ -> [])
    env.scope_mods

let open_modules e = e.modules
let open_modules_and_namespaces env =
  List.filter_map (function
                   | Open_module_or_namespace (lid, _info, _restriction) -> Some lid
                   | _ -> None)
    env.scope_mods
let module_abbrevs env : list (ident & lident)=
  List.filter_map (function
                   | Module_abbrev (l, m) -> Some (l, m)
                   | _ -> None)
    env.scope_mods
let set_current_module e l = {e with curmodule=Some l}
let current_module env = match env.curmodule with
    | None -> failwith "Unset current module"
    | Some m -> m
let iface_decls env l =
    match env.remaining_iface_decls |>
          List.tryFind (fun (m, _) -> Ident.lid_equals l m) with
    | None -> None
    | Some (_, decls) -> Some decls
let set_iface_decls env l ds =
    let _, rest =
        FStarC.List.partition
            (fun (m, _) -> Ident.lid_equals l m)
            env.remaining_iface_decls in
    {env with remaining_iface_decls=(l, ds)::rest}
let qual = qual_id
let qualify env id =
    match env.curmonad with
    | None -> qual (current_module env) id
    | Some monad -> mk_field_projector_name_from_ident (qual (current_module env) monad) id
let syntax_only env = env.syntax_only
let set_syntax_only env b = { env with syntax_only = b }
let ds_hooks env = env.ds_hooks
let set_ds_hooks env hooks = { env with ds_hooks = hooks }
let new_sigmap () = SMap.create 100
let empty_env deps = {curmodule=None;
                    curmonad=None;
                    modules=[];
                    scope_mods=[];
                    exported_ids=new_sigmap();
                    trans_exported_ids=new_sigmap();
                    includes=new_sigmap();
                    sigaccum=[];
                    sigmap=new_sigmap();
                    iface=false;
                    admitted_iface=false;
                    expect_typ=false;
                    remaining_iface_decls=[];
                    syntax_only=false;
                    ds_hooks=default_ds_hooks;
                    dep_graph=deps;
                    no_prelude=false;
                    }
let dep_graph env = env.dep_graph
let set_dep_graph env ds = {env with dep_graph=ds}
let sigmap env = env.sigmap

let set_bv_range bv r =
    let id = set_id_range r bv.ppname in
    {bv with ppname=id}

let bv_to_name bv r = bv_to_name (set_bv_range bv r)

let unmangleMap = [("op_ColonColon", "Cons", Some Data_ctor);
                   ("not", "op_Negation", None)]

let unmangleOpName (id:ident) : option term =
  FStarC.Util.find_map unmangleMap (fun (x,y,dq) ->
    if string_of_id id = x
    then Some (S.fvar_with_dd (lid_of_path ["Prims"; y] (range_of_id id)) dq)
    else None)

type cont_t 'a =
    | Cont_ok of 'a  (* found *)
    | Cont_fail      (* not found, do not retry *)
    | Cont_ignore    (* not found, retry *)

let option_of_cont (k_ignore: unit -> option 'a) = function
    | Cont_ok a -> Some a
    | Cont_fail -> None
    | Cont_ignore -> k_ignore ()

(* Unqualified identifier lookup *)

let find_in_record ns id record cont =
 let typename' = lid_of_ids (ns @ [ident_of_lid record.typename]) in
 if lid_equals typename' record.typename
 then
      let fname = lid_of_ids (ns_of_lid record.typename @ [id]) in
      let find = BU.find_map record.fields (fun (f, _) ->
        if string_of_id id = string_of_id f
        then Some record
        else None)
      in
      match find with
      | Some r -> cont r
      | None -> Cont_ignore
 else
      Cont_ignore

let get_exported_id_set (e: env) (mname: string) : option (exported_id_kind -> ref string_set) =
    SMap.try_find e.exported_ids mname

let get_trans_exported_id_set (e: env) (mname: string) : option (exported_id_kind -> ref string_set) =
    SMap.try_find e.trans_exported_ids mname

let string_of_exported_id_kind = function
    | Exported_id_field -> "field"
    | Exported_id_term_type -> "term/type"

let is_exported_id_termtype = function
  | Exported_id_term_type -> true
  | _ -> false

let is_exported_id_field = function
  | Exported_id_field -> true
  | _ -> false


let find_in_module_with_includes
    (eikind: exported_id_kind)
    (find_in_module: lident -> cont_t 'a)
    (find_in_module_default: cont_t 'a)
    env
    (ns: lident)
    (id: ident)
    : cont_t 'a =
  let rec aux = function
  | [] ->
    find_in_module_default
  | (modul, id) :: q ->
    let mname = string_of_lid modul in
    let not_shadowed = match get_exported_id_set env mname with
    | None -> true
    | Some mex ->
      let mexports = !(mex eikind) in
      mem (string_of_id id) mexports
    in
    let mincludes = match SMap.try_find env.includes mname with
    | None -> []
    | Some minc ->
      !minc |> filter_map (fun (ns, restriction) ->
        let opt = is_ident_allowed_by_restriction id restriction in
        Option.map (fun id -> (ns, id)) opt)
    in
    let look_into =
     if not_shadowed
     then find_in_module (qual modul id)
     else Cont_ignore
    in
    begin match look_into with
    | Cont_ignore ->
      aux (mincludes @ q)
    | _ ->
      look_into
    end
  in aux [ (ns, id) ]

let try_lookup_id''
  env
  (id: ident)
  (eikind: exported_id_kind)
  (k_local_binding: local_binding -> cont_t 'a)
  (k_rec_binding:   rec_binding   -> cont_t 'a)
  (k_record: (record_or_dc) -> cont_t 'a)
  (find_in_module: lident -> cont_t 'a)
  (lookup_default_id: cont_t 'a -> ident -> cont_t 'a) : option 'a
  =
    let check_local_binding_id : local_binding -> bool = function
      (id', _, _) -> string_of_id id' = string_of_id id
    in
    let check_rec_binding_id : rec_binding -> bool = function
      (id', _, _) -> string_of_id id' = string_of_id id
    in
    let curmod_ns = ids_of_lid (current_module env) in
    let proc = function
      | Local_bindings lbs
        when Some? (PSMap.try_find lbs (string_of_id id)) ->
        let Some l = PSMap.try_find lbs (string_of_id id) in
        let (_, _, used_marker) = l in
        used_marker := true;
        k_local_binding l

      | Rec_binding r
        when check_rec_binding_id r ->
        let (_, _, used_marker) = r in
        used_marker := true;
        k_rec_binding r

      | Open_module_or_namespace (ns, Open_module, restriction) ->
        ( match is_ident_allowed_by_restriction id restriction with
        | None -> Cont_ignore
        | Some id -> find_in_module_with_includes eikind find_in_module Cont_ignore env ns id)

      | Top_level_defs ids
        when Some? (PSMap.try_find ids (string_of_id id)) ->
        (* indicates a global definition shadowing previous
        "open"s. If the definition is not actually found by the
        [lookup_default_id] finder, then it may mean that we are in a
        module and the [val] was already declared, with the actual
        [let] not defined yet, so we must not fail, but ignore. *)
        lookup_default_id Cont_ignore id

      | Record_or_dc r
        when (is_exported_id_field eikind) ->
        find_in_module_with_includes Exported_id_field (
            fun lid ->
            let id = ident_of_lid lid in
            find_in_record (ns_of_lid lid) id r k_record
        ) Cont_ignore env (lid_of_ids curmod_ns) id

      | Record_or_dc r
        when (is_exported_id_termtype eikind) ->
        if ident_equals (ident_of_lid r.typename) id
        then k_record r
        else Cont_ignore

      | _ ->
        Cont_ignore
    in
    let rec aux = function
      | a :: q ->
        option_of_cont (fun _ -> aux q) (proc a)
      | [] ->
        option_of_cont (fun _ -> None) (lookup_default_id Cont_fail id)

    in aux env.scope_mods

let found_local_binding r (id', x, _) =
    (bv_to_name x r)

let find_in_module env lid k_global_def k_not_found =
    begin match SMap.try_find (sigmap env) (string_of_lid lid) with
        | Some sb -> k_global_def lid sb
        | None -> k_not_found
    end

let try_lookup_id env (id:ident) : option term =
  match unmangleOpName id with
  | Some f -> Some f
  | _ ->
    try_lookup_id'' env id Exported_id_term_type (fun r -> Cont_ok (found_local_binding (range_of_id id) r)) (fun _ -> Cont_fail) (fun _ -> Cont_ignore) (fun i -> find_in_module env i (fun _ _ -> Cont_fail) Cont_ignore) (fun _ _ -> Cont_fail)

(* Unqualified identifier lookup, if lookup in all open namespaces failed. *)

let lookup_default_id
    env
    (id: ident)
    (k_global_def: lident -> sigelt & bool -> cont_t 'a)
    (k_not_found: cont_t 'a)
  =
  let find_in_monad = match env.curmonad with
  | Some _ ->
    let lid = qualify env id in
    begin match SMap.try_find (sigmap env) (string_of_lid lid) with
    | Some r -> Some (k_global_def lid r)
    | None -> None
    end
  | None -> None
  in
  match find_in_monad with
  | Some v -> v
  | None ->
    let lid = qual (current_module env) id in
    find_in_module env lid k_global_def k_not_found

let lid_is_curmod env lid =
  match env.curmodule with
  | None -> false
  | Some m -> lid_equals lid m

let module_is_defined env lid =
    lid_is_curmod env lid ||
    List.existsb (fun x -> lid_equals lid (fst x)) env.modules

let resolve_module_name env lid (honor_ns: bool) : option lident =
    let nslen = List.length (ns_of_lid lid) in
    let rec aux = function
        | [] ->
          if module_is_defined env lid
          then Some lid
          else None

        | Open_module_or_namespace (ns, Open_namespace, restriction) :: q
          when honor_ns ->
          let new_lid = lid_of_path (path_of_lid ns @ path_of_lid lid) (range_of_lid lid)
          in
          if module_is_defined env new_lid
          then
               Some new_lid
          else aux q

        | Module_abbrev (name, modul) :: _
          when nslen = 0 && (string_of_id name) = (string_of_id (ident_of_lid lid)) ->
          Some modul

        | _ :: q ->
          aux q

    in
    aux env.scope_mods

let is_open env lid open_kind =
  List.existsb (function
                | Open_module_or_namespace (ns, k, Unrestricted) -> k = open_kind && lid_equals lid ns
                | _ -> false) env.scope_mods

let namespace_is_open env lid =
  is_open env lid Open_namespace

let module_is_open env lid =
  lid_is_curmod env lid || is_open env lid Open_module

// FIXME this could be faster (module_is_open and namespace_is_open are slow)
let shorten_module_path env ids is_full_path =
  let rec aux revns id =
    let lid = FStarC.Ident.lid_of_ns_and_id (List.rev revns) id in
    if namespace_is_open env lid
    then Some (List.rev (id :: revns), [])
    else match revns with
         | [] -> None
         | ns_last_id :: rev_ns_prefix ->
           aux rev_ns_prefix ns_last_id |>
             Option.map (fun (stripped_ids, rev_kept_ids) ->
                            (stripped_ids, id :: rev_kept_ids)) in
  let do_shorten env ids =
    // Do the actual shortening.  FIXME This isn't optimal (no includes).
    match List.rev ids with
    | [] -> ([], [])
    | ns_last_id :: ns_rev_prefix ->
      match aux ns_rev_prefix ns_last_id with
      | None -> ([], ids)
      | Some (stripped_ids, rev_kept_ids) -> (stripped_ids, List.rev rev_kept_ids) in

  if is_full_path && List.length ids > 0 then
    // Try to strip the entire prefix.  This is the cheap common case.
    match resolve_module_name env (FStarC.Ident.lid_of_ids ids) true with
    | Some m when module_is_open env m -> (ids, [])
    | _ -> do_shorten env ids
  else
    do_shorten env ids

(* Generic name resolution. *)

let resolve_in_open_namespaces''
  env
  lid
  (eikind: exported_id_kind)
  (k_local_binding: local_binding -> cont_t 'a)
  (k_rec_binding:   rec_binding   -> cont_t 'a)
  (k_record: (record_or_dc) -> cont_t 'a)
  (f_module: lident -> cont_t 'a)
  (l_default: cont_t 'a -> ident -> cont_t 'a)
  : option 'a =
  match ns_of_lid lid with
  | _ :: _ ->
    begin match resolve_module_name env (set_lid_range (lid_of_ids (ns_of_lid lid)) (range_of_lid lid)) true with
    | None -> None
    | Some modul ->
        option_of_cont (fun _ -> None) (find_in_module_with_includes eikind f_module Cont_fail env modul (ident_of_lid lid))
    end
  | [] ->
    try_lookup_id'' env (ident_of_lid lid) eikind k_local_binding k_rec_binding k_record f_module l_default

let cont_of_option (k_none: cont_t 'a) = function
    | Some v -> Cont_ok v
    | None -> k_none

let resolve_in_open_namespaces'
  env
  lid
  (k_local_binding: local_binding -> option 'a)
  (k_rec_binding:   rec_binding   -> option 'a)
  (k_global_def: lident -> (sigelt & bool) -> option 'a)
  : option 'a =
  let k_global_def' k lid def = cont_of_option k (k_global_def lid def) in
  let f_module lid' = let k = Cont_ignore in find_in_module env lid' (k_global_def' k) k in
  let l_default k i = lookup_default_id env i (k_global_def' k) k in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l -> cont_of_option Cont_fail (k_local_binding l))
    (fun r -> cont_of_option Cont_fail (k_rec_binding r))
    (fun _ -> Cont_ignore)
    f_module
    l_default

let fv_qual_of_se = fun se -> match se.sigel with
    | Sig_datacon {ty_lid=l} ->
      let qopt = BU.find_map se.sigquals (function
          | RecordConstructor (_, fs) -> Some (Record_ctor(l, fs))
          | _ -> None) in
      begin match qopt with
        | None -> Some Data_ctor
        | x -> x
      end
    | Sig_declare_typ _ ->  //TODO: record projectors?
      None
    | _ -> None

let lb_fv lbs lid =
     BU.find_map lbs  (fun lb ->
        let fv = Inr?.v lb.lbname in
        if S.fv_eq_lid fv lid then Some fv else None) |> Option.must

let ns_of_lid_equals (lid: lident) (ns: lident) =
    List.length (ns_of_lid lid) = List.length (ids_of_lid ns) &&
    lid_equals (lid_of_ids (ns_of_lid lid)) ns

let try_lookup_name any_val exclude_interf env (lid:lident) : option foundname =
  let occurrence_range = Ident.range_of_lid lid in

  let k_global_def source_lid = function
      | (_, true) when exclude_interf -> None
      | (se, _) ->
        begin match se.sigel with
          | Sig_inductive_typ _ ->   Some (Term_name (S.fvar_with_dd source_lid None, se.sigattrs))
          | Sig_datacon _ ->         Some (Term_name (S.fvar_with_dd source_lid (fv_qual_of_se se), se.sigattrs))
          | Sig_let {lbs=(_, lbs)} ->
            let fv = lb_fv lbs source_lid in
            Some (Term_name (S.fvar_with_dd source_lid fv.fv_qual, se.sigattrs))
          | Sig_declare_typ {lid} ->
            let quals = se.sigquals in
            if any_val //only in scope in an interface (any_val is true) or if the val is assumed
            || quals |> BU.for_some (function Assumption -> true | _ -> false)
            then let lid = Ident.set_lid_range lid (Ident.range_of_lid source_lid) in
                 begin match BU.find_map quals (function Reflectable refl_monad -> Some refl_monad | _ -> None) with //this is really a M?.reflect
                 | Some refl_monad ->
                        let refl_const = S.mk (Tm_constant (FStarC.Const.Const_reflect refl_monad)) occurrence_range in
                        Some (Term_name (refl_const, se.sigattrs))
                 | _ ->
                   Some (Term_name(fvar_with_dd lid (fv_qual_of_se se), se.sigattrs))
                 end
            else None
          | Sig_new_effect(ne) -> Some (Eff_name(se, set_lid_range ne.mname (range_of_lid source_lid)))
          | Sig_effect_abbrev _ ->   Some (Eff_name(se, source_lid))
          | Sig_splice {lids; tac=t} ->
                // TODO: This depth is probably wrong
                Some (Term_name (S.fvar_with_dd source_lid None, []))
          | _ -> None
        end in

  let k_local_binding r = let t = found_local_binding (range_of_lid lid) r in Some (Term_name (t, []))
  in

  let k_rec_binding (id, l, used_marker) =
    used_marker := true;
    Some (Term_name(S.fvar_with_dd (set_lid_range l (range_of_lid lid)) None, []))
  in

  let found_unmangled = match ns_of_lid lid with
  | [] ->
    begin match unmangleOpName (ident_of_lid lid) with
    | Some t -> Some (Term_name (t, []))
    | _ -> None
    end
  | _ -> None
  in

  match found_unmangled with
  | None -> resolve_in_open_namespaces'  env lid k_local_binding k_rec_binding k_global_def
  | x -> x

let try_lookup_effect_name' exclude_interf env (lid:lident) : option (sigelt&lident) =
  match try_lookup_name true exclude_interf env lid with
    | Some (Eff_name(o, l)) -> Some (o,l)
    | _ -> None
let try_lookup_effect_name env l =
    match try_lookup_effect_name' (not env.iface) env l with
        | Some (o, l) -> Some l
        | _ -> None
let try_lookup_effect_name_and_attributes env l =
    match try_lookup_effect_name' (not env.iface) env l with
        | Some ({ sigel = Sig_new_effect(ne) }, l) -> Some (l, ne.cattributes)
        | Some ({ sigel = Sig_effect_abbrev {cflags=cattributes} }, l) -> Some (l, cattributes)
        | _ -> None
let try_lookup_effect_defn env l =
    match try_lookup_effect_name' (not env.iface) env l with
        | Some ({ sigel = Sig_new_effect(ne) }, _) -> Some ne
        | _ -> None
let is_effect_name env lid =
    match try_lookup_effect_name env lid with
        | None -> false
        | Some _ -> true
(* Same as [try_lookup_effect_name], but also traverses effect
abbrevs. TODO: once indexed effects are in, also track how indices and
other arguments are instantiated. *)
let try_lookup_root_effect_name env l =
    match try_lookup_effect_name' (not env.iface) env l with
	| Some ({ sigel = Sig_effect_abbrev {lid=l'} }, _) ->
	  let rec aux new_name =
	      match SMap.try_find (sigmap env) (string_of_lid new_name) with
	      | None -> None
	      | Some (s, _) ->
	        begin match s.sigel with
		| Sig_new_effect(ne)
		  -> Some (set_lid_range ne.mname (range_of_lid l))
		| Sig_effect_abbrev {comp=cmp} ->
                  let l'' = U.comp_effect_name cmp in
		  aux l''
	        | _ -> None
		end
	  in aux l'
	| Some (_, l') -> Some l'
	| _ -> None

let lookup_letbinding_quals_and_attrs env lid =
  let k_global_def lid = function
      | ({sigel = Sig_declare_typ _; sigquals=quals; sigattrs=attrs }, _) ->
          Some (quals, attrs)
      | _ ->
          None in
  match resolve_in_open_namespaces' env lid (fun _ -> None) (fun _ -> None) k_global_def with
    | Some qa -> qa
    | _ -> [], []

let try_lookup_module env path =
  match List.tryFind (fun (mlid, modul) -> path_of_lid mlid = path) env.modules with
    | Some (_, modul) -> Some modul
    | None -> None

let try_lookup_let env (lid:lident) =
  let k_global_def lid = function
      | ({ sigel = Sig_let {lbs=(_, lbs)} }, _) ->
        let fv = lb_fv lbs lid in
        Some (fvar_with_dd lid fv.fv_qual)
      | _ -> None in
  resolve_in_open_namespaces' env lid (fun _ -> None) (fun _ -> None) k_global_def

let try_lookup_definition env (lid:lident) =
    let k_global_def lid = function
      | ({ sigel = Sig_let {lbs} }, _) ->
        BU.find_map (snd lbs) (fun lb ->
            match lb.lbname with
                | Inr fv when S.fv_eq_lid fv lid ->
                  Some (lb.lbdef)
                | _ -> None)
      | _ -> None in
  resolve_in_open_namespaces' env lid (fun _ -> None) (fun _ -> None) k_global_def


let empty_include_smap : SMap.t (ref (list (lident & restriction))) = new_sigmap()
let empty_exported_id_smap : SMap.t exported_id_set = new_sigmap()

let try_lookup_lid' any_val exclude_interface env (lid:lident) : option (term & list attribute) =
  match try_lookup_name any_val exclude_interface env lid with
    | Some (Term_name (e, attrs)) -> Some (e, attrs)
    | _ -> None

let drop_attributes (x:option (term & list attribute)) :option (term) =
  match x with
  | Some (t, _) -> Some t
  | None        -> None

let try_lookup_lid_with_attributes (env:env) (l:lident) :(option (term & list attribute)) = try_lookup_lid' env.iface false env l
let try_lookup_lid (env:env) l = try_lookup_lid_with_attributes env l |> drop_attributes

let resolve_to_fully_qualified_name (env:env) (l:lident) : option lident =
  let r =
    match try_lookup_name true false env l with
    | Some (Term_name (e, attrs)) ->
      begin match (Subst.compress e).n with
      | Tm_fvar fv -> Some fv.fv_name
      | _ -> None
      end
    | Some (Eff_name (o, l)) -> Some l
    | None -> None
  in
  r

(* Is this module lid abbreviated? If there is a module M = A.B in scope,
then this returns Some M for A.B (but not for its descendants). *)
let is_abbrev env lid : option ipath =
  List.tryPick (function
                | Module_abbrev (id, ns) when lid_equals lid ns ->
                    Some [id]
                | _ -> None)
      env.scope_mods

(* Abbreviate a module lid. If there is a module M = A.B.C in scope,
then this returns Some (M, C.D) for A.B.C.D (unless there is a more
specific abbrev, such as one for A.B.C or A.B.C.D) *)
let try_shorten_abbrev (env:env) (ns:ipath) : option (ipath & list ident) =
  let rec aux (ns : ipath) (rest : list ident) =
    match ns with
    | [] -> None
    | hd::tl ->
      match is_abbrev env (lid_of_ids (rev ns)) with
      | Some short -> Some (short, rest)
      | _ ->
        aux tl (hd::rest)
  in
  aux (rev ns) []

let shorten_lid' (env:env) (lid0:lident) : lident =
  (* Id and namespace *)
  let id0 = ident_of_lid lid0 in
  let ns0 = ns_of_lid lid0 in

  (* If this lid is "below" some abbreviation, find it and use it unconditionally. *)
  let pref, ns =
    match try_shorten_abbrev env ns0 with
    | None -> [], ns0
    | Some (ns, rest) -> ns, rest
  in

  (* Move to FStar.List.Tot.Base? *)
  let rec tails l = match l with
    | [] -> [[]]
    | _::tl -> l::(tails tl)
  in

  (* Namespace suffixes, in increasing order of length *)
  let suffs = rev (tails ns) in

  (* Does this shortened lid' resolve to the original lid0? *)
  let try1 (lid' : lident) : bool =
    match resolve_to_fully_qualified_name env lid' with
    | Some lid2 when Ident.lid_equals lid2 lid0 -> true
    | _ -> false
  in

  let rec go (nss : list (list ident)) : lid =
    match nss with
    | ns::rest ->
      let lid' = lid_of_ns_and_id (pref @ ns) id0 in
      if try1 lid'
      then lid'
      else go rest

    | [] ->
      (* This should be unreachable. Warn? *)
      lid0
  in
  let r = go suffs in
  r

let shorten_lid env lid0 =
  match env.curmodule with
  | None -> lid0
  | _ -> shorten_lid' env lid0

let try_lookup_lid_with_attributes_no_resolve (env: env) l :option (term & list attribute) =
  let env' = {env with scope_mods = [] ; exported_ids=empty_exported_id_smap; includes=empty_include_smap }
  in
  try_lookup_lid_with_attributes env' l

let try_lookup_lid_no_resolve (env: env) l :option term = try_lookup_lid_with_attributes_no_resolve env l |> drop_attributes

let try_lookup_datacon env (lid:lident) =
  let k_global_def lid (se, _) =
      match se with
      | { sigel = Sig_declare_typ _; sigquals = quals } ->
        if quals |> BU.for_some (function Assumption -> true | _ -> false)
        then Some (lid_and_dd_as_fv lid None, se)
        else None
      | { sigel = Sig_splice _ } (* A spliced datacon *)
      | { sigel = Sig_datacon _ } ->
         let qual = fv_qual_of_se se in
         Some (lid_and_dd_as_fv lid qual, se)
      | _ -> None in
  resolve_in_open_namespaces' env lid (fun _ -> None) (fun _ -> None) k_global_def

let find_all_datacons env (lid:lident) =
  //
  // AR: TODO: What's happening here? The function name is find_all_datacons, but
  //           it is returning mutuals?
  //
  let k_global_def lid = function
      | ({ sigel = Sig_inductive_typ {mutuals=datas} }, _) -> Some datas
      | _ -> None in
  resolve_in_open_namespaces' env lid (fun _ -> None) (fun _ -> None) k_global_def

let record_cache_aux_with_filter =
    // push, pop, etc. already signal-atomic: no need for BU.atomically
    let record_cache : ref (list (list record_or_dc)) = mk_ref [[]] in
    let push () =
        record_cache := List.hd !record_cache::!record_cache in
    let pop () =
        record_cache := List.tl !record_cache in
    let snapshot () = Common.snapshot push record_cache () in
    let rollback depth = Common.rollback pop record_cache depth in
    let peek () = List.hd !record_cache in
    let insert r = record_cache := (r::peek())::List.tl (!record_cache) in
    (* remove private/abstract records *)
    let filter () =
        let rc = peek () in
        let filtered = List.filter (fun r -> not r.is_private) rc in
        record_cache := filtered :: List.tl !record_cache
    in
    let aux =
    ((push, pop), ((snapshot, rollback), (peek, insert)))
    in (aux, filter)

let record_cache_aux = fst record_cache_aux_with_filter
let filter_record_cache = snd record_cache_aux_with_filter
let push_record_cache = fst (fst record_cache_aux)
let pop_record_cache = snd (fst record_cache_aux)
let snapshot_record_cache = fst (fst (snd record_cache_aux))
let rollback_record_cache = snd (fst (snd record_cache_aux))
let peek_record_cache = fst (snd (snd record_cache_aux))
let insert_record_cache = snd (snd (snd record_cache_aux))

let extract_record (e:env) (new_globs: ref (list scope_mod)) = fun se -> match se.sigel with
  | Sig_bundle {ses=sigs} ->
    let is_record = BU.for_some (function
      | RecordType _
      | RecordConstructor _ -> true
      | _ -> false) in

    let find_dc dc =
      sigs |> Option.find (function
        | { sigel = Sig_datacon {lid} } -> lid_equals dc lid
        | _ -> false) in

    sigs |> List.iter (function
      | { sigel = Sig_inductive_typ {lid=typename;
                                     us=univs;
                                     params=parms;
                                     ds=[dc]}; sigquals = typename_quals } ->
        begin match Option.must (find_dc dc) with
            | { sigel = Sig_datacon {lid=constrname; t; num_ty_params=n} } ->
                let all_formals, _ = U.arrow_formals t in
                (* Ignore parameters, we don't create projectors for them *)
                let _params, formals = BU.first_N n all_formals in
                let is_rec = is_record typename_quals in
                let formals' = formals |> List.collect (fun f ->
                        if S.is_null_bv f.binder_bv
                        || (is_rec && S.is_bqual_implicit f.binder_qual)
                        then []
                        else [f] )
                in
                let fields' = formals' |> List.map (fun f -> (f.binder_bv.ppname, f.binder_bv.sort))
                in
                let fields = fields'
                in
                let record = {typename=typename;
                              constrname=ident_of_lid constrname;
                              parms=parms;
                              fields=fields;
                              is_private = List.contains Private typename_quals;
                              is_record=is_rec} in
                (* the record is added to the current list of
                top-level definitions, to allow shadowing field names
                that were reachable through previous "open"s. *)
                let () = new_globs := Record_or_dc record :: !new_globs in
                (* the field names are added into the set of exported fields for "include" *)
                let () =
                  let add_field (id, _) =
                    let modul = string_of_lid (lid_of_ids (ns_of_lid constrname)) in
                    match get_exported_id_set e modul with
                    | Some my_ex ->
                      let my_exported_ids = my_ex Exported_id_field in
                      let () = my_exported_ids := add (string_of_id id) !my_exported_ids in
                      (* also add the projector name *)
                      let projname = mk_field_projector_name_from_ident constrname id
                                     |> ident_of_lid
                                     |> string_of_id
                      in
                      let () = my_exported_ids := add projname !my_exported_ids in
                      ()
                    | None -> () (* current module was not prepared? should not happen *)
                  in
                  List.iter add_field fields'
                in
                insert_record_cache record
            | _ -> ()
        end
      | _ -> ())

  | _ -> ()

let try_lookup_record_or_dc_by_field_name env (fieldname:lident) =
  let find_in_cache fieldname =
    let ns, id = ns_of_lid fieldname, ident_of_lid fieldname in
    BU.find_map
      (peek_record_cache())
      (fun record ->
        option_of_cont (fun _ -> None) (find_in_record ns id record (fun r -> Cont_ok r)))
  in
  resolve_in_open_namespaces''
    env
    fieldname
    Exported_id_field
    (fun _ -> Cont_ignore)
    (fun _ -> Cont_ignore)
    (fun r -> Cont_ok r)
    (fun fn -> cont_of_option Cont_ignore (find_in_cache fn))
    (fun k _ -> k)

let try_lookup_record_by_field_name env (fieldname:lident) =
    match try_lookup_record_or_dc_by_field_name env fieldname with
        | Some r when r.is_record -> Some r
        | _ -> None

let try_lookup_record_type env (typename:lident) : option record_or_dc =
  let find_in_cache (name:lident) : option record_or_dc =
    let ns, id = ns_of_lid name, ident_of_lid name in
    BU.find_map (peek_record_cache()) (fun record ->
      if ident_equals (ident_of_lid record.typename) id
      then Some record
      else None
    )
  in
  resolve_in_open_namespaces'' env typename
      Exported_id_term_type
      (fun _ -> Cont_ignore)
      (fun _ -> Cont_ignore)
      (fun r -> Cont_ok r)
      (fun l -> cont_of_option Cont_ignore (find_in_cache l))
      (fun k _ -> k)

let belongs_to_record env lid record =
    (* first determine whether lid is a valid record field name, and
    that it resolves to a record' type in the same module as record
    (even though the record types may be different.) *)
    match try_lookup_record_by_field_name env lid with
    | Some record'
      when nsstr record.typename = nsstr record'.typename ->
      (* now, check whether field belongs to record *)
      begin match find_in_record (ns_of_lid record.typename) (ident_of_lid lid) record (fun _ -> Cont_ok ()) with
      | Cont_ok _ -> true
      | _ -> false
      end
    | _ -> false

let try_lookup_dc_by_field_name env (fieldname:lident) =
    match try_lookup_record_or_dc_by_field_name env fieldname with
        | Some r -> Some (set_lid_range (lid_of_ids (ns_of_lid r.typename @ [r.constrname])) (range_of_lid fieldname), r.is_record)
        | _ -> None

let string_set_ref_new () : ref string_set = mk_ref (empty ())
let exported_id_set_new () =
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    function
    | Exported_id_term_type -> term_type_set
    | Exported_id_field -> field_set

let unique any_val exclude_interface env lid =
  (* Disable name resolution altogether, thus lid is assumed to be fully qualified *)
  let filter_scope_mods = function
    | Rec_binding _
        -> true
    | _ -> false
  in
  let this_env = {env with scope_mods = List.filter filter_scope_mods env.scope_mods; exported_ids=empty_exported_id_smap; includes=empty_include_smap } in
  match try_lookup_lid' any_val exclude_interface this_env lid with
    | None -> true
    | Some _ -> false

let push_scope_mod env scope_mod =
 {env with scope_mods = scope_mod :: env.scope_mods}

let push_bv' env (x:ident) =
  let r = range_of_id x in
  let bv = S.gen_bv (string_of_id x) (Some r) ({ tun with pos = r }) in
  let used_marker = mk_ref false in
  let scope_mods =
    match env.scope_mods with
    | Local_bindings lbs :: rest ->
      Local_bindings (PSMap.add lbs (string_of_id x) (x, bv, used_marker)) :: rest
    | _ ->
      Local_bindings (PSMap.add (PSMap.empty()) (string_of_id x) (x, bv, used_marker)) :: env.scope_mods
  in
  { env with scope_mods }, bv, used_marker

let push_bv env x =
  let (env, bv, _) = push_bv' env x in
  (env, bv)

let push_top_level_rec_binding env0 (x:ident) : env & ref bool =
  let l = qualify env0 x in
  if unique false true env0 l || Options.interactive ()
  then
    let used_marker = mk_ref false in
    (push_scope_mod env0 (Rec_binding (x,l,used_marker)), used_marker)
  else raise_error l Errors.Fatal_DuplicateTopLevelNames
         ("Duplicate top-level names " ^ (string_of_lid l))

let push_sigelt' fail_on_dup env s =
  let err #a (l : lident) : a =
    let sopt = SMap.try_find (sigmap env) (string_of_lid l) in
    let r = match sopt with
      | Some (se, _) ->
        begin match Option.find (lid_equals l) (lids_of_sigelt se) with
          | Some l -> Range.string_of_range <| range_of_lid l
          | None -> "<unknown>"
        end
      | None -> "<unknown>" in
    raise_error l Errors.Fatal_DuplicateTopLevelNames [
      Errors.text (Format.fmt1 "Duplicate top-level names [%s]" (string_of_lid l));
      Errors.text (Format.fmt1 "Previously declared at %s" r)
    ]
  in
  let globals = mk_ref env.scope_mods in
  let env =
      let exclude_interface = match s.sigel with
        | Sig_let _
        | Sig_bundle _ -> true
        | _ -> false
      in
      let lids = lids_of_sigelt s in

      (* Discriminators and projectors do not affect the dsenv. The names become
        in-scope immediately after the type's sigelt is pushed. *)
      let lids = List.filter (fun lid -> not (BU.starts_with (show (ident_of_lid lid))  "uu___is_")) lids in
      let lids = List.filter (fun lid -> not (BU.starts_with (show (ident_of_lid lid))  "__proj__")) lids in

      (* Maybe check for duplicates. *)
      if fail_on_dup then
        (match BU.find_map lids (fun l -> if not (unique (*any_val:*)false exclude_interface env l) then Some l else None) with
          | Some l -> err l
          | _ -> ());

      extract_record env globals s;
      {env with sigaccum=s::env.sigaccum}
  in
  let env = {env with scope_mods = !globals} in
  let lss = match s.sigel with
    | Sig_bundle {ses} -> List.map (fun se -> (lids_of_sigelt se, se)) ses
    | _ -> [lids_of_sigelt s, s]
  in
  let push_top_level_def id stack =
    match stack with
    | Top_level_defs ids :: rest ->
      Top_level_defs (PSMap.add ids (string_of_id id) ()) :: rest
    | _ ->
      Top_level_defs (PSMap.add (PSMap.empty()) (string_of_id id) ()) :: stack
  in
  let add1 lid se : unit =
    let () = globals := push_top_level_def (ident_of_lid lid) !globals in
    (* the identifier is added into the list of global identifiers
       of the corresponding module to shadow any "include" *)
    let modul = string_of_lid (lid_of_ids (ns_of_lid lid)) in
    let () = match get_exported_id_set env modul with
    | Some f ->
      let my_exported_ids = f Exported_id_term_type in
      my_exported_ids := add (string_of_id (ident_of_lid lid)) !my_exported_ids
    | None -> () (* current module was not prepared? should not happen *)
    in
    let is_iface = env.iface && not env.admitted_iface in
    // printfn "Adding %s at key %s with flag %A" (FStarC.Syntax.Print.sigelt_to_string_short se) (string_of_lid lid) is_iface;
    SMap.add (sigmap env) (string_of_lid lid) (se, env.iface && not env.admitted_iface);
    ()
  in
  lss |> List.iter (fun (lids, se) ->
    let dummysig l =
      let se = mk_sigelt (Sig_declare_typ {us=[]; lid=l; t=S.tun}) in
      { se with sigquals = [S.Assumption] }
    in
    lids |> List.iter (fun lid -> add1 lid se);
    (* Also add projs/discriminators *)
    let () =
      match se.sigel with
      | Sig_datacon {lid; proj_disc_lids} ->
        proj_disc_lids |> List.iter (fun lid -> add1 lid (dummysig lid))
      | _ -> ()
    in
    ()
  );
  let env = {env with scope_mods = !globals } in
  env

let push_sigelt       env se = push_sigelt' true  env se
let push_sigelt_force env se = push_sigelt' false env se

let find_data_constructors_for_typ env (lid:lident) =
  let k_global_def lid = function
      | ({ sigel = Sig_inductive_typ {ds} }, _) -> Some ds
      | _ -> None in
  resolve_in_open_namespaces' env lid (fun _ -> None) (fun _ -> None) k_global_def

let find_binders_for_datacons: env -> lident -> option (list ident) =
  let debug = FStarC.Debug.get_toggle "open_include_restrictions" in
  fun env lid ->
    let ns = ns_of_lid lid in
    let k_global_def lid = function
        | ({ sigel = Sig_datacon {t; num_ty_params} }, _) ->
            arrow_formals_comp_ln t |> fst
            // The first `num_ty_params` of each constructors of a type are
            // type params, not fields of the constructors: we skip those.
          |> List.splitAt num_ty_params |> snd
          |> List.map (fun x -> x.binder_bv.ppname)
          |> Some
        | _ -> None in
    let result = resolve_in_open_namespaces' env lid (fun _ -> None) (fun _ -> None) k_global_def in
    if !debug then Format.print_string ("find_binders_for_datacons(_, " ^ show lid ^ ") = " ^ show result ^ "\n");
    result

(** Elaborates a `restriction`: this function adds implicit names
(projectors, discriminators, record fields) that F* generates
automatically. It also checks that all the idents the user added
actually exists in the given namespace. *)
let elab_restriction f env ns restriction =
  let open FStarC.Class.Deq in
  match restriction with
  | Unrestricted -> f env ns restriction
  | AllowList l  ->
    let mk_lid (id: ident): lident = set_lid_range (lid_of_ids (ids_of_lid (qual_id ns id))) (range_of_id id) in
    let name_exists id =
      let lid = mk_lid id in
      match try_lookup_lid env lid with
      | Some _ -> true
      | None   -> try_lookup_record_or_dc_by_field_name env lid |> Some?
    in
    // For every inductive, we include its constructors
    let l = List.map (fun (id, renamed) ->
      let with_id_range = Option.dflt id renamed |> range_of_id |> set_id_range in
        match find_data_constructors_for_typ env (mk_lid id) with
      | Some idents -> List.map (fun id -> (ident_of_lid id |> with_id_range, None)) idents
      | None -> []
    ) l |> List.flatten |> List.append l in
    // For every constructor, we include possible desugared record
    // payloads types
    let l =
      (* A (precomputed) associated list that maps a constructors to
         types that comes from a "record-on-a-variant" desugar. E.g. `A`
         is mapped to `Mka__A__payload` for a `type a = | A {x:int}`. *)
      let constructor_lid_to_desugared_record_lids: list (ident * ident) =
        begin let! (_, {declarations}) = env.modules in
              let! sigelt = declarations in
              let! sigelt = match sigelt.sigel with | Sig_bundle {ses} -> ses | _ -> [] in
              let! lid = lids_of_sigelt sigelt in
              match U.get_attribute Const.desugar_of_variant_record_lid sigelt.sigattrs with
            | Some [({n = Tm_constant (FStarC.Const.Const_string (s, _))}, None)]
                -> [(lid_of_str s, lid)]
            | _ -> []
        end
        |> List.filter (fun (cons, lid) -> ns_of_lid cons =?  ns_of_lid lid
                                    && ns_of_lid lid  =? ids_of_lid ns)
        |> List.map (fun (cons, lid) -> (ident_of_lid cons, ident_of_lid lid))
      in constructor_lid_to_desugared_record_lids
       |> List.filter (fun (cons, _) -> List.find (fun (lid, _) -> lid =? cons) l |> Some?)
       |> List.map (fun (_, lid) -> (lid, None))
       |> List.append l
    in
    let l = List.map (fun (id, renamed) ->
      let with_renamed_range = Option.dflt id renamed |> range_of_id |> set_id_range in
      let with_id_range = Option.dflt id renamed |> range_of_id |> set_id_range in
      let lid = mk_lid id in
      begin
      // If `id` is a datatype, we include its projections
      ((match find_binders_for_datacons env lid with | None -> [] | Some l -> l)
      |> List.map (fun binder ->
        ( mk_field_projector_name_from_ident lid binder
          |> ident_of_lid
        , Option.map (fun renamed ->
            mk_field_projector_name_from_ident (lid_of_ids [renamed]) binder
            |> ident_of_lid
          ) renamed
        )
      ))
      // If `id` is a datatype, we include its discriminator
      // (actually, we always include a discriminator, it will be
      // removed if it doesn't exist)
      @ ( [ mk_discriminator (lid_of_ids [id])
          , Option.map (fun renamed -> mk_discriminator (lid_of_ids [renamed])) renamed
          ] |> List.map (fun (x, y) -> (ident_of_lid x, Option.map ident_of_lid y))
            |> List.filter (fun (x, _) -> name_exists x))
      // If `id` is a record, we include its fields
      @ ( match try_lookup_record_type env lid with
        | Some {constrname; fields} -> List.map (fun (id, _) -> (id, None)) fields
        | None -> [])
      end |> List.map (fun (id, renamed) -> (with_id_range id, Option.map with_renamed_range renamed))
    ) l |> List.flatten |> List.append l in
    let _error_on_duplicates =
      let final_idents = List.mapi (fun i (id, renamed) -> (Option.dflt id renamed, i)) l in
      match final_idents |> FStarC.Util.find_dup (fun (x, _) (y, _) -> x =? y) with
      | Some (id, i) ->
        let others = List.filter (fun (id', i') -> id =? id' && not (i =? i')) final_idents in
        List.mapi (fun nth (other, _) ->
          let nth = match nth with | 0 -> "first" | 1 -> "second" | 2 -> "third" | nth -> show (nth + 1) ^ "th" in
          {
            issue_msg = [show other ^ " " ^ nth ^ " occurence comes from this declaration" |> FStarC.Errors.Msg.text];
            issue_level = EError;
            issue_range = Some (range_of_id other);
            issue_number = None;
            issue_ctx = [];
          }
        ) others |> add_issues;
        raise_error id Errors.Fatal_DuplicateTopLevelNames
          (Format.fmt1 ("The name %s was imported " ^ show (List.length others + 1) ^ " times") (string_of_id id))
      | None -> ()
    in
    l |> List.iter (fun (id, _renamed) ->
        if name_exists id |> not then
          raise_error id Errors.Fatal_NameNotFound [
            text <| Format.fmt1 "Definition %s cannot be found." (mk_lid id |> string_of_lid);
          ]);
    f env ns (AllowList l)

let push_namespace' env ns restriction =
  (* namespace resolution disabled, but module abbrevs enabled *)
  (* GM: What's the rationale for this? *)
  let (ns', kd) =
    match resolve_module_name env ns false with
    | None -> (
      let module_names = List.map fst env.modules in
      let module_names =
        match env.curmodule with
        | None -> module_names
        | Some l -> l::module_names
      in
      if module_names |>
         BU.for_some
           (fun m ->
             BU.starts_with (Ident.string_of_lid m ^ ".")
                            (Ident.string_of_lid ns ^ "."))
      then (ns, Open_namespace)
      else
        let open FStarC.Pprint in
        let open FStarC.Class.PP in
        raise_error ns Errors.Fatal_NameSpaceNotFound [
          text <| Format.fmt1 "Namespace '%s' cannot be found." (Ident.string_of_lid ns);
          typo_msg (Ident.string_of_lid ns) (List.map Ident.string_of_lid module_names);
        ]
    )
    | Some ns' ->
      (ns', Open_module)
  in
     env.ds_hooks.ds_push_open_hook env (ns', kd, restriction);
     push_scope_mod env (Open_module_or_namespace (ns', kd, restriction))

let push_include' env ns restriction =
    (* similarly to push_namespace in the case of modules, we allow
       module abbrevs, but not namespace resolution *)
    let ns0 = ns in
    match resolve_module_name env ns false with
    | Some ns ->
      env.ds_hooks.ds_push_include_hook env ns;
      (* from within the current module, include is equivalent to open *)
      let env = push_scope_mod env (Open_module_or_namespace (ns, Open_module, restriction)) in
      (* update the list of includes *)
      let curmod = string_of_lid (current_module env) in
      let () = match SMap.try_find env.includes curmod with
      | None -> ()
      | Some incl -> incl := (ns, restriction) :: !incl
      in
      (* the names of the included module and its transitively
         included modules shadow the names of the current module *)
      begin match get_trans_exported_id_set env (string_of_lid ns) with
      | Some ns_trans_exports ->
        let () = match (get_exported_id_set env curmod, get_trans_exported_id_set env curmod) with
        | (Some cur_exports, Some cur_trans_exports) ->
          let update_exports (k: exported_id_kind) =
            let ns_ex = ! (ns_trans_exports k) |> filter (fun id -> is_ident_allowed_by_restriction (id_of_text id) restriction |> Some?) in
            let ex = cur_exports k in
            let () = ex := diff (!ex) ns_ex in
            let trans_ex = cur_trans_exports k in
            let () = trans_ex := union (!trans_ex) ns_ex in
            ()
          in
          List.iter update_exports all_exported_id_kinds
        | _ -> () (* current module was not prepared? should not happen *)
        in
        env
      | None ->
        (* module to be included was not prepared, so forbid the 'include'. It may be the case for modules such as FStarC.Effect, etc. *)
        raise_error ns Errors.Fatal_IncludeModuleNotPrepared
          (Format.fmt1 "include: Module %s was not prepared" (string_of_lid ns))
      end
    | _ ->
      raise_error ns Errors.Fatal_ModuleNotFound
        (Format.fmt1 "include: Module %s cannot be found" (string_of_lid ns))

let push_namespace = elab_restriction push_namespace'
let push_include   = elab_restriction push_include'

let push_module_abbrev env x l =
  (* both namespace resolution and module abbrevs disabled:
     in 'module A = B', B must be fully qualified *)
  if module_is_defined env l
  then begin
       env.ds_hooks.ds_push_module_abbrev_hook env x l;
       push_scope_mod env (Module_abbrev (x,l))
  end else raise_error l Errors.Fatal_ModuleNotFound
             (Format.fmt1 "Module %s cannot be found" (Ident.string_of_lid l))

let check_admits env m =
  let admitted_sig_lids =
    env.sigaccum |> List.fold_left (fun lids se ->
      match se.sigel with
      | Sig_declare_typ {lid=l; us=u; t} when not (se.sigquals |> List.contains Assumption) ->
        // l is already fully qualified, so no name resolution
        begin match SMap.try_find (sigmap env) (string_of_lid l) with
          | Some ({sigel=Sig_let _}, _)
          | Some ({sigel=Sig_inductive_typ _}, _)
          | Some ({sigel=Sig_splice _}, _) ->
            (* ok *)
            lids
          | _ ->
            if not (Options.interactive ()) then begin
              let open FStarC.Pprint in
              let open FStarC.Class.PP in
              FStarC.Errors.log_issue l Errors.Error_AdmitWithoutDefinition [
                 doc_of_string (show l) ^/^ text "is declared but no definition was found";
                 text "Add an 'assume' if this is intentional"
              ]
            end;
            let quals = Assumption :: se.sigquals in
            SMap.add (sigmap env) (string_of_lid l) ({ se with sigquals = quals }, false);
            l::lids
        end
      | _ -> lids) []
  in
  m
  
let finish env modul =
  modul.declarations |> List.iter (fun se ->
    let quals = se.sigquals in
    match se.sigel with
    | Sig_bundle {ses} ->
      if List.contains Private quals
      then ses |> List.iter (fun se -> match se.sigel with
                | Sig_datacon {lid} ->
                  SMap.remove (sigmap env) (string_of_lid lid)
                | Sig_inductive_typ {lid;us=univ_names;params=binders;t=typ} ->
                  SMap.remove (sigmap env) (string_of_lid lid);
                  if not (List.contains Private quals)
                  then //it's only abstract; add it back to the environment as an abstract type
                       let sigel = Sig_declare_typ {lid;us=univ_names;t=S.mk (Tm_arrow {bs=binders; comp=S.mk_Total typ}) (Ident.range_of_lid lid)} in
                       let se = {se with sigel=sigel; sigquals=Assumption::quals} in
                       SMap.add (sigmap env) (string_of_lid lid) (se, false)
                | _ -> ())

    | Sig_declare_typ {lid} ->
      if List.contains Private quals
      then SMap.remove (sigmap env) (string_of_lid lid)

    | Sig_let {lbs=(_,lbs)} ->
      if List.contains Private quals
      then begin
           lbs |> List.iter (fun lb -> SMap.remove (sigmap env) (string_of_lid (Inr?.v lb.lbname).fv_name))
      end

    | _ -> ());
  (* update the sets of transitively exported names of this module by
     adding the unshadowed names defined only in the current module. *)
  let curmod = string_of_lid (current_module env) in
  let () = match (get_exported_id_set env curmod, get_trans_exported_id_set env curmod) with
    | (Some cur_ex, Some cur_trans_ex) ->
      let update_exports eikind =
        let cur_ex_set = ! (cur_ex eikind) in
        let cur_trans_ex_set_ref = cur_trans_ex eikind in
        cur_trans_ex_set_ref := union cur_ex_set (!cur_trans_ex_set_ref)
       in
       List.iter update_exports all_exported_id_kinds
    | _ -> ()
  in
  (* remove abstract/private records *)
  let () = filter_record_cache () in
  {env with
    curmodule=None;
    modules=(modul.name, modul)::env.modules;
    scope_mods = [];
    sigaccum=[];
  }

let stack: ref (list env) = mk_ref []
let push env = BU.atomically (fun () ->
  push_record_cache();
  stack := env::!stack;
  {env with exported_ids = SMap.copy env.exported_ids;
            trans_exported_ids = SMap.copy env.trans_exported_ids;
            includes = SMap.copy env.includes;
            sigmap = SMap.copy env.sigmap })

let pop () = BU.atomically (fun () ->
  match !stack with
  | env::tl ->
    pop_record_cache();
    stack := tl;
    env
  | _ -> failwith "Impossible: Too many pops")

let snapshot env = Common.snapshot push stack env
let rollback depth = Common.rollback pop stack depth

let export_interface (m:lident) env =
//    printfn "Exporting interface %s" (string_of_lid m);
    let sigelt_in_m se =
        match U.lids_of_sigelt se with
            | l::_ -> (nsstr l)=(string_of_lid m)
            | _ -> false in
    let sm = sigmap env in
    let env = pop () in // FIXME PUSH POP
    let keys = SMap.keys sm in
    let sm' = sigmap env in
    keys |> List.iter (fun k ->
    match SMap.try_find sm' k with
        | Some (se, true) when sigelt_in_m se ->
          SMap.remove sm' k;
//          printfn "Exporting %s" k;
          let se = match se.sigel with
            | Sig_declare_typ {lid=l; us=u; t} ->
              { se with sigquals = Assumption::se.sigquals }
            | _ -> se in
          SMap.add sm' k (se, false)
        | _ -> ());
    env

let finish_module_or_interface env modul =
  let modul = if not modul.is_interface then check_admits env modul else modul in
  finish env modul, modul

type exported_ids = {
    exported_id_terms : string_set;
    exported_id_fields: string_set;
}
let as_exported_ids (e:exported_id_set) =
    let terms  = (!(e Exported_id_term_type)) in
    let fields = (!(e Exported_id_field)) in
    {exported_id_terms=terms;
     exported_id_fields=fields}

let as_exported_id_set (e:option exported_ids) =
    match e with
    | None -> exported_id_set_new ()
    | Some e ->
      let terms =
          mk_ref (e.exported_id_terms) in
      let fields =
          mk_ref (e.exported_id_fields) in
      function
        | Exported_id_term_type -> terms
        | Exported_id_field -> fields


type module_inclusion_info = {
    mii_exported_ids:option exported_ids;
    mii_trans_exported_ids:option exported_ids;
    mii_includes:option (list (lident & restriction));
    mii_no_prelude:bool;
}

let default_mii = {
    mii_exported_ids=None;
    mii_trans_exported_ids=None;
    mii_includes=None;
    mii_no_prelude=false;
}

let as_includes = function
    | None -> mk_ref []
    | Some l -> mk_ref l

let inclusion_info env (l:lident) =
   let mname = FStarC.Ident.string_of_lid l in
   let as_ids_opt m =
      Option.map as_exported_ids (SMap.try_find m mname)
   in
   {
      mii_exported_ids = as_ids_opt env.exported_ids;
      mii_trans_exported_ids = as_ids_opt env.trans_exported_ids;
      mii_includes = Option.map (fun r -> !r) (SMap.try_find env.includes mname);
      mii_no_prelude = env.no_prelude;
   }

let prepare_module_or_interface intf admitted env mname (mii:module_inclusion_info) = (* AR: open the pervasives namespace *)
  let prep env =
    let filename = BU.strcat (string_of_lid mname) ".fst" in
    let auto_open = if mii.mii_no_prelude then [] else FStarC.Parser.Dep.prelude in
    let auto_open =
      let convert_kind = function
      | FStarC.Parser.Dep.Open_namespace -> Open_namespace
      | FStarC.Parser.Dep.Open_module -> Open_module
      in
      auto_open |> List.map (fun (kind, lid) -> (lid, convert_kind kind, Unrestricted))
    in
    let namespace_of_module =
      if List.length (ns_of_lid mname) > 0
      then [ (lid_of_ids (ns_of_lid mname), Open_namespace, Unrestricted) ]
      else []
    in
    (* [scope_mods] is a stack, so reverse the order *)
    let auto_open = namespace_of_module @ List.rev auto_open in

    (* Create new empty set of exported identifiers for the current module, for 'include' *)
    let () = SMap.add env.exported_ids (string_of_lid mname) (as_exported_id_set mii.mii_exported_ids) in
    (* Create new empty set of transitively exported identifiers for the current module, for 'include' *)
    let () = SMap.add env.trans_exported_ids (string_of_lid mname) (as_exported_id_set mii.mii_trans_exported_ids) in
    (* Create new empty list of includes for the current module *)
    let () = SMap.add env.includes (string_of_lid mname) (as_includes mii.mii_includes) in
    let env' = {
      env with curmodule=Some mname;
      sigmap=env.sigmap;
      scope_mods = List.map (fun x -> Open_module_or_namespace x) auto_open;
      iface=intf;
      admitted_iface=admitted } in
    List.iter (fun op -> env.ds_hooks.ds_push_open_hook env' op) (List.rev auto_open);
    env'
  in

  match env.modules |> Option.find (fun (l, _) -> lid_equals l mname) with
    | None ->
        prep env, false
    | Some (_, m) ->
        if not (Options.interactive ()) && (not m.is_interface || intf)
        then raise_error mname Errors.Fatal_DuplicateModuleOrInterface
               (Format.fmt1 "Duplicate module or interface name: %s" (string_of_lid mname));
        //we have an interface for this module already; if we're not interactive then do not export any symbols from this module
        prep (push env), true //push a context so that we can pop it when we're done // FIXME PUSH POP

let enter_monad_scope env mname =
  match env.curmonad with
  | Some mname' ->
    raise_error mname Errors.Fatal_MonadAlreadyDefined
      ("Trying to define monad " ^ (show mname) ^ ", but already in monad scope " ^ (show mname')) 
  | None -> {env with curmonad = Some mname}

let fail_or env lookup lid =
  match lookup lid with
  | Some r -> r
  | None ->
    (* We couldn't find it. Try to report a nice error. *)
    let opened_modules = List.map (fun (lid, _) -> string_of_lid lid) env.modules in
    let open FStarC.Class.PP in
    if List.length (ns_of_lid lid) = 0 then
      raise_error lid Errors.Fatal_IdentifierNotFound [
        Pprint.prefix 2 1 (text "Identifier not found:") (pp lid);
        typo_msg (Ident.string_of_lid lid) (all_local_names env);
      ]
    else
      let all_ids_in_module (m : lident) : list string =
        let m = string_of_lid m in
        match SMap.try_find env.trans_exported_ids m with
        | Some f ->
          let exported_ids = !(f Exported_id_term_type) in
          exported_ids |> Class.Setlike.elems
        | None -> []
      in
      let modul = lid_of_ids (ns_of_lid lid) in
      let modul =
        let h::t = ids_of_lid modul in
        let rng = List.fold_right (fun i r -> Range.union_ranges (range_of_id i) r) t (range_of_id h) in
        set_lid_range modul rng
      in
      (* ^ Make the range point to the namespace component of the lid, to highlight X.Y in X.Y.z *)
      let open FStarC.Pprint in
      match resolve_module_name env modul true with
      | None ->
        raise_error modul Errors.Fatal_IdentifierNotFound [
          flow (break_ 1) [
            text "Module name";
            pp modul;
            text "could not be resolved.";
          ];
          typo_msg (Ident.string_of_lid modul) (all_mod_names env);
        ]

      | Some modul' when (not (List.existsb (fun m -> m = (string_of_lid modul')) opened_modules)) ->
        (* How can this happen? *)
        raise_error modul Errors.Fatal_IdentifierNotFound [
          flow (break_ 1) [
            text "Module name";
            pp modul;
            text "resolved to";
            pp modul';
            text "which is not in scope.";
          ];
          if Debug.any ()
          then text "Opened modules =" ^/^ (String.concat ", " opened_modules |> Errors.text)
          else empty;
        ]

      | Some modul' ->
        raise_error lid Errors.Fatal_IdentifierNotFound [
          flow (break_ 1) [
            text "Identifier";
            pp (ident_of_lid lid);
            text "not found in module";
            pp modul;
            (let open FStarC.Class.Deq in
              if modul <>? modul' then
              Pprint.parens (Pprint.prefix 2 1 (text "resolved to") (pp modul'))
            else
              empty);
          ];
          typo_msg (Ident.string_of_id (ident_of_lid lid)) (all_ids_in_module modul');
        ]

let fail_or2 env lookup id = match lookup id with
  | Some r -> r
  | None ->
    let open FStarC.Class.PP in
    raise_error id Errors.Fatal_IdentifierNotFound [
      Pprint.prefix 2 1 (text "Identifier not found:") (pp id);
      typo_msg (Ident.string_of_id id) (all_local_names env);
    ]

let resolve_name (e:env) (name:lident)
  : option (either bv fv)
  = match try_lookup_name false false e name with
    | None -> None
    | Some (Term_name (e, attrs)) -> (
        match (Subst.compress e).n with
        | Tm_name n -> Some (Inl n)
        | Tm_fvar fv -> Some (Inr fv)
        | _ -> None
    )
    | Some (Eff_name(se, l)) ->
      Some (Inr (S.lid_and_dd_as_fv l None))

let set_no_prelude (e:env) (b:bool) =
  { e with no_prelude = b }
