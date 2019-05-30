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
#light "off"

module FStar.SMTEncoding.Env
open FStar.ST
open FStar.Exn
open FStar.All
open Prims
open FStar
open FStar.TypeChecker.Env
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.TypeChecker
open FStar.SMTEncoding.Term
open FStar.Ident
open FStar.SMTEncoding.Util

module SS = FStar.Syntax.Subst
module BU = FStar.Util
module U = FStar.Syntax.Util

exception Inner_let_rec

let add_fuel x tl = if (Options.unthrottle_inductives()) then tl else x::tl
let withenv c (a, b) = (a,b,c)
let vargs args = List.filter (function (BU.Inl _, _) -> false | _ -> true) args
(* ------------------------------------ *)
(* Some operations on constants *)
let escape (s:string) = BU.replace_char s '\'' '_'
let mk_term_projector_name lid (a:bv) =
    escape <| BU.format2 "%s_%s" lid.str a.ppname.idText
let primitive_projector_by_pos env lid i =
    let fail () = failwith (BU.format2 "Projector %s on data constructor %s not found" (string_of_int i) (lid.str)) in
    let _, t = Env.lookup_datacon env lid in
    match (SS.compress t).n with
        | Tm_arrow(bs, c) ->
          let binders, _ = SS.open_comp bs c in
          if ((i < 0) || i >= List.length binders) //this has to be within bounds!
          then fail ()
          else let b = List.nth binders i in
                mk_term_projector_name lid (fst b)
        | _ -> fail ()
let mk_term_projector_name_by_pos lid (i:int) = escape <| BU.format2 "%s_%s" lid.str (string_of_int i)
let mk_term_projector (lid:lident) (a:bv) : term =
    mkFreeV <| mk_fv (mk_term_projector_name lid a, Arrow(Term_sort, Term_sort))
let mk_term_projector_by_pos (lid:lident) (i:int) : term =
    mkFreeV <| mk_fv (mk_term_projector_name_by_pos lid i, Arrow(Term_sort, Term_sort))
let mk_data_tester env l x = mk_tester (escape l.str) x
(* ------------------------------------ *)
(* New name generation *)
type varops_t = {
    push: unit -> unit;
    pop: unit -> unit;
    snapshot: unit -> (int * unit);
    rollback: option<int> -> unit;
    new_var:ident -> int -> string; (* each name is distinct and has a prefix corresponding to the name used in the program text *)
    new_fvar:lident -> string;
    fresh:string -> string -> string;  (* module name -> prefix -> name *)
    reset_fresh:unit -> unit;
    string_const:string -> term;
    next_id: unit -> int;
    mk_unique:string -> string;
}
let varops =
    let initial_ctr = 100 in
    let ctr = BU.mk_ref initial_ctr in
    let new_scope () = (BU.smap_create 100, BU.smap_create 100) in (* a scope records all the names and string constants used in that scope *)
    let scopes = BU.mk_ref [new_scope ()] in
    let mk_unique y =
        let y = escape y in
        let y = match BU.find_map (!scopes) (fun (names, _) -> BU.smap_try_find names y) with
                  | None -> y
                  | Some _ -> BU.incr ctr; y ^ "__" ^ (string_of_int !ctr) in
        let top_scope = fst <| List.hd !scopes in
        BU.smap_add top_scope y true; y in
    let new_var pp rn = mk_unique <| pp.idText ^ "__" ^ (string_of_int rn) in
    let new_fvar lid = mk_unique lid.str in
    let next_id () = BU.incr ctr; !ctr in
    //AR: adding module name after the prefix, else it interferes for name matching for fuel arguments
    //    see try_lookup_free_var below
    let fresh mname pfx = BU.format3 "%s_%s_%s" pfx mname (string_of_int <| next_id()) in
    //the fresh counter is reset after every module
    let reset_fresh () = ctr := initial_ctr in
    let string_const s = match BU.find_map !scopes (fun (_, strings) -> BU.smap_try_find strings s) with
        | Some f -> f
        | None ->
            let id = next_id () in
            let f = Term.boxString <| mk_String_const id in
            let top_scope = snd <| List.hd !scopes in
            BU.smap_add top_scope s f;
            f in
    let push () = scopes := new_scope() :: !scopes in // already signal-atomic
    let pop () = scopes := List.tl !scopes in // already signal-atomic
    let snapshot () = FStar.Common.snapshot push scopes () in
    let rollback depth = FStar.Common.rollback pop scopes depth in
    {push=push;
     pop=pop;
     snapshot=snapshot;
     rollback=rollback;
     new_var=new_var;
     new_fvar=new_fvar;
     fresh=fresh;
     reset_fresh=reset_fresh;
     string_const=string_const;
     next_id=next_id;
     mk_unique=mk_unique}

(* ---------------------------------------------------- *)
(* <Environment> *)
(* Each entry maps a Syntax variable to its encoding as a SMT2 term *)
(* free variables, depending on whether or not they are fully applied ...  *)
(* ... are mapped either to SMT2 functions, or to nullary tokens *)
type fvar_binding = {
    fvar_lid:  lident;
    smt_arity: int;
    smt_id:    string;
    smt_token: option<term>;
    smt_fuel_partial_app:option<term>;
    fvb_thunked: bool
}
let fvb_to_string fvb =
  let term_opt_to_string = function
    | None -> "None"
    | Some s -> Term.print_smt_term s
  in
  BU.format5 "{ lid = %s;\n  smt_id = %s;\n  smt_token = %s;\n smt_fuel_partial_app = %s;\n fvb_thunked = %s }"
    (Ident.string_of_lid fvb.fvar_lid)
    fvb.smt_id
    (term_opt_to_string fvb.smt_token)
    (term_opt_to_string fvb.smt_fuel_partial_app)
    (BU.string_of_bool fvb.fvb_thunked)

let check_valid_fvb fvb =
    if (Option.isSome fvb.smt_token
     || Option.isSome fvb.smt_fuel_partial_app)
    && fvb.fvb_thunked
    then failwith (BU.format1 "Unexpected thunked SMT symbol: %s" (Ident.string_of_lid fvb.fvar_lid))
    else if fvb.fvb_thunked && fvb.smt_arity <> 0
    then failwith (BU.format1 "Unexpected arity of thunked SMT symbol: %s" (Ident.string_of_lid fvb.fvar_lid));
    match fvb.smt_token with
    | Some ({tm=FreeV _}) ->
      failwith (BU.format1 "bad fvb\n%s" (fvb_to_string fvb))
    | _ -> ()


let binder_of_eithervar v = (v, None)

type env_t = {
    bvar_bindings: BU.psmap<BU.pimap<(bv * term)>>;
    fvar_bindings: (BU.psmap<fvar_binding> * list<fvar_binding>);  //list of fvar bindings for the current module
                                                                   //remember them so that we can store them in the checked file
    depth:int; //length of local var/tvar bindings
    tcenv:Env.env;
    warn:bool;
    nolabels:bool;
    use_zfuel_name:bool;
    encode_non_total_function_typ:bool;
    current_module_name:string;
    encoding_quantifier:bool;
    global_cache:BU.smap<decls_elt>  //cache for hashconsing -- see Encode.fs where it is used and updated
}

let print_env e =
    let bvars = BU.psmap_fold e.bvar_bindings (fun _k pi acc ->
        BU.pimap_fold pi (fun _i (x, _term) acc ->
            Print.bv_to_string x :: acc) acc) [] in
    let allvars = BU.psmap_fold (e.fvar_bindings |> fst) (fun _k fvb acc ->
        fvb.fvar_lid :: acc) [] in
    let last_fvar =
      match List.rev allvars with
      | [] -> ""
      | l::_ -> "...," ^ Print.lid_to_string l
    in
    String.concat ", " (last_fvar :: bvars)

let lookup_bvar_binding env bv =
    match BU.psmap_try_find env.bvar_bindings bv.ppname.idText with
    | Some bvs -> BU.pimap_try_find bvs bv.index
    | None -> None

let lookup_fvar_binding env lid =
    BU.psmap_try_find (env.fvar_bindings |> fst) lid.str

let add_bvar_binding bvb bvbs =
  BU.psmap_modify bvbs (fst bvb).ppname.idText
    (fun pimap_opt ->
     BU.pimap_add (BU.dflt (BU.pimap_empty ()) pimap_opt) (fst bvb).index bvb)

let add_fvar_binding fvb (fvb_map, fvb_list) =
  (BU.psmap_add fvb_map fvb.fvar_lid.str fvb, fvb::fvb_list)

let fresh_fvar mname x s = let xsym = varops.fresh mname x in xsym, mkFreeV <| mk_fv (xsym, s)
(* generate terms corresponding to a variable and record the mapping in the environment *)

(* Bound term variables *)
let gen_term_var (env:env_t) (x:bv) =
    let ysym = "@x"^(string_of_int env.depth) in
    let y = mkFreeV <| mk_fv (ysym, Term_sort) in
    ysym, y, {env with bvar_bindings=add_bvar_binding (x, y) env.bvar_bindings; depth=env.depth + 1}
let new_term_constant (env:env_t) (x:bv) =
    let ysym = varops.new_var x.ppname x.index in
    let y = mkApp(ysym, []) in
    ysym, y, {env with bvar_bindings=add_bvar_binding (x, y) env.bvar_bindings}
let new_term_constant_from_string (env:env_t) (x:bv) str =
    let ysym = varops.mk_unique str in
    let y = mkApp(ysym, []) in
    ysym, y, {env with bvar_bindings=add_bvar_binding (x, y) env.bvar_bindings}
let push_term_var (env:env_t) (x:bv) (t:term) =
    {env with bvar_bindings=add_bvar_binding (x,t) env.bvar_bindings}
let lookup_term_var env a =
    match lookup_bvar_binding env a with
    | None ->
        (match lookup_bvar_binding env a with
         | None -> failwith (BU.format2 "Bound term variable not found  %s in environment: %s"
                                        (Print.bv_to_string a)
                                        (print_env env))
         | Some (b,t) -> t)
    | Some (b,t) -> t

(* Qualified term names *)
let mk_fvb lid fname arity ftok fuel_partial_app thunked =
    let fvb = {
        fvar_lid  = lid;
        smt_arity = arity;
        smt_id    = fname;
        smt_token = ftok;
        smt_fuel_partial_app = fuel_partial_app;
        fvb_thunked = thunked;
        }
    in
    check_valid_fvb fvb;
    fvb
let new_term_constant_and_tok_from_lid_aux (env:env_t) (x:lident) arity thunked =
    let fname = varops.new_fvar x in
    let ftok_name, ftok =
        if thunked then None, None
        else let ftok_name = fname^"@tok" in
             let ftok = mkApp(ftok_name, []) in
             Some ftok_name, Some ftok
    in
    let fvb = mk_fvb x fname arity ftok None thunked in
//    Printf.printf "Pushing %A @ %A, %A\n" x fname ftok;
    fname, ftok_name, {env with fvar_bindings=add_fvar_binding fvb env.fvar_bindings}
let new_term_constant_and_tok_from_lid (env:env_t) (x:lident) arity =
    let fname, ftok_name_opt, env = new_term_constant_and_tok_from_lid_aux env x arity false in
    fname, Option.get ftok_name_opt, env
let new_term_constant_and_tok_from_lid_maybe_thunked (env:env_t) (x:lident) arity th =
    new_term_constant_and_tok_from_lid_aux env x arity th
let lookup_lid env a =
    match lookup_fvar_binding env a with
    | None -> failwith (BU.format1 "Name not found: %s" (Print.lid_to_string a))
    | Some s -> check_valid_fvb s; s
let push_free_var_maybe_thunked env (x:lident) arity fname ftok thunked =
    let fvb = mk_fvb x fname arity ftok None thunked in
    {env with fvar_bindings=add_fvar_binding fvb env.fvar_bindings}
let push_free_var env (x:lident) arity fname ftok =
    push_free_var_maybe_thunked env x arity fname ftok false
let push_free_var_thunk env (x:lident) arity fname ftok =
    push_free_var_maybe_thunked env x arity fname ftok (arity=0)
let push_zfuel_name env (x:lident) f =
    let fvb = lookup_lid env x in
    let t3 = mkApp(f, [mkApp("ZFuel", [])]) in
    let fvb = mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token (Some t3) false in
    {env with fvar_bindings=add_fvar_binding fvb env.fvar_bindings}
let force_thunk fvb =
    if not (fvb.fvb_thunked) || fvb.smt_arity <> 0
    then failwith "Forcing a non-thunk in the SMT encoding";
    mkFreeV <| (fvb.smt_id, Term_sort, true)
module TcEnv = FStar.TypeChecker.Env
let try_lookup_free_var env l =
    match lookup_fvar_binding env l with
    | None -> None
    | Some fvb ->
      if TcEnv.debug env.tcenv <| Options.Other "PartialApp"
      then BU.print2 "Looked up %s found\n%s\n"
             (Ident.string_of_lid l)
             (fvb_to_string fvb);
      if fvb.fvb_thunked
      then Some (force_thunk fvb)
      else
      begin
      match fvb.smt_fuel_partial_app with
      | Some f when env.use_zfuel_name -> Some f
      | _ ->
        begin
        match fvb.smt_token with
        | Some t ->
          begin
          match t.tm with
          | App(_, [fuel]) ->
            if (BU.starts_with (Term.fv_of_term fuel |> fv_name) "fuel")
            then Some <| mk_ApplyTF(mkFreeV <| mk_fv (fvb.smt_id, Term_sort)) fuel
            else Some t
          | _ -> Some t
          end
        | _ -> None
        end
      end
let lookup_free_var env a =
    match try_lookup_free_var env a.v with
    | Some t -> t
    | None -> failwith (BU.format1 "Name not found: %s" (Print.lid_to_string a.v))
let lookup_free_var_name env a = lookup_lid env a.v
let lookup_free_var_sym env a =
    let fvb = lookup_lid env a.v in
    match fvb.smt_fuel_partial_app with
    | Some({tm=App(g, zf)})
        when env.use_zfuel_name ->
      BU.Inl g, zf, fvb.smt_arity + 1
    | _ ->
        begin
        match fvb.smt_token with
        | None when fvb.fvb_thunked ->
            BU.Inr (force_thunk fvb), [], fvb.smt_arity
        | None ->
            BU.Inl (Var fvb.smt_id), [], fvb.smt_arity
        | Some sym ->
            begin
            match sym.tm with
            | App(g, [fuel]) ->
                BU.Inl g, [fuel], fvb.smt_arity + 1
            | _ ->
                BU.Inl (Var fvb.smt_id), [], fvb.smt_arity
            end
        end

let tok_of_name env nm =
  match
    BU.psmap_find_map (env.fvar_bindings |> fst) (fun _ fvb ->
      check_valid_fvb fvb;
      if fvb.smt_id = nm then fvb.smt_token else None)
  with
  | Some b -> Some b
  | None -> //this must be a bvar
    BU.psmap_find_map env.bvar_bindings (fun _ pi ->
    BU.pimap_fold pi (fun _ y res ->
      match res, y with
      | Some _, _ -> res
      | None, (_, {tm=App(Var sym, [])}) when sym=nm ->
        Some (snd y)
      | _ -> None) None)

let reset_current_module_fvbs env = { env with fvar_bindings = (env.fvar_bindings |> fst, []) }
let get_current_module_fvbs env = env.fvar_bindings |> snd
let add_fvar_binding_to_env fvb env =
  { env with fvar_bindings = add_fvar_binding fvb env.fvar_bindings }

(* </Environment> *)
