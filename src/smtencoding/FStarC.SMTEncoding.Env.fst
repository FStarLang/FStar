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
module FStarC.SMTEncoding.Env

open FStarC
open FStarC.Effect
open FStarC.TypeChecker.Env
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Syntax.Print {}
open FStarC.TypeChecker
open FStarC.SMTEncoding.Term
open FStarC.Ident
open FStarC.SMTEncoding.Util

module SS = FStarC.Syntax.Subst
module BU = FStarC.Util

open FStarC.Class.Show

let dbg_PartialApp = Debug.get_toggle "PartialApp"

let add_fuel x tl = if (Options.unthrottle_inductives()) then tl else x::tl
let withenv c (a, b) = (a,b,c)
let vargs args = List.filter (function (Inl _, _) -> false | _ -> true) args
(* ------------------------------------ *)
(* Some operations on constants *)
let escape (s:string) = BU.replace_char s '\'' '_'
let mk_term_projector_name lid (a:bv) =
    escape <| Format.fmt2 "%s_@%s" (string_of_lid lid) (string_of_id a.ppname)
let mk_univ_projector_name lid (i:int) =
    escape <| Format.fmt2 "%s_@%s" (string_of_lid lid) (string_of_int i)
let primitive_projector_by_pos env lid i =
    let fail () = failwith (Format.fmt2 "Projector %s on data constructor %s not found" (show i) (string_of_lid lid)) in
    let _, t = Env.lookup_datacon env lid in
    match (SS.compress t).n with
        | Tm_arrow {bs; comp=c} ->
          let binders, _ = SS.open_comp bs c in
          if ((i < 0) || i >= List.length binders) //this has to be within bounds!
          then fail ()
          else let b = List.nth binders i in
                mk_term_projector_name lid b.binder_bv
        | _ -> fail ()
let mk_term_projector_name_by_pos lid (i:int) = escape <| Format.fmt2 "%s_@%s" (string_of_lid lid) (show i)
let mk_term_projector (lid:lident) (a:bv) : term =
    mkFreeV <| mk_fv (mk_term_projector_name lid a, Arrow(Term_sort, Term_sort))
let mk_term_projector_by_pos (lid:lident) (i:int) : term =
    mkFreeV <| mk_fv (mk_term_projector_name_by_pos lid i, Arrow(Term_sort, Term_sort))
let mk_data_tester env l x = mk_tester (escape (string_of_lid l)) x
(* ------------------------------------ *)
(* New name generation *)
type varops_t = {
    push: unit -> unit;
    pop: unit -> unit;
    snapshot: unit -> (int & unit);
    rollback: option int -> unit;
    new_var:ident -> int -> string; (* each name is distinct and has a prefix corresponding to the name used in the program text *)
    new_fvar:lident -> string;
    fresh:string -> string -> string;  (* module name -> prefix -> name *)
    reset_fresh:unit -> unit;
    next_id: unit -> int;
    mk_unique:string -> string;
    reset_scope: unit -> unit
}
let varops =
    let initial_ctr = 100 in
    let ctr = mk_ref initial_ctr in
    let new_scope () : SMap.t bool = SMap.create 100 in (* a scope records all the names used in that scope *)
    let scopes = mk_ref [new_scope ()] in
    let mk_unique y =
        let y = escape y in
        let y = match BU.find_map (!scopes) (fun names -> SMap.try_find names y) with
                  | None -> y
                  | Some _ -> BU.incr ctr; y ^ "__" ^ (show !ctr) in
        let top_scope = List.hd !scopes in
        SMap.add top_scope y true; y in
    let new_var pp rn = mk_unique <| (string_of_id pp) ^ "__" ^ (show rn) in
    let new_fvar lid = mk_unique (string_of_lid lid) in
    let next_id () = BU.incr ctr; !ctr in
    //AR: adding module name after the prefix, else it interferes for name matching for fuel arguments
    //    see try_lookup_free_var below
    let fresh mname pfx = Format.fmt3 "%s_%s_%s" pfx mname (show <| next_id()) in
    //the fresh counter is reset after every module
    let reset_fresh () = ctr := initial_ctr in
    let push () =
      if Debug.any() then Format.print_string "SMTEncoding.scopes.push\n";
      scopes := new_scope() :: !scopes in // already signal-atomic
    let pop () = 
      if Debug.any() then Format.print_string "SMTEncoding.scopes.pop\n";
      scopes := List.tl !scopes in // already signal-atomic
    let snapshot () = FStarC.Common.snapshot "SMTEncoding.scopes" push scopes () in
    let rollback depth = FStarC.Common.rollback "SMTEncoding.scopes" pop scopes depth in
    {push=push;
     pop=pop;
     snapshot=snapshot;
     rollback=rollback;
     new_var=new_var;
     new_fvar=new_fvar;
     fresh=fresh;
     reset_fresh=reset_fresh;
     next_id=next_id;
     mk_unique=mk_unique;
     reset_scope=fun () -> 
      if Debug.any() then Format.print_string "reset_scope!\n";
      scopes := [new_scope ()]}

(* ---------------------------------------------------- *)
(* <Environment> *)
(* Each entry maps a Syntax variable to its encoding as a SMT2 term *)
(* free variables, depending on whether or not they are fully applied ...  *)
(* ... are mapped either to SMT2 functions, or to nullary tokens *)
type fvar_binding = {
    fvar_lid:  lident;
    univ_arity : int;
    smt_arity: int;
    smt_id:    string;
    smt_token: option term;
    smt_fuel_partial_app:option (term & term);
    fvb_thunked: bool;
    needs_fuel_and_universe_instantiations: option univ_names;
}

let list_of (i:int) (f:int -> 'a)
: list 'a
= let rec aux i out =
    if i = 0 then f i :: out
    else aux (i - 1) (f i :: out)
  in
  if i <= 0 then []
  else aux (i - 1) []

let kick_partial_app (fvb:fvar_binding) =
  match fvb.smt_token, fvb.needs_fuel_and_universe_instantiations with
  | None, _ -> None
  | _, Some _ -> None
  | Some ({tm=FreeV (FV(tok, _, _))}), _
  | Some ({tm=App(Var tok, _)}), _ ->
    if fvb.univ_arity = 0
    then (
      let t = mkApp(tok, []) in
      Some <| mk_Valid <| mk_ApplyTT (mkApp("__uu__PartialApp", [])) t
    )
    else (
      let vars =
        list_of
            (fvb.smt_arity + fvb.univ_arity)
            (fun i ->
                let sort = if i < fvb.univ_arity then univ_sort else Term_sort in
                mk_fv (("@u" ^ string_of_int i), sort))
      in
      let var_terms = List.map mkFreeV vars in
      let vapp = mkApp(fvb.smt_id, var_terms) in
      let univs, rest = List.splitAt fvb.univ_arity var_terms in
      let vtok_app = List.fold_left mk_ApplyTT (mkApp(tok, univs)) rest in
      Some <| mkForall Range.dummyRange ([[vapp]], vars, mkEq(vapp, vtok_app))
    )

let fvb_to_string fvb =
  let term_opt_to_string = function
    | None -> "None"
    | Some s -> Term.print_smt_term s
  in
  let term_pair_opt_to_string = function
    | None -> "None"
    | Some (s0, s1) -> show (s0, s1)
  in
  Format.fmt6 "{ lid = %s;\n  smt_arity = %s;\n  smt_id = %s;\n  smt_token = %s;\n  smt_fuel_partial_app = %s;\n  fvb_thunked = %s }"
    (show fvb.fvar_lid)
    (show fvb.smt_arity)
    fvb.smt_id
    (term_opt_to_string fvb.smt_token)
    (term_pair_opt_to_string fvb.smt_fuel_partial_app)
    (show fvb.fvb_thunked)

instance showable_fvar_binding : showable fvar_binding =
  {
    show = fvb_to_string
  }

let check_valid_fvb fvb =
    if (Some? fvb.smt_token
     || Some? fvb.smt_fuel_partial_app)
    && fvb.fvb_thunked
    then failwith (Format.fmt1 "Unexpected thunked SMT symbol: %s" (Ident.string_of_lid fvb.fvar_lid))
    else if fvb.fvb_thunked && fvb.smt_arity <> 0
    then failwith (Format.fmt1 "Unexpected arity of thunked SMT symbol: %s" (Ident.string_of_lid fvb.fvar_lid));
    match fvb.smt_token with
    | Some ({tm=FreeV _}) ->
      failwith (Format.fmt1 "bad fvb\n%s" (fvb_to_string fvb))
    | _ -> ()


let binder_of_eithervar v = (v, None)

type env_t = {
    bvar_bindings: PSMap.t (PIMap.t (bv & term));
    fvar_bindings: (PSMap.t fvar_binding & list fvar_binding);  //list of fvar bindings for the current module
                                                                   //remember them so that we can store them in the checked file
    depth:int; //length of local var/tvar bindings
    tcenv:Env.env;
    warn:bool;
    nolabels:bool;
    use_zfuel_name:bool;
    encode_non_total_function_typ:bool;
    current_module_name:string;
    encoding_quantifier:bool;
    global_cache:SMap.t (decls_elt & lident);  //cache for hashconsing, 2nd arg is the module name of the decl -- see Encode.fs where it is used and updated
}

let print_env (e:env_t) : string =
    let bvars = PSMap.fold e.bvar_bindings (fun _k pi acc ->
        PIMap.fold pi (fun _i (x, _term) acc ->
            show x :: acc) acc) [] in
    let allvars = PSMap.fold (e.fvar_bindings |> fst) (fun _k fvb acc ->
        fvb.fvar_lid :: acc) [] in
    let last_fvar =
      match List.rev allvars with
      | [] -> ""
      | l::_ -> "...," ^ show l
    in
    Format.fmt2 "{allvars=%s; bvars=%s }" (show allvars) (show bvars)

let lookup_bvar_binding env bv =
    match PSMap.try_find env.bvar_bindings (string_of_id bv.ppname) with
    | Some bvs -> PIMap.try_find bvs bv.index
    | None -> None

let lookup_fvar_binding env lid =
    PSMap.try_find (env.fvar_bindings |> fst) (string_of_lid lid)

let add_bvar_binding bvb bvbs =
  PSMap.modify bvbs (string_of_id (fst bvb).ppname)
    (fun pimap_opt ->
     PIMap.add (Option.dflt (PIMap.empty ()) pimap_opt) (fst bvb).index bvb)

let add_fvar_binding fvb (fvb_map, fvb_list) =
  (PSMap.add fvb_map (string_of_lid fvb.fvar_lid) fvb, fvb::fvb_list)

let fresh_fvar mname x s = let xsym = varops.fresh mname x in xsym, mkFreeV <| mk_fv (xsym, s)
(* generate terms corresponding to a variable and record the mapping in the environment *)

(* Bound term variables *)
let gen_term_var (env:env_t) (x:bv) =
    let ysym = "@x"^(show env.depth) in
    let y = mkFreeV <| mk_fv (ysym, Term_sort) in
    (* Note: the encoding of impure function arrows (among other places
    probably) relies on the fact that this is exactly a FreeV. See getfreeV in
    FStarC.SMTEncoding.EncodeTerm.fst *)
    ysym, y, {env with bvar_bindings=add_bvar_binding (x, y) env.bvar_bindings
                     ; tcenv = Env.push_bv env.tcenv x
                     ; depth = env.depth + 1 }

let new_term_constant (env:env_t) (x:bv) =
    let ysym = varops.new_var x.ppname x.index in
    let y = mkApp(ysym, []) in
    ysym, y, {env with bvar_bindings=add_bvar_binding (x, y) env.bvar_bindings
                     ; tcenv = Env.push_bv env.tcenv x}

let new_term_constant_from_string (env:env_t) (x:bv) str =
    let ysym = varops.mk_unique str in
    let y = mkApp(ysym, []) in
    ysym, y, {env with bvar_bindings=add_bvar_binding (x, y) env.bvar_bindings
                     ; tcenv = Env.push_bv env.tcenv x}

let push_term_var (env:env_t) (x:bv) (t:term) =
    {env with bvar_bindings=add_bvar_binding (x,t) env.bvar_bindings
            ; tcenv = Env.push_bv env.tcenv x}

let lookup_term_var env a =
    match lookup_bvar_binding env a with
    | Some (b,t) -> t
    | None ->
      failwith (Format.fmt2 "Bound term variable not found  %s in environment: %s"
                           (show a)
                           (print_env env))

(* Qualified term names *)
let mk_fvb lid fname arity univ_arity ftok fuel_partial_app thunked univs =
    let fvb = {
        fvar_lid  = lid;
        univ_arity;
        smt_arity = arity;
        smt_id    = fname;
        smt_token = ftok;
        smt_fuel_partial_app = fuel_partial_app;
        fvb_thunked = thunked;
        needs_fuel_and_universe_instantiations = univs;
        }
    in
    check_valid_fvb fvb;
    fvb
let new_term_constant_and_tok_from_lid_aux (env:env_t) (x:lident) arity  univ_arity thunked =
    let fname = varops.new_fvar x in
    let ftok_name, ftok =
        if thunked then None, None
        else let ftok_name = fname^"@tok" in
             let ftok = mkApp(ftok_name, []) in
             Some ftok_name, Some ftok
    in
    let fvb = mk_fvb x fname arity univ_arity ftok None thunked None in
//    Printf.printf "Pushing %A @ %A, %A\n" x fname ftok;
    fname, ftok_name, {env with fvar_bindings=add_fvar_binding fvb env.fvar_bindings}
let new_term_constant_and_tok_from_lid (env:env_t) (x:lident) arity univ_arity =
    let fname, ftok_name_opt, env = new_term_constant_and_tok_from_lid_aux env x arity univ_arity false in
    fname, Some?.v ftok_name_opt, env
let new_term_constant_and_tok_from_lid_maybe_thunked (env:env_t) (x:lident) arity th =
    new_term_constant_and_tok_from_lid_aux env x arity th
let fail_fvar_lookup env a =
  let q = Env.lookup_qname env.tcenv a in
  match q with
  | None ->
    failwith (Format.fmt1 "Name %s not found in the smtencoding and typechecker env" (show a))
  | _ ->
    let quals = Env.quals_of_qninfo q in
    if Some? quals &&
       (quals |> Some?.v |> List.contains Unfold_for_unification_and_vcgen)
    then Errors.raise_error a Errors.Fatal_IdentifierNotFound
           (Format.fmt1 "Name %s not found in the smtencoding env (the symbol is marked unfold, expected it to reduce)" (show a))
    else failwith (Format.fmt1 "Name %s not found in the smtencoding env" (show a))
let lookup_lid env a =
    match lookup_fvar_binding env a with
    | None -> fail_fvar_lookup env a
    | Some s -> check_valid_fvb s; s
let push_free_var_maybe_thunked_with_univs env (x:lident) arity univ_arity fname ftok thunked univs =
    let fvb = mk_fvb x fname arity univ_arity ftok None thunked univs in
    {env with fvar_bindings=add_fvar_binding fvb env.fvar_bindings}
let push_free_var_maybe_thunked env x arity univ_arity fname ftok fthunked =
    push_free_var_maybe_thunked_with_univs env x arity univ_arity fname ftok fthunked None
let push_free_var_tok_with_fuel_and_univs env (x:lident) arity univ_arity fname ftok univs =
    push_free_var_maybe_thunked_with_univs env x arity univ_arity fname ftok false (Some univs)
let push_free_var env (x:lident) arity univ_arity fname ftok =
    push_free_var_maybe_thunked env x arity univ_arity fname ftok false
let push_free_var_thunk env (x:lident) arity univ_arity fname ftok =
    push_free_var_maybe_thunked env x arity univ_arity fname ftok (arity=0)
let push_zfuel_name env (x:lident) f ftok =
    let fvb = lookup_lid env x in
    let t3 = mkApp(f, [mkApp("ZFuel", [])]) in
    let t3' = mk_ApplyTF (mkApp(ftok, [])) (mkApp("ZFuel", [])) in
    let fvb = mk_fvb x fvb.smt_id fvb.smt_arity fvb.univ_arity fvb.smt_token (Some (t3, t3')) false None in
    {env with fvar_bindings=add_fvar_binding fvb env.fvar_bindings}
let force_thunk fvb =
    if not (fvb.fvb_thunked) || fvb.smt_arity <> 0
    then failwith (Format.fmt1 "Forcing a non-thunk %s in the SMT encoding" (string_of_lid fvb.fvar_lid));
    mkFreeV <| FV (fvb.smt_id, Term_sort, true)
let try_lookup_free_var env l =
    match lookup_fvar_binding env l with
    | None -> None
    | Some fvb ->
      if !dbg_PartialApp
      then Format.print2 "Looked up %s found\n%s\n"
             (Ident.string_of_lid l)
             (fvb_to_string fvb);
      if fvb.fvb_thunked
      then Some (force_thunk fvb)
      else
      begin
      match fvb.smt_fuel_partial_app with
      | Some (_, f) when env.use_zfuel_name -> Some f
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
let lookup_free_var env (a : lident) =
    match try_lookup_free_var env a with
    | Some t -> t
    | None -> fail_fvar_lookup env a
let lookup_free_var_name env (a : lident) = lookup_lid env a
let lookup_free_var_sym env (a : lident) =
    let fvb = lookup_lid env a in
    match fvb.smt_fuel_partial_app with
    | Some({tm=App(g, zf)}, _)
        when env.use_zfuel_name ->
      Inl g, zf, fvb.smt_arity + 1
    | _ ->
        begin
        match fvb.smt_token with
        | None when fvb.fvb_thunked ->
            Inr (force_thunk fvb), [], fvb.smt_arity
        | None ->
            Inl (Var fvb.smt_id), [], fvb.smt_arity
        | Some sym ->
            begin
            match sym.tm with
            | App(g, [fuel]) ->
                Inl g, [fuel], fvb.smt_arity + 1
            | _ ->
                Inl (Var fvb.smt_id), [], fvb.smt_arity
            end
        end

let tok_of_name env nm =
  match
    PSMap.find_map (env.fvar_bindings |> fst) (fun _ fvb ->
      check_valid_fvb fvb;
      if fvb.smt_id = nm then fvb.smt_token else None)
  with
  | Some b -> Some b
  | None -> //this must be a bvar
    PSMap.find_map env.bvar_bindings (fun _ pi ->
    PIMap.fold pi (fun _ y res ->
      match res, y with
      | Some _, _ -> res
      | None, (_, {tm=App(Var sym, [])}) when sym=nm ->
        Some (snd y)
      | _ -> None) None)

let reset_current_module_fvbs env = { env with fvar_bindings = (env.fvar_bindings |> fst, []) }
let get_current_module_fvbs env = env.fvar_bindings |> snd
let add_fvar_binding_to_env fvb env =
  { env with fvar_bindings = add_fvar_binding fvb env.fvar_bindings }
