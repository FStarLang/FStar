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

module FStar.TypeChecker.Env

open FStar
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Syntax.Util
open FStar.Util
open FStar.Ident
open FStar.Range
open FStar.TypeChecker.Common

type binding =
  | Binding_var      of bv
  | Binding_lid      of lident * tscheme
  | Binding_sig      of list<lident> * sigelt
  | Binding_univ     of univ_name
  | Binding_sig_inst of list<lident> * sigelt * universes //the first component should always be a Sig_inductive

type delta_level =
  | NoDelta
  | Inlining
  | Eager_unfolding_only
  | Unfold of delta_depth

type mlift = typ -> typ -> typ

type edge = {
  msource :lident;
  mtarget :lident;
  mlift   :typ -> typ -> typ;
}
type effects = {
  decls :list<eff_decl>;
  order :list<edge>;                                       (* transitive closure of the order in the signature *)
  joins :list<(lident * lident * lident * mlift * mlift)>; (* least upper bounds *)
}
type cached_elt = either<(universes * typ), (sigelt * option<universes>)>
type env = {
  solver         :solver_t;                     (* interface to the SMT solver *)
  range          :Range.range;                  (* the source location of the term being checked *)
  curmodule      :lident;                       (* Name of this module *)
  gamma          :list<binding>;                (* Local typing environment and signature elements *)
  gamma_cache    :Util.smap<cached_elt>;        (* Memo table for the local environment *)
  modules        :list<modul>;                  (* already fully type checked modules *)
  expected_typ   :option<typ>;                  (* type expected by the context *)
  sigtab         :Util.smap<sigelt>;            (* a dictionary of long-names to sigelts *)
  is_pattern     :bool;                         (* is the current term being checked a pattern? *)
  instantiate_imp:bool;                         (* instantiate implicit arguments? default=true *)
  effects        :effects;                      (* monad lattice *)
  generalize     :bool;                         (* should we generalize let bindings? *)
  letrecs        :list<(lbname * typ)>;         (* mutually recursive names and their types (for termination checking) *)
  top_level      :bool;                         (* is this a top-level term? if so, then discharge guards *)
  check_uvars    :bool;                         (* paranoid: re-typecheck unification variables *)
  use_eq         :bool;                         (* generate an equality constraint, rather than subtyping/subkinding *)
  is_iface       :bool;                         (* is the module we're currently checking an interface? *)
  admit          :bool;                         (* admit VCs in the current module *)
  lax            :bool;                         (* don't even generate VCs *)
  lax_universes  :bool;                         (* don't check universe constraints *)
  type_of        :env -> term -> term*typ*guard_t;   (* a callback to the type-checker; g |- e : Tot t *)
  universe_of    :env -> term -> universe;           (* a callback to the type-checker; g |- e : Tot (Type u) *)
  use_bv_sorts   :bool;                              (* use bv.sort for a bound-variable's type rather than consulting gamma *)
  qname_and_index:option<(lident*int)>;              (* the top-level term we're currently processing and the nth query for it *)
}
and solver_t = {
    init         :env -> unit;
    push         :string -> unit;
    pop          :string -> unit;
    mark         :string -> unit;
    reset_mark   :string -> unit;
    commit_mark  :string -> unit;
    encode_modul :env -> modul -> unit;
    encode_sig   :env -> sigelt -> unit;
    solve        :option<(unit -> string)> -> env -> typ -> unit;
    is_trivial   :env -> typ -> bool;
    finish       :unit -> unit;
    refresh      :unit -> unit;
}
and guard_t = {
  guard_f:    guard_formula;
  deferred:   deferred;
  univ_ineqs: list<univ_ineq>;
  implicits:  list<(string * env * uvar * term * typ * Range.range)>;
}
type env_t = env
type implicits = list<(env * uvar * term * typ * Range.range)>

type sigtable = Util.smap<sigelt>

// VALS_HACK_HERE

let should_verify env =
    not env.lax
    && not env.admit
    && Options.should_verify env.curmodule.str

let visible_at d q = match d, q with
  | NoDelta,    _
  | Eager_unfolding_only, Unfold_for_unification_and_vcgen
  | Unfold _,   Unfold_for_unification_and_vcgen
  | Unfold _,   Visible_default -> true
  | Inlining, Inline_for_extraction -> true
  | _ -> false

let default_table_size = 200
let new_sigtab () = Util.smap_create default_table_size
let new_gamma_cache () = Util.smap_create 100

let initial_env type_of universe_of solver module_lid =
  { solver=solver;
    range=dummyRange;
    curmodule=module_lid;
    gamma= [];
    gamma_cache=new_gamma_cache();
    modules= [];
    expected_typ=None;
    sigtab=new_sigtab();
    is_pattern=false;
    instantiate_imp=true;
    effects={decls=[]; order=[]; joins=[]};
    generalize=true;
    letrecs=[];
    top_level=false;
    check_uvars=false;
    use_eq=false;
    is_iface=false;
    admit=false;
    lax=false;
    lax_universes=false;
    type_of=type_of;
    universe_of=universe_of;
    use_bv_sorts=false;
    qname_and_index=None
  }

(* Marking and resetting the environment, for the interactive mode *)
let sigtab env = env.sigtab
let gamma_cache env = env.gamma_cache
type env_stack_ops = {
    es_push: env -> env;
    es_mark: env -> env;
    es_reset_mark: env -> env;
    es_commit_mark: env -> env;
    es_pop:env -> env;
    es_incr_query_index:env -> env
}

let stack_ops =
    let query_indices = Util.mk_ref [[]] in
    let push_query_indices () = match !query_indices with
        | [] -> failwith "Empty query indices!"
        | _ -> query_indices := (List.hd !query_indices)::!query_indices
    in
    let pop_query_indices () = match !query_indices with
        | [] -> failwith "Empty query indices!"
        | hd::tl -> query_indices := tl
    in
    let add_query_index (l, n) = match !query_indices with
        | hd::tl -> query_indices := ((l,n)::hd)::tl
        | _ -> failwith "Empty query indices"
    in
    let peek_query_indices () = List.hd !query_indices in
    let commit_query_index_mark () = match !query_indices with
        | hd::_::tl -> query_indices := hd::tl
        | _ -> failwith "Unmarked query index stack"
    in
    let stack = Util.mk_ref [] in
    let push_stack env =
        stack := env::!stack;
        {env with sigtab=Util.smap_copy (sigtab env);
                  gamma_cache=Util.smap_copy (gamma_cache env)}
    in
    let pop_stack env =
        match !stack with
        | env::tl ->
          stack := tl;
          env
        | _ -> failwith "Impossible: Too many pops"
    in
    let push env =
        push_query_indices();
        push_stack env
    in
    let pop env =
        pop_query_indices();
        pop_stack env
    in
    let mark env =
        push_query_indices();
        push_stack env
    in
    let commit_mark env =
        commit_query_index_mark();
        ignore (pop_stack env);
        env
    in
    let reset_mark env =
        pop_query_indices();
        pop_stack env
    in
    let incr_query_index env =
        let qix = peek_query_indices () in
        match env.qname_and_index with
        | None -> env
        | Some (l, n) ->
        match qix |> List.tryFind (fun (m, _) -> Ident.lid_equals l m) with
        | None ->
            let next = n + 1 in
            add_query_index (l, next);
            {env with qname_and_index=Some (l, next)}
        | Some (_, m) ->
            let next = m + 1 in
            add_query_index (l, next);
            {env with qname_and_index=Some (l, next)}
    in
    { es_push=push;
      es_pop=pop;
      es_mark=push;
      es_reset_mark=pop;
      es_commit_mark=commit_mark;
      es_incr_query_index=incr_query_index }



let push env msg =
    env.solver.push msg;
    stack_ops.es_push env
let mark env =
    env.solver.mark "USER MARK";
    stack_ops.es_mark env
let commit_mark env =
    env.solver.commit_mark "USER MARK";
    stack_ops.es_commit_mark env
let reset_mark env =
    env.solver.reset_mark "USER MARK";
    stack_ops.es_reset_mark env
let pop env msg =
    env.solver.pop msg;
    stack_ops.es_pop env
let incr_query_index env =
    stack_ops.es_incr_query_index env
////////////////////////////////////////////////////////////
// Checking the per-module debug level and position info  //
////////////////////////////////////////////////////////////
let debug env (l:Options.debug_level_t) =
    Options.debug_at_level env.curmodule.str l
let set_range e r = if r=dummyRange then e else {e with range=r}
let get_range e = e.range

////////////////////////////////////////////////////////////
// Private utilities                                      //
////////////////////////////////////////////////////////////
let modules env = env.modules
let current_module env = env.curmodule
let set_current_module env lid = {env with curmodule=lid}
let has_interface env l = env.modules |> Util.for_some (fun m -> m.is_interface && lid_equals m.name l)
let find_in_sigtab env lid = Util.smap_try_find (sigtab env) (text_of_lid lid)

let name_not_found (l:lid) =
  format1 "Name \"%s\" not found" l.str

let variable_not_found v =
  format1 "Variable \"%s\" not found" (Print.bv_to_string v)

//Construct a new universe unification variable
let new_u_univ () = U_unif (Unionfind.fresh None)

//Instantiate the universe variables in a type scheme with provided universes
let inst_tscheme_with : tscheme -> universes -> universes * term = fun ts us ->
    match ts, us with
    | ([], t), [] -> [], t
    | (formals, t), _ ->
      assert (List.length us = List.length formals);
      let n = List.length formals - 1 in
      let vs = us |> List.mapi (fun i u -> UN (n - i, u)) in
      us, Subst.subst vs t

//Instantiate the universe variables in a type scheme with new unification variables
let inst_tscheme : tscheme -> universes * term = function
    | [], t -> [], t
    | us, t ->
      let us' = us |> List.map (fun _ -> new_u_univ()) in
      inst_tscheme_with (us, t) us'

let inst_tscheme_with_range (r:range) (t:tscheme) =
    let us, t = inst_tscheme t in 
    us, Subst.set_use_range r t

let inst_effect_fun_with (insts:universes) (env:env) (ed:eff_decl) (us, t)  =
    match ed.binders with
        | [] ->
          let univs = ed.univs@us in
          if List.length insts <> List.length univs
          then failwith (Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                            (string_of_int <| List.length univs) (string_of_int <| List.length insts)
                            (Print.lid_to_string ed.mname) (Print.term_to_string t));
          snd (inst_tscheme_with (ed.univs@us, t) insts)
        | _  -> failwith (Util.format1 "Unexpected use of an uninstantiated effect: %s\n" (Print.lid_to_string ed.mname))

type tri =
    | Yes
    | No
    | Maybe

let in_cur_mod env (l:lident) : tri = (* TODO: need a more efficient namespace check! *)
    let cur = current_module env in
    if l.nsstr = cur.str then Yes (* fast case; works for everything except records *)
    else if Util.starts_with l.nsstr cur.str
    then let lns = l.ns@[l.ident] in
         let cur = cur.ns@[cur.ident] in
         let rec aux c l = match c, l with
            | [], _ -> Maybe
            | _, [] -> No
            | hd::tl, hd'::tl' when (hd.idText=hd'.idText) -> aux tl tl'
            | _ -> No in
         aux cur lns
    else No

let lookup_qname env (lid:lident) : option<either<(universes * typ), (sigelt * option<universes>)>>  =
  let cur_mod = in_cur_mod env lid in
  let cache t = Util.smap_add (gamma_cache env) lid.str t; Some t in
  let found = if cur_mod<>No
              then match Util.smap_try_find (gamma_cache env) lid.str with
                    | None ->
                      Util.find_map env.gamma (function
                        | Binding_lid(l,t) -> if lid_equals lid l then Some (Inl (inst_tscheme t)) else None
                        | Binding_sig (_, Sig_bundle(ses, _, _, _)) ->
                            Util.find_map ses (fun se ->
                                if lids_of_sigelt se |> Util.for_some (lid_equals lid)
                                then cache (Inr (se, None))
                                else None)
                        | Binding_sig (lids, s) ->
                          let maybe_cache t = match s with
                            | Sig_declare_typ _ -> Some t
                            | _ -> cache t in
                          if lids |> Util.for_some (lid_equals lid) then maybe_cache (Inr (s, None)) else None
                        | Binding_sig_inst (lids, s, us) ->
                          if lids |> Util.for_some (lid_equals lid) then Some (Inr (s, Some us)) else None
                        | _ -> None)
                    | se -> se
               else None in
  if is_some found
  then found
  else if cur_mod <> Yes || has_interface env env.curmodule
  then match find_in_sigtab env lid with
        | Some se -> Some (Inr (se, None))
        | None -> None
  else None

let rec add_sigelt env se = match se with
    | Sig_bundle(ses, _, _, _) -> add_sigelts env ses
    | _ ->
    let lids = lids_of_sigelt se in
    List.iter (fun l -> Util.smap_add (sigtab env) l.str se) lids;
    match se with
    | Sig_new_effect(ne, _) ->
      ne.actions |> List.iter (fun a ->
          let se_let = Util.action_as_lb a in
          Util.smap_add (sigtab env) a.action_name.str se_let)
    | _ -> ()

and add_sigelts env ses =
    ses |> List.iter (add_sigelt env)

////////////////////////////////////////////////////////////
// Lookup up various kinds of identifiers                 //
////////////////////////////////////////////////////////////
let try_lookup_bv env (bv:bv) =
  Util.find_map env.gamma (function
    | Binding_var id when bv_eq id bv ->
      Some id.sort
    | _ -> None)

let lookup_type_of_let se lid = match se with 
    | Sig_let((_, [lb]), _, _, _) -> 
      Some (inst_tscheme (lb.lbunivs, lb.lbtyp))

    | Sig_let((_, lbs), _, _, _) ->
        Util.find_map lbs (fun lb -> match lb.lbname with
          | Inl _ -> failwith "impossible"
          | Inr fv ->
            if fv_eq_lid fv lid
            then Some (inst_tscheme (lb.lbunivs, lb.lbtyp))
            else None)

    | _ -> None

let effect_signature se = 
    match se with
    | Sig_new_effect(ne, _) ->
        Some (inst_tscheme (ne.univs, Util.arrow ne.binders (mk_Total ne.signature)))

    | Sig_effect_abbrev (lid, us, binders, _, _, _, _) ->
        Some (inst_tscheme (us, Util.arrow binders (mk_Total teff)))

    | _ -> None

let try_lookup_lid_aux env lid =
  let mapper = function
    | Inl t ->
      Some t

    | Inr (Sig_datacon(_, uvs, t, _, _, _, _, _), None) ->
      Some (inst_tscheme (uvs, t))

    | Inr (Sig_declare_typ (l, uvs, t, qs, _), None) ->
      if in_cur_mod env l = Yes
      then if qs |> List.contains Assumption || env.is_iface
           then Some (inst_tscheme (uvs, t))
           else None
      else Some (inst_tscheme (uvs, t))

    | Inr (Sig_inductive_typ (lid, uvs, tps, k, _, _, _, _), None) ->
      begin match tps with
        | [] -> Some <| inst_tscheme (uvs, k)
        | _ ->  Some <| inst_tscheme (uvs, Util.flat_arrow tps (mk_Total k))
      end

    | Inr (Sig_inductive_typ (lid, uvs, tps, k, _, _, _, _), Some us) ->
      begin match tps with
        | [] -> Some <| inst_tscheme_with (uvs, k) us
        | _ ->  Some <| inst_tscheme_with (uvs, Util.flat_arrow tps (mk_Total k)) us
      end

    | Inr se ->
      begin match se with
        | Sig_let _, None ->
          lookup_type_of_let (fst se) lid
        | _ -> effect_signature (fst se)
      end
  in
    match Util.bind_opt (lookup_qname env lid) mapper with
      | Some (us, t) -> Some (us, {t with pos=range_of_lid lid})
      | None -> None

////////////////////////////////////////////////////////////////
//External interaface for querying identifiers
//Provides, in order from the interface env.fsi:
//        val lid_exists             : env -> lident -> bool
//        val lookup_bv              : env -> bv -> typ
//        val try_lookup_lid         : env -> lident -> option<(universes * typ)>
//        val lookup_lid             : env -> lident -> (universes * typ)
//        val lookup_univ            : env -> univ_name -> bool
//        val try_lookup_val_decl    : env -> lident -> option<(tscheme * list<qualifier>)>
//        val lookup_val_decl        : env -> lident -> (universes * typ)
//        val lookup_datacon         : env -> lident -> universes * typ
//        val datacons_of_typ        : env -> lident -> list<lident>
//        val typ_of_datacon         : env -> lident -> lident
//        val lookup_definition      : delta_level -> env -> lident -> option<(univ_names * term)>
//        val try_lookup_effect_lid  : env -> lident -> option<term>
//        val lookup_effect_lid      : env -> lident -> term
//        val lookup_effect_abbrev   : env -> universes -> lident -> option<(binders * comp)>
//        val norm_eff_name          : (env -> lident -> lident)
//        val lookup_effect_quals    : env -> lident -> list<qualifier>
//        val lookup_projector       : env -> lident -> int -> lident
//        val current_module         : env -> lident
//        val is_projector           : env -> lident -> bool
//        val is_datacon             : env -> lident -> bool
//        val is_record              : env -> lident -> bool
//        val is_interpreted         : (env -> term -> bool)
//        val is_type_constructor    : env -> lident -> bool
//Each of these functions that returns a term ensures to update
//the range information on the term with the currrent use-site
////////////////////////////////////////////////////////////////

let lid_exists env l = 
    match lookup_qname env l with 
    | None -> false
    | Some _ -> true

let lookup_bv env bv = 
    match try_lookup_bv env bv with 
    | None -> raise (Error(variable_not_found bv, range_of_bv bv))
    | Some t -> Subst.set_use_range (range_of_bv bv) t

let try_lookup_lid env l = 
    match try_lookup_lid_aux env l with 
    | None -> None
    | Some (us, t) -> 
      Some (us, Subst.set_use_range (range_of_lid l) t)

let lookup_lid env l =  
    match try_lookup_lid env l with 
    | None -> raise (Error(name_not_found l, range_of_lid l))
    | Some (us, t) -> (us, t)

let lookup_univ env x = 
    List.find (function
        | Binding_univ y -> x.idText=y.idText
//      | Binding_var({sort=t}) -> Util.set_mem x (Free.univnames t)
        | _ -> false) env.gamma
    |> Option.isSome

let try_lookup_val_decl env lid =
  //QUESTION: Why does this not inst_tscheme?
  match lookup_qname env lid with
    | Some (Inr (Sig_declare_typ(_, uvs, t, q, _), None)) ->
      Some ((uvs, Subst.set_use_range (range_of_lid lid) t),q)
    | _ -> None

let lookup_val_decl env lid =
  match lookup_qname env lid with
    | Some (Inr (Sig_declare_typ(_, uvs, t, _, _), None)) ->
      inst_tscheme_with_range (range_of_lid lid) (uvs, t)
    | _ -> raise (Error(name_not_found lid, range_of_lid lid))

let lookup_datacon env lid =
  match lookup_qname env lid with
    | Some (Inr (Sig_datacon (_, uvs, t, _, _, _, _, _), None)) -> 
      inst_tscheme_with_range (range_of_lid lid) (uvs, t) 
    | _ -> raise (Error(name_not_found lid, range_of_lid lid))

let datacons_of_typ env lid = 
  match lookup_qname env lid with
    | Some (Inr(Sig_inductive_typ(_, _, _, _, _, dcs, _, _), _)) -> dcs
    | _ -> []

let typ_of_datacon env lid = 
  match lookup_qname env lid with
    | Some (Inr (Sig_datacon (_, _, _, l, _, _, _, _), _)) -> l
    | _ -> failwith (Util.format1 "Not a datacon: %s" (Print.lid_to_string lid))

let lookup_definition delta_levels env lid =
  let visible quals =
      delta_levels |> Util.for_some (fun dl ->
      quals |> Util.for_some (visible_at dl))
  in
  match lookup_qname env lid with
    | Some (Inr (se, None)) ->
      begin match se with
        | Sig_let((_, lbs), _, _, quals) when visible quals ->
            Util.find_map lbs (fun lb ->
                let fv = right lb.lbname in
                if fv_eq_lid fv lid 
                then Some (lb.lbunivs, Subst.set_use_range (range_of_lid lid) (Util.unascribe lb.lbdef))
                else None)
        | _ -> None
      end
    | _ -> None

let try_lookup_effect_lid env (ftv:lident) : option<typ> =
  match lookup_qname env ftv with
    | Some (Inr (se, None)) -> 
      begin match effect_signature se with 
        | None -> None
        | Some (_, t) -> Some (Subst.set_use_range (range_of_lid ftv) t)
      end
    | _ -> None

let lookup_effect_lid env (ftv:lident) : typ =
  match try_lookup_effect_lid env ftv with
    | None -> raise (Error(name_not_found ftv, range_of_lid ftv))
    | Some k -> k

let lookup_effect_abbrev env (univ_insts:universes) lid0 =
  match lookup_qname env lid0 with
    | Some (Inr (Sig_effect_abbrev (lid, univs, binders, c, quals, _, _), None)) ->
      let lid = Ident.set_lid_range lid (Range.set_use_range (Ident.range_of_lid lid) (Ident.range_of_lid lid0)) in
      if quals |> Util.for_some (function Irreducible -> true | _ -> false)
      then None
      else let insts = if List.length univ_insts = List.length univs
                       then univ_insts
                       else if Ident.lid_equals lid Const.effect_Lemma_lid
                            && List.length univ_insts = 1 //TODO: Lemma is a hack! It is more universe polymorphic than expected,
                                                          //because of the SMTPats ... which should be irrelevant, but unfortunately are not
                       then univ_insts@[U_zero]
                       else failwith (Util.format2 "Unexpected instantiation of effect %s with %s universes"
                                            (Print.lid_to_string lid)
                                            (List.length univ_insts |> Util.string_of_int)) in
           begin match binders, univs with
             | [], _ -> failwith "Unexpected effect abbreviation with no arguments"
             | _, _::_::_ when not (Ident.lid_equals lid Const.effect_Lemma_lid) ->
                failwith (Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes"
                           (Print.lid_to_string lid) (string_of_int <| List.length univs))
             | _ -> let _, t = inst_tscheme_with (univs, Util.arrow binders c) insts in 
                    let t = Subst.set_use_range (range_of_lid lid) t in
                    begin match (Subst.compress t).n with 
                        | Tm_arrow(binders, c) -> 
                          Some (binders, c)
                        | _ -> failwith "Impossible"
                    end
          end
    | _ -> None

let norm_eff_name =
   let cache = Util.smap_create 20 in
   fun env (l:lident) ->
       let rec find l =
           match lookup_effect_abbrev env [U_unknown] l with //universe doesn't matter here; we're just normalizing the name
            | None -> None
            | Some (_, c) ->
                let l = Util.comp_effect_name c in
                match find l with
                    | None -> Some l
                    | Some l' -> Some l' in
       let res = match Util.smap_try_find cache l.str with
            | Some l -> l
            | None ->
              begin match find l with
                        | None -> l
                        | Some m -> Util.smap_add cache l.str m;
                                    m
              end in
       Ident.set_lid_range res (range_of_lid l)

let lookup_effect_quals env l =
    let l = norm_eff_name env l in
    match lookup_qname env l with
    | Some (Inr (Sig_new_effect(ne, _), _)) ->
      ne.qualifiers
    | _ -> []

let lookup_projector env lid i =
    let fail () = failwith (Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" (Util.string_of_int i) (Print.lid_to_string lid)) in
    let _, t = lookup_datacon env lid in
    match (compress t).n with
        | Tm_arrow(binders, _) ->
          if ((i < 0) || i >= List.length binders) //this has to be within bounds!
          then fail ()
          else let b = List.nth binders i in
               Util.mk_field_projector_name lid (fst b) i |> fst
        | _ -> fail ()

let is_projector env (l:lident) : bool =
    match lookup_qname env l with
        | Some (Inr (Sig_declare_typ(_, _, _, quals, _), _)) ->
          Util.for_some (function Projector _ -> true | _ -> false) quals
        | _ -> false

let is_datacon env lid =
  match lookup_qname env lid with
    | Some (Inr (Sig_datacon (_, _, _, _, _, _, _, _), _)) -> true
    | _ -> false

let is_record env lid =
  match lookup_qname env lid with
    | Some (Inr (Sig_inductive_typ(_, _, _, _, _, _, tags, _), _)) ->
        Util.for_some (function RecordType _ | RecordConstructor _ -> true | _ -> false) tags
    | _ -> false

let is_interpreted = 
    let interpreted_symbols = 
       [Const.op_Eq; 
        Const.op_notEq;
        Const.op_LT;   
        Const.op_LTE;  
        Const.op_GT;   
        Const.op_GTE;  
        Const.op_Subtraction; 
        Const.op_Minus;       
        Const.op_Addition;    
        Const.op_Multiply;    
        Const.op_Division;    
        Const.op_Modulus;     
        Const.op_And;         
        Const.op_Or;          
        Const.op_Negation] in
    fun (env:env) head -> 
        match (Util.un_uinst head).n with 
        | Tm_fvar fv -> 
            fv.fv_delta=Delta_equational
            //Util.for_some (Ident.lid_equals fv.fv_name.v) interpreted_symbols
        | _ -> false

let is_type_constructor env lid = 
    let mapper = function
        | Inl _ -> Some false
        | Inr (se, _) -> 
           begin match se with 
            | Sig_declare_typ (_, _, _, qs, _) -> 
              Some (List.contains New qs)
            | Sig_inductive_typ _ ->
              Some true
            | _ -> Some false
           end in
    match Util.bind_opt (lookup_qname env lid) mapper with
      | Some b -> b
      | None -> false

////////////////////////////////////////////////////////////
// Operations on the monad lattice                        //
////////////////////////////////////////////////////////////
let effect_decl_opt env l =
  env.effects.decls |> Util.find_opt (fun d -> lid_equals d.mname l)

let get_effect_decl env l =
  match effect_decl_opt env l with
    | None -> raise (Error(name_not_found l, range_of_lid l))
    | Some md -> md

let join env l1 l2 : (lident * (typ -> typ -> typ) * (typ -> typ -> typ)) =
  if lid_equals l1 l2
  then l1, (fun t wp -> wp), (fun t wp -> wp)
  else if lid_equals l1 Const.effect_GTot_lid && lid_equals l2 Const.effect_Tot_lid
       || lid_equals l2 Const.effect_GTot_lid && lid_equals l1 Const.effect_Tot_lid
  then Const.effect_GTot_lid, (fun t wp -> wp), (fun t wp -> wp)
  else match env.effects.joins |> Util.find_opt (fun (m1, m2, _, _, _) -> lid_equals l1 m1 && lid_equals l2 m2) with
        | None -> raise (Error(Util.format2 "Effects %s and %s cannot be composed" (Print.lid_to_string l1) (Print.lid_to_string l2), env.range))
        | Some (_, _, m3, j1, j2) -> m3, j1, j2

let monad_leq env l1 l2 : option<edge> =
  if lid_equals l1 l2
  || (lid_equals l1 Const.effect_Tot_lid && lid_equals l2 Const.effect_GTot_lid)
  then Some ({msource=l1; mtarget=l2; mlift=(fun t wp -> wp)})
  else env.effects.order |> Util.find_opt (fun e -> lid_equals l1 e.msource && lid_equals l2 e.mtarget)

let wp_sig_aux decls m =
  match decls |> Util.find_opt (fun d -> lid_equals d.mname m) with
  | None -> failwith (Util.format1 "Impossible: declaration for monad %s not found" m.str)
  | Some md ->
    let _, s = inst_tscheme (md.univs, md.signature) in
    let s = Subst.compress s in
    match md.binders, s.n with
      | [], Tm_arrow([(a, _); (wp, _)], c) when (is_teff (comp_result c)) -> a, wp.sort
      | _ -> failwith "Impossible"

let wp_signature env m = wp_sig_aux env.effects.decls m

let build_lattice env se = match se with
  | Sig_new_effect(ne, _) ->
    let effects = {env.effects with decls=ne::env.effects.decls} in
    {env with effects=effects}

  | Sig_sub_effect(sub, _) ->
    let compose_edges e1 e2 : edge =
       {msource=e1.msource;
        mtarget=e2.mtarget;
        mlift=(fun r wp1 -> e2.mlift r (e1.mlift r wp1))} in

    let mk_lift lift_t r wp1 =
        let _, lift_t = inst_tscheme lift_t in
        mk (Tm_app(lift_t, [as_arg r; as_arg wp1])) None wp1.pos in

    let sub_lift_wp = match sub.lift_wp with
      | Some sub_lift_wp ->
          sub_lift_wp
      | None ->
          failwith "sub effect should've been elaborated at this stage"
    in

    let edge =
      {msource=sub.source;
       mtarget=sub.target;
       mlift=mk_lift sub_lift_wp} in
    let id_edge l = {
       msource=sub.source;
       mtarget=sub.target;
       mlift=(fun t wp -> wp)
    } in
    let print_mlift l =
        let arg = lid_as_fv (lid_of_path ["ARG"] dummyRange) Delta_constant None in
        let wp = lid_as_fv (lid_of_path  ["WP"]  dummyRange) Delta_constant None in //A couple of bogus constants, just for printing
        Print.term_to_string (l arg wp) in
    let order = edge::env.effects.order in

    let ms = env.effects.decls |> List.map (fun (e:eff_decl) -> e.mname) in

    let find_edge order (i, j) =
      if lid_equals i j
      then id_edge i |> Some
      else order |> Util.find_opt (fun e -> lid_equals e.msource i && lid_equals e.mtarget j) in

    (* basically, this is Warshall's algorithm for transitive closure,
       except it's ineffcient because find_edge is doing a linear scan.
       and it's not incremental.
       Could be made better. But these are really small graphs (~ 4-8 vertices) ... so not worth it *)
    let order =
        ms |> List.fold_left (fun order k ->
        order@(ms |> List.collect (fun i ->
               if lid_equals i k then []
               else ms |> List.collect (fun j ->
                    if lid_equals j k
                    then []
                    else match find_edge order (i, k), find_edge order (k, j) with
                            | Some e1, Some e2 -> [compose_edges e1 e2]
                            | _ -> []))))
        order in
    let order = Util.remove_dups (fun e1 e2 -> lid_equals e1.msource e2.msource
                                            && lid_equals e1.mtarget e2.mtarget) order in
    let _ = order |> List.iter (fun edge ->
        if Ident.lid_equals edge.msource Const.effect_DIV_lid
        && lookup_effect_quals env edge.mtarget |> List.contains TotalEffect
        then raise (Error(Util.format1 "Divergent computations cannot be included in an effect %s marked 'total'" edge.mtarget.str,
                          get_range env))) in
    let joins =
        ms |> List.collect (fun i ->
        ms |> List.collect (fun j ->
        let join_opt = ms |> List.fold_left (fun bopt k ->
          match find_edge order (i, k), find_edge order (j, k) with
            | Some ik, Some jk ->
              begin match bopt with
                | None -> Some (k, ik, jk) //we don't have a current candidate as the upper bound; so we may as well use k

                | Some (ub, _, _) ->
                  if Util.is_some (find_edge order (k, ub))
                  && not (Util.is_some (find_edge order (ub, k)))
                  then Some (k, ik, jk) //k is less than ub
                  else bopt
              end
            | _ -> bopt) None in
        match join_opt with
            | None -> []
            | Some (k, e1, e2) -> [(i, j, k, e1.mlift, e2.mlift)])) in

    let effects = {env.effects with order=order; joins=joins} in
//    order |> List.iter (fun o -> Printf.printf "%s <: %s\n\t%s\n" o.msource.str o.mtarget.str (print_mlift o.mlift));
//    joins |> List.iter (fun (e1, e2, e3, l1, l2) -> if lid_equals e1 e2 then () else Printf.printf "%s join %s = %s\n\t%s\n\t%s\n" e1.str e2.str e3.str (print_mlift l1) (print_mlift l2));
    {env with effects=effects}

  | _ -> env

////////////////////////////////////////////////////////////
// Introducing identifiers and updating the environment   //
////////////////////////////////////////////////////////////

// The environment maintains the invariant that gamma is of the form:
//   l_1 ... l_n val_1 ... val_n
// where l_i is a local binding and val_i is a top-level binding.
//
// This function assumes that, in the case that the environment contains local
// bindings _and_ we push a top-level binding, then the top-level binding does
// not capture any of the local bindings (duh).
let push_in_gamma env s =
  let rec push x rest =
    match rest with
    | Binding_sig _ :: _
    | Binding_sig_inst _ :: _ ->
        x :: rest
    | [] ->
        [ x ]
    | local :: rest ->
        local :: push x rest
  in
  { env with gamma = push s env.gamma }

let push_sigelt env s =
  let env = push_in_gamma env (Binding_sig(lids_of_sigelt s, s)) in
  build_lattice env s

let push_sigelt_inst env s us =
  let env = push_in_gamma env (Binding_sig_inst(lids_of_sigelt s,s,us)) in
  build_lattice env s

let push_local_binding env b = {env with gamma=b::env.gamma}

let push_bv env x = push_local_binding env (Binding_var x)

let push_binders env (bs:binders) =
    List.fold_left (fun env (x, _) -> push_bv env x) env bs

let binding_of_lb (x:lbname) t = match x with
  | Inl x ->
    assert (fst t = []);
    let x = {x with sort=snd t} in
    Binding_var x
  | Inr fv ->
    Binding_lid(fv.fv_name.v, t)

let push_let_binding env lb ts =
    push_local_binding env (binding_of_lb lb ts)
let push_module env (m:modul) =
    add_sigelts env m.exports;
    {env with
      modules=m::env.modules;
      gamma=[];
      expected_typ=None}

let push_univ_vars (env:env_t) (xs:univ_names) : env_t =
    List.fold_left (fun env x -> push_local_binding env (Binding_univ x)) env xs

let set_expected_typ env t =
  {env with expected_typ = Some t; use_eq=false}

let expected_typ env = match env.expected_typ with
  | None -> None
  | Some t -> Some t

let clear_expected_typ env =
    {env with expected_typ=None; use_eq=false}, expected_typ env

let finish_module =
    let empty_lid = lid_of_ids [id_of_text ""] in
    fun env m ->
      let sigs =
        if lid_equals m.name Const.prims_lid
        then env.gamma |> List.collect (function
                | Binding_sig (_, se) -> [se]
                | _ -> []) |> List.rev
        else m.exports  in
      add_sigelts env sigs;
      {env with
        curmodule=empty_lid;
        gamma=[];
        modules=m::env.modules}

////////////////////////////////////////////////////////////
// Collections from the environment                       //
////////////////////////////////////////////////////////////
let uvars_in_env env =
  let no_uvs = new_uv_set () in
  let ext out uvs = Util.set_union out uvs in
  let rec aux out g = match g with
    | [] -> out
    | Binding_univ _ :: tl -> aux out tl
    | Binding_lid(_, (_, t))::tl
    | Binding_var({sort=t})::tl -> aux (ext out (Free.uvars t)) tl
    | Binding_sig _::_
    | Binding_sig_inst _::_ -> out in (* this marks a top-level scope ... no more uvars beyond this *)
  aux no_uvs env.gamma

let univ_vars env =
    let no_univs = Syntax.no_universe_uvars in
    let ext out uvs = Util.set_union out uvs in
    let rec aux out g = match g with
      | [] -> out
      | Binding_sig_inst _::tl
      | Binding_univ _ :: tl -> aux out tl
      | Binding_lid(_, (_, t))::tl
      | Binding_var({sort=t})::tl -> aux (ext out (Free.univs t)) tl
      | Binding_sig _::_ -> out in (* this marks a top-level scope ...  no more uvars beyond this *)
    aux no_univs env.gamma

let univnames env =
    let no_univ_names = Syntax.no_universe_names in
    let ext out uvs = Util.set_union out uvs in
    let rec aux out g = match g with
        | [] -> out
        | Binding_sig_inst _::tl -> aux out tl
        | Binding_univ uname :: tl -> aux (Util.set_add uname out) tl
        | Binding_lid(_, (_, t))::tl
        | Binding_var({sort=t})::tl -> aux (ext out (Free.univnames t)) tl
        | Binding_sig _::_ -> out in (* this marks a top-level scope ...  no more universe names beyond this *)
    aux no_univ_names env.gamma

let bound_vars_of_bindings bs =
  bs |> List.collect (function
        | Binding_var x -> [x]
        | Binding_lid _
        | Binding_sig _
        | Binding_univ _
        | Binding_sig_inst _ -> [])

let binders_of_bindings bs = bound_vars_of_bindings bs |> List.map Syntax.mk_binder |> List.rev

let bound_vars env = bound_vars_of_bindings env.gamma

let all_binders env = binders_of_bindings env.gamma

let fold_env env f a = List.fold_right (fun e a -> f a e) env.gamma a

let lidents env : list<lident> =
  let keys = List.fold_left (fun keys -> function
    | Binding_sig(lids, _) -> lids@keys
    | _ -> keys) [] env.gamma in
  Util.smap_fold (sigtab env) (fun _ v keys -> Util.lids_of_sigelt v@keys) keys


(* <Move> this out of here *)
let dummy_solver = {
    init=(fun _ -> ());
    push=(fun _ -> ());
    pop=(fun _ -> ());
    mark=(fun _ -> ());
    reset_mark=(fun _ -> ());
    commit_mark=(fun _ -> ());
    encode_sig=(fun _ _ -> ());
    encode_modul=(fun _ _ -> ());
    solve=(fun _ _ _ -> ());
    is_trivial=(fun _ _ -> false);
    finish=(fun () -> ());
    refresh=(fun () -> ());
}
(* </Move> *)
