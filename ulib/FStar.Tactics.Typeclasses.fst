(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Tactics.Typeclasses

open FStar.Reflection.V2
module R = FStar.Reflection.V2
open FStar.Stubs.Tactics.Common
open FStar.Tactics.Effect
open FStar.Stubs.Tactics.V2.Builtins
open FStar.Stubs.Tactics.Types
open FStar.Tactics.V2.SyntaxHelpers
open FStar.Tactics.V2.Derived
open FStar.Tactics.V2.SyntaxCoercions
open FStar.Tactics.NamedView

module L = FStar.List.Tot.Base
let (@) = L.op_At

let tc_norm_steps = [primops; iota; delta_qualifier ["unfold"]]

irreducible let tcinstance : unit = ()
irreducible let tcclass : unit = ()
irreducible let tcmethod : unit = ()
irreducible let fundeps (_ : list int) : unit = ()
irreducible let noinst : unit = ()
irreducible let no_method : unit = ()

(* An entry in the global instance map. *)
noeq
type glb_inst = {
  inst_name : fv;
  noinst : bool;
}

noeq
type glb_entry = {
  class_name : fv;
  instances  : list glb_inst;
}

(* Would be nice to define an unembedding class here.. but it's circular. *)
let unembed_int (t:term) : Tac (option int) =
  match inspect_ln t with
  | R.Tv_Const (C_Int i) -> Some i
  | _ -> None

let rec unembed_list (#a:Type) (u : term -> Tac (option a)) (t:term) : Tac (option (list a)) =
  match hua t with
  | Some (fv, _, [(ty, Q_Implicit); (hd, Q_Explicit); (tl, Q_Explicit)]) ->
    if implode_qn (inspect_fv fv) = `%Prims.Cons then
      match u hd, unembed_list u tl with
      | Some hd, Some tl -> Some (hd::tl)
      | _ -> None
    else
      None
  | Some (fv, _, [(ty, Q_Implicit)]) ->
    if implode_qn (inspect_fv fv) = `%Prims.Nil then
      Some []
    else
      None
  | _ ->
    None

let extract_fundeps (se : sigelt) : Tac (option (list int)) =
  let attrs = sigelt_attrs se in
  let rec aux (attrs : list term) : Tac (option (list int)) =
    match attrs with
    | [] -> None
    | attr::attrs' ->
      match collect_app attr with
      | hd, [(a0, Q_Explicit)] ->
        if FStar.Reflection.TermEq.Simple.term_eq hd (`fundeps) then
          unembed_list unembed_int a0
        else
          aux attrs'
      | _ ->
        aux attrs'
    in
    aux attrs

let sigelt_name (se:sigelt) : Tac fv =
  match FStar.Stubs.Reflection.V2.Builtins.inspect_sigelt se with
  | Stubs.Reflection.V2.Data.Sg_Let _ lbs -> (
    match lbs with
    | [lb] -> (FStar.Stubs.Reflection.V2.Builtins.inspect_lb lb).lb_fv
    | _ -> fail "GGG1"
  )
  | Stubs.Reflection.V2.Data.Sg_Val nm _ _ -> pack_fv nm
  | _ -> fail "GGG2"

let rec head_of (t:term) : Tac (option fv) =
  (* NB: must use `inspect` to make use of unionfind graph.
  inspect_ln won't work. *)
  match inspect t with
  | Tv_FVar fv
  | Tv_UInst fv _ -> Some fv
  | Tv_App h _ -> head_of h
  | v ->
    None

let rec res_typ (t:term) : Tac term =
  match inspect t with
  | Tv_Arrow _ c -> (
    match inspect_comp c with
    | C_Total t -> res_typ t
    | _ -> t
  )
  | _ -> t

val fv_eq : fv -> fv -> Tot bool
let fv_eq fv1 fv2 =
  let n1 = inspect_fv fv1 in
  let n2 = inspect_fv fv2 in
  n1 = n2

let rec compact (xs : list glb_entry) : Tac (list glb_entry) =
  match xs with
  | [] -> []
  | x::xs ->
    let (same, rest) = L.partition (fun y -> fv_eq x.class_name y.class_name) xs in
    { class_name = x.class_name;
      instances  = x.instances @ (same |> L.concatMap (fun y -> y.instances));
    } :: compact rest

let is_class_name (f : fv) : Tac bool =
  let se = lookup_typ (cur_env ()) (inspect_fv f) in
  match se with
  | None -> false
  | Some se ->
    let attrs = sigelt_attrs se in
    L.existsb (Reflection.TermEq.Simple.term_eq (`tcclass)) attrs

let class_of_typ (t:term) : Tac (option fv) =
  match head_of (res_typ t) with
  | None -> None
  | Some fv ->
    if is_class_name fv then
      Some fv
    else
      (* If the head of the result type of this instance
      does not look like a class, try normalizing. It may
      be an alias to a class. *)
      let t' =
        try norm_term (hnf :: tc_norm_steps) t with | _ -> t
      in
      head_of (res_typ t')

let type_matches_class (cfv:fv) (t:term) : Tac bool =
  match class_of_typ t with
  | None -> false
  | Some fv -> fv_eq cfv fv

let build_glb_map (all_glb : list sigelt) : Tac (list glb_entry) =
  let sigelt_to_inst (se : sigelt) : Tac glb_inst =
    let inst_name = sigelt_name se in
    let attrs = sigelt_attrs se in
    let noinst = L.existsb (Reflection.TermEq.Simple.term_eq (`noinst)) attrs in
    { inst_name; noinst; }
  in
  all_glb |> Tactics.Util.concatMap (fun se ->
    let entry = sigelt_to_inst se in
    let typ =
      try
        Some <| tc (cur_env()) (pack (Tv_FVar entry.inst_name))
        // FIXME: a bit slow... but at least it's a simple fvar
      with | _ -> None
    in
    match typ with
    | None -> []
    | Some typ ->
      let attrs = sigelt_attrs se in
      match class_of_typ typ with
      | None -> []
      | Some cvf -> [ { class_name = cvf; instances = [entry]; } ]
  ) |> compact

noeq
type st_t = {
  seen           : list term;
  glb            : list glb_entry;
  fuel           : int;
  rng            : range;
  (* ^ The range of the original goal, for error reporting.
  Probably exposing ps.entry_range would be better. *)
  warned_oof     : tref bool;
  (* ^ Whether we have warned about out of fuel. *)
  dbg            : bool;
  (* ^ Whether debugging is enabled. *)
}

(* Thunked version of debug *)
let debug (st:st_t) (f : unit -> Tac string) : Tac unit =
  if st.dbg then
    print (f ())

noeq
type tc_goal = {
  g              : term;
  (* ^ The goal as a term *)
  head_fv        : fv;
  (* ^ Head fv of goal (g), i.e. the class name *)
  c_se           : option sigelt;
  (* ^ Class sigelt *)
  fundeps        : option (list int);
  (* ^ Functional dependendcies of class, if any. *)
  args_and_uvars : list (argv & bool);
  (* ^ The arguments of the goal, and whether they are
  unresolved, even partially. I.e. the boolean is true
  when the arg contains uvars. *)
}

(* Would be good to use different exceptions for each reason
the search stops, but it takes some work to properly account
for them and report proper errors. *)
exception Next

let skip #a (st:st_t) (s : string)
  : TacH a True (fun _ -> False)
  = if st.dbg then
      print ("skip: " ^ s);
    raise Next

let orskip #a (st:st_t) (s : string) (k : unit -> Tac a) : Tac a =
  try k () with
  | e -> skip st s

let ( >>> ) #a (t1 t2 : unit -> Tac a) () : Tac a =
  try t1 ()
  with | Next -> t2 ()
       | e -> raise e

let run #a (t : unit -> Tac a) : Tac a = t ()

private
let rec first (f : 'a -> Tac 'b) (l : list 'a) : Tac 'b =
    match l with
    | [] -> raise Next
    | x::xs ->
      run ((fun () -> f x) >>> (fun () -> first f xs))

private
let rec maybe_intros () : Tac unit =
  let g = cur_goal () in
  match inspect g with
  | Tv_Arrow _ _ ->
    ignore (intro ());
    maybe_intros ()
  | _ -> ()

let trywith (st:st_t) (g:tc_goal) (t : term) (noinst : bool) (k : st_t -> Tac unit) : Tac unit =
  (* debug st (fun () -> "trying " ^ term_to_string t); *)
  (* debug st (fun () -> "of type: " ^ term_to_string typ); *)
  (* print ("head_fv = " ^ fv_to_string g.head_fv); *)
  // print ("fundeps = " ^ Util.string_of_option (Util.string_of_list (fun i -> string_of_int i)) fundeps);
  // print ("unresolved_args = " ^ Util.string_of_list (fun i -> string_of_int i) unresolved_args);

  let unresolved_args = g.args_and_uvars |> Util.mapi (fun i (_, b) -> if b then [i <: int] else []) |> List.Tot.flatten in
  debug st (fun () -> "Trying to apply hypothesis/instance: " ^ term_to_string t);
  (fun () ->
    if noinst then (
      (* If this instance has the noinst attribute, force using apply_noinst.
        This means we will not let this instance instantiate the goal, regardless
        of any fundeps on the class. *)
      orskip st "apply_noinst" (fun () -> apply_noinst t)
    ) else if Cons? unresolved_args then (
      (* If some args have uvars, we check to see if they are
        functional dependencies of the class. If so, we apply
        the instance and instantiate the uvars. Otherwise skip. *)
      if None? g.fundeps then
        skip st "Will not continue as there are unresolved args (and no fundeps)";

      let Some fundeps = g.fundeps in
      debug st (fun () -> "checking fundeps");
      if unresolved_args |> L.existsb (fun i -> not (List.Tot.mem i fundeps)) then
        skip st "fundeps: a non-fundep is unresolved";

      (* Gor for it, with the full apply. *)
      orskip st "apply" (fun () -> apply t)
    ) else (
      orskip st "apply_noinst" (fun () -> apply_noinst t)
    )
  ) `seq` (fun () ->
    debug st (fun () -> dump "next"; "apply of " ^ term_to_string t ^ " seems to have worked");
    let st = { st with fuel = st.fuel - 1 } in
    k st)

let local (st:st_t) (g:tc_goal) (k : st_t -> Tac unit) () : Tac unit =
    debug st (fun () -> "local, goal = " ^ term_to_string g.g);
    let bs = vars_of_env (cur_env ()) in
    bs |> first fun (b:binding) ->
       if type_matches_class g.head_fv b.sort then
         trywith st g (pack (Tv_Var b)) false k
       else
         skip st "head mismatch"

let global (st:st_t) (g:tc_goal) (k : st_t -> Tac unit) () : Tac unit =
    debug st (fun () -> "global, goal = " ^ term_to_string g.g);
    (* Find the set of instances for this class and try them. There can only
    be one. Would be nice to use a map here to avoid the lookup. *)
    let rec go (l : list glb_entry) : Tac unit =
      match l with
      | [] -> skip st "no more global instances"
      | { class_name ; instances } :: rest ->
        if type_matches_class g.head_fv (pack (Tv_FVar class_name)) then
          instances |> first fun i -> trywith st g (pack (Tv_FVar i.inst_name)) i.noinst k
        else
          go rest
    in
    go st.glb

let rec unrefine t : Tac term =
  match t with
  | Tv_Refine b t -> unrefine b.sort
  | Tv_AscribedT e _ _ _ -> unrefine e
  | Tv_AscribedC e _ _ _ -> unrefine e
  | _ -> t

let try_trivial (g:term) (k : st_t -> Tac unit) () : Tac unit =
  match hua (unrefine g) with
  | Some (fv, u, a)-> (
    if implode_qn (inspect_fv fv) = `%unit then
      exact (`())
    else if implode_qn (inspect_fv fv) = `%squash then
      smt ()
    else raise Next
  )
  | _ -> raise Next

(* returns true iff it did anything *)
let rec tac_unrefine () : Tac bool =
  let g = cur_goal () in
  (* the named view is uncomfortable here, since we need to use the subst_t type. *)
  match inspect_ln g with
  | R.Tv_Refine b ref ->
    let t = (inspect_binder b).sort in
    (* goal for the actual term *)
    let uv = fresh_uvar (Some t) in

    exact_with_ref uv;

    (* Make the term uvar the new goal *)
    unshelve uv;
    (* Keep on unrefining, maybe *)
    ignore (tac_unrefine ());
    true

  | _ -> false

let try_unrefining (st:st_t) (k : st_t -> Tac unit) () : Tac unit =
  if tac_unrefine () then
    k st
  else
    raise Next

let try_instances (st:st_t) (k : st_t -> Tac unit) () : Tac unit =
  let g = cur_goal () in
  match hua g with
  | None ->
    debug st (fun () -> "Goal does not look like a typeclass: " ^ term_to_string g);
    raise Next

  | Some (head_fv, us, args) ->
    (* ^ Maybe should check is this really is a class too? *)
    let c_se = lookup_typ (cur_env ()) (inspect_fv head_fv) in
    let fundeps = match c_se with
      | None -> None
      | Some se -> extract_fundeps se
    in

    let args_and_uvars = args |> Util.map (fun (a, q) -> (a, q), Cons? (free_uvars a)) in
    let st = { st with seen = g :: st.seen } in
    let g = { g; head_fv; c_se; fundeps; args_and_uvars } in
    run <| (
      local st g k >>>
      global st g k
    )

(*
  tcresolve': the main typeclass instantiation function.

  It mostly creates a tc_goal record and calls the functions above.
*)
let rec tcresolve' (st:st_t) : Tac unit =
    if st.fuel <= 0 then (
      let r = st.warned_oof in
      if not (read r) then (
        let open FStar.Stubs.Errors.Msg in
        log_issues [FStar.Issue.mk_issue_doc "Warning" [
          text "Warning: fuel exhausted during typeclass resolution.";
          text "This usually indicates a loop in your instances.";
        ] (Some st.rng) None []];
        write r true
      );
      raise Next
    );
    debug st (fun () -> "fuel = " ^ string_of_int st.fuel);

    norm tc_norm_steps;
    maybe_intros();
    let g = cur_goal () in

    (* Try to detect loops *)
    if L.existsb (Reflection.TermEq.Simple.term_eq g) st.seen then (
      debug st (fun () -> "loop");
      raise Next
    );

    run <| (
      try_trivial g tcresolve' >>>
      try_instances st tcresolve' >>>
      try_unrefining st tcresolve')

[@@plugin]
let __tcresolve (dbg : bool) : Tac unit =
    let open FStar.Pprint in
    if dbg then (
       dump "tcresolve entry point"
    );
    let w = cur_witness () in
    set_dump_on_failure false; (* We report our own errors *)

    // Not using intros () directly, since that unfolds aggressively if the term is not a literal arrow
    maybe_intros ();

    // Fetch a list of all instances in scope right now.
    // TODO: turn this into a hash map per class, ideally one that can be
    // persisted across calls.
    let all_glb = lookup_attr_ses (`tcinstance) (cur_env ()) in
    let glb = build_glb_map all_glb in
    let st0 = {
      seen = [];
      glb = glb;
      fuel = 16;
      rng = range_of_term (cur_goal ());
      warned_oof = alloc false;
      dbg = dbg;
    } in
    try
      tcresolve' st0;
      debug st0 (fun () -> "Solved to:\n\t" ^ term_to_string w)
    with
    | Next ->
      let open FStar.Pprint in
      fail_doc [
        prefix 2 1 (text "Could not solve typeclass constraint")
          (bquotes (term_to_doc (cur_goal ())));
      ]
    | TacticFailure (msg,r) ->
      fail_doc_at ([text "Typeclass resolution failed."] @ msg) r
    | e -> raise e

[@@plugin] let tcresolve       () : Tac unit = __tcresolve (debugging ())
[@@plugin] let tcresolve_debug () : Tac unit = __tcresolve true

(**** Generating methods from a class ****)

(* In TAC, not Tot *)
private
let rec mk_abs (bs : list binder) (body : term) : Tac term (decreases bs) =
    match bs with
    | [] -> body
    | b::bs -> pack (Tv_Abs b (mk_abs bs body))

private
let rec last (l : list 'a) : Tac 'a =
  match l with
  | [] -> fail "last: empty list"
  | [x] -> x
  | _::xs -> last xs

private
let filter_no_method_binders (bs:binders)
  : Tac binders
  = let open FStar.Reflection.TermEq.Simple in
    let has_no_method_attr (b:binder) : bool =
      L.existsb (term_eq (`no_method)) b.attrs
    in
    bs |> Tactics.Util.filter (fun b ->
      let nm = unseal b.ppname in
      assume (String.length nm > 0); (* should be provided by F*? *)
      if FStar.String.index nm 0 = '_' then false
      else not (has_no_method_attr b))

private
let binder_set_meta (b : binder) (t : term) : binder =
  { b with qual = Q_Meta t }

let debug' (f : unit -> Tac string) : Tac unit =
  if debugging () then
    print (f ())
    
#push-options "--z3rlimit_factor 2"
[@@plugin]
let mk_class (nm:string) : Tac decls =
    let ns = explode_qn nm in
    let r = lookup_typ (top_env ()) ns in
    guard (Some? r);
    let Some se = r in
    let to_propagate = L.filter (function Inline_for_extraction | NoExtract -> true | _ -> false) (sigelt_quals se) in
    let sv = inspect_sigelt se in
    guard (Sg_Inductive? sv);
    let Sg_Inductive {nm=name;univs=us;params;typ=ity;ctors} = sv in
    debug' (fun () -> "params = " ^ Tactics.Util.string_of_list binder_to_string params);
    debug' (fun () -> "got it, name = " ^ implode_qn name);
    debug' (fun () -> "got it, ity = " ^ term_to_string ity);
    let ctor_name = last name in
    // Must have a single constructor
    guard (L.length ctors = 1);
    let [(c_name, ty)] = ctors in
    debug' (fun () -> "got ctor " ^ implode_qn c_name ^ " of type " ^ term_to_string ty);
    let bs, cod = collect_arr_bs ty in
    let r = inspect_comp cod in
    guard (C_Total? r);
    let C_Total cod = r in (* must be total *)

    debug' (fun () -> "params = " ^ Tactics.Util.string_of_list binder_to_string params);
    debug' (fun () -> "n_params = " ^ string_of_int (List.Tot.Base.length params));
    debug' (fun () -> "n_univs = " ^ string_of_int (List.Tot.Base.length us));
    debug' (fun () -> "cod = " ^ term_to_string cod);

    (* print ("n_bs = " ^ string_of_int (List.Tot.Base.length bs)); *)

    let base : string = "__proj__Mk" ^ ctor_name ^ "__item__" in

    (* Make a sigelt for each method *)
    filter_no_method_binders bs
    |> Tactics.Util.map (fun (b:binder) ->
      let s = name_of_binder b in
      debug' (fun () -> "processing method " ^ s);
      let ns = cur_module () in
      let sfv = pack_fv (ns @ [s]) in
      let dbv = fresh_namedv_named "d" in
      let tcr = (`tcresolve) in
      let tcdict = {
        ppname = seal "dict";
        sort   = cod;
        uniq   = fresh();
        qual   = Q_Meta tcr;
        attrs  = [];
      } in
      let proj_name = cur_module () @ [base ^ s] in
      let proj = pack (Tv_FVar (pack_fv proj_name)) in

      let proj_se =
        match lookup_typ (top_env ()) proj_name with
        | None -> fail "mk_class: proj not found?"
        | Some se -> se
      in
      let proj_attrs = sigelt_attrs proj_se in
      let proj_lb =
        match inspect_sigelt proj_se with
        | Sg_Let {lbs} ->
          lookup_lb lbs proj_name
        | _ -> fail "mk_class: proj not Sg_Let?"
      in
      debug' (fun () -> "proj_ty = " ^ term_to_string proj_lb.lb_typ);

      let ty =
        let bs, cod = collect_arr_bs proj_lb.lb_typ in
        let ps, bs = List.Tot.Base.splitAt (List.Tot.Base.length params) bs in
        match bs with
        | [] -> fail "mk_class: impossible, no binders"
        | b1::bs' ->
            let b1 = binder_set_meta b1 tcr in
            mk_arr (ps@(b1::bs')) cod
      in
      let def =
        let bs, body = collect_abs proj_lb.lb_def in
        let ps, bs = List.Tot.Base.splitAt (List.Tot.Base.length params) bs in
        match bs with
        | [] -> fail "mk_class: impossible, no binders"
        | b1::bs' ->
            let b1 = binder_set_meta b1 tcr in
            mk_abs (ps@(b1::bs')) body
      in
      debug' (fun () -> "def = " ^ term_to_string def);
      debug' (fun () -> "ty  = " ^ term_to_string ty);

      let ty : term = ty in
      let def : term = def in
      let sfv : fv = sfv in

      let lb = { lb_fv=sfv; lb_us=proj_lb.lb_us; lb_typ=ty; lb_def=def } in
      let se = pack_sigelt (Sg_Let {isrec=false; lbs=[lb]}) in
      let se = set_sigelt_quals to_propagate se in
      let se = set_sigelt_attrs ((`tcmethod) :: proj_attrs @ b.attrs) se in
      //debug' (fun () -> "trying to return : " ^ term_to_string (quote se));
      se
    )
#pop-options