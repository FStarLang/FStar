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
open FStar.Tactics.V2.SyntaxHelpers
open FStar.Tactics.V2.Derived
open FStar.Tactics.V2.SyntaxCoercions
open FStar.Tactics.NamedView

(* Thunked version of debug *)
let debug (f : unit -> Tac string) : Tac unit =
  if debugging () then
    print (f ())

module L = FStar.List.Tot.Base
let (@) = L.op_At

(* The attribute that marks classes *)
irreducible
let tcclass : unit = ()

(* The attribute that marks instances *)
irreducible
let tcinstance : unit = ()

(* Functional dependencies of a class. *)
irreducible
let fundeps (_ : list int) : unit = ()

(* The attribute that marks class fields
   to signal that no method should be generated for them *)
irreducible
let no_method : unit = ()

noeq
type st_t = {
  seen : list term;
  glb : list (sigelt & fv);
  fuel : int;
}

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


val fv_eq : fv -> fv -> Tot bool
let fv_eq fv1 fv2 =
  let n1 = inspect_fv fv1 in
  let n2 = inspect_fv fv2 in
  n1 = n2

let rec head_of (t:term) : Tac (option fv) =
  (* NB: must use `inspect` to make use of unionfind graph.
  inspect_ln won't work. *)
  match inspect t with
  | Tv_FVar fv
  | Tv_UInst fv _ -> Some fv
  | Tv_App h _ -> head_of h
  | v -> None

let rec res_typ (t:term) : Tac term =
  match inspect t with
  | Tv_Arrow _ c -> (
    match inspect_comp c with
    | C_Total t -> res_typ t
    | _ -> t
  )
  | _ -> t

(* Would be good to use different exceptions for each reason
the search stops, but it takes some work to properly account
for them and report proper errors. *)
exception NoInst

private
let rec first (f : 'a -> Tac 'b) (l : list 'a) : Tac 'b =
    match l with
    | [] -> raise NoInst
    | x::xs -> (fun () -> f x) `or_else` (fun () -> first f xs)

private
let rec maybe_intros () : Tac unit =
  let g = cur_goal () in
  match inspect g with
  | Tv_Arrow _ _ ->
    ignore (intro ());
    maybe_intros ()
  | _ -> ()

let sigelt_name (se:sigelt) : list fv =
  match FStar.Stubs.Reflection.V2.Builtins.inspect_sigelt se with
  | Stubs.Reflection.V2.Data.Sg_Let _ lbs -> (
    match lbs with
    | [lb] -> [(FStar.Stubs.Reflection.V2.Builtins.inspect_lb lb).lb_fv]
    | _ -> []
  )
  | Stubs.Reflection.V2.Data.Sg_Val nm _ _ -> [pack_fv nm]
  | _ -> []

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
        if FStar.Reflection.TermEq.Simple.term_eq hd (`fundeps) then (
          unembed_list unembed_int a0
        ) else
          aux attrs'
      | _ ->
        aux attrs'
    in
    aux attrs

let trywith (st:st_t) (g:tc_goal) (t typ : term) (k : st_t -> Tac unit) : Tac unit =
    // print ("head_fv = " ^ fv_to_string g.head_fv);
    // print ("fundeps = " ^ Util.string_of_option (Util.string_of_list (fun i -> string_of_int i)) fundeps);
    let unresolved_args = g.args_and_uvars |> Util.mapi (fun i (_, b) -> if b then [i <: int] else []) |> List.Tot.flatten in
    // print ("unresolved_args = " ^ Util.string_of_list (fun i -> string_of_int i) unresolved_args);

    match head_of (res_typ typ) with
    | None ->
      debug (fun () -> "no head for typ of this? " ^ term_to_string t ^ "    typ=" ^ term_to_string typ);
      raise NoInst
    | Some fv' ->
      if not (fv_eq fv' g.head_fv) then
        raise NoInst; // class mismatch, would be better to not even get here
      debug (fun () -> "Trying to apply hypothesis/instance: " ^ term_to_string t);
      (fun () ->
        if Cons? unresolved_args && None? g.fundeps then
          fail "Will not continue as there are unresolved args (and no fundeps)"
        else if Cons? unresolved_args && Some? g.fundeps then (
          let Some fundeps = g.fundeps in
          debug (fun () -> "checking fundeps");
          let all_good = List.Tot.for_all (fun i -> List.Tot.mem i fundeps) unresolved_args in
          if all_good then apply t else fail "fundeps"
        ) else (
          apply_noinst t
        )
      ) `seq` (fun () ->
        debug (fun () -> dump "next"; "apply seems to have worked");
        let st = { st with fuel = st.fuel - 1 } in
        k st)

let local (st:st_t) (g:tc_goal) (k : st_t -> Tac unit) () : Tac unit =
    debug (fun () -> "local, goal = " ^ term_to_string g.g);
    let bs = vars_of_env (cur_env ()) in
    first (fun (b:binding) ->
              trywith st g (pack (Tv_Var b)) b.sort k)
          bs

let global (st:st_t) (g:tc_goal) (k : st_t -> Tac unit) () : Tac unit =
    debug (fun () -> "global, goal = " ^ term_to_string g.g);
    first (fun (se, fv) ->
              let typ = tc (cur_env()) (pack (Tv_FVar fv)) in // FIXME: a bit slow.. but at least it's a simple fvar
              trywith st g (pack (Tv_FVar fv)) typ k)
          st.glb

exception Next
let try_trivial (st:st_t) (g:tc_goal) (k : st_t -> Tac unit) () : Tac unit =
  match g.g with
  | Tv_FVar fv ->
    if implode_qn (inspect_fv fv) = `%unit
    then exact (`())
    else raise Next
  | _ -> raise Next

let ( <|> ) (t1 t2  : unit -> Tac 'a) : unit -> Tac 'a =
  fun () ->
    try t1 () with _ -> t2 ()

(*
  tcresolve': the main typeclass instantiation function.

  It mostly creates a tc_goal record and calls the functions above.
*)
let rec tcresolve' (st:st_t) : Tac unit =
    if st.fuel <= 0 then
      raise NoInst;
    debug (fun () -> "fuel = " ^ string_of_int st.fuel);

    maybe_intros();
    let g = cur_goal () in

    (* Try to detect loops *)
    if L.existsb (Reflection.TermEq.Simple.term_eq g) st.seen then (
      debug (fun () -> "loop");
      raise NoInst
    );

    match hua g with
    | None ->
      debug (fun () -> "Goal does not look like a typeclass");
      raise NoInst

    | Some (head_fv, us, args) ->
      (* ^ Maybe should check is this really is a class too? *)
      let c_se = lookup_typ (cur_env ()) (inspect_fv head_fv) in
      let fundeps = match c_se with
        | None -> None
        | Some se -> extract_fundeps se
      in

      let args_and_uvars = args |> Util.map (fun (a, q) -> (a, q), Cons? (free_uvars a )) in
      let st = { st with seen = g :: st.seen } in
      let g = { g; head_fv; c_se; fundeps; args_and_uvars } in
      (try_trivial st g tcresolve' <|>
       local st g tcresolve' <|>
       global st g tcresolve') ()

[@@plugin]
let tcresolve () : Tac unit =
    let open FStar.Stubs.Pprint in
    debug (fun () -> dump ""; "tcresolve entry point");
    norm [];
    let w = cur_witness () in
    set_dump_on_failure false; (* We report our own errors *)

    // Not using intros () directly, since that unfolds aggressively if the term is not a literal arrow
    maybe_intros ();

    // Fetch a list of all instances in scope right now.
    // TODO: turn this into a hash map per class, ideally one that can be
    // persisted across calss.
    let glb = lookup_attr_ses (`tcinstance) (cur_env ()) in
    let glb = glb |> Tactics.Util.concatMap (fun se ->
              sigelt_name se |> Tactics.Util.concatMap (fun fv -> [(se, fv)])
    )
    in
    let st0 = {
      seen = [];
      glb = glb;
      fuel = 16;
    } in
    try
      tcresolve' st0;
      debug (fun () -> "Solved to:\n\t" ^ term_to_string w)
    with
    | NoInst ->
      let open FStar.Stubs.Pprint in
      fail_doc [
        prefix 2 1 (text "Could not solve typeclass constraint")
          (bquotes (term_to_doc (cur_goal ())));
      ]
    | TacticFailure (msg,r) ->
      fail_doc_at ([text "Typeclass resolution failed."] @ msg) r
    | e -> raise e

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
  : binders
  = let open FStar.Reflection.TermEq.Simple in
    let has_no_method_attr (b:binder) : bool =
      L.existsb (term_eq (`no_method)) b.attrs
    in
    bs |> L.filter (fun b -> not (has_no_method_attr b))

private
let binder_set_meta (b : binder) (t : term) : binder =
  { b with qual = Q_Meta t }

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
    debug (fun () -> "params = " ^ Tactics.Util.string_of_list binder_to_string params);
    debug (fun () -> "got it, name = " ^ implode_qn name);
    debug (fun () -> "got it, ity = " ^ term_to_string ity);
    let ctor_name = last name in
    // Must have a single constructor
    guard (L.length ctors = 1);
    let [(c_name, ty)] = ctors in
    debug (fun () -> "got ctor " ^ implode_qn c_name ^ " of type " ^ term_to_string ty);
    let bs, cod = collect_arr_bs ty in
    let r = inspect_comp cod in
    guard (C_Total? r);
    let C_Total cod = r in (* must be total *)

    debug (fun () -> "params = " ^ Tactics.Util.string_of_list binder_to_string params);
    debug (fun () -> "n_params = " ^ string_of_int (List.Tot.Base.length params));
    debug (fun () -> "n_univs = " ^ string_of_int (List.Tot.Base.length us));
    debug (fun () -> "cod = " ^ term_to_string cod);

    (* print ("n_bs = " ^ string_of_int (List.Tot.Base.length bs)); *)

    let base : string = "__proj__Mk" ^ ctor_name ^ "__item__" in

    (* Make a sigelt for each method *)
    filter_no_method_binders bs
    |> Tactics.Util.map (fun (b:binder) ->
      let s = name_of_binder b in
      debug (fun () -> "processing method " ^ s);
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

      let proj_lb =
        match lookup_typ (top_env ()) proj_name with
        | None -> fail "mk_class: proj not found?"
        | Some se ->
          match inspect_sigelt se with
          | Sg_Let {lbs} -> lookup_lb lbs proj_name
          | _ -> fail "mk_class: proj not Sg_Let?"
      in
      debug (fun () -> "proj_ty = " ^ term_to_string proj_lb.lb_typ);

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
      debug (fun () -> "def = " ^ term_to_string def);
      debug (fun () -> "ty  = " ^ term_to_string ty);

      let ty : term = ty in
      let def : term = def in
      let sfv : fv = sfv in

      let lb = { lb_fv=sfv; lb_us=proj_lb.lb_us; lb_typ=ty; lb_def=def } in
      let se = pack_sigelt (Sg_Let {isrec=false; lbs=[lb]}) in
      let se = set_sigelt_quals to_propagate se in
      let se = set_sigelt_attrs b.attrs se in
      //debug (fun () -> "trying to return : " ^ term_to_string (quote se));
      se
    )
