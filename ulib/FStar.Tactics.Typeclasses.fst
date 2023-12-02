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

(* The attribute that marks class fields
   to signal that no method should be generated for them *)
irreducible
let no_method : unit = ()

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

(*
 tcresolve': the main typeclass instantiation function.

 seen : a list of goals we've seen already in this path of the search,
        used to prevent loops
 glb : a list of all global instances in scope, for all classes
 fuel : amount of steps we allow in this path, we stop if we reach zero
 head_fv : the head of the goal we're trying to solve, i.e. the class name

 TODO: some form of memoization
*)
private
let rec tcresolve' (seen : list term) (glb : list fv) (fuel : int) : Tac unit =
    if fuel <= 0 then
      raise NoInst;
    debug (fun () -> "fuel = " ^ string_of_int fuel);

    let g = cur_goal () in

    (* Try to detect loops *)
    if L.existsb (Reflection.V2.TermEq.term_eq g) seen then (
      debug (fun () -> "loop");
      raise NoInst
    );

    match head_of g with
    | None ->
      debug (fun () -> "goal does not look like a typeclass");
      raise NoInst

    | Some head_fv ->
      (* ^ Maybe should check is this really is a class too? *)
      let seen = g :: seen in
      local head_fv seen glb fuel
       `or_else`
      global head_fv seen glb fuel

and local (head_fv : fv) (seen : list term) (glb : list fv) (fuel : int) () : Tac unit =
    let bs = vars_of_env (cur_env ()) in
    first (fun (b:binding) ->
              trywith head_fv seen glb fuel (pack (Tv_Var b)) b.sort)
          bs

and global (head_fv : fv) (seen : list term) (glb : list fv) (fuel : int) () : Tac unit =
    first (fun fv ->
              let typ = tc (cur_env()) (pack (Tv_FVar fv)) in // FIXME: a bit slow.. but at least it's a simple fvar
              trywith head_fv seen glb fuel (pack (Tv_FVar fv)) typ)
          glb

and trywith (head_fv : fv) (seen:list term) (glb : list fv) (fuel:int) (t typ : term) : Tac unit =
    debug (fun () -> "trywith " ^ term_to_string t);
    match head_of (res_typ typ) with
    | None ->
      debug (fun () -> "no head for typ of this? " ^ term_to_string t ^ "    typ=" ^ term_to_string typ);
      raise NoInst
    | Some fv' ->
      if fv_eq fv' head_fv
      then (
        debug (fun () -> "Trying to apply hypothesis/instance: " ^ term_to_string t);
        (fun () -> apply_noinst t) `seq` (fun () ->
          debug (fun () -> dump "next"; "apply seems to have worked");
          tcresolve' seen glb (fuel-1))
      ) else (
        debug (fun () -> "different class: " ^ fv_to_string fv' ^ " <> " ^ fv_to_string head_fv);
        raise NoInst
      )

private
let rec maybe_intros () : Tac unit =
  let g = cur_goal () in
  match inspect g with
  | Tv_Arrow _ _ ->
    ignore (intro ());
    maybe_intros ()
  | _ -> ()

[@@plugin]
let tcresolve () : Tac unit =
    debug (fun () -> dump ""; "tcresolve entry point");
    // We sometimes get goal type as _ -> t
    // So intro if that's the case
    // Not using intros () directly, since that unfolds aggressively if the term is not an arrow
    // TODO: Should we..?  Why wouldn't the head always be an FV?
    maybe_intros ();

    // Fetch a list of all instances in scope right now.
    // TODO: turn this into a hash map per class, ideally one that can be
    // stored.
    let glb = lookup_attr (`tcinstance) (cur_env ()) in
    try
      tcresolve' [] glb 16
    with
    | NoInst ->
      fail ("Could not solve constraint " ^ term_to_string (cur_goal ()))
    | TacticFailure s ->
      fail ("Typeclass resolution failed: " ^ s)
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
  = let has_no_method_attr (b:binder)
      : bool
      = let attrs = b.attrs in
        let is_no_method (t:term)
          : bool
          = match inspect_ln t with
            | Reflection.V2.Tv_FVar fv  ->
              let n = flatten_name (inspect_fv fv) in
              n = `%no_method
            | _ -> false
        in
        L.existsb is_no_method attrs
    in
    L.filter (fun b -> not (has_no_method_attr b)) bs

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
    (* print ("params = " ^ Tactics.Util.string_of_list binder_to_string params); *)
    (* print ("got it, name = " ^ implode_qn name); *)
    (* print ("got it, ity = " ^ term_to_string ity); *)
    let ctor_name = last name in
    // Must have a single constructor
    guard (L.length ctors = 1);
    let [(c_name, ty)] = ctors in
    (* print ("got ctor " ^ implode_qn c_name ^ " of type " ^ term_to_string ty); *)
    let bs, cod = collect_arr_bs ty in
    let r = inspect_comp cod in
    guard (C_Total? r);
    let C_Total cod = r in (* must be total *)

    (* print ("params = " ^ Tactics.Util.string_of_list binder_to_string params); *)
    (* print ("n_params = " ^ string_of_int (List.Tot.Base.length params)); *)
    (* print ("n_univs = " ^ string_of_int (List.Tot.Base.length us)); *)
    (* print ("cod = " ^ term_to_string cod); *)

    (* print ("n_bs = " ^ string_of_int (List.Tot.Base.length bs)); *)

    let base : string = "__proj__Mk" ^ ctor_name ^ "__item__" in

    (* Make a sigelt for each method *)
    Tactics.Util.map (fun (b:binder) ->
                  let s = name_of_binder b in
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
                  (* print ("proj_ty = " ^ term_to_string proj_lb.lb_typ); *)

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
                  (* print ("def = " ^ term_to_string def); *)
                  (* print ("ty  = " ^ term_to_string ty); *)

                  let ty : term = ty in
                  let def : term = def in
                  let sfv : fv = sfv in

                  let lb = { lb_fv=sfv; lb_us=proj_lb.lb_us; lb_typ=ty; lb_def=def } in
                  let se = pack_sigelt (Sg_Let {isrec=false; lbs=[lb]}) in
                  let se = set_sigelt_quals to_propagate se in
                  let se = set_sigelt_attrs b.attrs se in
                  (* print ("trying to return : " ^ term_to_string (quote se)); *)
                  se
    ) (filter_no_method_binders bs)
