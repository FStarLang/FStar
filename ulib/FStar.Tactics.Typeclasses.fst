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

irreducible let tcinstance : unit = ()
irreducible let tcclass : unit = ()
irreducible let tcmethod : unit = ()
irreducible let fundeps (_ : list int) : unit = ()
irreducible let no_method : unit = ()

(* Typeclass resolution is implemented natively, see
   FStarC.TypeChecker.TcResolve. *)
[@@plugin] let tcresolve       () : Tac unit = tcresolve_native ()
[@@plugin] let tcresolve_debug () : Tac unit = tcresolve_native ()

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
let binder_set_tcarg (b : binder) : binder =
  { b with qual = Q_TcArg }

let debug' (f : unit -> Tac string) : Tac unit =
  if debugging () then
    print (f ())

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
    guard (is_tot_comp r); (* must be total *)
    let cod = r.result_typ in

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
      let proj_name = cur_module () @ [base ^ s] in
      let proj = pack (Tv_FVar (pack_fv proj_name)) in

      let proj_se =
        match lookup_typ (top_env ()) proj_name with
        | None -> fail "mk_class: proj not found?"
        | Some se -> se
      in
      let proj_attrs = sigelt_attrs proj_se in
      let proj_us, proj_typ, proj_fv =
        match inspect_sigelt proj_se with
        | Sg_Let {lbs} ->
          let lb = lookup_lb lbs proj_name in
          lb.lb_us, lb.lb_typ, lb.lb_fv
        | Sg_Val {univs; typ} ->
          univs, typ, pack_fv proj_name
        | _ -> fail "mk_class: proj not Sg_Let or Sg_Val?"
      in
      debug' (fun () -> "proj_ty = " ^ term_to_string proj_typ);

      let ty =
        let bs, cod = collect_arr_bs proj_typ in
        let ps, bs = List.Tot.Base.splitAt (List.Tot.Base.length params) bs in
        match bs with
        | [] -> fail "mk_class: impossible, no binders"
        | b1::bs' ->
            let b1 = binder_set_tcarg b1 in
            mk_arr (ps@(b1::bs')) cod
      in
      let def =
        if false then
          let bs, body = collect_abs proj_typ in
          let ps, bs = List.Tot.Base.splitAt (List.Tot.Base.length params) bs in
          match bs with
          | [] -> fail "mk_class: impossible, no binders"
          | b1::bs' ->
              let b1 = binder_set_tcarg b1 in
              mk_abs (ps@(b1::bs')) body
        else
          let bs, _cod = collect_arr_bs proj_typ in
          let ps, bs = List.Tot.Base.splitAt (List.Tot.Base.length params) bs in
          match bs with
          | [] -> fail "mk_class: impossible, no binders"
          | b1::bs' ->
            let b1 = binder_set_tcarg b1 in
            mk_abs (ps@[b1]) <|
              mk_app (Tv_FVar proj_fv)
                (L.map (fun p -> (binder_to_term p, Q_Implicit)) ps
                @ [binder_to_term b1, Q_Explicit])
      in
      debug' (fun () -> "def = " ^ term_to_string def);
      debug' (fun () -> "ty  = " ^ term_to_string ty);

      let ty : term = ty in
      let def : term = def in
      let sfv : fv = sfv in

      let lb = { lb_fv=sfv; lb_us=proj_us; lb_typ=ty; lb_def=def } in
      let se = pack_sigelt (Sg_Let {isrec=false; lbs=[lb]}) in
      let se = set_sigelt_quals to_propagate se in
      (* A method's result type is typically a function, so its SMT arity has to
         be pinned down explicitly rather than read off the (flattened) arrow
         spine of its type; see FStar.Attributes.smt_arity. The class parameters
         are the right choice: methods are habitually used partially applied,
         and this is the arity the encoding used before arrows became unary. *)
      let arity = pack (Tv_Const (C_Int (L.length params) (FStar.Sealed.seal Dec))) in
      let se = set_sigelt_attrs ((`(FStar.Attributes.smt_arity (`#arity)))
                                :: (`tcmethod) :: proj_attrs @ b.attrs) se in
      // debug' (fun () -> "trying to return : " ^ term_to_string (quote se));
      se
    )
