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

(* TODO: This must be in the FStar.Tactics.* namespace or we fail to build
 * fstarlib. That seems silly, but I forget the details of the library split. *)

open FStar.Tactics
module T = FStar.Tactics

(* The attribute that marks instances *)
irreducible
let tcinstance : unit = ()

let rec first (f : 'a -> Tac 'b) (l : list 'a) : Tac 'b =
    match l with
    | [] -> fail "no cands"
    | x::xs -> (fun () -> f x) `or_else` (fun () -> first f xs)

(* TODO: memoization?. And better errors. *)
private
let rec tcresolve' (seen:list term) (fuel:int) : Tac unit =
    if fuel <= 0 then
        fail "out of fuel";
    debug ("fuel = " ^ string_of_int fuel);
    let g = cur_goal () in
    if FStar.List.Tot.Base.existsb (term_eq g) seen then
      fail "loop";
    let seen = g :: seen in
    local seen fuel `or_else` (fun () -> global seen fuel `or_else` (fun () -> fail ("could not solve constraint: " ^ term_to_string g)))
and local (seen:list term) (fuel:int) () : Tac unit =
    let bs = binders_of_env (cur_env ()) in
    first (fun b -> trywith seen fuel (pack (Tv_Var (bv_of_binder b)))) bs
and global (seen:list term) (fuel:int) () : Tac unit =
    let cands = lookup_attr (`tcinstance) (cur_env ()) in
    first (fun fv -> trywith seen fuel (pack (Tv_FVar fv))) cands
and trywith (seen:list term) (fuel:int) (t:term) : Tac unit =
    debug ("Trying to apply hypothesis/instance: " ^ term_to_string t);
    (fun () -> apply_noinst t) `seq` (fun () -> tcresolve' seen (fuel-1))

[@@plugin]
let tcresolve () : Tac unit =
    try tcresolve' [] 16
    with
    | TacticFailure s -> fail ("Typeclass resolution failed: " ^ s)
    | e -> raise e

(* Solve an explicit argument by typeclass resolution *)
unfold let solve (#a:Type) (#[tcresolve ()] ev : a) : Tot a = ev

(**** Generating methods from a class ****)

(* In TAC, not Tot *)
let rec mk_abs (bs : list binder) (body : term) : Tac term (decreases bs) =
    match bs with
    | [] -> body
    | b::bs -> pack (Tv_Abs b (mk_abs bs body))

let rec last (l : list 'a) : Tac 'a =
  match l with
  | [] -> fail "last: empty list"
  | [x] -> x
  | _::xs -> last xs

[@@plugin]
let mk_class (nm:string) : Tac decls =
    let ns = explode_qn nm in
    let r = lookup_typ (top_env ()) ns in
    guard (Some? r);
    let Some se = r in
    let to_propagate = List.Tot.filter (function Inline_for_extraction | NoExtract -> true | _ -> false) (sigelt_quals se) in
    let sv = inspect_sigelt se in
    guard (Sg_Inductive? sv);
    let Sg_Inductive name us params ty ctors = sv in
    (* dump ("got it, name = " ^ implode_qn name); *)
    (* dump ("got it, ty = " ^ term_to_string ty); *)
    let ctor_name = last name in
    // Must have a single constructor
    guard (List.Tot.Base.length ctors = 1);
    let [(c_name, ty)] = ctors in
    (* dump ("got ctor " ^ implode_qn c_name ^ " of type " ^ term_to_string ty); *)
    let bs, cod = collect_arr_bs ty in
    let r = inspect_comp cod in
    guard (C_Total? r);
    let C_Total cod _ = r in (* must be total *)

    (* print ("n_univs = " ^ string_of_int (List.Tot.Base.length us)); *)

    let base : string = "__proj__Mk" ^ ctor_name ^ "__item__" in

    (* Make a sigelt for each method *)
    T.map (fun b ->
                  (* dump ("b = " ^ term_to_string (type_of_binder b)); *)
                  let s = name_of_binder b in
                  (* dump ("b = " ^ s); *)
                  let ns = cur_module () in
                  let sfv = pack_fv (ns @ [s]) in
                  let dbv = fresh_bv_named "d" cod in
                  let tcr = (`tcresolve) in
                  let tcdict = pack_binder dbv (Q_Meta tcr) in
                  let proj_name = cur_module () @ [base ^ s] in
                  let proj = pack (Tv_FVar (pack_fv (cur_module () @ [base ^ s]))) in

                  let proj_ty =
                    match lookup_typ (top_env ()) proj_name with
                    | None -> fail "mk_class: proj not found?"
                    | Some se ->
                      match inspect_sigelt se with
                      | Sg_Let _ _ _ t _ -> t
                      | _ -> fail "mk_class: proj not Sg_Let?"
                  in
                  //dump ("proj_ty = " ^ term_to_string proj_ty);
                  let ty =
                    let bs, cod = collect_arr_bs proj_ty in
                    let ps, bs = List.Tot.Base.splitAt (List.Tot.Base.length params) bs in
                    match bs with
                    | [] -> fail "mk_class: impossible, no binders"
                    | b1::bs' ->
                        let (bv, aq) = inspect_binder b1 in
                        let b1 = pack_binder bv (Q_Meta tcr) in
                        mk_arr (ps@(b1::bs')) cod
                  in

                  let def : term =
                    let bs = (map (fun b -> binder_set_qual Q_Implicit b) params)
                                    @ [tcdict] in
                    mk_abs bs (mk_e_app proj [binder_to_term tcdict])
                  in
                  //dump ("def = " ^ term_to_string def);
                  //dump ("ty  = " ^ term_to_string ty);

                  let ty : term = ty in
                  let def : term = def in
                  let sfv : fv = sfv in
                  let se = pack_sigelt (Sg_Let false sfv us ty def) in
                  let se = set_sigelt_quals to_propagate se in
                  //let se = set_sigelt_attrs [`tcnorm] se in
                  //dump ("trying to return : " ^ term_to_string (quote se));
                  se
    ) bs
