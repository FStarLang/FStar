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
module Printers
open FStar.List.Tot
(* TODO: This is pretty much a blast-to-the-past of Meta-F*, we can do
 * much better now. *)

open FStar.Tactics.V2
module TU = FStar.Tactics.Util

let print_Prims_string : string -> Tot string = fun s -> "\"" ^ s ^ "\""
let print_Prims_int : int -> Tot string = string_of_int

let mk_concat (sep : term) (ts : list term) : Tac term =
    mk_e_app (pack (Tv_FVar (pack_fv ["FStar"; "String"; "concat"]))) [sep; mk_list ts]

let mk_flatten ts = mk_concat (`"") ts

let paren (e : term) : Tac term =
    mk_flatten [mk_stringlit "("; e; mk_stringlit ")"]

let mk_print_bv (self : name) (f : term) (bvty : namedv & typ) : Tac term =
    let bv, ty = bvty in
    (* debug ("self = " ^ String.concat "." self ^ "\n>>>>>> f = : " ^ term_to_string f); *)
    let mk n = pack (Tv_FVar (pack_fv n)) in
    match inspect ty with
    | Tv_FVar fv ->
        if inspect_fv fv = self
        then mk_e_app f [pack (Tv_Var bv)]
        else let f = mk (cur_module () @ ["print_" ^ (String.concat "_" (inspect_fv fv))]) in
             mk_e_app f [pack (Tv_Var bv)]
    | _ ->
        mk_stringlit "?"

let mk_printer_type (t : term) : Tac term =
    let b = fresh_binder_named "arg" t in
    let str = pack (Tv_FVar (pack_fv string_lid)) in
    let c = pack_comp (C_Total str) in
    pack (Tv_Arrow b c)

(* This tactics generates the entire let rec at once and
 * then uses exact. We could do something better. *)
let mk_printer_fun (dom : term) : Tac term =
    set_guard_policy SMT;
    let e = top_env () in
    (* Recursive binding *)
    let ff = fresh_namedv_named "ff_rec" in
    let ffty = mk_printer_type dom in
    let fftm = pack (Tv_Var ff) in

    let x = fresh_binder_named "v" dom in
    let xt_ns = match inspect dom with
                | Tv_FVar fv -> (inspect_fv fv)
                | _ -> fail "not a qname type?"
    in
    let se = match lookup_typ e xt_ns with
             | None -> fail "Type not found..?"
             | Some se -> se
    in

    match inspect_sigelt se with
    | Sg_Let _ -> fail "cannot create printer for let"
    | Sg_Inductive {params=bs; typ=y; ctors} ->
        let br1 ctor : Tac branch =
            let (name, t) = ctor in
            let pn = String.concat "." name in
            let t_args, _ = collect_arr t in
            let bv_ty_pats = TU.map (fun ti -> let bv = fresh_namedv_named "a" in ((bv, ti), (Pat_Var {v=bv; sort=seal ti}, false))) t_args in
            let bvs, pats = List.Tot.split bv_ty_pats in
            let head = pack (Tv_Const (C_String pn)) in
            let bod = mk_concat (mk_stringlit " ") (head :: TU.map (mk_print_bv xt_ns fftm) bvs) in
            let bod = match t_args with | [] -> bod | _ -> paren bod in
            (Pat_Cons {head=pack_fv name; univs=None; subpats=pats}, bod)
        in
        let branches = TU.map br1 ctors in
        let xi = fresh_binder_named "v_inner" dom in

        // Generate the match on the internal argument
        let m = pack (Tv_Match (pack (Tv_Var (binder_to_namedv xi))) None branches) in
        (* debug ("m = " ^ term_to_string m); *)

        // Wrap it into an internal function
        let f = pack (Tv_Abs xi m) in
        (* debug ("f = " ^ term_to_string f); *)

        // Wrap it in a let rec; basically:
        // let rec ff = fun t -> match t with { .... } in ff x
        let ff_bnd : binder = { namedv_to_simple_binder ff with sort = ffty } in
        let xtm = pack (Tv_Var (binder_to_namedv x)) in
        let b = pack (Tv_Let true [] ff_bnd f (mk_e_app fftm [xtm])) in
        (* print ("b = " ^ term_to_string b); *)

        // Wrap it in a lambda taking the initial argument
        let tm = pack (Tv_Abs x b) in
        (* debug ("tm = " ^ term_to_string tm); *)

        tm
    | _ -> fail "type not found?"

let rec maplast (f : 'a -> 'a) (l : list 'a) : list 'a =
    match l with
    | [] -> []
    | [x] -> [f x]
    | x::xs -> x :: (maplast f xs)

let mk_printer dom : Tac decls =
    let nm = match inspect dom with
             | Tv_FVar fv -> inspect_fv fv
             | _ -> fail "not an fv?"
    in
    let nm = maplast (fun s -> s ^ "_print") nm in
    let lb = {
      lb_fv = pack_fv nm;
      lb_us = [];
      lb_typ = mk_printer_type dom;
      lb_def = mk_printer_fun dom
    } in
    let sv : sigelt_view = Sg_Let {isrec=false; lbs=[lb]} in
    let ses : list sigelt = [pack_sigelt sv] in
    ses

noeq
type t1 =
    | A : int -> string -> t1
    | B : t1 -> int -> t1
    | C : t1
    | D : string -> t1
    | E : t1 -> t1
    | F : (unit -> t1) -> t1

(* We need to provide the name of the generated definition
 * by hand, since desugaring this module occurs entirely
 * before running the metaprograms. *)
%splice[t1_print] (mk_printer (`t1))

let _ = assert_norm (t1_print (A 5 "hey") = "(Printers.A 5 \"hey\")")
let _ = assert_norm (t1_print (B (D "thing") 42) = "(Printers.B (Printers.D \"thing\") 42)")
let _ = assert_norm (t1_print C = "Printers.C")
let _ = assert_norm (t1_print (D "test") = "(Printers.D \"test\")")
let _ = assert_norm (t1_print (E (B (D "thing") 42)) = "(Printers.E (Printers.B (Printers.D \"thing\") 42))")
let _ = assert_norm (t1_print (F (fun _ -> C)) = "(Printers.F ?)")
