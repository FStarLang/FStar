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

module FStar.SMTEncoding.Encode
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
open FStar.Const
open FStar.SMTEncoding
open FStar.SMTEncoding.Util
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module N = FStar.TypeChecker.Normalize
module BU = FStar.Util
module U = FStar.Syntax.Util
module TcUtil = FStar.TypeChecker.Util
module Const = FStar.Parser.Const
module R  = FStar.Reflection.Basic
module RD = FStar.Reflection.Data
module EMB = FStar.Syntax.Embeddings
module RE = FStar.Reflection.Embeddings
open FStar.SMTEncoding.Env
open FStar.SMTEncoding.EncodeTerm
open FStar.Parser

module Env = FStar.TypeChecker.Env

type prims_t = {
    mk:lident -> string -> term * int * list<decl>;
    is:lident -> bool;
}


let prims =
    let asym, a = fresh_fvar "a" Term_sort in
    let xsym, x = fresh_fvar "x" Term_sort in
    let ysym, y = fresh_fvar "y" Term_sort in
    let quant vars body : Range.range -> string -> term * int * list<decl> = fun rng x ->
        let xname_decl = Term.DeclFun(x, vars |> List.map snd, Term_sort, None) in
        let xtok = x ^ "@tok" in
        let xtok_decl = Term.DeclFun(xtok, [], Term_sort, None) in
        let xapp = mkApp(x, List.map mkFreeV vars) in //arity ok, see decl (#1383)
        let xtok = mkApp(xtok, []) in //arity ok, see decl (#1383)
        let xtok_app = mk_Apply xtok vars in
        xtok,
        List.length vars,
        [xname_decl;
         xtok_decl;
         Util.mkAssume(mkForall rng ([[xapp]], vars, mkEq(xapp, body)), None, "primitive_" ^x);
         Util.mkAssume(mkForall rng ([[xtok_app]],
                     vars,
                     mkEq(xtok_app, xapp)),
                     Some "Name-token correspondence",
                     "token_correspondence_"^x)]
    in
    let axy = [(asym, Term_sort); (xsym, Term_sort); (ysym, Term_sort)] in
    let xy = [(xsym, Term_sort); (ysym, Term_sort)] in
    let qx = [(xsym, Term_sort)] in
    let prims = [
        (Const.op_Eq,          (quant axy (boxBool <| mkEq(x,y))));
        (Const.op_notEq,       (quant axy (boxBool <| mkNot(mkEq(x,y)))));
        (Const.op_LT,          (quant xy  (boxBool <| mkLT(unboxInt x, unboxInt y))));
        (Const.op_LTE,         (quant xy  (boxBool <| mkLTE(unboxInt x, unboxInt y))));
        (Const.op_GT,          (quant xy  (boxBool <| mkGT(unboxInt x, unboxInt y))));
        (Const.op_GTE,         (quant xy  (boxBool <| mkGTE(unboxInt x, unboxInt y))));
        (Const.op_Subtraction, (quant xy  (boxInt  <| mkSub(unboxInt x, unboxInt y))));
        (Const.op_Minus,       (quant qx  (boxInt  <| mkMinus(unboxInt x))));
        (Const.op_Addition,    (quant xy  (boxInt  <| mkAdd(unboxInt x, unboxInt y))));
        (Const.op_Multiply,    (quant xy  (boxInt  <| mkMul(unboxInt x, unboxInt y))));
        (Const.op_Division,    (quant xy  (boxInt  <| mkDiv(unboxInt x, unboxInt y))));
        (Const.op_Modulus,     (quant xy  (boxInt  <| mkMod(unboxInt x, unboxInt y))));
        (Const.op_And,         (quant xy  (boxBool <| mkAnd(unboxBool x, unboxBool y))));
        (Const.op_Or,          (quant xy  (boxBool <| mkOr(unboxBool x, unboxBool y))));
        (Const.op_Negation,    (quant qx  (boxBool <| mkNot(unboxBool x))));
        ]
    in
    let mk : lident -> string -> term * int * list<decl> =
        fun l v ->
            prims |>
            List.find (fun (l', _) -> lid_equals l l') |>
            Option.map (fun (_, b) -> b (Ident.range_of_lid l) v) |>
            Option.get in
    let is : lident -> bool =
        fun l -> prims |> BU.for_some (fun (l', _) -> lid_equals l l') in
    {mk=mk;
     is=is}

let pretype_axiom rng env tapp vars =
    let xxsym, xx = fresh_fvar "x" Term_sort in
    let ffsym, ff = fresh_fvar "f" Fuel_sort in
    let xx_has_type = mk_HasTypeFuel ff xx tapp in
    let tapp_hash = Term.hash_of_term tapp in
    let module_name = env.current_module_name in
    Util.mkAssume(mkForall rng ([[xx_has_type]], (xxsym, Term_sort)::(ffsym, Fuel_sort)::vars,
                                mkImp(xx_has_type, mkEq(tapp, mkApp("PreType", [xx])))),
                         Some "pretyping",
                         (varops.mk_unique (module_name ^ "_pretyping_" ^ (BU.digest_of_string tapp_hash))))

let primitive_type_axioms : env_t -> lident -> string -> term -> list<decl> * env_t =
    let xx = ("x", Term_sort) in
    let x = mkFreeV xx in

    let yy = ("y", Term_sort) in
    let y = mkFreeV yy in

    let wrap (f:env -> string -> term -> decls_t) = fun env s t ->
      f env.tcenv s t, env
    in
    let mk_unit : env -> string -> term -> decls_t = fun env nm tt ->
        let typing_pred = mk_HasType x tt in
        [Util.mkAssume(mk_HasType mk_Term_unit tt,
                       Some "unit typing",
                       "unit_typing");
         Util.mkAssume(mkForall_fuel (Env.get_range env)
                                     ([[typing_pred]],
                                       [xx],
                                       mkImp(typing_pred, mkEq(x, mk_Term_unit))),
                                     Some "unit inversion",
                                     "unit_inversion");]
    in
    let mk_bool : env -> string -> term -> decls_t = fun env nm tt ->
        let typing_pred = mk_HasType x tt in
        let bb = ("b", Bool_sort) in
        let b = mkFreeV bb in
        [Util.mkAssume(mkForall (Env.get_range env)
                                ([[Term.boxBool b]],
                                  [bb],
                                  mk_HasType (Term.boxBool b) tt),
                                Some "bool typing",
                                "bool_typing");
         Util.mkAssume(mkForall_fuel (Env.get_range env)
                                     ([[typing_pred]],
                                       [xx],
                                       mkImp(typing_pred, mk_tester (fst boxBoolFun) x)),
                                     Some "bool inversion",
                                     "bool_inversion")]
    in
    let mk_int : env -> string -> term -> decls_t  = fun env nm tt ->
        let lex_t = mkFreeV (text_of_lid Const.lex_t_lid, Term_sort) in
        let typing_pred = mk_HasType x tt in
        let typing_pred_y = mk_HasType y tt in
        let aa = ("a", Int_sort) in
        let a = mkFreeV aa in
        let bb = ("b", Int_sort) in
        let b = mkFreeV bb in
        let precedes_y_x = mk_Valid <| mkApp("Prims.precedes", [lex_t; lex_t;y;x]) in
        [Util.mkAssume(mkForall (Env.get_range env)
                                ([[Term.boxInt b]], [bb], mk_HasType (Term.boxInt b) tt),
                                Some "int typing",
                                "int_typing");
         Util.mkAssume(mkForall_fuel (Env.get_range env)
                                     ([[typing_pred]],
                                       [xx],
                                       mkImp(typing_pred, mk_tester (fst boxIntFun) x)),
                                     Some "int inversion",
                                     "int_inversion");
         Util.mkAssume(mkForall_fuel (Env.get_range env)
                                     ([[typing_pred; typing_pred_y;precedes_y_x]],
                                     [xx;yy],
                                     mkImp(mk_and_l
                                            [typing_pred;
                                             typing_pred_y;
                                             mkGT (Term.unboxInt x, mkInteger' 0);
                                             mkGTE (Term.unboxInt y, mkInteger' 0);
                                             mkLT (Term.unboxInt y, Term.unboxInt x)],
                                           precedes_y_x)),
                                  Some "well-founded ordering on nat (alt)",
                                  "well-founded-ordering-on-nat")] in
    let mk_str : env -> string -> term -> decls_t  = fun env nm tt ->
        let typing_pred = mk_HasType x tt in
        let bb = ("b", String_sort) in
        let b = mkFreeV bb in
        [Util.mkAssume(mkForall (Env.get_range env)
                                ([[Term.boxString b]],
                                  [bb],
                                  mk_HasType (Term.boxString b) tt),
                                Some "string typing",
                                "string_typing");
         Util.mkAssume(mkForall_fuel (Env.get_range env)
                                     ([[typing_pred]],
                                       [xx],
                                       mkImp(typing_pred, mk_tester (fst boxStringFun) x)),
                                     Some "string inversion",
                                     "string_inversion")] in
    let mk_true_interp : env -> string -> term -> decls_t = fun env nm true_tm ->
        let valid = mkApp("Valid", [true_tm]) in
        [Util.mkAssume(valid, Some "True interpretation", "true_interp")]
    in
    let mk_false_interp : env -> string -> term -> decls_t = fun env nm false_tm ->
        let valid = mkApp("Valid", [false_tm]) in
        [Util.mkAssume(mkIff(mkFalse, valid), Some "False interpretation", "false_interp")]
    in
    let mk_macro_name s =
        FStar.Ident.reserved_prefix ^ s
    in
    let bind_macro env lid macro_name =
        let fvb = lookup_lid env lid in
        push_free_var env lid fvb.smt_arity macro_name fvb.smt_token
    in
    let mk_and_interp : env_t -> string -> term -> decls_t * env_t = fun env conj _ ->
        let aa = ("a", Term_sort) in
        let bb = ("b", Term_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let l_and_a_b = mkApp(conj, [a;b]) in
        let valid = mkApp("Valid", [l_and_a_b]) in
        let valid_a = mkApp("Valid", [a]) in
        let valid_b = mkApp("Valid", [b]) in
        (*
             (define-fun l_and_macro  ((a Term) (b Term)) Term
                         (l_and a (ite (Valid a) b mk_Term_unit)))

        *)
        let macro_name = mk_macro_name conj in
        let macro =
          mkDefineFun(macro_name,
                      [aa;bb],
                      Term_sort,
                      mkApp(conj, [a; mkITE(valid_a, b, mk_Term_unit)]),
                      Some "macro for embedded conjunction")
        in
        [Util.mkAssume(mkForall (Env.get_range env.tcenv)
                                ([[l_and_a_b]],
                                 [aa;bb],
                                 mkIff(mkAnd(valid_a, valid_b), valid)),
                                 Some "/\ interpretation",
                                 "l_and-interp");
         macro],
         bind_macro env FStar.Parser.Const.and_lid macro_name
    in
    let mk_or_interp : env_t -> string -> term -> decls_t * env_t = fun env disj _ ->
        let aa = ("a", Term_sort) in
        let bb = ("b", Term_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let l_or_a_b = mkApp(disj, [a;b]) in
        let valid = mkApp("Valid", [l_or_a_b]) in
        let valid_a = mkApp("Valid", [a]) in
        let valid_b = mkApp("Valid", [b]) in
          (*
             (define-fun l_or_macro  ((a Term) (b Term)) Term
                         (l_or a (ite (not (Valid a)) b mk_Term_unit)))

          *)
        let macro_name = mk_macro_name disj in
        let macro =
          mkDefineFun(macro_name,
                      [aa;bb],
                      Term_sort,
                      mkApp(disj, [a; mkITE(mkNot valid_a, b, mk_Term_unit)]),
                      Some "macro for embedded disjunction")
        in
        [Util.mkAssume(mkForall (Env.get_range env.tcenv)
                                ([[l_or_a_b]],
                                 [aa;bb],
                                 mkIff(mkOr(valid_a, valid_b), valid)),
                                 Some "\/ interpretation",
                                 "l_or-interp");
         macro],
         bind_macro env FStar.Parser.Const.or_lid macro_name
    in
    let mk_imp_interp : env_t -> string -> term -> decls_t * env_t = fun env imp tt ->
        let aa = ("a", Term_sort) in
        let bb = ("b", Term_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let l_imp_a_b = mkApp(imp, [a;b]) in
        let valid = mkApp("Valid", [l_imp_a_b]) in
        let valid_a = mkApp("Valid", [a]) in
        let valid_b = mkApp("Valid", [b]) in
          (*
             (define-fun l_imp_macro  ((a Term) (b Term)) Term
                         (l_imp a (ite (Valid a) b mk_Term_unit)))

          *)
        let macro_name = mk_macro_name imp in
        let macro =
          mkDefineFun(macro_name,
                      [aa;bb],
                      Term_sort,
                      mkApp(imp, [a; mkITE(valid_a, b, mk_Term_unit)]),
                      Some "macro for embedded implication")
        in
        [Util.mkAssume(mkForall (Env.get_range env.tcenv)
                                ([[l_imp_a_b]], [aa;bb], mkIff(mkImp(valid_a, valid_b), valid)),
                                Some "==> interpretation",
                                "l_imp-interp");
         macro],
        bind_macro env FStar.Parser.Const.imp_lid macro_name
    in
    let mk_iff_interp : env -> string -> term -> decls_t = fun env iff tt ->
        let aa = ("a", Term_sort) in
        let bb = ("b", Term_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let l_iff_a_b = mkApp(iff, [a;b]) in
        let valid = mkApp("Valid", [l_iff_a_b]) in
        let valid_a = mkApp("Valid", [a]) in
        let valid_b = mkApp("Valid", [b]) in
        [Util.mkAssume(mkForall (Env.get_range env)
                                ([[l_iff_a_b]], [aa;bb], mkIff(mkIff(valid_a, valid_b), valid)),
                                Some "<==> interpretation",
                                "l_iff-interp")]
    in
    let mk_not_interp : env -> string -> term -> decls_t = fun env l_not tt ->
        let aa = ("a", Term_sort) in
        let a = mkFreeV aa in
        let l_not_a = mkApp(l_not, [a]) in
        let valid = mkApp("Valid", [l_not_a]) in
        let not_valid_a = mkNot <| mkApp("Valid", [a]) in
        [Util.mkAssume(mkForall (Env.get_range env)
                                ([[l_not_a]], [aa], mkIff(not_valid_a, valid)),
                                Some "not interpretation",
                                "l_not-interp")]
    in
    let mk_eq2_interp : env -> string -> term -> decls_t = fun env eq2 tt ->
        let aa = ("a", Term_sort) in
        let xx = ("x", Term_sort) in
        let yy = ("y", Term_sort) in
        let a = mkFreeV aa in
        let x = mkFreeV xx in
        let y = mkFreeV yy in
        let eq2_x_y = mkApp(eq2, [a;x;y]) in
        let valid = mkApp("Valid", [eq2_x_y]) in
        [Util.mkAssume(mkForall (Env.get_range env)
                                ([[eq2_x_y]],
                                 [aa;xx;yy],
                                 mkIff(mkEq(x, y), valid)),
                                Some "Eq2 interpretation",
                                "eq2-interp")]
    in
    let mk_eq3_interp : env -> string -> term -> decls_t = fun env eq3 tt ->
        let aa = ("a", Term_sort) in
        let bb = ("b", Term_sort) in
        let xx = ("x", Term_sort) in
        let yy = ("y", Term_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let x = mkFreeV xx in
        let y = mkFreeV yy in
        let eq3_x_y = mkApp(eq3, [a;b;x;y]) in
        let valid = mkApp("Valid", [eq3_x_y]) in
        [Util.mkAssume(mkForall (Env.get_range env)
                                ([[eq3_x_y]], [aa;bb;xx;yy], mkIff(mkEq(x, y), valid)),
                                Some "Eq3 interpretation",
                                "eq3-interp")]
   in
   let mk_range_interp : env -> string -> term -> decls_t = fun env range tt ->
        let range_ty = mkApp(range, []) in
        [Util.mkAssume(mk_HasTypeZ (mk_Range_const ()) range_ty,
                       Some "Range_const typing",
                       varops.mk_unique "typing_range_const")]
   in
   let mk_inversion_axiom : env -> string -> term -> decls_t = fun env inversion tt ->
       // (assert (forall ((t Term))
       //            (! (implies (Valid (FStar.Pervasives.inversion t))
       //                        (forall ((x Term))
       //                                (! (implies (HasTypeFuel ZFuel x t)
       //                                            (HasTypeFuel (SFuel ZFuel) x t))
       //                                   :pattern ((HasTypeFuel ZFuel x t)))))
       //               :pattern ((FStar.Pervasives.inversion t)))))
        let tt = ("t", Term_sort) in
        let t = mkFreeV tt in
        let xx = ("x", Term_sort) in
        let x = mkFreeV xx in
        let inversion_t = mkApp(inversion, [t]) in
        let valid = mkApp("Valid", [inversion_t]) in
        let body =
          let hastypeZ = mk_HasTypeZ x t in
          let hastypeS = mk_HasTypeFuel (n_fuel 1) x t in
          mkForall (Env.get_range env) ([[hastypeZ]], [xx], mkImp(hastypeZ, hastypeS))
        in
        [Util.mkAssume(mkForall (Env.get_range env)
                                ([[inversion_t]], [tt], mkImp(valid, body)),
                                Some "inversion interpretation",
                                "inversion-interp")]
   in
   let mk_with_type_axiom : env -> string -> term -> decls_t = fun env with_type tt ->
        (* (assert (forall ((t Term) (e Term))
                           (! (and (= (Prims.with_type t e)
                                       e)
                                   (HasType (Prims.with_type t e) t))
                            :weight 0
                            :pattern ((Prims.with_type t e)))))
         *)
        let tt = ("t", Term_sort) in
        let t = mkFreeV tt in
        let ee = ("e", Term_sort) in
        let e = mkFreeV ee in
        let with_type_t_e = mkApp(with_type, [t; e]) in
        [Util.mkAssume(mkForall' (Env.get_range env) ([[with_type_t_e]],
                                 Some 0, //weight
                                 [tt;ee],
                                 mkAnd(mkEq(with_type_t_e, e),
                                       mk_HasType with_type_t_e t)),
                       Some "with_type primitive axiom",
                       "@with_type_primitive_axiom")] //the "@" in the name forces it to be retained even when the contex is pruned
   in
   let prims =  [(Const.unit_lid,      wrap mk_unit);
                 (Const.bool_lid,      wrap mk_bool);
                 (Const.int_lid,       wrap mk_int);
                 (Const.string_lid,    wrap mk_str);
                 (Const.true_lid,      wrap mk_true_interp);
                 (Const.false_lid,     wrap mk_false_interp);
                 (Const.and_lid,       mk_and_interp);
                 (Const.or_lid,        mk_or_interp);
                 (Const.imp_lid,       mk_imp_interp);
                 (Const.iff_lid,       wrap mk_iff_interp);
                 (Const.not_lid,       wrap mk_not_interp);
                 (Const.eq2_lid,       wrap mk_eq2_interp);
                 (Const.eq3_lid,       wrap mk_eq3_interp);
                 (Const.range_lid,     wrap mk_range_interp);
                 (Const.inversion_lid, wrap mk_inversion_axiom);
                 (Const.with_type_lid, wrap mk_with_type_axiom)
                ] in
    (fun (env:env_t) (t:lident) (s:string) (tt:term) ->
        match BU.find_opt (fun (l, _) -> lid_equals l t) prims with
            | None -> [], env
            | Some(_, f) -> f env s tt)

let encode_smt_lemma env fv t =
    let lid = fv.fv_name.v in
    let form, decls = encode_function_type_as_formula t env in
    decls@[Util.mkAssume(form, Some ("Lemma: " ^ lid.str), ("lemma_"^lid.str))]

let encode_free_var uninterpreted env fv tt t_norm quals =
    let lid = fv.fv_name.v in
    if not <| (U.is_pure_or_ghost_function t_norm || is_reifiable_function env.tcenv t_norm)
    || U.is_lemma t_norm
    || uninterpreted
    then let arg_sorts = match (SS.compress t_norm).n with
            | Tm_arrow(binders, _) -> binders |> List.map (fun _ -> Term_sort)
            | _ -> [] in
         let arity = List.length arg_sorts in
         let vname, vtok, env = new_term_constant_and_tok_from_lid env lid arity in
         let d = Term.DeclFun(vname, arg_sorts, Term_sort, Some "Uninterpreted function symbol for impure function") in
         let dd = Term.DeclFun(vtok, [], Term_sort, Some "Uninterpreted name for impure function") in
         [d;dd], env
    else if prims.is lid
         then let vname = varops.new_fvar lid in
              let tok, arity, definition = prims.mk lid vname in
              let env = push_free_var env lid arity vname (Some tok) in
              definition, env
         else let encode_non_total_function_typ = lid.nsstr <> "Prims" in
              let formals, (pre_opt, res_t) =
                let args, comp = curried_arrow_formals_comp t_norm in
                let comp =
                  if is_reifiable_comp env.tcenv comp
                  then S.mk_Total (reify_comp ({env.tcenv with lax=true}) comp U_unknown)
                  else comp
                in
                if encode_non_total_function_typ
                then args, TypeChecker.Util.pure_or_ghost_pre_and_post env.tcenv comp
                else args, (None, U.comp_result comp)
              in
              let arity = List.length formals in
              let vname, vtok, env = new_term_constant_and_tok_from_lid env lid arity in
              let vtok_tm = match formals with
                | [] -> mkFreeV(vname, Term_sort)
                | _ -> mkApp(vtok, []) in
              let mk_disc_proj_axioms guard encoded_res_t vapp vars = quals |> List.collect (function
                | Discriminator d ->
                    let _, (xxsym, _) = BU.prefix vars in
                    let xx = mkFreeV(xxsym, Term_sort) in
                    [Util.mkAssume(mkForall (S.range_of_fv fv) ([[vapp]], vars,
                                            mkEq(vapp, Term.boxBool <| mk_tester (escape d.str) xx)),
                                          Some "Discriminator equation",
                                          ("disc_equation_"^escape d.str))]

                | Projector(d, f) ->
                    let _, (xxsym, _) = BU.prefix vars in
                    let xx = mkFreeV(xxsym, Term_sort) in
                    let f = {ppname=f; index=0; sort=tun} in
                    let tp_name = mk_term_projector_name d f in //arity ok, primitive projector (#1383)
                    let prim_app = mkApp(tp_name, [xx]) in
                    [Util.mkAssume(mkForall (S.range_of_fv fv) ([[vapp]], vars,
                                            mkEq(vapp, prim_app)), Some "Projector equation", ("proj_equation_"^tp_name))]
                | _ -> []) in
              let vars, guards, env', decls1, _ = encode_binders None formals env in
              let guard, decls1 = match pre_opt with
                | None -> mk_and_l guards, decls1
                | Some p -> let g, ds = encode_formula p env' in mk_and_l (g::guards), decls1@ds in
              let vtok_app = mk_Apply vtok_tm vars in

              let vapp = mkApp(vname, List.map mkFreeV vars) in //arity ok, see decl below, arity is |formals| = |vars| (#1383)
              let decls2, env =
                let vname_decl = Term.DeclFun(vname, formals |> List.map (fun _ -> Term_sort), Term_sort, None) in
                let tok_typing, decls2 =
                    let env = {env with encode_non_total_function_typ=encode_non_total_function_typ} in
                    if not(head_normal env tt)
                    then encode_term_pred None tt env vtok_tm
                    else encode_term_pred None t_norm env vtok_tm in //NS:Unfortunately, this is duplicated work --- we effectively encode the function type twice
                let tok_decl, env =
                    match formals with
                    | [] ->
                      let tok_typing =
                        Util.mkAssume(tok_typing, Some "function token typing", ("function_token_typing_"^vname))
                      in
                      decls2@[tok_typing], push_free_var env lid arity vname (Some <| mkFreeV(vname, Term_sort))
                    | _ ->
                     (* Generate a token and a function symbol;
                        equate the two, and use the function symbol for full applications *)
                      let vtok_decl = Term.DeclFun(vtok, [], Term_sort, None) in
                      let vtok_app_0 = mk_Apply vtok_tm [List.hd vars] in
                      let name_tok_corr_formula pat =
                          mkForall (S.range_of_fv fv) ([[pat]], vars, mkEq(vtok_app, vapp))
                      in
                      //See issue #613 for the choice of patterns here
                      let name_tok_corr =
                          //this allows rewriting (ApplyTT tok ... x1..xn) to f x1...xn
                          Util.mkAssume(name_tok_corr_formula vtok_app,
                                        Some "Name-token correspondence",
                                        ("token_correspondence_"^vname)) in
                      let tok_typing =
                        let ff = ("ty", Term_sort) in
                        let f = mkFreeV ff in
                        let vtok_app_l = mk_Apply vtok_tm [ff] in
                        let vtok_app_r = mk_Apply f [(vtok, Term_sort)] in
                        //guard the token typing assumption with a Apply(f, tok), where f is typically __uu__PartialApp
                        //Additionally, the body of the term becomes
                        //                NoHoist f (and (HasType tok ...)
                        //                               (forall (x1..xn).{:pattern (f x1..xn)} f x1..xn=ApplyTT (ApplyTT tok x1) ... xn
                        //which provides a typing hypothesis for the token
                        //and a rule to rewrite f x1..xn to ApplyTT tok ... x1..xn
                        //The NoHoist prevents the Z3 simplifier from hoisting the (HasType tok ...) part out
                        //Since the top-levels of modules are full of function typed terms
                        //not guarding it this way causes every typing assumption of an arrow type to be fired immediately
                        //regardless of whether or not the function is used ... leading to bloat
                        //these patterns aim to restrict the use of the typing assumption until such point as it is actually needed
                        let guarded_tok_typing =
                          mkForall (S.range_of_fv fv)
                                   ([[vtok_app_r]],
                                    [ff],
                                    mkAnd(Term.mk_NoHoist f tok_typing,
                                          name_tok_corr_formula vapp)) in
                        Util.mkAssume(guarded_tok_typing, Some "function token typing", ("function_token_typing_"^vname))
                      in
                      decls2@[vtok_decl;name_tok_corr;tok_typing], env
                in
                vname_decl::tok_decl, env in
              let encoded_res_t, ty_pred, decls3 =
                   let res_t = SS.compress res_t in
                   let encoded_res_t, decls = encode_term res_t env' in
                   encoded_res_t, mk_HasType vapp encoded_res_t, decls in //occurs positively, so add fuel
              let typingAx = Util.mkAssume(mkForall (S.range_of_fv fv) ([[vapp]], vars, mkImp(guard, ty_pred)),
                                         Some "free var typing",
                                         ("typing_"^vname)) in
              let freshness =
                if quals |> List.contains New
                then [Term.fresh_constructor (S.range_of_fv fv) (vname, vars |> List.map snd, Term_sort, varops.next_id());
                      pretype_axiom (S.range_of_fv fv) env vapp vars]
                else [] in
              let g = decls1@decls2@decls3@freshness@typingAx::mk_disc_proj_axioms guard encoded_res_t vapp vars in
              g, env


let declare_top_level_let env x t t_norm =
  match lookup_fvar_binding env x.fv_name.v with
  (* Need to introduce a new name decl *)
  | None ->
      let decls, env = encode_free_var false env x t t_norm [] in
      let fvb = lookup_lid env x.fv_name.v in
      fvb, decls, env

  (* already declared, only need an equation *)
  | Some fvb ->
      fvb, [], env


let encode_top_level_val uninterpreted env lid t quals =
    let tt = norm env t in
//        if Env.debug env.tcenv <| Options.Other "SMTEncoding"
//        then Printf.printf "Encoding top-level val %s : %s\Normalized to is %s\n"
//            (Print.lid_to_string lid)
//            (Print.term_to_string t)
//            (Print.term_to_string tt);
    let decls, env = encode_free_var uninterpreted env lid t tt quals in
    if U.is_smt_lemma t
    then decls@encode_smt_lemma env lid tt, env
    else decls, env

let encode_top_level_vals env bindings quals =
    bindings |> List.fold_left (fun (decls, env) lb ->
        let decls', env = encode_top_level_val false env (BU.right lb.lbname) lb.lbtyp quals in
        decls@decls', env) ([], env)

let is_tactic t =
    let fstar_tactics_tactic_lid = FStar.Parser.Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n with
    | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_tactic_lid ->
      true
    | Tm_arrow(_, c) ->
      let effect_name = U.comp_effect_name c in
      BU.starts_with "FStar.Tactics" effect_name.str
    | _ -> false

exception Let_rec_unencodeable

let copy_env (en:env_t) = { en with cache = BU.smap_copy en.cache }  //Make a copy of all the mutable state of env_t, central place for keeping track of mutable fields in env_t

let encode_top_level_let :
    env_t -> (bool * list<letbinding>) -> list<qualifier> -> list<decl> * env_t =
    fun env (is_rec, bindings) quals ->

    let eta_expand binders formals body t =
      let nbinders = List.length binders in
      let formals, extra_formals = BU.first_N nbinders formals in
      let subst = List.map2 (fun (formal, _) (binder, _) -> NT(formal, S.bv_to_name binder)) formals binders in
      let extra_formals = extra_formals |> List.map (fun (x, i) -> {x with sort=SS.subst subst x.sort}, i) |> U.name_binders in
      let body = Syntax.extend_app_n (SS.compress body) (snd <| U.args_of_binders extra_formals) None body.pos in
      binders@extra_formals, body
    in

    let destruct_bound_function flid t_norm e
      : (S.binders    //arguments of the lambda abstraction
      * S.term        //body of the lambda abstraction
      * S.binders     //arguments of the function type, length of this component is equal to the first
      * S.typ)        //result type
      * bool          //if set, we should generate a curried application of f
    =
      (* The input type [t_norm] might contain reifiable computation type which must be reified at this point *)
      let get_result_type c =
          if is_reifiable_comp env.tcenv c
          then reify_comp ({env.tcenv with lax = true}) c U_unknown
          else U.comp_result c
      in

      let rec aux norm t_norm =
        let binders, body, lopt = U.abs_formals e in
        match binders with
        | _::_ -> begin
            match (U.unascribe <| SS.compress t_norm).n with
            | Tm_arrow(formals, c) ->
              let formals, c = SS.open_comp formals c in
              let nformals = List.length formals in
              let nbinders = List.length binders in
              let tres = get_result_type c in
              if nformals < nbinders && U.is_total_comp c (* explicit currying *)
              then let bs0, rest = BU.first_N nformals binders in
                      let c =
                          let subst = List.map2 (fun (x, _) (b, _) -> NT(x, S.bv_to_name b)) formals bs0 in
                          SS.subst_comp subst c in
                      let body = U.abs rest body lopt in
                      (bs0, body, bs0, get_result_type c), false
              else if nformals > nbinders (* eta-expand before translating it *)
              then let binders, body = eta_expand binders formals body tres in
                      (binders, body, formals, tres), false
              else (binders, body, formals, tres), false

            | Tm_refine(x, _) ->
                fst (aux norm x.sort), true

            (* have another go, after unfolding all definitions *)
            | _ when not norm ->
              let t_norm = N.normalize [Env.AllowUnboundUniverses; Env.Beta; Env.Weak; Env.HNF;
                                        (* we don't know if this will terminate; so don't do recursive steps *)
                                        Env.Exclude Env.Zeta;
                                        Env.UnfoldUntil delta_constant; Env.EraseUniverses] env.tcenv t_norm
              in
                aux true t_norm

            | _ ->
                failwith (BU.format3 "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                        flid.str (Print.term_to_string e) (Print.term_to_string t_norm))
          end
        | _ -> begin
            let rec aux' (t_norm:S.term) =
              match (SS.compress t_norm).n with
              | Tm_arrow(formals, c) ->
                let formals, c = SS.open_comp formals c in
                let tres = get_result_type c in
                let binders, body = eta_expand [] formals e tres in
                (binders, body, formals, tres), false
              | Tm_refine (bv, _) -> aux' bv.sort
              | _ -> ([], e, [], t_norm), false
            in
            aux' t_norm
          end
      in
      aux false t_norm
    in


    try
      if bindings |> BU.for_all (fun lb -> U.is_lemma lb.lbtyp || is_tactic lb.lbtyp)
      then encode_top_level_vals env bindings quals
      else
        let toks, typs, decls, env =
          bindings |> List.fold_left (fun (toks, typs, decls, env) lb ->
            (* some, but not all are lemmas; impossible *)
            if U.is_lemma lb.lbtyp then raise Let_rec_unencodeable;
            let t_norm = whnf env lb.lbtyp in
            (* We are declaring the top_level_let with t_norm which might contain *)
            (* non-reified reifiable computation type. *)
            (* TODO : clear this mess, the declaration should have a type corresponding to *)
            (* the encoded term *)
            let tok, decl, env = declare_top_level_let env (BU.right lb.lbname) lb.lbtyp t_norm in
            tok::toks, t_norm::typs, decl::decls, env)
            ([], [], [], env)
        in
        let toks_fvbs = List.rev toks in
        let decls = List.rev decls |> List.flatten in
        (*
         * AR: decls are the declarations for the top-level lets
         *     if one of the let body contains a let rec (inner let rec), we simply return decls at that point, inner let recs are not encoded to the solver yet (see Inner_let_rec below)
         *     the way it is implemented currently is that, the call to encode the let body throws an exception Inner_let_rec which is caught below in this function
         *     and the exception handler simply returns decls
         *     however, it seems to mess up the env cache
         *     basically, the let rec can be quite deep in the body, and then traversing the body before it, we might encode new decls, add them to the cache etc.
         *     since the cache is stateful, this would mean that there would be some symbols in the cache but not in the returned decls list (which only contains the top-level lets)
         *     this results in z3 errors
         *     so, taking a snapshot of the env, and return this env in handling of the Inner_let_rec (see also #1502)
         *)
        let env_decls = copy_env env in
        let typs = List.rev typs in

        let mk_app rng curry fvb vars =
            let mk_fv () =
              if fvb.smt_arity = 0
              then mkFreeV(fvb.smt_id, Term_sort)
              else raise_arity_mismatch fvb.smt_id fvb.smt_arity 0 rng
            in
            match vars with
            | [] ->
              mk_fv ()
            | _ ->
              if curry
              then match fvb.smt_token with
                   | Some ftok ->
                     mk_Apply ftok vars
                   | None ->
                     mk_Apply (mk_fv()) vars
              else maybe_curry_app rng (Var fvb.smt_id) fvb.smt_arity (List.map mkFreeV vars)
        in

        let encode_non_rec_lbdef
                (bindings:list<letbinding>)
                (typs:list<S.term>)
                (toks:list<fvar_binding>)
                (env:env_t) =
            match bindings, typs, toks with
            | [{lbunivs=uvs;lbdef=e;lbname=lbn}], [t_norm], [fvb] ->

                (* Open universes *)
                let flid = fvb.fvar_lid in
                let env', e, t_norm =
                  let tcenv', _, e_t =
                      Env.open_universes_in env.tcenv uvs [e; t_norm] in
                  let e, t_norm =
                      match e_t with
                      | [e; t_norm] -> e, t_norm
                      | _ -> failwith "Impossible" in
                  {env with tcenv=tcenv'}, e, t_norm
                in

                (* Open binders *)
                let (binders, body, _, t_body), curry = destruct_bound_function flid t_norm e in
                if Env.debug env.tcenv <| Options.Other "SMTEncoding"
                then BU.print2 "Encoding let : binders=[%s], body=%s\n"
                                (Print.binders_to_string ", " binders)
                                (Print.term_to_string body);
                (* Encode binders *)
                let vars, guards, env', binder_decls, _ = encode_binders None binders env' in

                let body =
                  (* Reify the body if needed *)
                  if is_reifiable_function env'.tcenv t_norm
                  then TcUtil.reify_body env'.tcenv body
                  else U.ascribe body (BU.Inl t_body, None)
                in
                let app = mk_app (FStar.Syntax.Util.range_of_lbname lbn) curry fvb vars in
                let pat, app, (body, decls2) =
                  let is_logical =
                    match (SS.compress t_body).n with
                    | Tm_fvar fv when S.fv_eq_lid fv FStar.Parser.Const.logical_lid -> true
                    | _ -> false
                  in
                  let is_prims = lbn |> FStar.Util.right |> lid_of_fv |> (fun lid -> lid_equals (lid_of_ids lid.ns) Const.prims_lid) in
                  if not is_prims && (quals |> List.contains Logic || is_logical)
                  then app, mk_Valid app, encode_formula body env'
                  else app, app, encode_term body env'
                in

                //NS 05.25: This used to be mkImp(mk_and_l guards, mkEq(app, body))),
                //But the guard is unnecessary given the pattern
                let eqn = Util.mkAssume(mkForall (U.range_of_lbname lbn)
                                                 ([[pat]], vars, mkEq(app,body)),
                                    Some (BU.format1 "Equation for %s" flid.str),
                                    ("equation_"^fvb.smt_id)) in
                let pt_axioms, env = primitive_type_axioms env flid fvb.smt_id app in
                decls@binder_decls@decls2@[eqn]@pt_axioms,
                env
            | _ -> failwith "Impossible"
        in

        let encode_rec_lbdefs (bindings:list<letbinding>)
                              (typs:list<S.term>)
                              (toks:list<fvar_binding>)
                              (env:env_t) =
          (* encoding recursive definitions using fuel to throttle unfoldings *)
          (* We create a new variable corresponding to the current fuel *)
          let fuel = varops.fresh "fuel", Fuel_sort in
          let fuel_tm = mkFreeV fuel in
          let env0 = env in
          (* For each declaration, we push in the environment its fuel-guarded copy (using current fuel) *)
          let gtoks, env = toks |> List.fold_left (fun (gtoks, env) fvb -> //(flid_fv, (f, ftok)) ->
            let flid = fvb.fvar_lid in
            let g = varops.new_fvar (Ident.lid_add_suffix flid "fuel_instrumented") in
            let gtok = varops.new_fvar (Ident.lid_add_suffix flid "fuel_instrumented_token") in
            let env = push_free_var env flid fvb.smt_arity gtok (Some <| mkApp(g, [fuel_tm])) in
            (fvb, g, gtok)::gtoks, env) ([], env)
          in
          let gtoks = List.rev gtoks in

          let encode_one_binding env0 (fvb, g, gtok) t_norm ({lbunivs=uvs;lbname=lbn; lbdef=e}) =

            (* Open universes *)
            let env', e, t_norm =
                let tcenv', _, e_t =
                    Env.open_universes_in env.tcenv uvs [e; t_norm] in
                let e, t_norm =
                    match e_t with
                    | [e; t_norm] -> e, t_norm
                    | _ -> failwith "Impossible" in
                {env with tcenv=tcenv'}, e, t_norm
            in
            if Env.debug env0.tcenv <| Options.Other "SMTEncoding"
            then BU.print3 "Encoding let rec %s : %s = %s\n"
                        (Print.lbname_to_string lbn)
                        (Print.term_to_string t_norm)
                        (Print.term_to_string e);

            (* Open binders *)
            let (binders, body, formals, tres), curry = destruct_bound_function fvb.fvar_lid t_norm e in
            if Env.debug env0.tcenv <| Options.Other "SMTEncoding"
            then BU.print4 "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                              (Print.binders_to_string ", " binders)
                              (Print.term_to_string body)
                              (Print.binders_to_string ", " formals)
                              (Print.term_to_string tres);
            let _ = if curry then failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type" in


            let vars, guards, env', binder_decls, _ = encode_binders None binders env' in
            let decl_g = Term.DeclFun(g, Fuel_sort::List.map snd vars, Term_sort, Some "Fuel-instrumented function name") in
            let env0 = push_zfuel_name env0 fvb.fvar_lid g in
            let decl_g_tok = Term.DeclFun(gtok, [], Term_sort, Some "Token for fuel-instrumented partial applications") in
            let vars_tm = List.map mkFreeV vars in
            let app = mkApp(fvb.smt_id, List.map mkFreeV vars) in
            let gsapp = mkApp(g, mkApp("SFuel", [fuel_tm])::vars_tm) in
            let gmax = mkApp(g, mkApp("MaxFuel", [])::vars_tm) in
            let body = if is_reifiable_function env'.tcenv t_norm then TcUtil.reify_body env'.tcenv body else body in
            let body_tm, decls2 = encode_term body env' in

            //NS 05.25: This used to be  mkImp(mk_and_l guards, mkEq(gsapp, body_tm)
            //But, the pattern ensures that this only applies to well-typed terms
            //NS 08/10: Setting the weight of this quantifier to 0, since its instantiations are controlled by F* fuel
            let eqn_g = Util.mkAssume(mkForall' (U.range_of_lbname lbn) ([[gsapp]], Some 0, fuel::vars, mkEq(gsapp, body_tm)),
                                    Some (BU.format1 "Equation for fuel-instrumented recursive function: %s" fvb.fvar_lid.str),
                                    ("equation_with_fuel_" ^g)) in
            let eqn_f = Util.mkAssume(mkForall (U.range_of_lbname lbn) ([[app]], vars, mkEq(app, gmax)),
                                    Some "Correspondence of recursive function to instrumented version",
                                    ("@fuel_correspondence_"^g)) in
            let eqn_g' = Util.mkAssume(mkForall (U.range_of_lbname lbn) ([[gsapp]], fuel::vars, mkEq(gsapp,  mkApp(g, Term.n_fuel 0::vars_tm))),
                                    Some "Fuel irrelevance",
                                    ("@fuel_irrelevance_" ^g)) in
            let aux_decls, g_typing =
              let vars, v_guards, env, binder_decls, _ = encode_binders None formals env0 in
              let vars_tm = List.map mkFreeV vars in
              let gapp = mkApp(g, fuel_tm::vars_tm) in
              let tok_corr =
                let tok_app = mk_Apply (mkFreeV (gtok, Term_sort)) (fuel::vars) in
                Util.mkAssume(mkForall (U.range_of_lbname lbn) ([[tok_app]], fuel::vars, mkEq(tok_app, gapp)),
                            Some "Fuel token correspondence",
                            ("fuel_token_correspondence_"^gtok))
              in
              let aux_decls, typing_corr =
                let g_typing, d3 = encode_term_pred None tres env gapp in
                d3, [Util.mkAssume(mkForall (U.range_of_lbname lbn) ([[gapp]], fuel::vars, mkImp(mk_and_l v_guards, g_typing)),
                                    Some "Typing correspondence of token to term",
                                    ("token_correspondence_"^g))]
              in
              binder_decls@aux_decls, typing_corr@[tok_corr]
            in

            binder_decls@decls2@aux_decls@[decl_g;decl_g_tok], [eqn_g;eqn_g';eqn_f]@g_typing, env0
          in

          let decls, eqns, env0 = List.fold_left (fun (decls, eqns, env0) (gtok, ty, lb) ->
              let decls', eqns', env0 = encode_one_binding env0 gtok ty lb in
              decls'::decls, eqns'@eqns, env0)
            ([decls], [], env0)
            (List.zip3 gtoks typs bindings)
          in
          (* Function declarations must come first to be defined in all recursive definitions *)
          let prefix_decls, rest =
            let isDeclFun = function | DeclFun _ -> true | _ -> false in
            decls |> List.flatten |> List.partition isDeclFun
          in
          let eqns = List.rev eqns in
          prefix_decls@rest@eqns, env0
        in

        if quals |> BU.for_some (function HasMaskedEffect -> true | _ -> false)
        || typs  |> BU.for_some (fun t -> not <| (U.is_pure_or_ghost_function t ||
                                                  is_reifiable_function env.tcenv t))
        then decls, env_decls
        else
          try
            if not is_rec
            then
              (* Encoding non-recursive definitions *)
              encode_non_rec_lbdef bindings typs toks_fvbs env
            else
              encode_rec_lbdefs bindings typs toks_fvbs env
          with Inner_let_rec -> decls, env_decls  //decls are type declarations for the lets, if there is an inner let rec, only those are encoded to the solver

    with Let_rec_unencodeable ->
      let msg = bindings |> List.map (fun lb -> Print.lbname_to_string lb.lbname) |> String.concat " and " in
      let decl = Caption ("let rec unencodeable: Skipping: " ^msg) in
      [decl], env


let rec encode_sigelt (env:env_t) (se:sigelt) : (decls_t * env_t) =
    let nm =
        match U.lid_of_sigelt se with
        | None -> ""
        | Some l -> l.str in
    let g, env = encode_sigelt' env se in
    let g =
        match g with
         | [] -> [Caption (BU.format1 "<Skipped %s/>" nm)]
         | _ -> Caption (BU.format1 "<Start encoding %s>" nm)
                ::g
                @[Caption (BU.format1 "</end encoding %s>" nm)] in
    g, env

and encode_sigelt' (env:env_t) (se:sigelt) : (decls_t * env_t) =
    let is_opaque_to_smt (t:S.term) =
        match (SS.compress t).n with
        | Tm_constant (Const_string(s, _)) -> s = "opaque_to_smt"
        | _ -> false
    in
    let is_uninterpreted_by_smt (t:S.term) =
        match (SS.compress t).n with
        | Tm_constant (Const_string(s, _)) -> s = "uninterpreted_by_smt"
        | _ -> false
    in
    match se.sigel with
     | Sig_new_effect_for_free _ ->
         failwith "impossible -- new_effect_for_free should have been removed by Tc.fs"
     | Sig_splice _ ->
         failwith "impossible -- splice should have been removed by Tc.fs"
     | Sig_pragma _
     | Sig_main _
     | Sig_effect_abbrev _
     | Sig_sub_effect _ -> [], env

     | Sig_new_effect(ed) ->
       if not (Env.is_reifiable_effect env.tcenv ed.mname)
       then [], env
       else (* The basic idea:
                    1. Encode M.bind_repr: a:Type -> b:Type -> wp_a -> wp_b -> f:st_repr a wp_a -> g:(a -> st_repr b) : st_repr b
                                       = e
                       by encoding a function (erasing type arguments)
                       M.bind_repr (f Term) (g Term) : [[e]]]

                    2. Likewise for M.return_repr

                    3. For each action, a : x1:n -> ... -> xn:tn -> st_repr t wp = fun x1..xn -> e
                        encode forall x1..xn. Reify (Apply a x1 ... xn) = [[e]]
            *)
            let close_effect_params tm =
              match ed.binders with
              | [] -> tm
              | _ -> S.mk (Tm_abs(ed.binders, tm, Some (U.mk_residual_comp Const.effect_Tot_lid None [TOTAL]))) None tm.pos
            in

            let encode_action env (a:S.action) =
              let formals, _ = U.arrow_formals_comp a.action_typ in
              let arity = List.length formals in
              let aname, atok, env = new_term_constant_and_tok_from_lid env a.action_name arity in
              let tm, decls = encode_term (close_effect_params a.action_defn) env in
              let a_decls =
                [Term.DeclFun(aname, formals |> List.map (fun _ -> Term_sort), Term_sort, Some "Action");
                  Term.DeclFun(atok, [], Term_sort, Some "Action token")]
              in
              let _, xs_sorts, xs =
                let aux (bv, _) (env, acc_sorts, acc) =
                  let xxsym, xx, env = gen_term_var env bv in
                  env, (xxsym, Term_sort)::acc_sorts, xx::acc
                in
                List.fold_right aux formals (env, [], [])
              in
              (* let app = mkApp("Reify", [mkApp(aname, xs)]) in *)
              let app = mkApp(aname, xs) in //arity ok; length xs = length formals = arity
              let a_eq =
                Util.mkAssume(mkForall (Ident.range_of_lid a.action_name) ([[app]], xs_sorts, mkEq(app, mk_Apply tm xs_sorts)),
                            Some "Action equality",
                            (aname ^"_equality"))
              in
              let tok_correspondence =
                let tok_term = mkFreeV(atok,Term_sort) in
                let tok_app = mk_Apply tok_term xs_sorts in
                Util.mkAssume(mkForall (Ident.range_of_lid a.action_name) ([[tok_app]], xs_sorts, mkEq(tok_app, app)),
                            Some "Action token correspondence", (aname ^ "_token_correspondence"))
              in
              env, decls@a_decls@[a_eq; tok_correspondence]
            in

            let env, decls2 = BU.fold_map encode_action env ed.actions in
            List.flatten decls2, env

     | Sig_declare_typ(lid, _, _) when (lid_equals lid Const.precedes_lid) ->
        let tname, ttok, env = new_term_constant_and_tok_from_lid env lid 4 in
        [], env

     | Sig_declare_typ(lid, _, t) ->
        let quals = se.sigquals in
        let will_encode_definition = not (quals |> BU.for_some (function
            | Assumption | Projector _ | Discriminator _ | Irreducible -> true
            | _ -> false)) in
        if will_encode_definition
        then [], env //nothing to do at the declaration; wait to encode the definition
        else let fv = S.lid_as_fv lid delta_constant None in
             let decls, env =
               encode_top_level_val
                 (se.sigattrs |> BU.for_some is_uninterpreted_by_smt)
                 env fv t quals in
             let tname = lid.str in
             let tsym = mkFreeV(tname, Term_sort) in
             let pt_axioms, env = primitive_type_axioms env lid tname tsym in
             decls
             @ pt_axioms,
             env

     | Sig_assume(l, us, f) ->
        let uvs, f = SS.open_univ_vars us f in
        let env = { env with tcenv = Env.push_univ_vars env.tcenv uvs } in
        let f = N.normalize [Env.Beta; Env.Eager_unfolding] env.tcenv f in
        let f, decls = encode_formula f env in
        let g = [Util.mkAssume(f, Some (BU.format1 "Assumption: %s" (Print.lid_to_string l)), (varops.mk_unique ("assumption_"^l.str)))] in
        decls@g, env

     | Sig_let(lbs, _)
        when se.sigquals |> List.contains S.Irreducible
          || se.sigattrs |> BU.for_some is_opaque_to_smt ->
       let attrs = se.sigattrs in
       let env, decls = BU.fold_map (fun env lb ->
        let lid = (BU.right lb.lbname).fv_name.v in
        if Option.isNone <| Env.try_lookup_val_decl env.tcenv lid
        then let val_decl = { se with sigel = Sig_declare_typ(lid, lb.lbunivs, lb.lbtyp);
                                      sigquals = S.Irreducible :: se.sigquals } in
             let decls, env = encode_sigelt' env val_decl in
             env, decls
        else env, []) env (snd lbs) in
       List.flatten decls, env

     | Sig_let((_, [{lbname=BU.Inr b2t}]), _) when S.fv_eq_lid b2t Const.b2t_lid ->
       let tname, ttok, env = new_term_constant_and_tok_from_lid env b2t.fv_name.v 1 in
       let xx = ("x", Term_sort) in
       let x = mkFreeV xx in
       let b2t_x = mkApp("Prims.b2t", [x]) in
       let valid_b2t_x = mkApp("Valid", [b2t_x]) in //NS: Explicitly avoid the Vaild(b2t t) inlining
       let decls = [Term.DeclFun(tname, [Term_sort], Term_sort, None);
                    Util.mkAssume(mkForall (S.range_of_fv b2t) ([[b2t_x]], [xx],
                                           mkEq(valid_b2t_x, mkApp(snd boxBoolFun, [x]))),
                                Some "b2t def",
                                "b2t_def")] in
       decls, env

    | Sig_let(_, _) when (se.sigquals |> BU.for_some (function Discriminator _ -> true | _ -> false)) ->
      //Discriminators are encoded directly via (our encoding of) theory of datatypes
      [], env

    | Sig_let(_, lids) when (lids |> BU.for_some (fun (l:lident) -> (List.hd l.ns).idText = "Prims")
                             && se.sigquals |> BU.for_some (function Unfold_for_unification_and_vcgen -> true | _ -> false)) ->
        //inline lets from prims are never encoded as definitions --- since they will be inlined
      [], env

    | Sig_let((false, [lb]), _)
         when (se.sigquals |> BU.for_some (function Projector _ -> true | _ -> false)) ->
     //Projectors are also are encoded directly via (our encoding of) theory of datatypes
     //Except in some cases where the front-end does not emit a declare_typ for some projector, because it doesn't know how to compute it
     let fv = BU.right lb.lbname in
     let l = fv.fv_name.v in
     begin match try_lookup_free_var env l with
        | Some _ ->
          [], env //already encoded
        | None ->
          let se = {se with sigel = Sig_declare_typ(l, lb.lbunivs, lb.lbtyp); sigrng = Ident.range_of_lid l } in
          encode_sigelt env se
     end

    | Sig_let((is_rec, bindings), _) ->
      encode_top_level_let env (is_rec, bindings) se.sigquals

    | Sig_bundle(ses, _) ->
       let g, env = encode_sigelts env ses in
       let g', inversions = g |> List.partition (function
        | Term.Assume({assumption_caption=Some "inversion axiom"}) -> false
        | _ -> true) in
       let decls, rest = g' |> List.partition (function
        | Term.DeclFun _ -> true
        | _ -> false) in
       decls@rest@inversions, env

     | Sig_inductive_typ(t, _, tps, k, _, datas) ->
        let quals = se.sigquals in
        let is_logical = quals |> BU.for_some (function Logic | Assumption -> true | _ -> false) in
        let constructor_or_logic_type_decl (c:constructor_t) =
            if is_logical
            then let name, args, _, _, _ = c in
                 [Term.DeclFun(name, args |> List.map (fun (_, sort, _) -> sort), Term_sort, None)]
            else constructor_to_decl (Ident.range_of_lid t) c in

        let inversion_axioms tapp vars =
            if datas |> BU.for_some (fun l -> Env.try_lookup_lid env.tcenv l |> Option.isNone) //Q: Why would this happen?
            then []
            else
                 let xxsym, xx = fresh_fvar "x" Term_sort in
                 let data_ax, decls = datas |> List.fold_left (fun (out, decls) l ->
                    let _, data_t = Env.lookup_datacon env.tcenv l in
                    let args, res = U.arrow_formals data_t in
                    let indices = match (SS.compress res).n with
                        | Tm_app(_, indices) -> indices
                        | _ -> [] in
                    let env = args |> List.fold_left
                        (fun env (x, _) -> push_term_var env x (mkApp(mk_term_projector_name l x, [xx])))
                        env in
                    let indices, decls' = encode_args indices env in
                    if List.length indices <> List.length vars
                    then failwith "Impossible";
                    let eqs = List.map2 (fun v a -> mkEq(mkFreeV v, a)) vars indices |> mk_and_l in
                    mkOr(out, mkAnd(mk_data_tester env l xx, eqs)), decls@decls') (mkFalse, []) in
                let ffsym, ff = fresh_fvar "f" Fuel_sort in
                let fuel_guarded_inversion =
                    let xx_has_type_sfuel =
                        if List.length datas > 1
                        then mk_HasTypeFuel (mkApp("SFuel", [ff])) xx tapp
                        else mk_HasTypeFuel ff xx tapp in //no point requiring non-zero fuel if there are no disjunctions
                    Util.mkAssume(mkForall (Ident.range_of_lid t) ([[xx_has_type_sfuel]], add_fuel (ffsym, Fuel_sort) ((xxsym, Term_sort)::vars),
                                        mkImp(xx_has_type_sfuel, data_ax)),
                                Some "inversion axiom", //this name matters! see Sig_bundle case near line 1493
                                (varops.mk_unique ("fuel_guarded_inversion_"^t.str))) in
                decls
                @[fuel_guarded_inversion] in

        let formals, res = match (SS.compress k).n with
                | Tm_arrow(formals, kres) ->
                  tps@formals, U.comp_result kres
                | _ ->
                  tps, k in

        let formals, res = SS.open_term formals res in
        let vars, guards, env', binder_decls, _ = encode_binders None formals env in
        let arity = List.length vars in
        let tname, ttok, env = new_term_constant_and_tok_from_lid env t arity in
        let ttok_tm = mkApp(ttok, []) in
        let guard = mk_and_l guards in
        let tapp = mkApp(tname, List.map mkFreeV vars) in //arity ok
        let decls, env =
            //See: https://github.com/FStarLang/FStar/commit/b75225bfbe427c8aef5b59f70ff6d79aa014f0b4
            //See: https://github.com/FStarLang/FStar/issues/349
            let tname_decl = constructor_or_logic_type_decl (tname,
                                                             vars |> List.map (fun (n, s) -> (tname^n,s,false)), //The false here is extremely important; it makes sure that type-formers are not injective
                                                             Term_sort,
                                                             varops.next_id(),
                                                             false) in
            let tok_decls, env =
                match vars with
                | [] -> [], push_free_var env t arity tname (Some <| mkApp(tname, []))
                | _ ->
                        let ttok_decl = Term.DeclFun(ttok, [], Term_sort, Some "token") in
                        let ttok_fresh = Term.fresh_token (ttok, Term_sort) (varops.next_id()) in
                        let ttok_app = mk_Apply ttok_tm vars in
                        let pats = [[ttok_app]; [tapp]] in
                        // These patterns allow rewriting (ApplyT T@tok args) to (T args) and vice versa
                        // This seems necessary for some proofs, but the bidirectional rewriting may be inefficient
                        let name_tok_corr = Util.mkAssume(mkForall' (Ident.range_of_lid t) (pats, None, vars, mkEq(ttok_app, tapp)),
                                                        Some "name-token correspondence",
                                                        ("token_correspondence_"^ttok)) in
                        [ttok_decl; ttok_fresh; name_tok_corr], env in
            if lid_equals t Const.lex_t_lid then tok_decls, env  //AR: for lex_t, we add the declaration in the prelude itself
            else tname_decl@tok_decls, env in
        let kindingAx =
            let k, decls = encode_term_pred None res env' tapp in
            let karr =
                if List.length formals > 0
                then [Util.mkAssume(mk_tester "Tm_arrow" (mk_PreType ttok_tm), Some "kinding", ("pre_kinding_"^ttok))]
                else [] in
            decls@karr@[Util.mkAssume(mkForall (Ident.range_of_lid t) ([[tapp]], vars, mkImp(guard, k)), None, ("kinding_"^ttok))] in
        let aux =
            kindingAx
            @(inversion_axioms tapp vars)
            @[pretype_axiom (Ident.range_of_lid t) env tapp vars] in

        let g = decls
                @binder_decls
                @aux in
        g, env

    | Sig_datacon(d, _, _, _, _, _) when (lid_equals d Const.lexcons_lid) -> [], env

    | Sig_datacon(d, _, t, _, n_tps, _) ->
        let quals = se.sigquals in
        let formals, t_res = U.arrow_formals t in
        let arity = List.length formals in
        let ddconstrsym, ddtok, env = new_term_constant_and_tok_from_lid env d arity in
        let ddtok_tm = mkApp(ddtok, []) in
        let fuel_var, fuel_tm = fresh_fvar "f" Fuel_sort in
        let s_fuel_tm = mkApp("SFuel", [fuel_tm]) in
        let vars, guards, env', binder_decls, names = encode_binders (Some fuel_tm) formals env in
        let fields = names |> List.mapi (fun n x ->
            let projectible = true in
//            let projectible = n >= n_tps in //Note: the type parameters are not projectible,
                                            //i.e., (MkTuple2 int bool 0 false) is only injective in its last two arguments
                                            //This allows the term to both have type (int * bool)
                                            //as well as (nat * bool), without leading us to conclude that int=nat
                                            //Also see https://github.com/FStarLang/FStar/issues/349
            mk_term_projector_name d x, Term_sort, projectible) in
        let datacons = (ddconstrsym, fields, Term_sort, varops.next_id(), true) |> Term.constructor_to_decl (Ident.range_of_lid d) in
        let app = mk_Apply ddtok_tm vars in
        let guard = mk_and_l guards in
        let xvars = List.map mkFreeV vars in
        let dapp =  mkApp(ddconstrsym, xvars) in //arity ok; |xvars| = |formals| = arity

        let tok_typing, decls3 = encode_term_pred None t env ddtok_tm in
        let tok_typing =
             match fields with
             | _::_ ->
               let ff = ("ty", Term_sort) in
               let f = mkFreeV ff in
               let vtok_app_l = mk_Apply ddtok_tm [ff] in
               let vtok_app_r = mk_Apply f [(ddtok, Term_sort)] in
                //guard the token typing assumption with a Apply(tok, f) or Apply(f, tok)
                //Additionally, the body of the term becomes NoHoist f (HasType tok ...)
                //   to prevent the Z3 simplifier from hoisting the (HasType tok ...) part out
                //Since the top-levels of modules are full of function typed terms
                //not guarding it this way causes every typing assumption of an arrow type to be fired immediately
                //regardless of whether or not the function is used ... leading to bloat
                //these patterns aim to restrict the use of the typing assumption until such point as it is actually needed
               mkForall (Ident.range_of_lid d)
                        ([[vtok_app_l]; [vtok_app_r]],
                        [ff],
                        Term.mk_NoHoist f tok_typing)
             | _ -> tok_typing in
        let vars', guards', env'', decls_formals, _ = encode_binders (Some fuel_tm) formals env in //NS/CH: used to be s_fuel_tm
        let ty_pred', decls_pred =
             let xvars = List.map mkFreeV vars' in
             let dapp =  mkApp(ddconstrsym, xvars) in //arity ok; |xvars| = |formals| = arity
             encode_term_pred (Some fuel_tm) t_res env'' dapp in
        let guard' = mk_and_l guards' in
        let proxy_fresh = match formals with
            | [] -> []
            | _ -> [Term.fresh_token (ddtok, Term_sort) (varops.next_id())] in

        let encode_elim () =
            let head, args = U.head_and_args t_res in
            match (SS.compress head).n with
                | Tm_uinst({n=Tm_fvar fv}, _)
                | Tm_fvar fv ->
                  let encoded_head, encoded_head_arity = lookup_free_var_name env' fv.fv_name in
                  let encoded_args, arg_decls = encode_args args env' in
                  let guards_for_parameter (orig_arg:S.term)(arg:term) xv =
                    let fv =
                      match arg.tm with
                      | FreeV fv -> fv
                      | _ ->
                         Errors.raise_error (Errors.Fatal_NonVariableInductiveTypeParameter,
                           BU.format1 "Inductive type parameter %s must be a variable ; \
                                       You may want to change it to an index."
                                      (FStar.Syntax.Print.term_to_string orig_arg)) orig_arg.pos
                    in
                    let guards = guards |> List.collect (fun g ->
                        if List.contains fv (Term.free_variables g)
                        then [Term.subst g fv xv]
                        else [])
                    in
                    mk_and_l guards
                  in
                  let _, arg_vars, elim_eqns_or_guards, _ =
                    List.fold_left (fun (env, arg_vars, eqns_or_guards, i) (orig_arg, arg) ->
                      let _, xv, env = gen_term_var env (S.new_bv None tun) in
                      (* we only get equations induced on the type indices, not parameters; *)
                      (* Also see https://github.com/FStarLang/FStar/issues/349 *)
                      let eqns =
                        if i < n_tps
                        then guards_for_parameter (fst orig_arg) arg xv::eqns_or_guards
                        else mkEq(arg, xv)::eqns_or_guards
                      in
                      (env, xv::arg_vars, eqns, i + 1))
                      (env', [], [], 0) (FStar.List.zip args encoded_args)
                  in
                  let arg_vars = List.rev arg_vars in
                  let ty = maybe_curry_app fv.fv_name.p (Var encoded_head) encoded_head_arity arg_vars in
                  let xvars = List.map mkFreeV vars in
                  let dapp =  mkApp(ddconstrsym, xvars) in //arity ok; |xvars| = |formals| = arity
                  let ty_pred = mk_HasTypeWithFuel (Some s_fuel_tm) dapp ty in
                  let arg_binders = List.map fv_of_term arg_vars in
                  let typing_inversion =
                    Util.mkAssume(mkForall (Ident.range_of_lid d) ([[ty_pred]],
                                        add_fuel (fuel_var, Fuel_sort) (vars@arg_binders),
                                        mkImp(ty_pred, mk_and_l (elim_eqns_or_guards@guards))),
                               Some "data constructor typing elim",
                               ("data_elim_" ^ ddconstrsym)) in
                  let subterm_ordering =
                    let lex_t = mkFreeV (text_of_lid Const.lex_t_lid, Term_sort) in
                    if lid_equals d Const.lextop_lid
                    then let x = varops.fresh "x", Term_sort in
                         let xtm = mkFreeV x in
                         Util.mkAssume(mkForall (Ident.range_of_lid d)
                                                ([[mk_Precedes lex_t lex_t xtm dapp]], [x], mkImp(mk_tester "LexCons" xtm, mk_Precedes lex_t lex_t xtm dapp)),
                                     Some "lextop is top",
                                     (varops.mk_unique "lextop"))
                    else (* subterm ordering *)
                      let prec =
                        vars
                          |> List.mapi (fun i v ->
                                (* it's a parameter, so it's inaccessible and no need for a sub-term ordering on it *)
                                if i < n_tps
                                then []
                                else [mk_Precedes lex_t lex_t (mkFreeV v) dapp])
                          |> List.flatten
                      in
                      Util.mkAssume(mkForall (Ident.range_of_lid d)
                                             ([[ty_pred]], add_fuel (fuel_var, Fuel_sort) (vars@arg_binders), mkImp(ty_pred, mk_and_l prec)),
                                    Some "subterm ordering",
                                    ("subterm_ordering_"^ddconstrsym))
                  in
                  arg_decls, [typing_inversion; subterm_ordering]

                | _ ->
                  Errors.log_issue se.sigrng (Errors.Warning_ConstructorBuildsUnexpectedType, (BU.format2 "Constructor %s builds an unexpected type %s\n"
                        (Print.lid_to_string d) (Print.term_to_string head)));
                  [], [] in
        let decls2, elim = encode_elim () in
        let g = binder_decls
                @decls2
                @decls3
                @[Term.DeclFun(ddtok, [], Term_sort, Some (BU.format1 "data constructor proxy: %s" (Print.lid_to_string d)))]
                @proxy_fresh
                @decls_formals
                @decls_pred
                @[Util.mkAssume(tok_typing, Some "typing for data constructor proxy", ("typing_tok_"^ddtok));
                  Util.mkAssume(mkForall (Ident.range_of_lid d)
                                         ([[app]], vars,
                                          mkEq(app, dapp)), Some "equality for proxy", ("equality_tok_"^ddtok));
                  Util.mkAssume(mkForall (Ident.range_of_lid d)
                                         ([[ty_pred']],add_fuel (fuel_var, Fuel_sort) vars', mkImp(guard', ty_pred')),
                              Some "data constructor typing intro",
                              ("data_typing_intro_"^ddtok));
                  ]
                @elim in
        datacons@g, env

and encode_sigelts env ses =
    ses |> List.fold_left (fun (g, env) se ->
      let g', env = encode_sigelt env se in
      g@g', env) ([], env)


let encode_env_bindings (env:env_t) (bindings:list<S.binding>) : (decls_t * env_t) =
     (* Encoding Binding_var and Binding_typ as local constants leads to breakages in hash consing.

               Consider:

                type t
                type Good : nat -> Type
                type s (ps:nat) = m:t{Good ps}
                let f (ps':nat) (pi:(s ps' * unit))  =  e

               When encoding a goal formula derived from e, ps' and pi are Binding_var in the environment.
               They get encoded to constants, declare-fun ps', pi etc.
               Now, when encoding the type of pi, we encode the (s ps') as a refinement type (m:t{Good ps'}).
               So far so good.
               But, the trouble is that since ps' is a constant, we build a formula for the refinement type that does not
               close over ps'---constants are not subject to closure.
               So, we get a formula that is syntactically different than what we get when encoding the type s, where (ps:nat) is
               a locally bound free variable and _is_ subject to closure.
               The syntactic difference leads to the hash consing lookup failing.

               So:
                  Instead of encoding Binding_vars as declare-funs, we can try to close the query formula over the vars in the context,
                  thus demoting them to free variables subject to closure.

    *)
    let encode_binding b (i, decls, env) = match b with
        | S.Binding_univ _ ->
          i+1, decls, env

        | S.Binding_var x ->
            let t1 = N.normalize [Env.Beta; Env.Eager_unfolding; Env.Simplify; Env.Primops; Env.EraseUniverses] env.tcenv x.sort in
            if Env.debug env.tcenv <| Options.Other "SMTEncoding"
            then (BU.print3 "Normalized %s : %s to %s\n" (Print.bv_to_string x) (Print.term_to_string x.sort) (Print.term_to_string t1));
            let t, decls' = encode_term t1 env in
            let t_hash = Term.hash_of_term t in
            let xxsym, xx, env' =
                new_term_constant_from_string env x
                    ("x_" ^ BU.digest_of_string t_hash ^ "_" ^ (string_of_int i)) in
            let t = mk_HasTypeWithFuel None xx t in
            let caption =
                if Options.log_queries()
                then Some (BU.format3 "%s : %s (%s)" (Print.bv_to_string x) (Print.term_to_string x.sort) (Print.term_to_string t1))
                else None in
            let ax =
                let a_name = ("binder_"^xxsym) in
                Util.mkAssume(t, Some a_name, a_name) in
            let g = [Term.DeclFun(xxsym, [], Term_sort, caption)]
                    @decls'
                    @[ax] in
            i+1, decls@g, env'

        | S.Binding_lid(x, (_, t)) ->
            let t_norm = whnf env t in
            let fv = S.lid_as_fv x delta_constant None in
//            Printf.printf "Encoding %s at type %s\n" (Print.lid_to_string x) (Print.term_to_string t);
            let g, env' = encode_free_var false env fv t t_norm [] in
            i+1, decls@g, env'
    in
    let _, decls, env = List.fold_right encode_binding bindings (0, [], env) in
    decls, env

let encode_labels labs =
    let prefix = labs |> List.map (fun (l, _, _) -> Term.DeclFun(fst l, [], Bool_sort, None)) in
    let suffix = labs |> List.collect (fun (l, _, _) -> [Echo <| fst l; Eval (mkFreeV l)]) in
    prefix, suffix

(* caching encodings of the environment and the top-level API to the encoding *)
let last_env : ref<list<env_t>> = BU.mk_ref []
let init_env tcenv = last_env := [{bvar_bindings=BU.psmap_empty ();
                                   fvar_bindings=BU.psmap_empty ();
                                   tcenv=tcenv; warn=true; depth=0;
                                   cache=BU.smap_create 100; nolabels=false; use_zfuel_name=false;
                                   encode_non_total_function_typ=true; encoding_quantifier=false;
                                   current_module_name=Env.current_module tcenv |> Ident.string_of_lid}]
let get_env cmn tcenv = match !last_env with
    | [] -> failwith "No env; call init first!"
    | e::_ -> {e with tcenv=tcenv; current_module_name=Ident.string_of_lid cmn}
let set_env env = match !last_env with
    | [] -> failwith "Empty env stack"
    | _::tl -> last_env := env::tl

let push_env () = match !last_env with
    | [] -> failwith "Empty env stack"
    | hd::tl ->
      let top = copy_env hd in
      last_env := top::hd::tl
let pop_env () = match !last_env with
    | [] -> failwith "Popping an empty stack"
    | _::tl -> last_env := tl
let snapshot_env () = FStar.Common.snapshot push_env last_env ()
let rollback_env depth = FStar.Common.rollback pop_env last_env depth
(* TOP-LEVEL API *)

let init tcenv =
    init_env tcenv;
    Z3.init ();
    Z3.giveZ3 [DefPrelude]
let snapshot msg = BU.atomically (fun () ->
    let env_depth, () = snapshot_env () in
    let varops_depth, () = varops.snapshot () in
    let z3_depth, () = Z3.snapshot msg in
    (env_depth, varops_depth, z3_depth), ())
let rollback msg depth = BU.atomically (fun () ->
    let env_depth, varops_depth, z3_depth = match depth with
        | Some (s1, s2, s3) -> Some s1, Some s2, Some s3
        | None -> None, None, None in
    rollback_env env_depth;
    varops.rollback varops_depth;
    Z3.rollback msg z3_depth)
let push msg = snd (snapshot msg)
let pop msg = ignore (rollback msg None)

//////////////////////////////////////////////////////////////////////////
//guarding top-level terms with fact database triggers
//////////////////////////////////////////////////////////////////////////
let open_fact_db_tags (env:env_t) : list<fact_db_id> = [] //TODO

let place_decl_in_fact_dbs (env:env_t) (fact_db_ids:list<fact_db_id>) (d:decl) : decl =
    match fact_db_ids, d with
    | _::_, Assume a ->
      Assume ({a with assumption_fact_ids=fact_db_ids})
    | _ -> d

let fact_dbs_for_lid (env:env_t) (lid:Ident.lid) =
    Name lid
    ::Namespace (Ident.lid_of_ids lid.ns)
    ::open_fact_db_tags env

let encode_top_level_facts (env:env_t) (se:sigelt) =
    let fact_db_ids =
        U.lids_of_sigelt se |> List.collect (fact_dbs_for_lid env)
    in
    let g, env = encode_sigelt env se in
    let g = g |> List.map (place_decl_in_fact_dbs env fact_db_ids) in
    g, env
//////////////////////////////////////////////////////////////////////////
//end: guarding top-level terms with fact database triggers
//////////////////////////////////////////////////////////////////////////

let encode_sig tcenv se =
   let caption decls =
    if Options.log_queries()
    then Term.Caption ("encoding sigelt " ^ (U.lids_of_sigelt se |> List.map Print.lid_to_string |> String.concat ", "))::decls
    else decls in
   if Env.debug tcenv Options.Low
   then BU.print1 "+++++++++++Encoding sigelt %s\n" (Print.sigelt_to_string se);
   let env = get_env (Env.current_module tcenv) tcenv in
   let decls, env = encode_top_level_facts env se in
   set_env env;
   Z3.giveZ3 (caption decls)

let encode_modul tcenv modul =
    if Options.lax() && Options.ml_ish() then () else
    let name = BU.format2 "%s %s" (if modul.is_interface then "interface" else "module")  modul.name.str in
    if Env.debug tcenv Options.Low
    then BU.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name (List.length modul.exports |> string_of_int);
    let env = get_env modul.name tcenv in
    let encode_signature (env:env_t) (ses:sigelts) =
        ses |> List.fold_left (fun (g, env) se ->
          let g', env = encode_top_level_facts env se in
          g@g', env) ([], env)
    in
    let decls, env = encode_signature ({env with warn=false}) modul.exports in
    let caption decls =
    if Options.log_queries()
    then let msg = "Externals for " ^ name in
         [Module(name, Caption msg::decls@[Caption ("End " ^ msg)])]
    else decls in
    set_env ({env with warn=true});
    if Env.debug tcenv Options.Low then BU.print1 "Done encoding externals for %s\n" name;
    let decls = caption decls in
    Z3.giveZ3 decls

open FStar.SMTEncoding.Z3
let encode_query use_env_msg tcenv q
  : list<decl>  //prelude, translation of tcenv
  * list<ErrorReporting.label> //labels in the query
  * decl        //the query itself
  * list<decl>  //suffix, evaluating labels in the model, etc.
  = Z3.query_logging.set_module_name (TypeChecker.Env.current_module tcenv).str;
    let env = get_env (Env.current_module tcenv) tcenv in
    let q, bindings =
        let rec aux bindings = match bindings with
            | S.Binding_var x::rest ->
                let out, rest = aux rest in
                let t =
                    match (FStar.Syntax.Util.destruct_typ_as_formula x.sort) with
                    | Some _ ->
                      U.refine (S.new_bv None t_unit) x.sort
                      //add a squash to trigger the shallow embedding,
                      //if the assumption is of the form x:(forall y. P) etc.
                    | _ ->
                      x.sort in
                let t = N.normalize [Env.Eager_unfolding; Env.Beta; Env.Simplify; Env.Primops; Env.EraseUniverses] env.tcenv t in
                Syntax.mk_binder ({x with sort=t})::out, rest
            | _ -> [], bindings in
        let closing, bindings = aux tcenv.gamma in
        U.close_forall_no_univs (List.rev closing) q, bindings
    in
    let env_decls, env = encode_env_bindings env bindings in
    if debug tcenv Options.Low
    || debug tcenv <| Options.Other "SMTEncoding"
    || debug tcenv <| Options.Other "SMTQuery"
    then BU.print1 "Encoding query formula: %s\n" (Print.term_to_string q);
    let phi, qdecls = encode_formula q env in
    let labels, phi = ErrorReporting.label_goals use_env_msg (Env.get_range tcenv) phi in
    let label_prefix, label_suffix = encode_labels labels in
    let caption =
        if Options.log_queries ()
        then [Caption ("Encoding query formula: " ^ (Print.term_to_string q))]
        else []
    in
    let query_prelude =
        env_decls
        @label_prefix
        @qdecls
        @caption in
    let qry = Util.mkAssume(mkNot phi, Some "query", (varops.mk_unique "@query")) in
    let suffix = [Term.Echo "<labels>"] @ label_suffix @ [Term.Echo "</labels>"; Term.Echo "Done!"] in
    query_prelude, labels, qry, suffix
