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
module FStarC.SMTEncoding.Encode
open FStarC.Effect
open FStarC.List
open FStarC
open FStarC.TypeChecker.Env
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.TypeChecker
open FStarC.SMTEncoding.Term
open FStarC.Ident
open FStarC.Const
open FStarC.SMTEncoding
open FStarC.SMTEncoding.Util
open FStarC.SMTEncoding.Env
open FStarC.SMTEncoding.EncodeTerm
open FStarC.Class.Show

module BU     = FStarC.Util
module Const  = FStarC.Parser.Const
module Env    = FStarC.TypeChecker.Env
module N      = FStarC.TypeChecker.Normalize
module S      = FStarC.Syntax.Syntax
module SS     = FStarC.Syntax.Subst
module TcUtil = FStarC.TypeChecker.Util
module UF     = FStarC.Syntax.Unionfind
module U      = FStarC.Syntax.Util
module TEQ    = FStarC.TypeChecker.TermEqAndSimplify

let dbg_SMTEncoding = Debug.get_toggle "SMTEncoding"
let dbg_SMTQuery    = Debug.get_toggle "SMTQuery"
let dbg_Time        = Debug.get_toggle "Time"

let norm_before_encoding env t =
    let steps = [Env.Eager_unfolding;
                 Env.Simplify;
                 Env.Primops;
                 Env.Exclude Env.Zeta] in
    Profiling.profile
      (fun () -> N.normalize steps env.tcenv t)
      (Some (Ident.string_of_lid (Env.current_module env.tcenv)))
      "FStarC.SMTEncoding.Encode.norm_before_encoding"

let norm_before_encoding_us env us (t:S.term) =
  let env_u = {env with tcenv = Env.push_univ_vars env.tcenv us} in
  let us, t = SS.open_univ_vars us t in
  let t = norm_before_encoding env_u t in
  SS.close_univ_vars us t

let norm_with_steps steps env t =
  Profiling.profile
      (fun () -> N.normalize steps env t)
      (Some (Ident.string_of_lid (Env.current_module env)))
      "FStarC.SMTEncoding.Encode.norm"

type prims_t = {
    mk:lident -> string -> term & int & list decl;
    is:lident -> bool;
}

(* Only for the definitions of prims below *)
type defn_rel_type = | Eq | ValidIff
let rel_type_f = function
  | Eq -> mkEq
  | ValidIff -> fun (x, y) ->
    mkEq (mk_Valid x, y)

let prims =
    let module_name = "Prims" in
    let asym, a = fresh_fvar module_name "a" Term_sort in
    let xsym, x = fresh_fvar module_name "x" Term_sort in
    let ysym, y = fresh_fvar module_name "y" Term_sort in
    let quant_with_pre (rel:defn_rel_type) vars precondition body : Range.t -> string -> term & int & list decl = fun rng x ->
        let xname_decl = Term.DeclFun(x, vars |> List.map fv_sort, Term_sort, None) in
        let xtok = x ^ "@tok" in
        let xtok_decl = Term.DeclFun(xtok, [], Term_sort, None) in
        let xapp = mkApp(x, List.map mkFreeV vars) in //arity ok, see decl (#1383)
        let xtok = mkApp(xtok, []) in //arity ok, see decl (#1383)
        let xtok_app = mk_Apply xtok vars in

        (*
         * AR: adding IsTotFun axioms for the symbol itself, and its partial applications
         *     NOTE: there are no typing guards here, but then there are no typing guards in
         *           any of the other axioms too
         *)
        let tot_fun_axioms =
          let all_vars_but_one = BU.prefix vars |> fst in
          let axiom_name = "primitive_tot_fun_" ^ x in
          //IsTotFun axiom for the symbol itself
          let tot_fun_axiom_for_x = Util.mkAssume (mk_IsTotFun xtok, None, axiom_name) in
          let axioms, _, _ =  //collect other axioms for partial applications
            List.fold_left (fun (axioms, app, vars) var ->
              let app = mk_Apply app [var] in
              let vars = vars @ [var] in
              let axiom_name = axiom_name ^ "." ^ (show (vars |> List.length)) in
              Util.mkAssume (mkForall rng ([[app]], vars, mk_IsTotFun app), None, axiom_name) :: axioms,
              app,
              vars
            ) ([tot_fun_axiom_for_x], xtok, []) all_vars_but_one
          in
          List.rev axioms
        in

        let rel_body =
          let rel_body = (rel_type_f rel) (xapp, body) in
          match precondition with
          | None -> rel_body
          | Some pre -> mkImp(pre, rel_body)
        in

        xtok,
        List.length vars,
        ([xname_decl;
          xtok_decl;
          Util.mkAssume(mkForall rng ([[xapp]], vars, rel_body), None, "primitive_" ^x)] @
         tot_fun_axioms @
         [Util.mkAssume(mkForall rng ([[xtok_app]],
                        vars,
                        mkEq(xtok_app, xapp)),
                        Some "Name-token correspondence",
                        "token_correspondence_"^x)])
    in
    let quant rel vars body = quant_with_pre rel vars None body in
    let axy = List.map mk_fv [(asym, Term_sort); (xsym, Term_sort); (ysym, Term_sort)] in
    let xy = List.map mk_fv [(xsym, Term_sort); (ysym, Term_sort)] in
    let qx = List.map mk_fv [(xsym, Term_sort)] in
    let prims = [
        //equality
        (Const.op_Eq,          (quant Eq axy (boxBool <| mkEq(x,y))));
        (Const.op_notEq,       (quant Eq axy (boxBool <| mkNot(mkEq(x,y)))));
        //boolean ops
        (Const.op_And,         (quant Eq xy  (boxBool <| mkAnd(unboxBool x, unboxBool y))));
        (Const.op_Or,          (quant Eq xy  (boxBool <| mkOr(unboxBool x, unboxBool y))));
        (Const.op_Negation,    (quant Eq qx  (boxBool <| mkNot(unboxBool x))));
        //integer ops
        (Const.op_LT,          (quant Eq xy  (boxBool <| mkLT(unboxInt x, unboxInt y))));
        (Const.op_LTE,         (quant Eq xy  (boxBool <| mkLTE(unboxInt x, unboxInt y))));
        (Const.op_GT,          (quant Eq xy  (boxBool <| mkGT(unboxInt x, unboxInt y))));
        (Const.op_GTE,         (quant Eq xy  (boxBool <| mkGTE(unboxInt x, unboxInt y))));
        (Const.op_Subtraction, (quant Eq xy  (boxInt  <| mkSub(unboxInt x, unboxInt y))));
        (Const.op_Minus,       (quant Eq qx  (boxInt  <| mkMinus(unboxInt x))));
        (Const.op_Addition,    (quant Eq xy  (boxInt  <| mkAdd(unboxInt x, unboxInt y))));
        (Const.op_Multiply,    (quant Eq xy  (boxInt  <| mkMul(unboxInt x, unboxInt y))));
        (Const.op_Division,    (quant_with_pre Eq xy (Some (mkNot (mkEq (unboxInt y, mkInteger "0")))) (boxInt  <| mkDiv(unboxInt x, unboxInt y))));
        (Const.op_Modulus,     (quant_with_pre Eq xy (Some (mkNot (mkEq (unboxInt y, mkInteger "0")))) (boxInt  <| mkMod(unboxInt x, unboxInt y))));
        //real ops
        (Const.real_op_LT,          (quant ValidIff xy  (mkLT(unboxReal x, unboxReal y))));
        (Const.real_op_LTE,         (quant ValidIff xy  (mkLTE(unboxReal x, unboxReal y))));
        (Const.real_op_GT,          (quant ValidIff xy  (mkGT(unboxReal x, unboxReal y))));
        (Const.real_op_GTE,         (quant ValidIff xy  (mkGTE(unboxReal x, unboxReal y))));
        (Const.real_op_Subtraction, (quant Eq xy  (boxReal <| mkSub(unboxReal x, unboxReal y))));
        (Const.real_op_Addition,    (quant Eq xy  (boxReal <| mkAdd(unboxReal x, unboxReal y))));
        (Const.real_op_Multiply,    (quant Eq xy  (boxReal <| mkMul(unboxReal x, unboxReal y))));
        (Const.real_op_Division,    (quant_with_pre Eq xy (Some (mkNot (mkEq (unboxReal y, mkReal "0")))) (boxReal <| mkRealDiv(unboxReal x, unboxReal y))));
        (Const.real_of_int,         (quant Eq qx  (boxReal <| mkRealOfInt (unboxInt x) Range.dummyRange)))
        ]
    in
    let mk : lident -> string -> term & int & list decl =
        fun l v ->
            prims |>
            List.find (fun (l', _) -> lid_equals l l') |>
            Option.map (fun (_, b) -> b (Ident.range_of_lid l) v) |>
            Option.must in
    let is : lident -> bool =
        fun l -> prims |> BU.for_some (fun (l', _) -> lid_equals l l') in
    {mk=mk;
     is=is}

let pretype_axiom term_constr_eq rng env tapp vars =
    let xxsym, xx = fresh_fvar env.current_module_name "x" Term_sort in
    let ffsym, ff = fresh_fvar env.current_module_name "f" Fuel_sort in
    let xx_has_type = mk_HasTypeFuel ff xx tapp in
    let tapp_hash = Term.hash_of_term tapp in
    let module_name = env.current_module_name in
    Util.mkAssume(mkForall rng ([[xx_has_type]], mk_fv (xxsym, Term_sort)::mk_fv (ffsym, Fuel_sort)::vars,
                                mkImp(xx_has_type, 
                                     (if term_constr_eq
                                      then mkEq(mkApp ("Term_constr_id", [tapp]), 
                                                mkApp ("Term_constr_id", [mkApp("PreType", [xx])]))
                                      else mkEq(tapp, 
                                                mkApp("PreType", [xx]))))),
                         Some "pretyping",
                         (varops.mk_unique (module_name ^ "_pretyping_" ^ (BU.digest_of_string tapp_hash))))

let primitive_type_axioms : env -> lident -> string -> term -> list decl =
    let xx = mk_fv ("x", Term_sort) in
    let x = mkFreeV xx in

    let yy = mk_fv ("y", Term_sort) in
    let y = mkFreeV yy in

    let mkForall_fuel env = mkForall_fuel (Ident.string_of_lid (Env.current_module env)) in

    let mk_unit : env -> string -> term -> list decl = fun env nm tt ->
        let typing_pred = mk_HasType x tt in
        [Util.mkAssume(mk_HasType mk_Term_unit tt, Some "unit typing", "unit_typing");
         Util.mkAssume(mkForall_fuel env (Env.get_range env)
                                     ([[typing_pred]], [xx], mkImp(typing_pred, mkEq(x, mk_Term_unit))),  Some "unit inversion", "unit_inversion");] in
    let mk_bool : env -> string -> term -> list decl = fun env nm tt ->
        let typing_pred = mk_HasType x tt in
        let bb = mk_fv ("b", Bool_sort) in
        let b = mkFreeV bb in
        [Util.mkAssume(mkForall (Env.get_range env)
                                ([[Term.boxBool b]], [bb], mk_HasType (Term.boxBool b) tt), Some "bool typing", "bool_typing");
         Util.mkAssume(mkForall_fuel env (Env.get_range env)
                                     ([[typing_pred]], [xx], mkImp(typing_pred, mk_tester (fst boxBoolFun) x)), Some "bool inversion", "bool_inversion")] in
    let mk_int : env -> string -> term -> list decl  = fun env nm tt ->
        let lex_t = mkFreeV <| mk_fv (string_of_lid Const.lex_t_lid, Term_sort) in
        let typing_pred = mk_HasType x tt in
        let typing_pred_y = mk_HasType y tt in
        let aa = mk_fv ("a", Int_sort) in
        let a = mkFreeV aa in
        let bb = mk_fv ("b", Int_sort) in
        let b = mkFreeV bb in
        let precedes_y_x = mk_Valid <| mkApp("Prims.precedes", [mk_U_zero; mk_U_zero; lex_t; lex_t;y;x]) in
        [Util.mkAssume(mkForall (Env.get_range env) ([[Term.boxInt b]], [bb], mk_HasType (Term.boxInt b) tt), Some "int typing", "int_typing");
         Util.mkAssume(mkForall_fuel env (Env.get_range env) ([[typing_pred]], [xx], mkImp(typing_pred, mk_tester (fst boxIntFun) x)), Some "int inversion", "int_inversion");
         Util.mkAssume(mkForall_fuel env (Env.get_range env) ([[typing_pred; typing_pred_y;precedes_y_x]],
                                   [xx;yy],
                                   mkImp(mk_and_l [typing_pred;
                                                   typing_pred_y;
                                                   mkGT (Term.unboxInt x, mkInteger' 0);
                                                   mkGTE (Term.unboxInt y, mkInteger' 0);
                                                   mkLT (Term.unboxInt y, Term.unboxInt x)],
                                         precedes_y_x)),
                                  Some "well-founded ordering on nat (alt)", "well-founded-ordering-on-nat")] in
    let mk_real : env -> string -> term -> list decl  = fun env nm tt ->
        let typing_pred = mk_HasType x tt in
        let aa = mk_fv ("a", Sort "Real") in
        let a = mkFreeV aa in
        let bb = mk_fv ("b", Sort "Real") in
        let b = mkFreeV bb in
        [Util.mkAssume(mkForall
                         (Env.get_range env)
                         ([[Term.boxReal b]],
                          [bb],
                          mk_HasType (Term.boxReal b) tt),
                          Some "real typing",
                          "real_typing");
         Util.mkAssume(mkForall_fuel
                         env
                         (Env.get_range env)
                         ([[typing_pred]],
                          [xx],
                          mkImp(typing_pred,
                                mk_tester (fst boxRealFun) x)),
                          Some "real inversion",
                          "real_inversion")]
    in
    let mk_str : env -> string -> term -> list decl  = fun env nm tt ->
        let typing_pred = mk_HasType x tt in
        let bb = mk_fv ("b", String_sort) in
        let b = mkFreeV bb in
        [Util.mkAssume(mkForall (Env.get_range env) ([[Term.boxString b]], [bb], mk_HasType (Term.boxString b) tt), Some "string typing", "string_typing");
         Util.mkAssume(mkForall_fuel env (Env.get_range env) ([[typing_pred]], [xx], mkImp(typing_pred, mk_tester (fst boxStringFun) x)),  Some "string inversion", "string_inversion")] in
    let mk_true_interp : env -> string -> term -> list decl = fun env nm true_tm ->
        let valid = mkApp("Valid", [true_tm]) in
        [Util.mkAssume(valid, Some "True interpretation", "true_interp")] in
    let mk_false_interp : env -> string -> term -> list decl = fun env nm false_tm ->
        let valid = mkApp("Valid", [false_tm]) in
        [Util.mkAssume(mkIff(mkFalse, valid), Some "False interpretation", "false_interp")] in
    let mk_and_interp : env -> string -> term -> list decl = fun env conj _ ->
        let aa = mk_fv ("a", Term_sort) in
        let bb = mk_fv ("b", Term_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let l_and_a_b = mkApp(conj, [a;b]) in
        let valid = mkApp("Valid", [l_and_a_b]) in
        let valid_a = mkApp("Valid", [a]) in
        let valid_b = mkApp("Valid", [b]) in
        [Util.mkAssume(mkForall (Env.get_range env) ([[l_and_a_b]], [aa;bb], mkIff(mkAnd(valid_a, valid_b), valid)), Some "/\ interpretation", "l_and-interp")] in
    let mk_or_interp : env -> string -> term -> list decl = fun env disj _ ->
        let aa = mk_fv ("a", Term_sort) in
        let bb = mk_fv ("b", Term_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let l_or_a_b = mkApp(disj, [a;b]) in
        let valid = mkApp("Valid", [l_or_a_b]) in
        let valid_a = mkApp("Valid", [a]) in
        let valid_b = mkApp("Valid", [b]) in
        [Util.mkAssume(mkForall (Env.get_range env) ([[l_or_a_b]], [aa;bb], mkIff(mkOr(valid_a, valid_b), valid)), Some "\/ interpretation", "l_or-interp")] in
    let mk_eq2_interp : env -> string -> term -> list decl = fun env eq2 tt ->
        let uu = mk_fv ("u", univ_sort) in
        let aa = mk_fv ("a", Term_sort) in
        let xx = mk_fv ("x", Term_sort) in
        let yy = mk_fv ("y", Term_sort) in
        let u = mkFreeV uu in
        let a = mkFreeV aa in
        let x = mkFreeV xx in
        let y = mkFreeV yy in
        let eq2_x_y = mkApp(eq2, [u;a;x;y]) in
        let valid = mkApp("Valid", [eq2_x_y]) in
        [Util.mkAssume(mkForall (Env.get_range env)
                                ([[eq2_x_y]], [uu;aa;xx;yy], mkIff(mkEq(x, y), valid)),
                       Some "Eq2 interpretation",
                       "eq2-interp")]
    in
    let mk_eq3_interp : env -> string -> term -> list decl = fun env eq3 tt ->
        let uu = mk_fv ("u", univ_sort) in
        let aa = mk_fv ("a", Term_sort) in
        let bb = mk_fv ("b", Term_sort) in
        let xx = mk_fv ("x", Term_sort) in
        let yy = mk_fv ("y", Term_sort) in
        let u = mkFreeV uu in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let x = mkFreeV xx in
        let y = mkFreeV yy in
        let eq3_x_y = mkApp(eq3, [u;a;b;x;y]) in
        let valid = mkApp("Valid", [eq3_x_y]) in
        [Util.mkAssume(mkForall (Env.get_range env) ([[eq3_x_y]], [uu;aa;bb;xx;yy], mkIff(mkEq(x, y), valid)),
                       Some "Eq3 interpretation",
                       "eq3-interp")]
    in
    let mk_imp_interp : env -> string -> term -> list decl = fun env imp tt ->
        let aa = mk_fv ("a", Term_sort) in
        let bb = mk_fv ("b", Term_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let l_imp_a_b = mkApp(imp, [a;b]) in
        let valid = mkApp("Valid", [l_imp_a_b]) in
        let valid_a = mkApp("Valid", [a]) in
        let valid_b = mkApp("Valid", [b]) in
        [Util.mkAssume(mkForall (Env.get_range env) ([[l_imp_a_b]], [aa;bb], mkIff(mkImp(valid_a, valid_b), valid)), Some "==> interpretation", "l_imp-interp")] in
    let mk_iff_interp : env -> string -> term -> list decl = fun env iff tt ->
        let aa = mk_fv ("a", Term_sort) in
        let bb = mk_fv ("b", Term_sort) in
        let a = mkFreeV aa in
        let b = mkFreeV bb in
        let l_iff_a_b = mkApp(iff, [a;b]) in
        let valid = mkApp("Valid", [l_iff_a_b]) in
        let valid_a = mkApp("Valid", [a]) in
        let valid_b = mkApp("Valid", [b]) in
        [Util.mkAssume(mkForall (Env.get_range env) ([[l_iff_a_b]], [aa;bb], mkIff(mkIff(valid_a, valid_b), valid)), Some "<==> interpretation", "l_iff-interp")] in
    let mk_not_interp : env -> string -> term -> list decl = fun env l_not tt ->
        let aa = mk_fv ("a", Term_sort) in
        let a = mkFreeV aa in
        let l_not_a = mkApp(l_not, [a]) in
        let valid = mkApp("Valid", [l_not_a]) in
        let not_valid_a = mkNot <| mkApp("Valid", [a]) in
        [Util.mkAssume(mkForall (Env.get_range env) ([[l_not_a]], [aa], mkIff(not_valid_a, valid)), Some "not interpretation", "l_not-interp")] in
   let mk_range_interp : env -> string -> term -> list decl = fun env range tt ->
        let range_ty = mkApp(range, []) in
        [Util.mkAssume(mk_HasTypeZ (mk_Range_const ()) range_ty, Some "Range_const typing", (varops.mk_unique "typing_range_const"))] in
   let mk_inversion_axiom : env -> string -> term -> list decl = fun env inversion tt ->
       // (assert (forall ((u Universe) (t Term))
       //            (! (implies (Valid (FStar.Pervasives.inversion u t))
       //                        (forall ((x Term))
       //                                (! (implies (HasTypeFuel ZFuel x t)
       //                                            (HasTypeFuel (SFuel ZFuel) x t))
       //                                   :pattern ((HasTypeFuel ZFuel x t)))))
       //               :pattern ((FStar.Pervasives.inversion t)))))
        let uu = mk_fv ("u", univ_sort) in
        let u = mkFreeV uu in
        let tt = mk_fv ("t", Term_sort) in
        let t = mkFreeV tt in
        let xx = mk_fv ("x", Term_sort) in
        let x = mkFreeV xx in
        let inversion_t = mkApp(inversion, [u;t]) in
        let valid = mkApp("Valid", [inversion_t]) in
        let body =
          let hastypeZ = mk_HasTypeZ x t in
          let hastypeS = mk_HasTypeFuel (n_fuel 1) x t in
          mkForall (Env.get_range env) ([[hastypeZ]], [xx], mkImp(hastypeZ, hastypeS))
        in
        [Util.mkAssume(mkForall (Env.get_range env) ([[inversion_t]], [uu;tt], mkImp(valid, body)), Some "inversion interpretation", "inversion-interp")]
   in
   let mk_with_type_axiom : env -> string -> term -> list decl = fun env with_type tt ->
        (* (assert (forall ((u Universe) (t Term) (e Term))
                           (! (and (= (Prims.with_type u t e)
                                       e)
                                   (HasType (Prims.with_type u t e) t))
                            :weight 0
                            :pattern ((Prims.with_type t e)))))
         *)
        let uu = mk_fv ("u", univ_sort) in
        let u = mkFreeV uu in
        let tt = mk_fv ("t", Term_sort) in
        let t = mkFreeV tt in
        let ee = mk_fv ("e", Term_sort) in
        let e = mkFreeV ee in
        let with_type_t_e = mkApp(with_type, [u; t; e]) in
        [Util.mkAssume(mkForall' (Env.get_range env) ([[with_type_t_e]],
                                 Some 0, //weight
                                 [uu;tt;ee],
                                 mkAnd(mkEq(with_type_t_e, e),
                                       mk_HasType with_type_t_e t)),
                       Some "with_type primitive axiom",
                       "@with_type_primitive_axiom")] //the "@" in the name forces it to be retained even when the contex is pruned
   in
   let prims =  [(Const.unit_lid,   mk_unit);
                 (Const.bool_lid,   mk_bool);
                 (Const.int_lid,    mk_int);
                 (Const.real_lid,   mk_real);
                 (Const.string_lid, mk_str);
                 (Const.true_lid,   mk_true_interp);
                 (Const.false_lid,  mk_false_interp);
                 (Const.and_lid,    mk_and_interp);
                 (Const.or_lid,     mk_or_interp);
                 (Const.eq2_lid,    mk_eq2_interp);
                 (Const.imp_lid,    mk_imp_interp);
                 (Const.iff_lid,    mk_iff_interp);
                 (Const.not_lid,    mk_not_interp);
                 //(Const.forall_lid, mk_forall_interp);
                 //(Const.exists_lid, mk_exists_interp);
                 (Const.range_lid,  mk_range_interp);
                 (Const.inversion_lid,mk_inversion_axiom);
                ] in
    (fun (env:env) (t:lident) (s:string) (tt:term) ->
        match Option.find (fun (l, _) -> lid_equals l t) prims with
            | None -> []
            | Some(_, f) -> f env s tt)

let forall_univs rng univ_fvs body =
  match univ_fvs with
  | [] -> body
  | us ->
    let univ_vars = List.map encode_univ_name us in
    let cvars = List.map fst univ_vars in
    let csorts = List.map fv_sort cvars in
    let body = abstr cvars body in
    match body with
    | {tm=Quant (Forall, pats, wopt, sorts, body); rng} ->
      mkForall'' rng (pats, wopt, csorts @ sorts, body)
    | _ ->
      mkForall'' rng ([], None, csorts, body)

let encode_smt_lemma env fv t =
    let lid = fv.fv_name in
    let t = U.canon_arrow t in // Make sure we flatten to catch SMTPats, see #2596
    let form, decls = encode_function_type_as_formula t env in
    let form = forall_univs (range_of_fv fv) (Free.univnames t |> FlatSet.elems) form in
    decls@([Util.mkAssume(form, Some ("Lemma: " ^ (string_of_lid lid)), ("lemma_"^(string_of_lid lid)))]
           |> mk_decls_trivial)

let close_universes rng univ_fvs pat body = mkForall rng ([[pat]], univ_fvs, body)

let encode_free_var uninterpreted env fv us tt t_norm quals :decls_t & env_t =
    let lid = fv.fv_name in
    let univ_fvs, univs = List.map EncodeTerm.encode_univ_name us |> List.unzip in
    let univ_sorts = univs |> List.map (fun _ -> univ_sort) in
    if not <| (U.is_pure_or_ghost_function t_norm || is_smt_reifiable_function env.tcenv t_norm)
    || U.is_lemma t_norm
    || uninterpreted
    then let arg_sorts = match (SS.compress t_norm).n with
            | Tm_arrow {bs=binders} -> binders |> List.map (fun _ -> Term_sort)
            | _ -> [] in
         let arity = List.length arg_sorts in
         let univ_arity = List.length us in
         let vname, vtok, env = new_term_constant_and_tok_from_lid env lid arity univ_arity in
         let univ_sorts = List.map (fun _ -> univ_sort) us in
         let d = Term.DeclFun(vname, univ_sorts @ arg_sorts, Term_sort, Some "Uninterpreted function symbol for impure function") in
         let dd = Term.DeclFun(vtok, univ_sorts, Term_sort, Some "Uninterpreted name for impure function") in
         [d;dd] |> mk_decls_trivial, env
    else if prims.is lid
         then let _ = if List.length us <> 0 then failwith "Impossible: unexpected universe-polymorphic primitive function" in
              let vname = varops.new_fvar lid in
              let tok, arity, definition = prims.mk lid vname in
              let env = push_free_var env lid arity 0 vname (Some tok) in
              definition |> mk_decls_trivial, env
         else let encode_non_total_function_typ = nsstr lid <> "Prims" in
              let formals, (pre_opt, res_t) =
                let args, comp = curried_arrow_formals_comp t_norm in
                let tcenv_comp = Env.push_binders env.tcenv args in
                let comp =
                  if is_smt_reifiable_comp env.tcenv comp
                  then S.mk_Total (reify_comp ({tcenv_comp with admit=true}) comp U_unknown)
                  else comp
                in
                if encode_non_total_function_typ
                then args, TypeChecker.Util.pure_or_ghost_pre_and_post tcenv_comp comp
                else args, (None, U.comp_result comp)
              in
              let mk_disc_proj_axioms guard encoded_res_t vapp (vars:fvs) =
                quals |> List.collect
                (function
                  | Discriminator d ->
                    let _, xxv = BU.prefix vars in
                    let xx = mkFreeV <| mk_fv (fv_name xxv, Term_sort) in
                    [Util.mkAssume(mkForall (S.range_of_fv fv)
                                            ([[vapp]],
                                             univ_fvs@vars,
                                             mkEq(vapp, Term.boxBool <| mk_tester (escape (string_of_lid d)) xx)),
                                   Some "Discriminator equation",
                                   "disc_equation_"^escape (string_of_lid d))]

                  | Projector(d, f) ->
                    let _, xxv = BU.prefix vars in
                    let xx = mkFreeV <| mk_fv (fv_name xxv, Term_sort) in
                    let f = {ppname=f; index=0; sort=tun} in
                    let tp_name = mk_term_projector_name d f in //arity ok, primitive projector (#1383)
                    let prim_app = mkApp(tp_name, [xx]) in
                    [Util.mkAssume(mkForall (S.range_of_fv fv)
                                            ([[vapp]], univ_fvs@vars, mkEq(vapp, prim_app)),
                                   Some "Projector equation",
                                   "proj_equation_"^tp_name)]
                  | _ -> [])
              in
              let vars, guards, env', decls1, _ = encode_binders None formals env in
              let guard, decls1 = match pre_opt with
                | None -> mk_and_l guards, decls1
                | Some p -> let g, ds = encode_formula p env' in mk_and_l (g::guards), decls1@ds in
              let dummy_var = mk_fv ("@dummy", dummy_sort) in
              let dummy_tm = Term.mkFreeV dummy_var Range.dummyRange in
              let should_thunk () =
                //See note [Thunking Nullary Constants] in FStarC.SMTEncoding.Term.fs
                let is_type t =
                    match (SS.compress t).n with
                    | Tm_type _ -> true
                    | _ -> false
                in
                let is_squash t =
                    let head, _ = U.head_and_args t in
                    match (U.un_uinst head).n with
                    | Tm_fvar fv ->
                      Syntax.fv_eq_lid fv FStarC.Parser.Const.squash_lid

                    | Tm_refine {b={sort={n=Tm_fvar fv}}} ->
                      Syntax.fv_eq_lid fv FStarC.Parser.Const.unit_lid

                    | _ -> false
                in
                // Thunk if ...
                nsstr lid <> "Prims"  //not in prims
                && List.length us = 0 //has no universe binders
                && not (quals |> List.contains Logic) //not logic qualified terms
                && not (is_squash t_norm) //not ambient squashed properties
                && not (is_type t_norm) //not : Type terms, since ambient typing hypotheses for these are cheap
              in
              let thunked, vars =
                 match vars with
                 | [] when should_thunk () ->
                   true, [dummy_var]
                 | _ -> false, vars
              in
              let arity = List.length formals in
              let univ_arity = List.length univs in
              let vname, vtok_opt, env = new_term_constant_and_tok_from_lid_maybe_thunked env lid arity univ_arity thunked in
              let get_vtok () = Option.must vtok_opt in
              let vtok_tm =
                    match formals with
                    | [] when thunked ->  //univ_vars must be []
                      mkApp(vname, [dummy_tm])
                    | [] when not thunked ->
                      mkApp(vname, univs)
                    | _ ->
                      mkApp(get_vtok(), univs) //not thunked
              in
              let vtok_app = mk_Apply vtok_tm vars in
              let vapp = mkApp(vname, univs @ List.map mkFreeV vars) in //arity ok, see decl below, arity is |vars| (#1383)
              let decls2, env =
                let vname_decl = Term.DeclFun(vname, univ_sorts @ (vars |> List.map fv_sort), Term_sort, None) in
                let tok_typing, decls2 =
                    let env = {env with encode_non_total_function_typ=encode_non_total_function_typ} in
                    if not(head_normal env tt)
                    then encode_term_pred None tt env vtok_tm
                    else encode_term_pred None t_norm env vtok_tm
                in
                //close over the universe variables, if any
                let tok_typing = close_universes (S.range_of_fv fv) univ_fvs vtok_tm tok_typing in
                //NS:Unfortunately, this is duplicated work --- we effectively encode the function type twice
                let tok_decl, env =
                    match vars with
                    | [] ->
                      let tok_typing =
                        Util.mkAssume(tok_typing, Some "function token typing", ("function_token_typing_"^vname))
                      in
                      decls2@([tok_typing] |> mk_decls_trivial),
                      push_free_var env lid arity univ_arity vname (Some <| mkApp(vname, []))

                    | _ when thunked ->
                      decls2, env

                    | _ ->
                     (* Generate a token and a function symbol;
                        equate the two, and use the function symbol for full applications *)
                      let vtok = get_vtok() in
                      let vtok_decl = Term.DeclFun(vtok, univ_sorts, Term_sort, None) in
                      let name_tok_corr_formula pat =
                          match univ_fvs with
                          | [] ->
                            mkForall (S.range_of_fv fv)
                                     ([[pat]], vars, mkEq(vtok_app, vapp))
                                     //use the patterns provided by the caller
                          | _ ->
                            let inner_quant =
                              mkForall (S.range_of_fv fv)
                                       ([[vtok_app];[vapp]], vars, mkEq(vtok_app, vapp))
                                       //patterns for rewriting in both directions
                                       //since it is nested within a quantifier guarded by
                                       //a universe-application of the token
                            in
                            mkForall (S.range_of_fv fv) ([[vtok_tm]], univ_fvs, inner_quant)
                      in
                      //See issue #613 for the choice of patterns here
                      let name_tok_corr =
                          //this allows rewriting (ApplyTT tok ... x1..xn) to f x1...xn
                          Util.mkAssume(name_tok_corr_formula vtok_app,
                                        Some "Name-token correspondence",
                                        ("token_correspondence_"^vname)) in
                      let tok_typing =
                        let guarded_tok_typing =
                          match univ_fvs with
                          | _::_ ->
                            //This assumption is already protected by a universe quantifier;
                            //No need to guard it further
                            tok_typing
                          | _ ->
                            let ff = mk_fv ("ty", Term_sort) in
                            let f = mkFreeV ff in
                            let vtok_app_r = mk_Apply f [mk_fv (vtok, Term_sort)] in
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
                            mkForall (S.range_of_fv fv)
                                     ([[vtok_app_r]],
                                      [ff],
                                      mkAnd(Term.mk_NoHoist f tok_typing,
                                            name_tok_corr_formula vapp))
                        in
                        Util.mkAssume(guarded_tok_typing, Some "function token typing", ("function_token_typing_"^vname))
                      in
                      decls2@([vtok_decl;name_tok_corr;tok_typing] |> mk_decls_trivial),
                      env
                in
                ([vname_decl] |> mk_decls_trivial)@tok_decl, env
              in
              let encoded_res_t, ty_pred, decls3 =
                   let res_t = SS.compress res_t in
                   let encoded_res_t, decls = encode_term res_t env' in
                   encoded_res_t, mk_HasType vapp encoded_res_t, decls in //occurs positively, so add fuel
              let typingAx = Util.mkAssume(mkForall (S.range_of_fv fv)
                                            ([[vapp]], univ_fvs@vars, mkImp(guard, ty_pred)),
                                            Some "free var typing",
                                            ("typing_"^vname)) in
              let freshness =
                if quals |> List.contains New
                then [Term.fresh_constructor (S.range_of_fv fv) (vname, univ_sorts @ (vars |> List.map fv_sort), Term_sort, varops.next_id());
                      pretype_axiom false (S.range_of_fv fv) env vapp (univ_fvs@vars)]
                else [] in
              let g = decls1@decls2@decls3@(freshness@typingAx::mk_disc_proj_axioms guard encoded_res_t vapp vars
                                            |> mk_decls_trivial) in
              g, env


let declare_top_level_let env x us t t_norm : fvar_binding & decls_t & env_t =
  match lookup_fvar_binding env x.fv_name with
  (* Need to introduce a new name decl *)
  | None ->
      let decls, env = encode_free_var false env x us t t_norm [] in
      let fvb = lookup_lid env x.fv_name in
      fvb, decls, env

  (* already declared, only need an equation *)
  | Some fvb ->
      fvb, [], env


let encode_top_level_val uninterpreted env us fv t quals =
    let tt =
      if FStarC.Ident.nsstr (lid_of_fv fv) = "FStar.Ghost"
      then norm_with_steps //no primops nor Simplify for FStar.Ghost, otherwise things like reveal/hide get simplified away too early
                [Env.Eager_unfolding;
                 Env.AllowUnboundUniverses;
                 Env.Exclude Env.Zeta]
                 env.tcenv t
      else norm_before_encoding env t
    in
    if !dbg_SMTEncoding
    then Format.print4 "Encoding top-level val %s %s : %s\nNormalized to is %s\n"
           (show fv)
           (show us)
           (show t)
           (show tt);
    let decls, env = encode_free_var uninterpreted env fv us t tt quals in
    if U.is_smt_lemma t
    then decls@encode_smt_lemma env fv tt, env
    else decls, env

let encode_top_level_vals env bindings quals =
  let decls, env =
    bindings |> List.fold_left (fun (decls, env) lb ->
        let env', us, [t] = Env.open_universes_in env.tcenv lb.lbunivs [lb.lbtyp] in
        let env' = { env with tcenv = env' } in
        let decls', env' = encode_top_level_val false env' us (Inr?.v lb.lbname) t quals in
        List.rev_append decls' decls, env') ([], env)
  in
  List.rev decls, env

exception Let_rec_unencodeable

//Make a copy of all the mutable state of env_t, central place for keeping track of mutable fields in env_t
let copy_env (en:env_t) = { en with global_cache = SMap.copy en.global_cache}

let encode_top_level_let :
    env_t -> (bool & list letbinding) -> list qualifier -> decls_t & env_t =
    fun env (is_rec, bindings) quals ->


    let eta_expand binders formals body t =
      let nbinders = List.length binders in
      let formals, extra_formals = BU.first_N nbinders formals in
      let subst =
        List.map2 (fun ({binder_bv=formal}) ({binder_bv=binder}) ->
          NT(formal, S.bv_to_name binder)
        ) formals binders in
      let extra_formals =
        extra_formals
          |> List.map (fun b ->
              {b with
               binder_bv={b.binder_bv with
                          sort=SS.subst subst b.binder_bv.sort}})
          |> U.name_binders in
      let body = Syntax.extend_app_n
        (SS.compress body)
        (snd <| U.args_of_binders extra_formals) body.pos in
      binders@extra_formals, body
    in

    let destruct_bound_function t e
      : (S.binders    //arguments of the (possibly reified) lambda abstraction
       & S.term       //body of the (possibly reified) lambda abstraction
       & S.comp)      //result comp
//       * bool         //if set, we should generate a curried application of f
    =
      (* The input type [t_norm] might contain reifiable computation type which must be reified at this point *)

      let tcenv = {env.tcenv with admit=true} in

      let subst_comp formals actuals comp =
          let subst = List.map2 (fun ({binder_bv=x}) ({binder_bv=b}) -> NT(x, S.bv_to_name b)) formals actuals in
          SS.subst_comp subst comp
      in

      let rec arrow_formals_comp_norm norm t =
        //NS: tried using U.arrow_formals_comp here
        //    but that flattens Tot effects quite aggressively
        let t = U.unascribe <| SS.compress t in
        match t.n with
        | Tm_arrow {bs=formals; comp} ->
          SS.open_comp formals comp

        | Tm_refine _ ->
          arrow_formals_comp_norm norm (U.unrefine t)

        | _ when not norm ->
          let t_norm = norm_with_steps [Env.Beta; Env.Weak; Env.HNF;
                                        (* we don't know if this will terminate; so don't do recursive steps *)
                                        Env.Exclude Env.Zeta;
                                        Env.UnfoldUntil delta_constant]
                        tcenv t
          in
          arrow_formals_comp_norm true t_norm

        | _ ->
          [], S.mk_Total t
      in

      let aux t e =
          let binders, body, lopt = U.abs_formals e in
          let formals, comp =
              match binders with
              | [] -> arrow_formals_comp_norm true t
                //don't normalize t to avoid poorly encoding points-free code
                //see, e.g., Benton2004.RHL.Example2
              | _ -> arrow_formals_comp_norm false t
          in
          let nformals = List.length formals in
          let nbinders = List.length binders in
          let binders, body, comp =
              if nformals < nbinders (* explicit currying *)
              then let bs0, rest = BU.first_N nformals binders in
                   let body = U.abs rest body lopt in
                   bs0, body, subst_comp formals bs0 comp
              else if nformals > nbinders (* eta-expand before translating it *)
              then let binders, body = eta_expand binders formals body (U.comp_result comp) in
                   binders, body, subst_comp formals binders comp
              else binders, body, subst_comp formals binders comp
          in
          binders, body, comp
      in
      let binders, body, comp = aux t e in
      let binders, body, comp =
          let tcenv = Env.push_binders tcenv binders in
          if is_smt_reifiable_comp tcenv comp
          then let eff_name = comp |> U.comp_effect_name in
               let comp = reify_comp tcenv comp U_unknown in
               let body = TcUtil.norm_reify tcenv []
                 (U.mk_reify body (Some eff_name)) in
               let more_binders, body, comp = aux comp body in
               binders@more_binders, body, comp
          else binders, body, comp
      in
      binders,
      //setting the use_eq ascription flag to false,
      //  doesn't matter since the flag is irrelevant outside the typechecker
      U.ascribe body (Inl (U.comp_result comp), None, false),
      comp
    in


    try
      if bindings |> BU.for_all (fun lb -> U.is_lemma lb.lbtyp)
      then encode_top_level_vals env bindings quals
      else
        let toks, typs, decls, env =
          bindings |> List.fold_left (fun (toks, typs, decls, env) lb ->
            (* some, but not all are lemmas; impossible *)
            if U.is_lemma lb.lbtyp then raise Let_rec_unencodeable;
            let us, t = SS.open_univ_vars lb.lbunivs lb.lbtyp in
            let env = { env with tcenv = Env.push_univ_vars env.tcenv us } in
            (* #2894: If this is a recursive definition, make sure to unfold the type
            until the arrow structure is evident (we use whnf for it). Otherwise
            there will be thunking inconsistencies in the encoding. *)
            let t_norm =
              if is_rec
              then N.unfold_whnf' [Env.AllowUnboundUniverses] env.tcenv t
              else norm_before_encoding env t
            in
            (* We are declaring the top_level_let with t_norm which might contain *)
            (* non-reified reifiable computation type. *)
            (* TODO : clear this mess, the declaration should have a type corresponding to *)
            (* the encoded term *)
            let tok, decl, env = declare_top_level_let env (Inr?.v lb.lbname) us t t_norm in
            (tok,us)::toks, t_norm::typs, decl::decls, env)
            ([], [], [], env)
        in
        let toks_fvbs = List.rev toks in
        let decls = List.rev decls |> List.flatten in
        (*
         * GM: Not accurate any more.
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

        let encode_non_rec_lbdef
                (bindings:list letbinding)
                (typs:list S.term)
                (toks:list (fvar_binding & S.univ_names))
                (env:env_t) =
            match bindings, typs, toks with
            | [{lbunivs=uvs;lbdef=e;lbname=lbn}], [t_norm], [(fvb, _)] ->

                (* Open universes *)
                let flid = fvb.fvar_lid in
                let env', univ_names, e_t =
                      Env.open_universes_in env.tcenv uvs [e; t_norm]
                in
                let env' = { env with tcenv = env' } in
                let e, t_norm =
                      match e_t with
                      | [e; t_norm] -> e, t_norm
                      | _ -> failwith "Impossible"
                in
                let univ_vars, univ_terms =
                  List.map EncodeTerm.encode_univ_name univ_names
                  |> List.unzip
                in
                (* Open binders *)
                let (binders, body, t_body_comp) = destruct_bound_function t_norm e in
                let t_body = U.comp_result t_body_comp in
                if !dbg_SMTEncoding
                then Format.print2 "Encoding let : binders=[%s], body=%s\n"
                                (show binders)
                                (show body);
                (* Encode binders *)
                let vars, binder_guards, env', binder_decls, _ = encode_binders None binders env' in
                let vars, app =
                    if fvb.fvb_thunked
                    && vars = []
                    && univ_vars = []
                    then let dummy_var = mk_fv ("@dummy", dummy_sort) in
                         let dummy_tm = Term.mkFreeV dummy_var Range.dummyRange in
                         let app = Term.mkApp (fvb.smt_id, [dummy_tm]) (S.range_of_lbname lbn) in
                         [dummy_var], app
                    else univ_vars@vars,
                         maybe_curry_fvb (S.range_of_lbname lbn)
                                         ({fvb with smt_arity = List.length univ_terms + fvb.smt_arity})
                                         (univ_terms @ List.map mkFreeV vars)
                in
                let is_logical =
                  match (SS.compress t_body).n with
                  | Tm_fvar fv when S.fv_eq_lid fv FStarC.Parser.Const.logical_lid -> true
                  | _ -> false
                in
                let is_smt_theory_symbol =
                    let fv = Inr?.v lbn in
                    Env.fv_has_attr env.tcenv fv FStarC.Parser.Const.smt_theory_symbol_attr_lid
                in
                let is_sub_singleton = U.is_sub_singleton body in
                let should_encode_logical =
                    not is_smt_theory_symbol
                    && (quals |> List.contains Logic || is_logical)
                in
                let make_eqn name pat app body =
                    //NS 05.25: This used to be mkImp(mk_and_l guards, mkEq(app, body))),
                    //But the guard is unnecessary given the pattern
                    Util.mkAssume(mkForall (S.range_of_lbname lbn)
                                           ([[pat]], vars, mkEq(app,body)),
                                  Some (Format.fmt1 "Equation for %s" (string_of_lid flid)),
                                  (name ^ "_" ^ fvb.smt_id))
                in
                let eqns,decls2 =
                  let basic_eqn_name =
                    if should_encode_logical
                    then "defn_equation"
                    else "equation"
                  in
                  let basic_eqn, decls =
                    let app_is_prop = Term.mk_subtype_of_unit app in
                    if should_encode_logical
                    then (
                      if is_sub_singleton && not (Options.Ext.enabled "retain_old_prop_typing")
                      then (
                        Util.mkAssume(mkForall (S.range_of_lbname lbn)
                                            ([[app_is_prop]], vars, mkImp(mk_and_l binder_guards, mk_Valid <| app_is_prop)),
                                      Some (Format.fmt1 "Prop-typing for %s" (string_of_lid flid)),
                                    (basic_eqn_name ^ "_" ^ fvb.smt_id)),
                        []
                      )
                      else (
                        let body, decls = encode_term body env' in
                        make_eqn basic_eqn_name app_is_prop app body,
                        decls
                      )
                    )
                    else (
                      let body, decls = encode_term body env' in
                      make_eqn basic_eqn_name app app body, decls
                    )
                  in
                  if should_encode_logical
                  then let pat, app, (body, decls2) =
                           app, mk_Valid app, encode_formula body env'
                       in
                       let logical_eqn = make_eqn "equation" pat app body in
                       [logical_eqn; basic_eqn], decls@decls2
                  else [basic_eqn], decls
                in
                decls@binder_decls@decls2@((eqns@primitive_type_axioms env.tcenv flid fvb.smt_id app)
                                                 |> mk_decls_trivial),
                env
            | _ -> failwith "Impossible"
        in

        let encode_rec_lbdefs (bindings:list letbinding)
                              (typs:list S.term)
                              (toks:list (fvar_binding & S.univ_names))
                              (env:env_t) =
          (* encoding recursive definitions using fuel to throttle unfoldings *)
          (* We create a new variable corresponding to the current fuel *)
          let fuel = mk_fv (varops.fresh env.current_module_name "fuel", Fuel_sort) in
          let fuel_tm = mkFreeV fuel in
          let env0 = env in
          (* For each declaration, we push in the environment its fuel-guarded copy (using current fuel) *)
          let gtoks, env = toks |> List.fold_left (fun (gtoks, env) (fvb, univ_names) -> //(flid_fv, (f, ftok)) ->
            let flid = fvb.fvar_lid in
            let g = varops.new_fvar (Ident.lid_add_suffix flid "fuel_instrumented") in
            let gtok = varops.new_fvar (Ident.lid_add_suffix flid "fuel_instrumented_token") in
            let env = 
              push_free_var_tok_with_fuel_and_univs
                env 
                flid 
                fvb.smt_arity 
                fvb.univ_arity
                gtok 
                (Some <| mkApp(g, [fuel_tm]))
                univ_names
            in
            (fvb, g, gtok)::gtoks, env) ([], env)
          in
          let gtoks = List.rev gtoks in

          let encode_one_binding env0 (fvb, g, gtok) t_norm ({lbunivs=uvs;lbname=lbn; lbdef=e}) =

            (* Open universes *)
            let env', e, univ_vars, t_norm =
                let env', univ_names, [e; t_norm] =
                  Env.open_universes_in env.tcenv uvs [e; t_norm] in
                let univ_vars, _ = List.map EncodeTerm.encode_univ_name univ_names |> List.unzip in
                {env with tcenv = env'}, e, univ_vars, t_norm
            in
            if !dbg_SMTEncoding
            then Format.print3 "Encoding let rec %s : %s = %s\n"
                        (show lbn)
                        (show t_norm)
                        (show e);

            (* Open binders *)
            let (binders, body, tres_comp) = destruct_bound_function t_norm e in
            let curry = fvb.smt_arity <> List.length binders in
            let pre_opt, tres = TcUtil.pure_or_ghost_pre_and_post env.tcenv tres_comp in
            if !dbg_SMTEncoding
            then Format.print4 "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                              (show lbn)
                              (show binders)
                              (show body)
                              (show tres_comp);
            //let _ =
            //    if curry
            //    then failwith "Unexpected type of let rec in SMT Encoding; \
            //                   expected it to be annotated with an arrow type"
            //in


            let vars, guards, env', binder_decls, _ = encode_binders None binders env' in
            let guard, guard_decls =
                match pre_opt with
                | None -> mk_and_l guards, []
                | Some pre ->
                  let guard, decls0 = encode_formula pre env' in
                  mk_and_l (guards@[guard]), decls0
            in
            let binder_decls = binder_decls @ guard_decls in
            let univ_sorts = List.map fv_sort univ_vars in
            let decl_g =
              Term.DeclFun(g,
                           (Fuel_sort::
                            univ_sorts @
                            List.map fv_sort (fst (BU.first_N fvb.smt_arity vars))),
                           Term_sort,
                           Some "Fuel-instrumented function name")
            in
            let env0 = push_zfuel_name env0 fvb.fvar_lid g gtok in
            let decl_g_tok = Term.DeclFun(gtok, univ_sorts, Term_sort, Some "Token for fuel-instrumented partial applications") in
            let univ_vars_tm = List.map mkFreeV univ_vars in
            let vars_tm = List.map mkFreeV vars in
            let rng = S.range_of_lbname lbn in
            let fvb_with_univs_arity = {fvb with smt_arity=List.length univ_vars + fvb.smt_arity} in
            let app = maybe_curry_fvb rng fvb_with_univs_arity (List.map mkFreeV (univ_vars@vars)) in
            let mk_g_app args =  maybe_curry_app rng (Inl (Var g)) (fvb_with_univs_arity.smt_arity + 1) args in
            let gsapp = mk_g_app (mkApp("SFuel", [fuel_tm])::univ_vars_tm@vars_tm) in
            let gmax = mk_g_app (mkApp("MaxFuel", [])::univ_vars_tm@vars_tm) in
            let body_tm, decls2 = encode_term body env' in

            //NS 05.25: This used to be  mkImp(mk_and_l guards, mkEq(gsapp, body_tm)
            //But, the pattern ensures that this only applies to well-typed terms
            //NS 08/10: Setting the weight of this quantifier to 0, since its instantiations are controlled by F* fuel
            //NS 11/28/2018: Restoring the mkImp (mk_and_l guards, mkEq(gsapp, body_tm))
            //   11/29/2018: Also guarding by the precondition of a Pure/Ghost function in addition to typing guards
            let eqn_g =
              Util.mkAssume
                (mkForall' (S.range_of_lbname lbn)
                           ([[gsapp]], Some 0, fuel::(univ_vars@vars), mkImp(guard, mkEq(gsapp, body_tm))),
                Some (Format.fmt1 "Equation for fuel-instrumented recursive function: %s" (string_of_lid fvb.fvar_lid)),
                "equation_with_fuel_" ^g)
            in
            let eqn_f =
              Util.mkAssume
                (mkForall (S.range_of_lbname lbn)
                          ([[app]], univ_vars@vars, mkEq(app, gmax)),
                 Some "Correspondence of recursive function to instrumented version",
                 "@fuel_correspondence_"^g)
            in
            let eqn_g' =
              Util.mkAssume
                (mkForall (S.range_of_lbname lbn)
                          ([[gsapp]], fuel::(univ_vars@vars), mkEq(gsapp,  mk_g_app (Term.n_fuel 0::(univ_vars_tm@vars_tm)))),
                Some "Fuel irrelevance",
                "@fuel_irrelevance_" ^g)
            in
            let aux_decls, g_typing =
              let gapp = mk_g_app (fuel_tm::(univ_vars_tm@vars_tm)) in
              let tok_corr =
                let gtok_univs_app = Util.mkApp' (Var gtok, univ_vars_tm) in
                let tok_app = mk_Apply gtok_univs_app (fuel::vars) in
                let tot_fun_axioms =
                  let head = gtok_univs_app in
                  let vars = fuel :: vars in
                  //the guards are trivial here since this tot_fun_axioms
                  //should never appear in a goal (see Bug1750.fst, test_currying)
                  let guards = List.map (fun _ -> mkTrue) vars in
                  let tot_fun_axioms =
                    EncodeTerm.isTotFun_axioms rng head [] vars guards (U.is_pure_comp tres_comp)
                  in
                  match univ_vars with
                  | [] -> tot_fun_axioms
                  | _ -> mkForall (S.range_of_lbname lbn) ([], univ_vars, tot_fun_axioms)
                in
                Util.mkAssume(mkAnd(mkForall (S.range_of_lbname lbn) ([[tok_app]], fuel::(univ_vars@vars), mkEq(tok_app, gapp)),
                                    tot_fun_axioms),
                              Some "Fuel token correspondence",
                              ("fuel_token_correspondence_"^gtok))
              in
              let aux_decls, typing_corr =
                let g_typing, d3 = encode_term_pred None tres env' gapp in
                d3, [Util.mkAssume(mkForall (S.range_of_lbname lbn)
                                            ([[gapp]], fuel::(univ_vars@vars), mkImp(guard, g_typing)),
                                    Some "Typing correspondence of token to term",
                                    ("token_correspondence_"^g))]
              in
              aux_decls, typing_corr@[tok_corr]
            in

            binder_decls@decls2@aux_decls@([decl_g;decl_g_tok] |> mk_decls_trivial),
            [eqn_g;eqn_g';eqn_f]@g_typing |> mk_decls_trivial, env0
          in

          let decls, eqns, env0 = List.fold_left (fun (decls, eqns, env0) (gtok, ty, lb) ->
              let decls', eqns', env0 = encode_one_binding env0 gtok ty lb in
              decls'::decls, eqns'@eqns, env0)
            ([decls], [], env0)
            (List.zip3 gtoks typs bindings)
          in
          (* Function declarations must come first to be defined in all recursive definitions *)
          let prefix_decls, elts, rest =
            let isDeclFun = function | DeclFun _ -> true | _ -> false in
            decls |> List.flatten |> (fun decls ->
              //decls is a list of decls_elt ... each of which contains a list decl in it
              //we need to go through each of those, accumulate DeclFuns and remove them from there
              let prefix_decls, elts, rest = List.fold_left (fun (prefix_decls, elts, rest) elt ->
                if elt.key |> Some? && List.existsb isDeclFun elt.decls
                then prefix_decls, elts@[elt], rest
                else let elt_decl_funs, elt_rest = List.partition isDeclFun elt.decls in
                     prefix_decls @ elt_decl_funs, elts, rest @ [{ elt with decls = elt_rest }]
              ) ([], [], []) decls in
              prefix_decls |> mk_decls_trivial, elts, rest)
          in
          let eqns = List.rev eqns in
          prefix_decls@elts@rest@eqns, env0
        in

        if quals |> BU.for_some (function HasMaskedEffect -> true | _ -> false)
        || typs  |> BU.for_some (fun t -> not <| (U.is_pure_or_ghost_function t ||
                                                  is_smt_reifiable_function env.tcenv t))
        then decls, env_decls
        else
          if not is_rec
          then
            (* Encoding non-recursive definitions *)
            encode_non_rec_lbdef bindings typs toks_fvbs env
          else
            encode_rec_lbdefs bindings typs toks_fvbs env

    with Let_rec_unencodeable ->
      let msg = bindings |> List.map (fun lb -> show lb.lbname) |> String.concat " and " in
      let decl = Caption ("let rec unencodeable: Skipping: " ^msg) in
      [decl] |> mk_decls_trivial, env

let encode_sig_inductive (env:env_t) (se:sigelt)
: decls_t & env_t
= let Sig_inductive_typ
        { lid=t; us=universe_names; params=tps;
          t=k; ds=datas; injective_type_params } = se.sigel in 
  let usubst, uvs = SS.univ_var_opening universe_names in
  let env = { env with tcenv = Env.push_univ_vars env.tcenv uvs } in
  let tps = SS.subst_binders usubst tps in
  let k = SS.subst (SS.shift_subst (List.length tps) usubst) k in
  let univ_vars, univ_terms = List.map EncodeTerm.encode_univ_name uvs |> List.unzip in
  let univ_arity = List.map (fun _ -> univ_sort) univ_vars in
  let t_lid = t in
  let tcenv = env.tcenv in
  let quals = se.sigquals in
  let is_logical = quals |> BU.for_some (function Logic | Assumption -> true | _ -> false) in
  let constructor_or_logic_type_decl (c:constructor_t) =
    if is_logical
    then [Term.DeclFun(c.constr_name, c.constr_fields |> List.map (fun f -> f.field_sort), Term_sort, None)]
    else constructor_to_decl (Ident.range_of_lid t) c in
  let inversion_axioms env tapp vars =
    if datas |> BU.for_some (fun l -> Env.try_lookup_lid env.tcenv l |> None?) //Q: Why would this happen?
    then []
    else (
      let xxsym, xx = fresh_fvar env.current_module_name "x" Term_sort in
      let data_ax, decls =
        datas |>
        List.fold_left
          (fun (out, decls) l ->
            let is_l = mk_data_tester env l xx in
            let univ_eqs = List.mapi (fun i u -> mkEq(mkFreeV u, mkApp(mk_univ_projector_name l i, [xx]))) univ_vars in
            let base_eqs = is_l::univ_eqs in
            let inversion_case, decls' =
              if injective_type_params
              || Options.Ext.enabled "compat:injectivity"
              then (
                let _univs, data_t = Env.lookup_datacon env.tcenv l in
                let args, res = U.arrow_formals data_t in
                let params_and_indices = res |> U.head_and_args_full |> snd in
                let env = args |> List.fold_left
                    (fun env ({binder_bv=x}) -> push_term_var env x (mkApp(mk_term_projector_name l x, [xx])))
                    env in
                let params_and_indices, decls' = encode_args params_and_indices env in
                if List.length params_and_indices <> List.length vars
                then failwith "Impossible";
                let eqs = List.map2 (fun v a -> mkEq(mkFreeV v, a)) vars params_and_indices in
                mk_and_l (base_eqs@eqs), decls'
              )
              else mk_and_l base_eqs, []
            in
            mkOr(out, inversion_case), decls@decls')
          (mkFalse, [])
      in
      let ffsym, ff = fresh_fvar env.current_module_name "f" Fuel_sort in
      let fuel_guarded_inversion =
        let xx_has_type_sfuel =
          if List.length datas > 1
          then mk_HasTypeFuel (mkApp("SFuel", [ff])) xx tapp
          else mk_HasTypeFuel ff xx tapp //no point requiring non-zero fuel if there are no disjunctions
        in
        Util.mkAssume(
          mkForall
            (Ident.range_of_lid t) 
            ([[xx_has_type_sfuel]],
             add_fuel (mk_fv (ffsym, Fuel_sort)) (mk_fv (xxsym, Term_sort)::univ_vars@vars),
            mkImp(xx_has_type_sfuel, data_ax)),
            Some "inversion axiom", //this name matters! see Sig_bundle case near line 1493
            (varops.mk_unique ("fuel_guarded_inversion_"^(string_of_lid t))))
      in
      decls
      @([fuel_guarded_inversion] |> mk_decls_trivial)
    )
  in
  let formals, res =
    let k =
      match tps with
      | [] -> k
      | _ -> S.mk (Tm_arrow {bs=tps; comp=S.mk_Total k}) k.pos
    in
    let k = norm_before_encoding env k in
    U.arrow_formals k
  in
  let vars, guards, env', binder_decls, _ = encode_binders None formals env in
  let arity = List.length vars in
  let univ_arity = List.length univ_terms in
  let tname, ttok, env = new_term_constant_and_tok_from_lid env t arity univ_arity in
  let ttok_tm = mkApp(ttok, univ_terms) in
  let guard = mk_and_l guards in
  let tapp = mkApp(tname, List.map mkFreeV (univ_vars@vars)) in //arity ok
  let decls, env =
    //See: https://github.com/FStarLang/FStar/commit/b75225bfbe427c8aef5b59f70ff6d79aa014f0b4
    //See: https://github.com/FStarLang/FStar/issues/349
    let tname_decl =
      constructor_or_logic_type_decl
        {
          constr_name = tname;
          constr_fields = univ_vars@vars |> List.map (fun fv -> {field_name=tname^fv_name fv; field_sort=fv_sort fv; field_projectible=false}) ;
          //The field_projectible=false above is extremely important; it makes sure that type-formers are not injective
          constr_sort=Term_sort;
          constr_id=Some (varops.next_id());
          constr_base=false
        }
    in
    let tok_decls, env =
      match vars with
      | [] -> [], push_free_var env t arity univ_arity tname (Some <| mkApp(tname, []))
      | _ ->
        let ttok_decl = Term.DeclFun(ttok, List.map fv_sort univ_vars, Term_sort, Some "token") in
        let ttok_fresh = Term.fresh_token (ttok_tm, univ_vars, Term_sort) (varops.next_id()) in
        let ttok_app = mk_Apply ttok_tm vars in
        let pats = [[ttok_app]; [tapp]] in
        // These patterns allow rewriting (ApplyT T@tok args) to (T args) and vice versa
        // This seems necessary for some proofs, but the bidirectional rewriting may be inefficient
        let name_tok_corr =
          Util.mkAssume(mkForall' (Ident.range_of_lid t) (pats, None, univ_vars@vars, mkEq(ttok_app, tapp)),
                        Some "name-token correspondence",
                        ("token_correspondence_"^ttok)) in
        [ttok_decl; ttok_fresh; name_tok_corr], env
    in
    tname_decl@tok_decls, env
  in
  let kindingAx =
    let k, decls = encode_term_pred None res env' tapp in
    let karr =
      if List.length formals > 0
      then [Util.mkAssume(
          mkForall (Ident.range_of_lid t) ([[ttok_tm]], univ_vars, mk_tester "Tm_arrow" (mk_PreType ttok_tm)),
          Some "kinding", ("pre_kinding_"^ttok))]
      else []
    in
    let rng = Ident.range_of_lid t in
    let tot_fun_axioms = EncodeTerm.isTotFun_axioms rng ttok_tm univ_vars vars (List.map (fun _ -> mkTrue) vars) true in
    decls@(karr@[Util.mkAssume(mkAnd(tot_fun_axioms, mkForall rng ([[tapp]], univ_vars@vars, mkImp(guard, k))),
                                None,
                                ("kinding_"^ttok))] |> mk_decls_trivial)
  in
  let aux =
    kindingAx
    @(inversion_axioms env tapp vars)
    @([pretype_axiom (not injective_type_params) (Ident.range_of_lid t) env tapp (univ_vars@vars)] |> mk_decls_trivial)
  in
  (decls |> mk_decls_trivial)@binder_decls@aux, env

let encode_datacon (env:env_t) (se:sigelt)
: decls_t & env_t
= let Sig_datacon {lid=d; us; t; num_ty_params=n_tps; mutuals; injective_type_params } = se.sigel in
  let quals = se.sigquals in
  let us, t = SS.open_univ_vars us t in
  let env = { env with tcenv = Env.push_univ_vars env.tcenv us } in
  let univ_fvs, univs = List.map EncodeTerm.encode_univ_name us |> List.unzip in
  let univ_sorts = univs |> List.map (fun _ -> univ_sort) in
  let t = norm_before_encoding env t in
  let formals, t_res = U.arrow_formals t in
  let arity = List.length formals in
  let univ_arity = List.length univs in
  let ddconstrsym, ddtok, env = new_term_constant_and_tok_from_lid env d arity univ_arity in
  let ddtok_tm = mkApp(ddtok, univs) in
  let fuel_var, fuel_tm = fresh_fvar env.current_module_name "f" Fuel_sort in
  let s_fuel_tm = mkApp("SFuel", [fuel_tm]) in
  let vars, guards, env', binder_decls, names = encode_binders (Some fuel_tm) formals env in
  let injective_type_params =
    injective_type_params || Options.Ext.enabled "compat:injectivity"
  in
  let univ_fields =
          univs
          |> List.mapi
            (fun i _ ->
              { field_name = mk_univ_projector_name d i; field_sort = univ_sort; field_projectible = true })
        in
  let n_univs = List.length univ_fields in
  let fields =
    names |>
    List.mapi
      (fun n x ->
        let field_projectible =
          n >= n_tps || //either this field is not a type parameter
          injective_type_params //or we are allowed to be injective on parameters
        in
        { field_name=mk_term_projector_name d x;
          field_sort=Term_sort;
          field_projectible })
  in
  let datacons = {
    constr_name=ddconstrsym;
    constr_fields=univ_fields@fields;
    constr_sort=Term_sort;
    constr_id=Some (varops.next_id());
    constr_base=not injective_type_params;
  } |> Term.constructor_to_decl (Ident.range_of_lid d) in
  let app = mk_Apply ddtok_tm vars in
  let guard = mk_and_l guards in
  let xvars = List.map mkFreeV vars in
  let dapp =  mkApp(ddconstrsym, univs@xvars) in //arity ok; |xvars| = |formals| = arity

  let tok_typing, decls3 = encode_term_pred None t env ddtok_tm in
  let tok_typing =
        match fields, univs with
        | _::_, [] ->
          let ff = mk_fv ("ty", Term_sort) in
          let f = mkFreeV ff in
          let vtok_app_l = mk_Apply ddtok_tm [ff] in
          let vtok_app_r = mk_Apply f [mk_fv (ddtok, Term_sort)] in
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
        | _ -> close_universes (Ident.range_of_lid d) univ_fvs ddtok_tm tok_typing in
  let ty_pred', t_res_tm, decls_pred =
        let t_res_tm, t_res_decls = encode_term t_res env' in
        mk_HasTypeWithFuel (Some fuel_tm) dapp t_res_tm, t_res_tm, t_res_decls in
  let proxy_fresh = match formals with
      | [] -> []
      | _ -> [Term.fresh_token (ddtok_tm, univ_fvs, Term_sort) (varops.next_id())] in

  let encode_elim () =
      let head, args = U.head_and_args t_res in
      match (SS.compress head).n with
      | Tm_uinst({n=Tm_fvar fv}, _)
      | Tm_fvar fv ->
        let encoded_head_fvb = lookup_free_var_name env' fv.fv_name in
        let encoded_args, arg_decls = encode_args args env' in
        let _, arg_vars, elim_eqns_or_guards, _ =
            List.fold_left
              (fun (env, arg_vars, eqns_or_guards, i) (orig_arg, arg) ->
                let _, xv, env = gen_term_var env (S.new_bv None tun) in
                (* we only get equations induced on the type indices, not parameters; *)
                (* Also see https://github.com/FStarLang/FStar/issues/349 *)
                let eqns =
                  if i < n_tps
                  then eqns_or_guards
                  else mkEq(arg, xv)::eqns_or_guards
                in
                (env, xv::arg_vars, eqns, i + 1))
              (env', [], [], 0)
              (FStarC.List.zip args encoded_args)
        in
        let arg_vars = List.rev arg_vars in
        let arg_params, _ = List.splitAt n_tps arg_vars in
        let data_arg_params, _ = List.splitAt n_tps vars in
        //Express the guards in terms of the parameters of the type constructor
        //not the arguments of the data constructor
        let elim_eqns_and_guards =
          List.fold_left2 
            (fun elim_eqns_and_guards data_arg_param arg_param ->
                Term.subst elim_eqns_and_guards data_arg_param arg_param)
            (mk_and_l (elim_eqns_or_guards@guards))
            data_arg_params
            arg_params
        in
        let ty = maybe_curry_fvb (pos fv.fv_name)
          ({encoded_head_fvb with smt_arity = List.length univs + encoded_head_fvb.smt_arity})
          (univs@arg_vars) in
        let xvars = List.map mkFreeV vars in
        let dapp =  mkApp(ddconstrsym, univs@xvars) in //arity ok; |xvars| = |formals| = arity
        let ty_pred = mk_HasTypeWithFuel (Some s_fuel_tm) dapp ty in
        let arg_binders = List.map fv_of_term arg_vars in
        let typing_inversion =
              Util.mkAssume(mkForall (Ident.range_of_lid d) ([[ty_pred]],
                                  add_fuel (mk_fv (fuel_var, Fuel_sort)) (univ_fvs@vars@arg_binders),
                                  mkImp(ty_pred, elim_eqns_and_guards)),
                          Some "data constructor typing elim",
                          ("data_elim_" ^ ddconstrsym)) in
        let lex_t = mkFreeV <| mk_fv (string_of_lid Const.lex_t_lid, Term_sort) in
        let subterm_ordering =
            (* subterm ordering *)
            let prec =
                  vars
                    |> List.mapi (fun i v ->
                          (* it's a parameter, so it's inaccessible and no need for a sub-term ordering on it *)
                          if i < n_tps
                          then []
                          else [mk_Precedes mk_U_zero mk_U_zero lex_t lex_t (mkFreeV v) dapp])
                    |> List.flatten
            in
            Util.mkAssume(mkForall (Ident.range_of_lid d)
                                    ([[ty_pred]],
                                    add_fuel (mk_fv (fuel_var, Fuel_sort)) (univ_fvs@vars@arg_binders),
                                    mkImp(ty_pred, mk_and_l prec)),
                          Some "subterm ordering",
                          ("subterm_ordering_"^ddconstrsym))
        in
        let codomain_ordering, codomain_decls =
          let _, formals' = BU.first_N n_tps formals in (* no codomain ordering for the parameters *)
          let _, vars' = BU.first_N n_tps vars in
          let norm t = 
              N.unfold_whnf' [Env.AllowUnboundUniverses;
                              Env.Unascribe;
                              //we don't know if this will terminate; so don't do recursive steps
                              Env.Exclude Env.Zeta]
                            env'.tcenv
                            t                
          in
          let warn_compat () =
            FStarC.Errors.log_issue fv FStarC.Errors.Warning_DeprecatedGeneric [
              Errors.Msg.text "Using 'compat:2954' to use a permissive encoding of the subterm ordering on the codomain of a constructor.";
              Errors.Msg.text "This is deprecated and will be removed in a future version of F*."
            ]
          in
          let codomain_prec_l, cod_decls =
            List.fold_left2
              (fun (codomain_prec_l, cod_decls) formal var ->
                  let rec binder_and_codomain_type t =
                      let t = U.unrefine t in
                      match (SS.compress t).n with
                      | Tm_arrow _ ->
                        let bs, c = U.arrow_formals_comp (U.unrefine t) in
                        begin
                        match bs with
                        | [] -> None
                        | _ when not (U.is_tot_or_gtot_comp c) -> None
                        | _ ->
                          if U.is_lemma_comp c
                          then None //not useful for lemmas
                          else
                            let t = U.unrefine (U.comp_result c) in
                            let t = norm t in
                            if is_type t || U.is_sub_singleton t
                            then None //ordering on Type and squashed values is not useful
                            else (
                              let head, _ = U.head_and_args_full t in
                              match (U.un_uinst head).n with
                              | Tm_fvar fv ->
                                if BU.for_some (S.fv_eq_lid fv) mutuals
                                then Some (bs, c)
                                else if Options.Ext.enabled "compat:2954"
                                then (warn_compat(); Some (bs, c)) //compatibility mode
                                else None
                              | _ ->
                                if Options.Ext.enabled "compat:2954"
                                then (warn_compat(); Some (bs, c)) //compatibility mode
                                else None
                            )
                        end
                      | _ ->
                        let head, _ = U.head_and_args t in
                        let t' = norm t in
                        let head', _ = U.head_and_args t' in
                        match TEQ.eq_tm env.tcenv head head' with
                        | TEQ.Equal -> None //no progress after whnf
                        | TEQ.NotEqual -> binder_and_codomain_type t'
                        | _ ->
                          //Did we actually make progress? Be conservative to avoid an infinite loop
                          match (SS.compress head).n with
                          | Tm_fvar _
                          | Tm_name _
                          | Tm_uinst _ ->
                            //The underlying name must have changed, otherwise we would have got Equal
                            //so, we made some progress
                            binder_and_codomain_type t'
                          | _ ->
                            //unclear if we made progress or not
                            None

                  in
                  match binder_and_codomain_type formal.binder_bv.sort with
                  | None -> 
                    codomain_prec_l, cod_decls
                  | Some (bs, c) ->
                    //var bs << D ... var ...
                    let bs', guards', _env', bs_decls, _ = encode_binders None bs env' in
                    let fun_app = mk_Apply (mkFreeV var) bs' in
                    mkForall (Ident.range_of_lid d)
                              ([[mk_Precedes mk_U_zero mk_U_zero lex_t lex_t fun_app dapp]],
                                bs',
                                //need to use ty_pred' here, to avoid variable capture
                                //Note, ty_pred' is indexed by fuel, not S_fuel
                                //That's ok, since the outer pattern is guarded on S_fuel
                                mkImp (mk_and_l (ty_pred'::guards'),
                                      mk_Precedes mk_U_zero mk_U_zero lex_t lex_t fun_app dapp))
                    :: codomain_prec_l,
                    bs_decls @ cod_decls)
              ([],[])
              formals'
              vars'
          in
          match codomain_prec_l with
          | [] ->
            [], cod_decls
          | _ ->
            [Util.mkAssume(mkForall (Ident.range_of_lid d)
                                    ([[ty_pred]],//we use ty_pred here as the pattern, which has an S_fuel guard
                                      add_fuel (mk_fv (fuel_var, Fuel_sort)) (univ_fvs@vars@arg_binders),
                                      mk_and_l codomain_prec_l),
                            Some "well-founded ordering on codomain",
                            ("well_founded_ordering_on_codomain_"^ddconstrsym))],
            cod_decls
        in
        arg_decls @ codomain_decls,
        [typing_inversion; subterm_ordering] @ codomain_ordering

      | _ ->
        Errors.log_issue se Errors.Warning_ConstructorBuildsUnexpectedType
          (Format.fmt2 "Constructor %s builds an unexpected type %s" (show d) (show head));
        [], []
  in
  let decls2, elim = encode_elim () in
  let data_cons_typing_intro_decl =
    //
    //AR:
    //
    //Typing intro for the data constructor
    //
    //We do a bit of manipulation for type indices
    //Consider the Cons data constructor of a length-indexed vector type:
    //  type vector : nat -> Type = | Emp : vector 0
    //  | Cons: n:nat -> hd:nat -> tl:vec n -> vec (n+1)
    //
    //So far we have
    //  ty_pred' = HasTypeFuel f (Cons n hd tl) (vector (n+1))
    //  vars = n, hd, tl
    //  guard = And of typing guards for n, hd, tl (i.e. (HasType n nat) etc.)
    //
    //If we emitted the straightforward typing axiom:
    //  forall n hd tl. HasTypeFuel f (Cons n hd tl) (vector (n+1))
    //with pattern
    //  HasTypeFuel f (Cons n hd tl) (vecor (n+1))
    //
    //It results in too restrictive a pattern,
    //Specifically, if we need to prove HasTypeFuel f (Cons 0 1 Emp) (vector 1),
    //  the axiom will not fire, since the pattern is specifically looking for
    //  (n+1) in the resulting vector type, whereas here we have a term 1,
    //  which is not addition syntactically
    //
    //So we do a little bit of surgery below to emit an axiom of the form:
    //  forall n hd tl m. m = n + 1 ==> HasTypeFuel f (Cons n hd tl) (vector m)
    //where m is a fresh variable
    //
    //Also see #2456
    //
    let ty_pred', vars, guard =
      match t_res_tm.tm with
      | App (op, args) ->
        //iargs are index arguments in the return type of the data constructor
        let targs, iargs = List.splitAt (n_univs + n_tps) args in
        //fresh vars for iargs
        let fresh_ivars, fresh_iargs =
          iargs |> List.map (fun _ -> fresh_fvar env.current_module_name "i" Term_sort)
                |> List.split in
        //equality guards
        let additional_guards =
          mk_and_l (List.map2 (fun a fresh_a -> mkEq (a, fresh_a)) iargs fresh_iargs) in

        mk_HasTypeWithFuel
          (Some fuel_tm)
          dapp
          ({t_res_tm with tm = App (op, targs@fresh_iargs)}),

        vars@(fresh_ivars |> List.map (fun s -> mk_fv (s, Term_sort))),

        mkAnd (guard, additional_guards)

      | _ -> ty_pred', vars, guard in  //When will this case arise?

    Util.mkAssume(mkForall (Ident.range_of_lid d)
                            ([[ty_pred']],add_fuel (mk_fv (fuel_var, Fuel_sort)) (univ_fvs@vars), mkImp(guard, ty_pred')),
                            Some "data constructor typing intro",
                            ("data_typing_intro_"^ddtok)) in

  let g = binder_decls
          @decls2
          @decls3
          @([Term.DeclFun(ddtok, univ_sorts, Term_sort, Some (Format.fmt1 "data constructor proxy: %s" (show d)))]
            @proxy_fresh |> mk_decls_trivial)
          @decls_pred
          @([Util.mkAssume(tok_typing, Some "typing for data constructor proxy", ("typing_tok_"^ddtok));
              Util.mkAssume(mkForall (Ident.range_of_lid d)
                                    ([[app]], univ_fvs@vars,
                                      mkEq(app, dapp)), Some "equality for proxy", ("equality_tok_"^ddtok));
              data_cons_typing_intro_decl;
              ]@elim |> mk_decls_trivial) in
  (datacons |> mk_decls_trivial) @ g, env


let rec encode_sigelt (env:env_t) (se:sigelt) : (decls_t & env_t) =
    let nm = Print.sigelt_to_string_short se in
    let g, env = Errors.with_ctx (Format.fmt1 "While encoding top-level declaration `%s`"
                                             (Print.sigelt_to_string_short se))
                   (fun () -> encode_sigelt' env se)
    in
    let g =
        match g with
         | [] ->
            begin
            if !dbg_SMTEncoding then
              Format.print1 "Skipped encoding of %s\n" nm;
            [Caption (Format.fmt1 "<Skipped %s/>" nm); EmptyLine] |> mk_decls_trivial
            end

         | _ -> ([Caption (Format.fmt1 "<Start encoding %s>" nm)] |> mk_decls_trivial)
                @g
                @([Caption (Format.fmt1 "</end encoding %s>" nm); EmptyLine] |> mk_decls_trivial) in
    g, env

and encode_sigelt' (env:env_t) (se:sigelt) : (decls_t & env_t) =
    if !dbg_SMTEncoding
    then (Format.print1 "@@@Encoding sigelt %s\n" (show se));

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
     | Sig_splice _ ->
         failwith "impossible -- splice should have been removed by Tc.fs"
     | Sig_fail _ ->
         failwith "impossible -- Sig_fail should have been removed by Tc.fs"
     | Sig_pragma _
     | Sig_effect_abbrev _
     | Sig_sub_effect _
     | Sig_polymonadic_bind _
     | Sig_polymonadic_subcomp _ -> [], env

     | Sig_new_effect(ed) ->
       if not (is_smt_reifiable_effect env.tcenv ed.mname)
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
            let ed_univs_subst, ed_univs = SS.univ_var_opening ed.univs in
            let close_effect_params tm =
              SS.subst ed_univs_subst
                (match ed.binders with
                  | [] -> tm
                  | _ -> S.mk (Tm_abs {bs=ed.binders;
                                      body=tm;
                                      rc_opt=Some (U.mk_residual_comp Const.effect_Tot_lid None [TOTAL])}) tm.pos)
            in

            let open_action_univs (a:S.action) =
              let action_univs_subst, action_univs = SS.univ_var_opening a.action_univs in
              SS.subst ed_univs_subst (SS.subst action_univs_subst a.action_defn),
              SS.subst ed_univs_subst (SS.subst action_univs_subst a.action_typ),
              action_univs

            in

            let encode_action env (a:S.action) =
              let action_univs_subst, action_univs = SS.univ_var_opening a.action_univs in
              let action_defn, action_typ, action_univs = open_action_univs a in
              let action_defn = norm_before_encoding env (close_effect_params action_defn) in
              let formals, _ = U.arrow_formals_comp action_typ in
              let arity = List.length formals in
              let univ_arity = List.length action_univs + List.length ed_univs in
              let aname, atok, env = new_term_constant_and_tok_from_lid env a.action_name arity univ_arity in
              let tm, decls = encode_term action_defn env in
              let univ_sorts = ed_univs@action_univs |> List.map (fun _ -> univ_sort) in
              let a_decls =
                [Term.DeclFun(aname, univ_sorts @ (formals |> List.map (fun _ -> Term_sort)), Term_sort, Some "Action");
                  Term.DeclFun(atok, univ_sorts, Term_sort, Some "Action token")]
              in
              let _, us_sorts, us = 
                let aux u (env, acc_sorts, acc) =
                  let fv, tm = encode_univ_name u in
                  env, fv::acc_sorts, tm::acc
                in
                List.fold_right aux (ed_univs@action_univs) (env, [], [])
              in
              let _, xs_sorts, xs =
                let aux ({binder_bv=bv}) (env, acc_sorts, acc) =
                  let xxsym, xx, env = gen_term_var env bv in
                  env, mk_fv (xxsym, Term_sort)::acc_sorts, xx::acc
                in
                List.fold_right aux formals (env, [], [])
              in
              let app = mkApp(aname, us@xs) in
              let a_eq =
                Util.mkAssume(mkForall (Ident.range_of_lid a.action_name) ([[app]], us_sorts@xs_sorts, mkEq(app, mk_Apply tm xs_sorts)),
                            Some "Action equality",
                            (aname ^"_equality"))
              in
              let tok_correspondence =
                let tok_term = mkApp(atok, us) in
                let tok_app = mk_Apply tok_term xs_sorts in
                Util.mkAssume(mkForall (Ident.range_of_lid a.action_name) ([[tok_app]], us_sorts@xs_sorts, mkEq(tok_app, app)),
                            Some "Action token correspondence", (aname ^ "_token_correspondence"))
              in
              env, decls@(a_decls@[a_eq; tok_correspondence] |> mk_decls_trivial)
            in

            let env, decls2 = BU.fold_map encode_action env ed.actions in
            List.flatten decls2, env

     | Sig_declare_typ {lid} when (lid_equals lid Const.precedes_lid) ->
        //precedes is added in the prelude, see FStarC.SMTEncoding.Term.fs
        let tname, ttok, env = new_term_constant_and_tok_from_lid env lid 4 2 in
        [], env

     | Sig_declare_typ {lid; us; t} ->
        let us, t = SS.open_univ_vars us t in
        let env = { env with tcenv = Env.push_univ_vars env.tcenv us } in
        let quals = se.sigquals in
        let will_encode_definition = not (quals |> BU.for_some (function
            | Assumption | Projector _ | Discriminator _ | Irreducible -> true
            | _ -> false)) in
        if will_encode_definition
        then [], env //nothing to do at the declaration; wait to encode the definition
        else let fv = S.lid_as_fv lid None in
             let decls, env =
               encode_top_level_val
                 (se.sigattrs |> BU.for_some is_uninterpreted_by_smt)
                 env us fv t quals in
             let tname = (string_of_lid lid) in
             let tsym = Option.must (try_lookup_free_var env lid) in
             decls
             @ (primitive_type_axioms env.tcenv lid tname tsym |> mk_decls_trivial),
             env

     | Sig_assume {lid=l; us; phi=f} ->
        let uvs, f = SS.open_univ_vars us f in
        let env = { env with tcenv = Env.push_univ_vars env.tcenv uvs } in
        let f = norm_before_encoding env f in
        let f, decls = encode_formula f env in
        let f =
          let univ_fvs, univ_tms =
            List.map EncodeTerm.encode_univ_name uvs
            |> List.unzip
          in
          Term.mkForall (Ident.range_of_lid l) ([], univ_fvs, f) //NS: flatten quantifier for a pattern
        in
        let g = [Util.mkAssume(f, Some (Format.fmt1 "Assumption: %s" (show l)), (varops.mk_unique ("assumption_"^(string_of_lid l))))]
                |> mk_decls_trivial in
        decls@g, env

     (* Irreducible and opaque lets. Replace the definitions by a dummy val decl (if none
        exists) and re-run. *)
     | Sig_let {lbs}
        when se.sigquals |> List.contains S.Irreducible
          || se.sigattrs |> BU.for_some is_opaque_to_smt ->
       let attrs = se.sigattrs in
       let env, decls = BU.fold_map (fun env lb ->
        let lid = (Inr?.v lb.lbname).fv_name in
        if None? <| Env.try_lookup_val_decl env.tcenv lid
        then let val_decl = { se with sigel = Sig_declare_typ {lid; us=lb.lbunivs; t=lb.lbtyp};
                                      sigquals = S.Irreducible :: se.sigquals } in
             let decls, env = encode_sigelt' env val_decl in
             env, decls
        else env, []) env (snd lbs) in
       List.flatten decls, env

     (* Special encoding for b2t *)
     | Sig_let {lbs=(_, [{lbname=Inr b2t}])} when S.fv_eq_lid b2t Const.b2t_lid ->
       let tname, ttok, env = new_term_constant_and_tok_from_lid env b2t.fv_name 1 0 in
       let xx = mk_fv ("x", Term_sort) in
       let x = mkFreeV xx in
       let b2t_x = mkApp("Prims.b2t", [x]) in
       let valid_b2t_x = mkApp("Valid", [b2t_x]) in //NS: Explicitly avoid the Vaild(b2t t) inlining
       let bool_ty = lookup_free_var env Const.bool_lid in
       let decls = [Term.DeclFun(tname, [Term_sort], Term_sort, None);
                    Util.mkAssume(mkForall (S.range_of_fv b2t) ([[b2t_x]], [xx],
                                           mkEq(valid_b2t_x, mkApp(snd boxBoolFun, [x]))),
                                Some "b2t def",
                                "b2t_def");
                    Util.mkAssume(mkForall (S.range_of_fv b2t) ([[b2t_x]], [xx],
                                           mkImp(mk_HasType x bool_ty,
                                                 mk_HasType b2t_x (mk_Term_type mk_U_zero))),
                                Some "b2t typing",
                                "b2t_typing")] in
       decls |> mk_decls_trivial, env

    (* Discriminators *)
    | Sig_let _ when (se.sigquals |> BU.for_some (function Discriminator _ -> true | _ -> false)) ->
      //Discriminators are encoded directly via (our encoding of) theory of datatypes
      if !dbg_SMTEncoding then
        Format.print1 "Not encoding discriminator '%s'\n" (Print.sigelt_to_string_short se);
      [], env

    (* `unfold let` definitions in prims do not get encoded. *)
    | Sig_let {lids} when (lids |> BU.for_some (fun (l:lident) -> string_of_id (List.hd (ns_of_lid l)) = "Prims")
                             && se.sigquals |> BU.for_some (function Unfold_for_unification_and_vcgen -> true | _ -> false)) ->
        //inline lets from prims are never encoded as definitions --- since they will be inlined
      if !dbg_SMTEncoding then
        Format.print1 "Not encoding unfold let from Prims '%s'\n" (Print.sigelt_to_string_short se);
      [], env

    (* Projectors *)
    | Sig_let {lbs=(false, [lb])}
         when (se.sigquals |> BU.for_some (function Projector _ -> true | _ -> false)) ->
     //Projectors are also are encoded directly via (our encoding of) theory of datatypes
     //Except in some cases where the front-end does not emit a declare_typ for some projector, because it doesn't know how to compute it
     let fv = Inr?.v lb.lbname in
     let l = fv.fv_name in
     begin match try_lookup_free_var env l with
        | Some _ ->
          [], env //already encoded
        | None ->
          let se = {se with sigel = Sig_declare_typ {lid=l; us=lb.lbunivs; t=lb.lbtyp}; sigrng = Ident.range_of_lid l } in
          encode_sigelt env se
     end

    (* A normal let, perhaps recursive. *)
    | Sig_let {lbs=(is_rec, bindings)} ->
      let bindings, _ = SS.open_let_rec bindings Syntax.Util.exp_unit in
      let bindings =
        List.map
          (fun lb ->
            let def = norm_before_encoding_us env lb.lbunivs lb.lbdef in
            let typ = norm_before_encoding_us env lb.lbunivs lb.lbtyp in
            {lb with lbdef=def; lbtyp=typ})
          bindings
      in
      let bindings, _ = SS.close_let_rec bindings Syntax.Util.exp_unit in
      encode_top_level_let env (is_rec, bindings) se.sigquals
    
    | Sig_bundle {ses; lids}
      when lids |> BU.for_some (Ident.lid_equals Parser.Const.lex_t_lid) ->
      [], env

    | Sig_bundle {ses} ->
      let g, env =
        ses |>
        List.fold_left
          (fun (g, env) se ->
            let g', env =
              match se.sigel with
              | Sig_inductive_typ _ ->
                encode_sig_inductive env se
              | Sig_datacon _ -> 
                encode_datacon env se
              | _ ->
                encode_sigelt env se
            in
            g@g', env) 
          ([], env)
      in      
      //reorder the generated decls in proper def-use order, 
      //i.e, declare all the function symbols first
      //1. move the inversions last; they rely on all the symbols
      let g', inversions =
        List.fold_left
          (fun (g', inversions) elt ->
              let elt_g', elt_inversions =
                elt.decls |>
                List.partition 
                  (function
                    | Term.Assume({assumption_caption=Some "inversion axiom"}) -> false
                    | _ -> true)
              in
              g' @ [ { elt with decls = elt_g' } ],
              inversions @ elt_inversions)
          ([], [])
          g
      in
      //2. decls are all the function symbol declarations
      //   elts: all elements that have a key and which contain function declarations (not sure why this class is important to pull out)
      //   rest: all the non-declarations, excepting the inversion axiom which is already identified above
      let decls, elts, rest =
        List.fold_left
          (fun (decls, elts, rest) elt ->
            if Some? elt.key //NS: Not sure what this case is for
            && List.existsb (function | Term.DeclFun _ -> true | _ -> false) elt.decls
            then decls, elts@[elt], rest 
            else ( //Pull the function symbol decls to the front
              let elt_decls, elt_rest =
                elt.decls |>
                List.partition
                  (function
                    | Term.DeclFun _ -> true
                    | _ -> false)
              in
              decls @ elt_decls, elts, rest @ [ { elt with decls = elt_rest }]
            ))
          ([], [], []) g'
      in
      (decls |> mk_decls_trivial) @ elts @ rest @ (inversions |> mk_decls_trivial), env

let encode_env_bindings (env:env_t) (bindings:list S.binding) : (decls_t & env_t) =
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
        | S.Binding_univ u ->
          let u_fv, u_tm = EncodeTerm.encode_univ_name u in
          let decls' = [Term.DeclFun(fv_name u_fv, [], univ_sort, Some "universe local constant")] |> mk_decls_trivial in
          i+1, decls@decls', env

        | S.Binding_var x ->
            let t1 = norm_before_encoding env x.sort in
            if !dbg_SMTEncoding
            then (Format.print3 "Normalized %s : %s to %s\n" (show x) (show x.sort) (show t1));
            let t, decls' = encode_term t1 env in
            let t_hash = Term.hash_of_term t in
            let xxsym, xx, env' =
                new_term_constant_from_string env x
                    ("x_" ^ BU.digest_of_string t_hash ^ "_" ^ (show i)) in
            let t = mk_HasTypeWithFuel None xx t in
            let caption =
                if Options.log_queries()
                then Some (Format.fmt3 "%s : %s (%s)" (show x) (show x.sort) (show t1))
                else None in
            let ax =
                let a_name = ("binder_"^xxsym) in
                Util.mkAssume(t, Some a_name, a_name) in
            let g = ([Term.DeclFun(xxsym, [], Term_sort, caption)] |> mk_decls_trivial)
                    @decls'
                    @([ax] |> mk_decls_trivial) in
            i+1, decls@g, env'

        | S.Binding_lid(x, (us, t)) ->
            let us, t = SS.open_univ_vars us t in
            let t_norm = norm_before_encoding env t in
            let fv = S.lid_as_fv x None in
//            Printf.printf "Encoding %s at type %s\n" (show x) (show t);
            let g, env' = encode_free_var false env fv us t t_norm [] in
            i+1, decls@g, env'
    in
    let _, decls, env = List.fold_right encode_binding bindings (0, [], env) in
    decls, env

let encode_labels (labs:list error_label) =
    let prefix = labs |> List.map (fun (l, _, _) -> Term.DeclFun(fv_name l, [], Bool_sort, None)) in
    let suffix = labs |> List.collect (fun (l, _, _) -> [Echo <| fv_name l; Eval (mkFreeV l)]) in
    prefix, suffix

(* caching encodings of the environment and the top-level API to the encoding *)
let last_env : ref (list env_t) = mk_ref []
let init_env tcenv = last_env := [{bvar_bindings=PSMap.empty ();
                                   fvar_bindings=(PSMap.empty (), []);
                                   tcenv=tcenv; warn=true; depth=0;
                                   nolabels=false; use_zfuel_name=false;
                                   encode_non_total_function_typ=true; encoding_quantifier=false;
                                   current_module_name=Env.current_module tcenv |> Ident.string_of_lid;
                                   global_cache = SMap.create 100}]
let get_env cmn tcenv = match !last_env with
    | [] -> failwith "No env; call init first!"
    | e::_ -> {e with tcenv=tcenv; current_module_name=Ident.string_of_lid cmn}
let set_env env = match !last_env with
    | [] -> failwith "Empty env stack"
    | _::tl -> last_env := env::tl
let get_current_env tcenv = get_env (Env.current_module tcenv) tcenv
let push_env () = match !last_env with
    | [] -> failwith "Empty env stack"
    | hd::tl ->
      let top = copy_env hd in
      last_env := top::hd::tl
let pop_env () = match !last_env with
    | [] -> failwith "Popping an empty stack"
    | _::tl -> last_env := tl
let snapshot_env () = FStarC.Common.snapshot "SMTEncoding.Encode.env" push_env last_env ()
let rollback_env depth = FStarC.Common.rollback "SMTEncoding.Encode.env" pop_env last_env depth
(* TOP-LEVEL API *)

let init tcenv =
    init_env tcenv;
    Z3.giveZ3 [DefPrelude]
let snapshot_encoding msg = BU.atomically (fun () ->
    if Debug.medium () then Format.print1 "Encode.snapshot_encoding: %s\n" msg;
    let env_depth, () = snapshot_env () in
    let varops_depth, () = varops.snapshot () in
    (env_depth, varops_depth))
let rollback_encoding msg (depth:option encoding_depth) = BU.atomically (fun () ->
    if Debug.medium () then Format.print2 "Encode.rollback_encoding: %s to %s\n" msg (show depth);
    let env_depth, varops_depth = match depth with
        | Some (s1, s2) -> Some s1, Some s2
        | None -> None, None in
    rollback_env env_depth;
    varops.rollback varops_depth)
let push_encoding_state msg = let _ = snapshot_encoding msg in ()
let pop_encoding_state msg = rollback_encoding msg None

//////////////////////////////////////////////////////////////////////////
//guarding top-level terms with fact database triggers
//////////////////////////////////////////////////////////////////////////
let open_fact_db_tags (env:env_t) : list fact_db_id = [] //TODO

let place_decl_in_fact_dbs (env:env_t) (fact_db_ids:list fact_db_id) (d:decl) : decl =
    match fact_db_ids, d with
    | _::_, Assume a ->
      Assume ({a with assumption_fact_ids=fact_db_ids})
    | _ -> d

let place_decl_elt_in_fact_dbs (env:env_t) (fact_db_ids:list fact_db_id) (elt:decls_elt) :decls_elt =
  { elt with decls = elt.decls |> List.map (place_decl_in_fact_dbs env fact_db_ids) }

let fact_dbs_for_lid (env:env_t) (lid:Ident.lid) =
    Name lid
    ::Namespace (Ident.lid_of_ids (ns_of_lid lid))
    ::open_fact_db_tags env

let encode_top_level_facts (env:env_t) (se:sigelt) =
    let fact_db_ids =
        U.lids_of_sigelt se |> List.collect (fact_dbs_for_lid env)
    in
    let g, env = encode_sigelt env se in
    let g = g |> List.map (place_decl_elt_in_fact_dbs env fact_db_ids) in
    g, env
//////////////////////////////////////////////////////////////////////////
//end: guarding top-level terms with fact database triggers
//////////////////////////////////////////////////////////////////////////


(*
 * AR: Recover hashconsing of decls -- both within a module and across modules
 *     Using and updating env.global_cache
 *)
let recover_caching_and_update_env (env:env_t) (decls:decls_t) :decls_t =
  decls |> List.collect (fun elt ->
    if elt.key = None then [elt]  //not meant to be hashconsed, keep it
    else (
      match SMap.try_find env.global_cache (elt.key |> Some?.v) with
      | Some (cache_elt, _) -> [Term.RetainAssumptions cache_elt.a_names] |> mk_decls_trivial  //hit, retain a_names from the hit entry
                                                                                             //AND drop elt
      | None ->  //no hit, update cache and retain elt
        SMap.add env.global_cache (elt.key |> Some?.v) (elt, Env.current_module env.tcenv);
        [elt]
    )
  )

let encode_sig tcenv se =
   Stats.record "encode_sig" fun () ->
   let caption decls =
    if Options.log_queries()
    then Term.Caption ("encoding sigelt " ^ Print.sigelt_to_string_short se)::decls
    else decls in
   if Debug.medium ()
   then Format.print1 "+++++++++++Encoding sigelt %s\n" (show se);
   let env = get_env (Env.current_module tcenv) tcenv in
   let decls, env = encode_top_level_facts env se in
   set_env env;
   Z3.giveZ3 (caption (decls |> recover_caching_and_update_env env |> decls_list_of))

let give_decls_to_z3_and_set_env (env:env_t) (name:string) (decls:decls_t) :unit =
  let caption decls =
    if Options.log_queries()
    then let msg = "Externals for " ^ name in
         [Module(name, Caption msg::decls@[Caption ("End " ^ msg)])]
    else [Module(name, decls)] in
  set_env ({env with warn=true});
  //recover caching and flatten before giving to Z3
  let z3_decls = caption (decls |> recover_caching_and_update_env env |> decls_list_of) in
  Z3.giveZ3 z3_decls

instance instance_showable_smap (#a:Type) {|_:showable a|} : Tot (showable (SMap.t a)) = {
  show = (fun smap -> SMap.fold smap (fun k v acc -> Format.fmt3 "%s -> %s\n%s" (show k) (show v) acc) "")
}

let encode_modul tcenv modul =
  if Options.lax() && Options.ml_ish() then [], []
  else begin
    let tcenv = Env.set_current_module tcenv modul.name in
    UF.with_uf_enabled (fun () ->
    varops.reset_fresh ();
    let name = Format.fmt2 "%s %s" (if modul.is_interface then "interface" else "module")  (string_of_lid modul.name) in
    if Debug.medium ()
    then Format.print2 "+++++++++++Encoding externals for %s ... %s declarations\n" name (List.length modul.declarations |> show);
    let env = get_env modul.name tcenv |> reset_current_module_fvbs in
    let clear_current_module env =
      //in fly_deps mode, remove all items from the cache
      //that resulted from encoding this module when checking its
      //internals, so that it can be encoded in a clean state
      //for persisting in a .checked file.
      //This is quite fiddly, but we cannot reset the scope to a
      //the state before the module was typechecked, because popping
      //the environment will also unload all modules that were loaded
      //on the fly.
      let keys = SMap.keys env.global_cache in
      List.iter
        (fun k ->
          match SMap.try_find env.global_cache k with
          | None -> ()
          | Some (elts, m) -> 
            if Ident.lid_equals m modul.name then SMap.remove env.global_cache k else ())
        keys;
      let fvb =
        PSMap.fold 
          (fst env.fvar_bindings)
          (fun key v fvb -> 
            if FStarC.Ident.(lid_of_ids (ns_of_lid v.fvar_lid) `lid_equals` modul.name)
            then fvb
            else PSMap.add fvb key v)
          (PSMap.empty())
      in
      if not (Options.interactive()) then varops.reset_scope();
      { env with fvar_bindings=(fvb, [])}
    in
    let env = 
      if FStarC.Parser.Dep.fly_deps_enabled ()
      then clear_current_module env
      else env in
    if Debug.high ()
    then (
      Format.print3 "Global cache contains %s entries\n{%s}\nenv={%s}" 
        (show (SMap.size env.global_cache))
        (show env.global_cache)
        (print_env env)
    );
    let encode_signature (env:env_t) (ses:sigelts) =
      let g', env =
        ses |> List.fold_left (fun (g, env) se ->
          let g', env = encode_top_level_facts env se in
          List.rev_append g' g, env) ([], env)
      in
      List.rev g', env
    in
    let decls, env = encode_signature ({env with warn=false}) modul.declarations in
    give_decls_to_z3_and_set_env env name decls;
    if Debug.medium () then Format.print1 "Done encoding externals for %s\n" name;
    decls, env |> get_current_module_fvbs
  ) end

let encode_modul_from_cache tcenv tcmod (decls, fvbs) =
  if Options.lax () && Options.ml_ish () then ()
  else
    let tcenv = Env.set_current_module tcenv tcmod.name in
    let name = Format.fmt2 "%s %s" (if tcmod.is_interface then "interface" else "module") (string_of_lid tcmod.name) in
    if Debug.medium ()
    then Format.print2 "+++++++++++Encoding externals from cache for %s ... %s decls\n" name (List.length decls |> show);
    let env = get_env tcmod.name tcenv |> reset_current_module_fvbs in
    let env =
      fvbs |> List.rev |> List.fold_left (fun env fvb ->
        add_fvar_binding_to_env fvb env
      ) env in
    give_decls_to_z3_and_set_env env name decls;
    if Debug.medium () then Format.print1 "Done encoding externals from cache for %s\n" name

open FStarC.SMTEncoding.Z3
let encode_query use_env_msg (tcenv:Env.env) (q:S.term)
  : list decl  //prelude, translation of  tcenv
  & list ErrorReporting.label //labels in the query
  & decl        //the query itself
  & list decl  //suffix, evaluating labels in the model, etc.
  =
  Errors.with_ctx "While encoding a query" (fun () ->
    Z3.query_logging.set_module_name (string_of_lid (TypeChecker.Env.current_module tcenv));
    let env = get_env (Env.current_module tcenv) tcenv in
    let q, bindings =
        let rec aux bindings = match bindings with
            | S.Binding_var x::rest ->
                let out, rest = aux rest in
                let t =
                    match (Syntax.Formula.destruct_typ_as_formula x.sort) with
                    | Some _ ->
                      U.refine (S.new_bv None t_unit) x.sort
                      //add a squash to trigger the shallow embedding,
                      //if the assumption is of the form x:(forall y. P) etc.
                    | _ ->
                      x.sort in
                let t = norm_with_steps [Env.Eager_unfolding; Env.Beta; Env.Simplify; Env.Primops] env.tcenv t in
                Syntax.mk_binder ({x with sort=t})::out, rest
            | _ -> [], bindings in
        let closing, bindings = aux tcenv.gamma in
        U.close_forall_no_univs (List.rev closing) q, bindings
    in
    let env_decls, env = encode_env_bindings env bindings in
    if Debug.medium () || !dbg_SMTEncoding
    then Format.print1 "Encoding query formula {: %s\n" (show q);
    let (phi, qdecls), ms = Timing.record_ms (fun () -> encode_formula q env) in
    let labels, phi = ErrorReporting.label_goals use_env_msg (Env.get_range tcenv) phi in
    let label_prefix, label_suffix = encode_labels labels in
    let caption =
      (* If these options are off, the Captions will be dropped anyway,
      but by checking here we can skip the printing. *)
      if Options.log_queries () || Options.log_failing_queries ()
      then [Caption ("Encoding query formula : " ^ (show q));
            Caption ("Context: " ^ String.concat "\n" (Errors.get_ctx ()))]
      else []
    in
    let query_prelude =
        env_decls
        @(label_prefix |> mk_decls_trivial)
        @qdecls
        @(caption |> mk_decls_trivial) |> recover_caching_and_update_env env |> decls_list_of in  //recover caching and flatten

    let qry = Util.mkAssume(mkNot phi, Some "query", (varops.mk_unique "@query")) in
    let suffix = [Term.Echo "<labels>"] @ label_suffix @ [Term.Echo "</labels>"; Term.Echo "Done!"] in
    if Debug.medium () || !dbg_SMTEncoding
    then Format.print_string "} Done encoding\n";
    if Debug.medium () || !dbg_SMTEncoding || !dbg_Time
    then Format.print1 "Encoding took %sms\n" (show ms);
    query_prelude, labels, qry, suffix
  )
