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
module FStar.TypeChecker.DMFF
open FStar.All

open FStar
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.Util
open FStar.Ident
open FStar.Errors
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Syntax.Util
open FStar.Const
open FStar.TypeChecker.Rel
open FStar.TypeChecker.Common
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module N  = FStar.TypeChecker.Normalize
module TcUtil = FStar.TypeChecker.Util
module BU = FStar.Util //basic util
module U  = FStar.Syntax.Util


type env = {
  // The type-checking environment which we abuse to store our DMFF-style types
  // when entering a binder.
  env: FStar.TypeChecker.Env.env;
  // The substitution from every [x: C] to its [x^w: C*].
  subst: list<subst_elt>;
  // Hack to avoid a dependency NS: env already has a type_of, so why not reuse that?
  tc_const: sconst -> typ;
}



let empty env tc_const = {
  env = env;
  subst = [];
  tc_const = tc_const
}

// Synthesis of WPs from a partial effect definition (in F*) ------------------

let gen_wps_for_free
  env (binders: binders) (a: bv) (wp_a: term) (ed: Syntax.eff_decl):
  Syntax.sigelts * Syntax.eff_decl
=
  // [wp_a] has been type-checked and contains universe unification variables;
  // we want to re-use [wp_a] and make it re-generalize accordingly
  let wp_a = N.normalize [N.Beta; N.EraseUniverses] env wp_a in
  let a = { a with sort = N.normalize [ N.EraseUniverses ] env a.sort } in

  // Debugging
  let d s = BU.print1 "\x1b[01;36m%s\x1b[00m\n" s in
  if Env.debug env (Options.Other "ED") then begin
    d "Elaborating extra WP combinators";
    BU.print1 "wp_a is: %s\n" (Print.term_to_string wp_a)
  end;

  (* Consider the predicate transformer st_wp:
   *   let st_pre_h  (heap:Type)          = heap -> GTot Type0
   *   let st_post_h (heap:Type) (a:Type) = a -> heap -> GTot Type0
   *   let st_wp_h   (heap:Type) (a:Type) = heap -> st_post_h heap a -> GTot Type0
   * after reduction we get:
   *   let st_wp_h (heap: Type) (a: Type) = heap -> (a -> heap -> GTot Type0) -> GTot Type0
   * we want:
   *   type st2_gctx (heap: Type) (a:Type) (t:Type) = heap -> (a -> heap -> GTot Type0) -> GTot t
   * we thus generate macros parameterized over [e] that build the right
   * context. [gamma] is the series of binders the precede the return type of
   * the context. *)
  let rec collect_binders (t : term) =
    match (U.unascribe <| compress t).n with
    | Tm_arrow (bs, comp) ->
        // TODO: dubious, assert no nested arrows
        let rest = match comp.n with
          | Total (t, _) -> t
          | _ -> failwith "wp_a contains non-Tot arrow"
        in
        bs @ (collect_binders rest)
    | Tm_type _ ->
        []
    | _ ->
        failwith "wp_a doesn't end in Type0" in

  let mk_lid name : lident = U.dm4f_lid ed name in

  let gamma = collect_binders wp_a |> U.name_binders in
  if Env.debug env (Options.Other "ED") then
    d (BU.format1 "Gamma is %s\n" (Print.binders_to_string ", " gamma));
  let unknown = S.tun in
  let mk x = mk x None Range.dummyRange in

  // The [register] function accumulates the top-level definitions that are
  // generated in the course of producing WP combinators
  let sigelts = BU.mk_ref [] in
  let register env lident def =
    let sigelt, fv = TcUtil.mk_toplevel_definition env lident def in
    sigelts := sigelt :: !sigelts;
    fv
  in

  (* Some helpers. *)
  let binders_of_list = List.map (fun (t, b) -> t, S.as_implicit b) in
  let mk_all_implicit = List.map (fun t -> fst t, S.as_implicit true) in
  let args_of_binders = List.map (fun bv -> S.as_arg (S.bv_to_name (fst bv))) in

  let env, mk_ctx, mk_gctx =
    // Neither [ctx_def] or [gctx_def] take implicit arguments.
    let ctx_def, gctx_def =
      let mk f: term =
        let t = S.gen_bv "t" None U.ktype in
        let body = U.arrow gamma (f (S.bv_to_name t)) in
        U.abs (binders @ [ S.mk_binder a; S.mk_binder t ]) body None
      in
      mk mk_Total,
      mk mk_GTotal
    in
    // Register these two top-level bindings in the environment
    let ctx_lid = mk_lid "ctx" in
    let ctx_fv = register env ctx_lid ctx_def in

    let gctx_lid = mk_lid "gctx" in
    let gctx_fv = register env gctx_lid gctx_def in

    let mk_app fv t =
      // The [mk_ctx] and [mk_gctx] helpers therefore do not use implicits either
      mk (Tm_app (fv,
        List.map (fun (bv, _) -> S.bv_to_name bv, S.as_implicit false) binders @
        [ S.bv_to_name a, S.as_implicit false; t, S.as_implicit false ]))
    in

    env, mk_app ctx_fv, mk_app gctx_fv
  in

  (* val st2_pure : #heap:Type -> #a:Type -> #t:Type -> x:t ->
       Tot (st2_ctx heap a t)
     let st2_pure #heap #a #t x = fun _post _h -> x *)
  let c_pure =
    let t = S.gen_bv "t" None U.ktype in
    let x = S.gen_bv "x" None (S.bv_to_name t) in
    let ret = Some (Inl (U.lcomp_of_comp (mk_Total (mk_ctx (S.bv_to_name t))))) in
    let body = U.abs gamma (S.bv_to_name x) ret in
    U.abs (mk_all_implicit binders @ binders_of_list [ a, true; t, true; x, false ]) body ret
  in
  let c_pure = register env (mk_lid "pure") c_pure in

  (* val st2_app : #heap:Type -> #a:Type -> #t1:Type -> #t2:Type ->
                  l:st2_gctx heap a (t1 -> GTot t2) ->
                  r:st2_gctx heap a t1 ->
                  Tot (st2_gctx heap a t2)
    let st2_app #heap #a #t1 #t2 l r = fun p h -> l p h (r p h) *)
  let c_app =
    let t1 = S.gen_bv "t1" None U.ktype in
    let t2 = S.gen_bv "t2" None U.ktype in
    let l = S.gen_bv "l" None (mk_gctx
      (U.arrow [ S.mk_binder (S.new_bv None (S.bv_to_name t1)) ] (S.mk_GTotal (S.bv_to_name t2))))
    in
    let r = S.gen_bv "r" None (mk_gctx (S.bv_to_name t1)) in
    let ret = Some (Inl (U.lcomp_of_comp (mk_Total (mk_gctx (S.bv_to_name t2))))) in
    let outer_body =
      let gamma_as_args = args_of_binders gamma in
      let inner_body =
        U.mk_app
          (S.bv_to_name l)
          (gamma_as_args @ [ S.as_arg (U.mk_app (S.bv_to_name r) gamma_as_args)])
      in
      U.abs gamma inner_body ret
    in
    U.abs (mk_all_implicit binders @ binders_of_list [ a, true; t1, true; t2, true; l, false; r, false ]) outer_body ret
  in
  let c_app = register env (mk_lid "app") c_app in

  (* val st2_liftGA1 : #heap:Type -> #a:Type -> #t1:Type -> #t2:Type ->
                       f : (t1 -> GTot t2) ->
                       st2_gctx heap a t1 ->
                       Tot (st2_gctx heap a t2)
    let st2_liftGA1 #heap #a #t1 #t2 f a1 =
                    st2_app (st2_pure f) a1
  *)
  let c_lift1 =
    let t1 = S.gen_bv "t1" None U.ktype in
    let t2 = S.gen_bv "t2" None U.ktype in
    let t_f = U.arrow [ S.null_binder (S.bv_to_name t1) ] (S.mk_GTotal (S.bv_to_name t2)) in
    let f = S.gen_bv "f" None t_f in
    let a1 = S.gen_bv "a1" None (mk_gctx (S.bv_to_name t1)) in
    let ret = Some (Inl (U.lcomp_of_comp (mk_Total (mk_gctx (S.bv_to_name t2))))) in
    U.abs (mk_all_implicit binders @ binders_of_list [ a, true; t1, true; t2, true; f, false; a1, false ]) (
      U.mk_app c_app (List.map S.as_arg [
        U.mk_app c_pure (List.map S.as_arg [ S.bv_to_name f ]);
        S.bv_to_name a1 ])
    ) ret
  in
  let c_lift1 = register env (mk_lid "lift1") c_lift1 in


  (* val st2_liftGA2 : #heap:Type -> #a:Type -> #t1:Type -> #t2:Type -> #t3:Type ->
                       f : (t1 -> t2 -> GTot t3) ->
                       a1: st2_gctx heap a t1 ->
                       a2: st2_gctx heap a t2 ->
                       Tot (st2_gctx heap a t3)
    let st2_liftGA2 #heap #a #t1 #t2 #t3 f a1 a2 =
      st2_app (st2_app (st2_pure f) a1) a2
  *)
  let c_lift2 =
    let t1 = S.gen_bv "t1" None U.ktype in
    let t2 = S.gen_bv "t2" None U.ktype in
    let t3 = S.gen_bv "t3" None U.ktype in
    let t_f = U.arrow
      [ S.null_binder (S.bv_to_name t1); S.null_binder (S.bv_to_name t2) ]
      (S.mk_GTotal (S.bv_to_name t3))
    in
    let f = S.gen_bv "f" None t_f in
    let a1 = S.gen_bv "a1" None (mk_gctx (S.bv_to_name t1)) in
    let a2 = S.gen_bv "a2" None (mk_gctx (S.bv_to_name t2)) in
    let ret = Some (Inl (U.lcomp_of_comp (mk_Total (mk_gctx (S.bv_to_name t3))))) in
    U.abs (mk_all_implicit binders @ binders_of_list [ a, true; t1, true; t2, true; t3, true; f, false; a1, false; a2, false ]) (
      U.mk_app c_app (List.map S.as_arg [
        U.mk_app c_app (List.map S.as_arg [
          U.mk_app c_pure (List.map S.as_arg [ S.bv_to_name f ]);
          S.bv_to_name a1 ]);
        S.bv_to_name a2 ])
    ) ret
  in
  let c_lift2 = register env (mk_lid "lift2") c_lift2 in

  (* val st2_push : #heap:Type -> #a:Type -> #t1:Type -> #t2:Type ->
                    f:(t1 -> Tot (st2_gctx heap a t2)) ->
                    Tot (st2_ctx heap a (t1->GTot t2))
    let st2_push #heap #a #t1 #t2 f = fun p h e1 -> f e1 p h *)
  let c_push =
    let t1 = S.gen_bv "t1" None U.ktype in
    let t2 = S.gen_bv "t2" None U.ktype in
    let t_f = U.arrow
      [ S.null_binder (S.bv_to_name t1) ]
      (S.mk_Total (mk_gctx (S.bv_to_name t2)))
    in
    let f = S.gen_bv "f" None t_f in
    let ret = Some (Inl (U.lcomp_of_comp (mk_Total (mk_ctx (
      U.arrow [ S.null_binder (S.bv_to_name t1) ] (S.mk_GTotal (S.bv_to_name t2)))))))
    in
    let e1 = S.gen_bv "e1" None (S.bv_to_name t1) in
    let body = U.abs (gamma @ [ S.mk_binder e1 ]) (
      U.mk_app (S.bv_to_name f) (S.as_arg (S.bv_to_name e1) :: args_of_binders gamma)
    ) ret in
    U.abs (mk_all_implicit binders @ binders_of_list [ a, true; t1, true; t2, true; f, false ]) body ret
  in
  let c_push = register env (mk_lid "push") c_push in

  let ret_tot_wp_a = Some (Inl (U.lcomp_of_comp (mk_Total wp_a))) in
  let mk_generic_app c =
    if List.length binders > 0 then
      mk (Tm_app (c, args_of_binders binders))
    else
      c
  in

  (* val st2_if_then_else : heap:Type -> a:Type -> c:Type0 ->
                            st2_wp heap a -> st2_wp heap a ->
                            Tot (st2_wp heap a)
    let st2_if_then_else heap a c = st2_liftGA2 (l_ITE c) *)
  let wp_if_then_else =
    let result_comp = (mk_Total ((U.arrow [ S.null_binder wp_a; S.null_binder wp_a ] (mk_Total wp_a)))) in
    let c = S.gen_bv "c" None U.ktype in
    U.abs (binders @ S.binders_of_list [ a; c ]) (
      let l_ite = fvar Const.ite_lid (S.Delta_defined_at_level 2) None in
      U.ascribe (
        U.mk_app c_lift2 (List.map S.as_arg [
          U.mk_app l_ite [S.as_arg (S.bv_to_name c)]
        ])
      ) (Inr result_comp, None)
    ) (Some (Inl (U.lcomp_of_comp result_comp)))
  in
  let wp_if_then_else = register env (mk_lid "wp_if_then_else") wp_if_then_else in
  let wp_if_then_else = mk_generic_app wp_if_then_else in

  (* val st2_assert_p : heap:Type ->a:Type -> q:Type0 -> st2_wp heap a ->
                       Tot (st2_wp heap a)
    let st2_assert_p heap a q wp = st2_app (st2_pure (l_and q)) wp *)
  let wp_assert =
    let q = S.gen_bv "q" None U.ktype in
    let wp = S.gen_bv "wp" None wp_a in
    let l_and = fvar Const.and_lid (S.Delta_defined_at_level 1) None in
    let body =
      U.mk_app c_app (List.map S.as_arg [
        U.mk_app c_pure (List.map S.as_arg [
          U.mk_app l_and [S.as_arg (S.bv_to_name q)]]);
        S.bv_to_name wp])
    in
    U.abs (binders @ S.binders_of_list [ a; q; wp ]) body ret_tot_wp_a
  in
  let wp_assert = register env (mk_lid "wp_assert") wp_assert in
  let wp_assert = mk_generic_app wp_assert in

  (* val st2_assume_p : heap:Type ->a:Type -> q:Type0 -> st2_wp heap a ->
                       Tot (st2_wp heap a)
    let st2_assume_p heap a q wp = st2_app (st2_pure (l_imp q)) wp *)
  let wp_assume =
    let q = S.gen_bv "q" None U.ktype in
    let wp = S.gen_bv "wp" None wp_a in
    let l_imp = fvar Const.imp_lid (S.Delta_defined_at_level 1) None in
    let body =
      U.mk_app c_app (List.map S.as_arg [
        U.mk_app c_pure (List.map S.as_arg [
          U.mk_app l_imp [S.as_arg (S.bv_to_name q)]]);
        S.bv_to_name wp])
    in
    U.abs (binders @ S.binders_of_list [ a; q; wp ]) body ret_tot_wp_a
  in
  let wp_assume = register env (mk_lid "wp_assume") wp_assume in
  let wp_assume = mk_generic_app wp_assume in

  (* val st2_close_wp : heap:Type -> a:Type -> b:Type ->
                        f:(b->Tot (st2_wp heap a)) ->
                        Tot (st2_wp heap a)
    let st2_close_wp heap a b f = st2_app (st2_pure l_Forall) (st2_push f) *)
  let wp_close =
    let b = S.gen_bv "b" None U.ktype in
    let t_f = U.arrow [ S.null_binder (S.bv_to_name b) ] (S.mk_Total wp_a) in
    let f = S.gen_bv "f" None t_f in
    let body =
      U.mk_app c_app (List.map S.as_arg [
        U.mk_app c_pure (List.map S.as_arg [ U.tforall ]);
        U.mk_app c_push (List.map S.as_arg [ S.bv_to_name f ])])
    in
    U.abs (binders @ S.binders_of_list [ a; b; f ]) body ret_tot_wp_a
  in
  let wp_close = register env (mk_lid "wp_close") wp_close in
  let wp_close = mk_generic_app wp_close in

  let ret_tot_type = Some (Inl (U.lcomp_of_comp <| S.mk_Total U.ktype)) in
  let ret_gtot_type = Some (Inl (U.lcomp_of_comp <| S.mk_GTotal U.ktype)) in
  let mk_forall (x: S.bv) (body: S.term): S.term =
    S.mk (Tm_app (U.tforall, [ S.as_arg (U.abs [ S.mk_binder x ] body ret_tot_type)])) None Range.dummyRange
  in

  (* For each (target) type t, we define a binary relation in t called ≤_t.

      x ≤_t y            =def=       x = y      [t is base type]
      x ≤_Type0 y        =def=       x ==> y
      x ≤_{a->b} y       =def=       ∀a1 : a, x a1 ≤_b y a1                if is_monotonic a
                                     ∀a1 a2, a1 ≤_a a2 ==> x a1 ≤_b y a2   otherwise
  *)
  (* Invariant: [x] and [y] have type [t] *)
  let rec is_discrete t = match (SS.compress t).n with
    | Tm_type _ -> false
    | Tm_arrow (bs, c) -> List.for_all (fun (b,_) -> is_discrete b.sort) bs && is_discrete (U.comp_result c)
    | _ -> true
  in
  let rec is_monotonic t = match (SS.compress t).n with
    | Tm_type _ -> true
    | Tm_arrow (bs, c) -> List.for_all (fun (b,_) -> is_discrete b.sort) bs && is_monotonic (U.comp_result c)
    | _ -> is_discrete t
  in
  let rec mk_rel rel t x y =
    let mk_rel = mk_rel rel in
    let t = N.normalize [ N.Beta; N.Eager_unfolding; N.UnfoldUntil S.Delta_constant ] env t in
    match (SS.compress t).n with
    | Tm_type _ ->
        (* BU.print2 "type0, x=%s, y=%s\n" (Print.term_to_string x) (Print.term_to_string y); *)
        rel x y
    | Tm_arrow ([ binder ], { n = GTotal (b, _) })
    | Tm_arrow ([ binder ], { n = Total (b, _) }) ->
        let a = (fst binder).sort in
        if is_monotonic a  || is_monotonic b //this is an important special case; most monads have zero-order results
        then let a1 = S.gen_bv "a1" None a in
             let body = mk_rel b
                            (U.mk_app x [ S.as_arg (S.bv_to_name a1) ])
                            (U.mk_app y [ S.as_arg (S.bv_to_name a1) ]) in
             mk_forall a1 body
        else
            (* BU.print2 "arrow, a=%s, b=%s\n" (Print.term_to_string a) (Print.term_to_string b); *)
            let a1 = S.gen_bv "a1" None a in
            let a2 = S.gen_bv "a2" None a in
            let body = U.mk_imp
              (mk_rel a (S.bv_to_name a1) (S.bv_to_name a2))
              (mk_rel b
                (U.mk_app x [ S.as_arg (S.bv_to_name a1) ])
                (U.mk_app y [ S.as_arg (S.bv_to_name a2) ]))
            in
            mk_forall a1 (mk_forall a2 body)
    | Tm_arrow (binder :: binders, comp) -> //TODO: a bit confusing, since binders may be []
        let t = { t with n = Tm_arrow ([ binder ], S.mk_Total (U.arrow binders comp)) } in
        mk_rel t x y
    | Tm_arrow _ ->
        failwith "unhandled arrow"
    | _ ->
        (* TODO: assert that this is a base type. *)
        (* BU.print2 "base, x=%s, y=%s\n" (Print.term_to_string x) (Print.term_to_string y); *)
        U.mk_untyped_eq2 x y
  in
  let stronger =
    let wp1 = S.gen_bv "wp1" None wp_a in
    let wp2 = S.gen_bv "wp2" None wp_a in
    let rec mk_stronger t x y =
        let t = N.normalize [ N.Beta; N.Eager_unfolding; N.UnfoldUntil S.Delta_constant ] env t in
        match (SS.compress t).n with
        | Tm_type _ -> U.mk_imp x y
        | Tm_app (head, args) when is_tuple_constructor (SS.compress head) ->
          let project i tuple =
            (* TODO : I guess a projector shouldn't be handled as a constant... *)
            let projector = S.fvar (Env.lookup_projector env (U.mk_tuple_data_lid (List.length args) Range.dummyRange) i) (S.Delta_defined_at_level 1) None in
            mk_app projector [tuple, None]
          in
          let (rel0,rels) =
              match List.mapi (fun i (t, q) -> mk_stronger t (project i x) (project i y)) args with
                  | [] -> failwith "Impossible : Empty application when creating stronger relation in DM4F"
                  | rel0 :: rels -> rel0, rels
          in
          List.fold_left U.mk_conj rel0 rels
        | Tm_arrow (binders, { n = GTotal (b, _) })
        | Tm_arrow (binders, { n = Total (b, _) }) ->
          let bvs = List.mapi (fun i (bv,q) -> S.gen_bv ("a" ^ string_of_int i) None bv.sort) binders in
          let args = List.map (fun ai -> S.as_arg (S.bv_to_name ai)) bvs in
          let body = mk_stronger b (U.mk_app x args) (U.mk_app y args) in
          List.fold_right (fun bv body -> mk_forall bv body) bvs body
        | _ ->
          failwith "Not a DM elaborated type"
    in
    let body = mk_stronger (U.unascribe wp_a) (S.bv_to_name wp1) (S.bv_to_name wp2) in
    U.abs (binders @ binders_of_list [ a, false; wp1, false; wp2, false ]) body ret_tot_type
  in
  let stronger = register env (mk_lid "stronger") stronger in
  let stronger = mk_generic_app stronger in

  let wp_ite =
    let wp = S.gen_bv "wp" None wp_a in
    let wp_args, post = BU.prefix gamma in
    // forall k: post a
    let k = S.gen_bv "k" None (fst post).sort in
    let equiv =
        let k_tm = S.bv_to_name k in
        let eq = mk_rel U.mk_iff k.sort
                          k_tm
                          (S.bv_to_name (fst post)) in
        match U.destruct_typ_as_formula eq with
        | Some (QAll (binders, [], body)) ->
          let k_app = U.mk_app k_tm (args_of_binders binders) in
          let guard_free =  S.fv_to_tm (S.lid_as_fv Const.guard_free Delta_constant None) in
          let pat = U.mk_app guard_free [as_arg k_app] in
          let pattern_guarded_body = mk (Tm_meta (body, Meta_pattern [[as_arg pat]])) in
          U.close_forall_no_univs binders pattern_guarded_body
        | _ -> failwith "Impossible: Expected the equivalence to be a quantified formula"
    in
    let body  = U.abs gamma (
      U.mk_forall_no_univ k (U.mk_imp
        equiv
        (U.mk_app (S.bv_to_name wp) (args_of_binders wp_args @ [ S.as_arg (S.bv_to_name k) ])))
    ) ret_gtot_type in
    U.abs (binders @ S.binders_of_list [ a; wp ]) body ret_gtot_type
  in
  let wp_ite = register env (mk_lid "wp_ite") wp_ite in
  let wp_ite = mk_generic_app wp_ite in

  let null_wp =
    let wp = S.gen_bv "wp" None wp_a in
    let wp_args, post = BU.prefix gamma in
    let x = S.gen_bv "x" None S.tun in
    let body = U.mk_forall_no_univ x (U.mk_app (S.bv_to_name <| fst post) [as_arg (S.bv_to_name x)]) in
    U.abs (binders @ S.binders_of_list [ a ] @ gamma) body ret_gtot_type in

  let null_wp = register env (mk_lid "null_wp") null_wp in
  let null_wp = mk_generic_app null_wp in

  (* val st2_trivial : heap:Type ->a:Type -> st2_wp heap a -> Tot Type0
    let st2_trivial heap a wp = st2_stronger heap a (st2_null_wp heap a) wp *)
  let wp_trivial =
    let wp = S.gen_bv "wp" None wp_a in
    let body = U.mk_app stronger (List.map S.as_arg [
      S.bv_to_name a;
      U.mk_app null_wp [ S.as_arg (S.bv_to_name a) ];
      S.bv_to_name wp
    ]) in
    U.abs (binders @ S.binders_of_list [ a; wp ]) body ret_tot_type
  in
  let wp_trivial = register env (mk_lid "wp_trivial") wp_trivial in
  let wp_trivial = mk_generic_app wp_trivial in

  if Env.debug env (Options.Other "ED") then
    d "End Dijkstra monads for free";

  let c = close binders in
  List.rev !sigelts, { ed with
    if_then_else = ([], c wp_if_then_else);
    assert_p     = ([], c wp_assert);
    assume_p     = ([], c wp_assume);
    close_wp     = ([], c wp_close);
    stronger     = ([], c stronger);
    trivial      = ([], c wp_trivial);
    ite_wp       = ([], c wp_ite);
    null_wp      = ([], c null_wp)
  }


// Some helpers for... --------------------------------------------------------
type env_ = env

let get_env env = env.env
let set_env dmff_env env' = { dmff_env with env = env' }

type nm = | N of typ | M of typ

type nm_ = nm

let nm_of_comp = function
  | Total (t, _) ->
      N t
  | Comp c when c.flags |> BU.for_some (function CPS -> true | _ -> false) ->
                //lid_equals c.effect_name Const.monadic_lid ->
      M c.result_typ
  | Comp c ->
      failwith (BU.format1 "[nm_of_comp]: impossible (%s)" (Print.comp_to_string <| mk_Comp c))
  | GTotal _ ->
      failwith "[nm_of_comp]: impossible (GTot)"

let string_of_nm = function
  | N t -> BU.format1 "N[%s]" (Print.term_to_string t)
  | M t -> BU.format1 "M[%s]" (Print.term_to_string t)

let is_monadic_arrow n =
  match n with
  | Tm_arrow (_, { n = n}) ->
      nm_of_comp n
  | _ ->
      failwith "unexpected_argument: [is_monadic_arrow]"

let is_monadic_comp c =
  match nm_of_comp c.n with
  | M _ -> true
  | N _ -> false


exception Not_found

// ... the _ and * transformations from the definition language to F* ---------

let double_star typ =
    let star_once typ = U.arrow [S.mk_binder <| S.new_bv None typ] (S.mk_Total U.ktype0) in
    star_once <| typ |> star_once

let rec mk_star_to_type mk env a =
  mk (Tm_arrow (
    [S.null_bv (star_type' env a), S.as_implicit false],
    mk_Total U.ktype0
  ))

// The *-transformation for types, purely syntactic. Has been enriched with the
// [Tm_abs] case to account for parameterized types

and star_type' env t =
  let mk x = mk x None t.pos in
  let mk_star_to_type = mk_star_to_type mk in
  //BU.print1 "[debug]: star_type' %s\n" (Print.term_to_string t);
  let t = SS.compress t in
  match t.n with
  | Tm_arrow (binders, _) ->
      // TODO: check that this is not a dependent arrow.
      let binders = List.map (fun (bv, aqual) ->
        { bv with sort = star_type' env bv.sort }, aqual
      ) binders in
      (* Catch the GTotal case early; it seems relatively innocuous to allow
       * GTotal to appear. TODO fix this as a clean, single pattern-matching. *)
      begin match t.n with
      | Tm_arrow (_, { n = GTotal (hn, _) }) ->
          mk (Tm_arrow (binders, mk_GTotal (star_type' env hn)))
      | _ ->
          match is_monadic_arrow t.n with
          | N hn ->
              // Simple case:
              //   (H_0  -> ... -> H_n)* = H_0* -> ... -> H_n*
              mk (Tm_arrow (binders, mk_Total (star_type' env hn)))
          | M a ->
              // F*'s arrows are n-ary (and the intermediary arrows are pure), so the rule is:
              //   (H_0  -> ... -> H_n  -t-> A)* = H_0* -> ... -> H_n* -> (A* -> Type) -> Type
              mk (Tm_arrow (
                binders @ [ S.null_bv (mk_star_to_type env a), S.as_implicit false ],
                mk_Total U.ktype0))
      end

  | Tm_app (head, args) ->
      // Sums and products. TODO: re-use the cache in [env] to not recompute
      // (st a)* every time.
      let debug t s =
        let string_of_set f s =
            let elts = BU.set_elements s in
            match elts with
            | [] -> "{}"
            | x::xs ->
                let strb = BU.new_string_builder () in
                BU.string_builder_append strb "{" ;
                BU.string_builder_append strb (f x) ;
                List.iter (fun x ->
                    BU.string_builder_append strb ", " ;
                    BU.string_builder_append strb (f x)
                ) xs ;
                BU.string_builder_append strb "}" ;
                BU.string_of_string_builder strb
        in
        BU.print2_warning "Dependency found in term %s : %s" (Print.term_to_string t) (string_of_set Print.bv_to_string s)
      in
      let rec is_non_dependent_arrow ty n =
        match (SS.compress ty).n with
        | Tm_arrow (binders, c) -> begin
                if not (U.is_tot_or_gtot_comp c)
                then false
                else
                    try
                        let non_dependent_or_raise s ty =
                            let sinter = set_intersect (Free.names ty) s in
                            if  not (set_is_empty sinter)
                            then (debug ty sinter ; raise Not_found)
                        in
                        let binders, c = SS.open_comp binders c in
                        let s = List.fold_left (fun s (bv, _) ->
                            non_dependent_or_raise s bv.sort ;
                            set_add bv s
                        ) S.no_names binders in
                        let ct = U.comp_result c in
                        non_dependent_or_raise s ct ;
                        let k = n - List.length binders in
                        if k > 0 then is_non_dependent_arrow ct k else true
                    with Not_found -> false
            end
        | _ ->
            BU.print1_warning "Not a dependent arrow : %s" (Print.term_to_string ty) ;
            false
      in
      let rec is_valid_application head =
        match (SS.compress head).n with
        | Tm_fvar fv when (
          // TODO: implement a better check (non-dependent, user-defined data type)
          fv_eq_lid fv Const.option_lid ||
          fv_eq_lid fv Const.either_lid ||
          fv_eq_lid fv Const.eq2_lid ||
          is_tuple_constructor (SS.compress head)
        ) ->
            true
        | Tm_fvar fv when is_non_dependent_arrow fv.fv_name.ty (List.length args) ->
            // We need to check that the result of the application is a datatype
             let res = N.normalize [N.Inlining ; N.UnfoldUntil S.Delta_constant] env.env t in
             begin match res.n with
             | Tm_app _ -> true
             | _ ->
                BU.print1_warning "Got a term which might be a non-dependent user-defined data-type %s\n" (Print.term_to_string head) ;
                false
             end
        | Tm_bvar _
        | Tm_name _ ->
            true
        | Tm_uinst (t, _) ->
            is_valid_application t
        | _ ->
            false
      in
      if is_valid_application head then
        mk (Tm_app (head, List.map (fun (t, qual) -> star_type' env t, qual) args))
      else
        raise (Err (BU.format1 "For now, only [either], [option] and [eq2] are \
          supported in the definition language (got: %s)"
            (Print.term_to_string t)))

  | Tm_bvar _
  | Tm_name _
  | Tm_type _ // TODO: does [Tm_type] make sense?
  | Tm_fvar _ ->
      t

  | Tm_abs (binders, repr, something) ->
      // For parameterized data types... TODO: check that this only appears at
      // top-level
      let binders, repr = SS.open_term binders repr in
      let env = { env with env = push_binders env.env binders } in
      let repr = star_type' env repr in
      U.abs binders repr something

  | Tm_refine (x, t) when false ->
      let x = freshen_bv x in
      let sort = star_type' env x.sort in
      let subst = [DB(0, x)] in
      let t = SS.subst subst t in
      let t = star_type' env t in
      let subst = [NM(x, 0)] in
      let t = SS.subst subst t in
      mk (Tm_refine ({ x with sort = sort }, t))

  | Tm_meta (t, m) ->
      mk (Tm_meta (star_type' env t, m))

  | Tm_ascribed (e, (Inl t, None), something) ->
      mk (Tm_ascribed (star_type' env e, (Inl (star_type' env t), None), something))

  | Tm_ascribed _ ->
      raise (Err (BU.format1 "Tm_ascribed is outside of the definition language: %s"
        (Print.term_to_string t)))

  | Tm_refine _ ->
      raise (Err (BU.format1 "Tm_refine is outside of the definition language: %s"
        (Print.term_to_string t)))

  | Tm_uinst _ ->
      raise (Err (BU.format1 "Tm_uinst is outside of the definition language: %s"
        (Print.term_to_string t)))
  | Tm_constant _ ->
      raise (Err (BU.format1 "Tm_constant is outside of the definition language: %s"
        (Print.term_to_string t)))
  | Tm_match _ ->
      raise (Err (BU.format1 "Tm_match is outside of the definition language: %s"
        (Print.term_to_string t)))
  | Tm_let _ ->
      raise (Err (BU.format1 "Tm_let is outside of the definition language: %s"
        (Print.term_to_string t)))
  | Tm_uvar _ ->
      raise (Err (BU.format1 "Tm_uvar is outside of the definition language: %s"
        (Print.term_to_string t)))
  | Tm_unknown ->
      raise (Err (BU.format1 "Tm_unknown is outside of the definition language: %s"
        (Print.term_to_string t)))

  | Tm_delayed _ ->
      failwith "impossible"


// The bi-directional *-transformation and checker for expressions ------------

let is_monadic = function
  | None ->
      failwith "un-annotated lambda?!"
  | Some (Inl { cflags = flags }) | Some (Inr (_, flags)) ->
      // lid_equals lid Const.monadic_lid
      flags |> BU.for_some (function CPS -> true | _ -> false)

// TODO: this function implements a (partial) check for the well-formedness of
// C-types...
// This function expects its argument [t] to be normalized.
let rec is_C (t: typ): bool =
  match (SS.compress t).n with
  // TODO: deal with more than tuples?
  | Tm_app (head, args) when U.is_tuple_constructor head ->
      let r = is_C (fst (List.hd args)) in
      if r then begin
        if not (List.for_all (fun (h, _) -> is_C h) args) then
          failwith "not a C (A * C)";
        true
      end else begin
        if not (List.for_all (fun (h, _) -> not (is_C h)) args) then
          failwith "not a C (C * A)";
        false
      end
  | Tm_arrow (binders, comp) ->
      begin match nm_of_comp comp.n with
      | M t ->
          if (is_C t) then
            failwith "not a C (C -> C)";
          true
      | N t ->
          // assert (List.exists is_C binders) ==> is_C comp
          is_C t
      end
  | Tm_meta (t, _)
  | Tm_uinst (t, _)
  | Tm_ascribed (t, _, _) ->
      is_C t
  | _ ->
      false


// This function assumes [e] has been starred already and returns:
//   [fun (p: t* -> Type) -> p e]
let mk_return env (t: typ) (e: term) =
  let mk x = mk x None e.pos in
  let p_type = mk_star_to_type mk env t in
  let p = S.gen_bv "p'" None p_type in
  let body = mk (Tm_app (S.bv_to_name p, [ e, S.as_implicit false ])) in
  U.abs [ S.mk_binder p ] body (Some (Inl (U.lcomp_of_comp (S.mk_Total U.ktype0))))

let is_unknown = function | Tm_unknown -> true | _ -> false

// [check] takes four kinds of [nm].
// - [N Tm_unknown] checks that the computation is pure and returns [N t] where
//   [t] is the inferred type of the original term;
// - [M Tm_unknown] checks that the computation is monadic and returns [N t]
//   where [t] is the inferred type of the original term;
// - [N T] checks that the computation is pure, has type T, and returns [N t];
// - [M T] checks that the computation is monadic, has type T, and returns [M t];
// [check] returns two terms:
// - the first is [e*], the CPS'd version of [e]
// - the second is [_e_], the elaborated version of [e]
let rec check (env: env) (e: term) (context_nm: nm): nm * term * term =
  // BU.print1 "[debug]: check %s\n" (Print.term_to_string e);
  let mk x = mk x None e.pos in
  // [s_e] as in "starred e"; [u_e] as in "underlined u" (per the paper)
  let return_if (rec_nm, s_e, u_e) =
    let check t1 t2 =
      if not (is_unknown t2.n) && not (Rel.is_trivial (Rel.teq env.env t1 t2)) then
        raise (Err (BU.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]"
          (Print.term_to_string e) (Print.term_to_string t1) (Print.term_to_string t2)))
    in
    match rec_nm, context_nm with
    | N t1, N t2
    | M t1, M t2 ->
        check t1 t2;
        rec_nm, s_e, u_e
    | N t1, M t2 ->
        check t1 t2;
        // no need to wrap [u_e] in an explicit [return]; F* will infer it later on
        M t1, mk_return env t1 s_e, u_e
    | M t1,  N t2 ->
        raise (Err (BU.format3
          "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
          (Print.term_to_string e)
          (Print.term_to_string t1)
          (Print.term_to_string t2)))

  in

  let ensure_m (env: env_) (e2: term): term * term * term =
    let strip_m = function
      | M t, s_e, u_e -> t, s_e, u_e
      | _ -> failwith "impossible"
    in
    match context_nm with
    | N t -> raise (Error ("let-bound monadic body has a non-monadic continuation \
        or a branch of a match is monadic and the others aren't : "  ^ Print.term_to_string t, e2.pos))
    | M _ -> strip_m (check env e2 context_nm)
  in

  match (SS.compress e).n with
  | Tm_bvar _
  | Tm_name _
  | Tm_fvar _
  | Tm_abs _
  | Tm_constant _
  | Tm_app _ ->
      return_if (infer env e)

  | Tm_let ((false, [ binding ]), e2) ->
      mk_let env binding e2
        // Body of the let is pure: just defer the check to the continuation
        (fun env e2 -> check env e2 context_nm)
        // Body of the let is monadic: this is a bind, and we must strengthen
        // the check on the continuation to ensure it is a monadic computation
        ensure_m

  | Tm_match (e0, branches) ->
      // This is similar to the [let] case above. The [match] checks that the
      // types of the branches work; it also demands that the scrutinee be a
      // non-monadic computation.
      mk_match env e0 branches (fun env body -> check env body context_nm)

  | Tm_meta (e, _)
  | Tm_uinst (e, _)
  | Tm_ascribed (e, _, _) ->
      (* TODO : reinstall the type annotation *)
      check env e context_nm

  | Tm_let _ ->
      failwith (BU.format1 "[check]: Tm_let %s" (Print.term_to_string e))
  | Tm_type _ ->
      failwith "impossible (DM stratification)"
  | Tm_arrow _ ->
      failwith "impossible (DM stratification)"
  | Tm_refine _ ->
      failwith (BU.format1 "[check]: Tm_refine %s" (Print.term_to_string e))
  | Tm_uvar _ ->
      failwith (BU.format1 "[check]: Tm_uvar %s" (Print.term_to_string e))
  | Tm_delayed _ ->
      failwith "impossible (compressed)"
  | Tm_unknown ->
      failwith (BU.format1 "[check]: Tm_unknown %s" (Print.term_to_string e))


and infer (env: env) (e: term): nm * term * term =
  // BU.print1 "[debug]: infer %s\n" (Print.term_to_string e);
  let mk x = mk x None e.pos in
  let normalize = N.normalize [ N.Beta; N.Eager_unfolding; N.UnfoldUntil S.Delta_constant; N.EraseUniverses ] env.env in
  match (SS.compress e).n with
  | Tm_bvar bv ->
      failwith "I failed to open a binder... boo"

  | Tm_name bv ->
      N bv.sort, e, e

  | Tm_abs (binders, body, what) ->
      let binders = SS.open_binders binders in
      let subst = SS.opening_of_binders binders in
      let body = SS.subst subst body in
      let env = { env with env = push_binders env.env binders } in

      // For the *-translation, [x: t] becomes [x: t*].
      let s_binders = List.map (fun (bv, qual) ->
        let sort = star_type' env bv.sort in
        { bv with sort = sort }, qual
      ) binders in

      // For the _-translation, things are a little bit trickier. We need to
      // update the substitution, and one binder may turn into two binders.
      let env, u_binders = List.fold_left (fun (env, acc) (bv, qual) ->
        let c = bv.sort in
        if is_C c then
          let xw = S.gen_bv (bv.ppname.idText ^ "__w") None (star_type' env c) in
          let x = { bv with sort = trans_F_ env c (S.bv_to_name xw) } in
          let env = { env with subst = NT (bv, S.bv_to_name xw) :: env.subst } in
          env, S.mk_binder x :: S.mk_binder xw :: acc
        else
          let x = { bv with sort = star_type' env bv.sort } in
          env, S.mk_binder x :: acc
      ) (env, []) binders in
      let u_binders = List.rev u_binders in

      (*
      BU.print2_warning "Term %s ::: what %s \n"
                                (Print.term_to_string body)
                                (Print.abs_ascription_to_string what) ;
      *)

      let comp, s_body, u_body =
        let check_what = if is_monadic what then check_m else check_n in
        let t, s_body, u_body = check_what env body in
        comp_of_nm (if is_monadic what then M t else N t), s_body, u_body
      in

      // From [comp], the inferred computation type for the (original), return
      // the inferred type for the original term.
      let t = U.arrow binders comp in

      let s_what = match what with
        | None -> None // That should not happen according to some other comment
        | Some (Inl lc) ->
            if lc.cflags |> BU.for_some (function CPS -> true | _ -> false)
            then
                let double_starred_comp = S.mk_Total (double_star <| U.comp_result (lc.comp ())) in
                let flags = List.filter (function CPS -> false | _ -> true) lc.cflags in
                Some (Inl (U.lcomp_of_comp (comp_set_flags double_starred_comp flags)))
            else Some (Inl ({ lc with comp = begin fun () ->
                        let c = lc.comp () in
                        let result_typ = star_type' env (U.comp_result c) in
                        U.set_result_typ c result_typ
                      end  }))
        | Some (Inr (lid, flags)) ->
            Some (Inr (if flags |> BU.for_some (function CPS -> true | _ -> false)
                       then (Const.effect_Tot_lid, List.filter (function CPS -> false | _ -> true) flags)
                       else (lid, flags)))
      in

      let u_body, u_what =
          let comp = trans_G env (U.comp_result comp) (is_monadic what) (SS.subst env.subst s_body) in
          (* TODO : consider removing this ascription *)
          U.ascribe u_body (Inr comp, None), Some (Inl (U.lcomp_of_comp comp))
      in

      let s_body = close s_binders s_body in
      let s_binders = close_binders s_binders in
      let s_term = mk (Tm_abs (s_binders, s_body, s_what)) in

      let u_body = close u_binders u_body in
      let u_binders = close_binders u_binders in
      let u_term = mk (Tm_abs (u_binders, u_body, u_what)) in
      N t, s_term, u_term

  | Tm_fvar { fv_name = { v = lid } } ->
      let _, t = fst <| Env.lookup_lid env.env lid in
      // Need to erase universes here! This is an F* type that is fully annotated.
      N (normalize t), e, e

  | Tm_app (head, args) ->
      let t_head, s_head, u_head = check_n env head in
      let is_arrow t = match (SS.compress t).n with | Tm_arrow _ -> true | _ -> false in
      // TODO: replace with BU.arrow_formals_comp
      let rec flatten t = match (SS.compress t).n with
        | Tm_arrow (binders, { n = Total (t, _) }) when is_arrow t ->
            let binders', comp = flatten t in
            binders @ binders', comp
        | Tm_arrow (binders, comp) ->
            binders, comp
        | Tm_ascribed (e, _, _) ->
            flatten e
        | _ ->
            raise (Err (BU.format1 "%s: not a function type" (Print.term_to_string t_head)))
      in
      let binders, comp = flatten t_head in
      // BU.print1 "[debug] type of [head] is %s\n" (Print.term_to_string t_head);

      // Making the assumption here that [Tm_arrow (..., Tm_arrow ...)]
      // implies [is_M comp]. F* should be fixed if it's not the case.
      let n = List.length binders in
      let n' = List.length args in
      if List.length binders < List.length args then
        raise (Err (BU.format3 "The head of this application, after being applied to %s \
          arguments, is an effectful computation (leaving %s arguments to be \
          applied). Please let-bind the head applied to the %s first \
          arguments." (string_of_int n) (string_of_int (n' - n)) (string_of_int n)));
      // BU.print2 "[debug] length binders=%s, length args=%s\n"
      //  (string_of_int n) (string_of_int n');

      let binders, comp = SS.open_comp binders comp in
      let rec final_type subst (binders, comp) args =
        match binders, args with
        | [], [] ->
            nm_of_comp (SS.subst_comp subst comp).n
        | binders, [] ->
            begin match (SS.compress (SS.subst subst (mk (Tm_arrow (binders, comp))))).n with
            | Tm_arrow (binders, comp) -> N (mk (Tm_arrow (binders, close_comp binders comp)))
            | _ -> failwith "wat?"
            end
        | [], _ :: _ ->
            failwith "just checked that?!"
        | (bv, _) :: binders, (arg, _) :: args ->
            final_type (NT (bv, arg) :: subst) (binders, comp) args
      in
      let final_type = final_type [] (binders, comp) args in
      // BU.print1 "[debug]: final type of application is %s\n" (string_of_nm final_type);

      let binders, _ = List.splitAt n' binders in

      let s_args, u_args = List.split (List.map2 (fun (bv, _) (arg, q) ->
        // TODO: implement additional check that the arguments are T-free if
        // head is [Tm_fvar ...] with [Mktuple], [Left], etc.
        // Note: not enforcing the types of the arguments because 1) it has
        // been enforced by the main F* type-checker and 2) it's a hassle with
        // binders and stuff
        match (SS.compress bv.sort).n with
        | Tm_type _ ->
            let arg = arg, q in
            arg, [ arg ]
        | _ ->
            let _, s_arg, u_arg = check_n env arg in
            (s_arg, q),
                (if is_C bv.sort
                then [ SS.subst env.subst s_arg, q; u_arg, q]
                else [ u_arg, q])
      ) binders args) in
      let u_args = List.flatten u_args in

      final_type, mk (Tm_app (s_head, s_args)), mk (Tm_app (u_head, u_args))

  | Tm_let ((false, [ binding ]), e2) ->
      mk_let env binding e2 infer check_m

  | Tm_match (e0, branches) ->
      mk_match env e0 branches infer

  | Tm_uinst (e, _)
  | Tm_meta (e, _)
  | Tm_ascribed (e, _, _) ->
      infer env e

  | Tm_constant c ->
      N (env.tc_const c), e, e

  | Tm_let _ ->
      failwith (BU.format1 "[infer]: Tm_let %s" (Print.term_to_string e))
  | Tm_type _ ->
      failwith "impossible (DM stratification)"
  | Tm_arrow _ ->
      failwith "impossible (DM stratification)"
  | Tm_refine _ ->
      failwith (BU.format1 "[infer]: Tm_refine %s" (Print.term_to_string e))
  | Tm_uvar _ ->
      failwith (BU.format1 "[infer]: Tm_uvar %s" (Print.term_to_string e))
  | Tm_delayed _ ->
      failwith "impossible (compressed)"
  | Tm_unknown ->
      failwith (BU.format1 "[infer]: Tm_unknown %s" (Print.term_to_string e))

and mk_match env e0 branches f =
  let mk x = mk x None e0.pos in

  // TODO: automatically [bind] when the scrutinee is monadic?
  let _, s_e0, u_e0 = check_n env e0 in
  let nms, branches = List.split (List.map (fun b ->
    match open_branch b with
    | pat, None, body ->
        let env = { env with env = List.fold_left push_bv env.env (pat_bvs pat) } in
        let nm, s_body, u_body = f env body in
        nm, (pat, None, (s_body, u_body, body))
    | _ ->
        raise (Err ("No when clauses in the definition language"))
  ) branches) in
  let t1 = match List.hd nms with | M t1 | N t1 -> t1 in
  let has_m = List.existsb (function | M _ -> true | _ -> false) nms in
  let nms, s_branches, u_branches = List.unzip3 (List.map2 (fun nm (pat, guard, (s_body, u_body, original_body)) ->
    match nm, has_m with
    | N t2, false
    | M t2, true ->
        nm, (pat, guard, s_body), (pat, guard, u_body)
    | N t2, true ->
        // In checking mode, all the branches are run through "check"... meaning
        // that they're either all N or all M... the lift from N to M can only
        // occur in infer mode... instead of calling [mk_return s_body],
        // re-check_m everything and get code that's better for z3
        let _, s_body, u_body = check env original_body (M t2) in
        M t2, (pat, guard, s_body), (pat, guard, u_body)
    | M _, false ->
        failwith "impossible"
  ) nms branches) in

  if has_m then begin
    // if the return type is monadic we add a
    // (fun p -> match ... with ... -> branch p)
    // in order to help the SMT
    // p: A* -> Type
    let p_type = mk_star_to_type mk env t1 in
    let p = S.gen_bv "p''" None p_type in
    let s_branches = List.map (fun (pat, guard, s_body) ->
      let s_body = mk (Tm_app (s_body, [ S.bv_to_name p, S.as_implicit false ])) in
        (pat, guard, s_body)
      ) s_branches in
    let s_branches = List.map close_branch s_branches in
    let u_branches = List.map close_branch u_branches in
    let s_e =
      U.abs [ S.mk_binder p ]
            (mk (Tm_match (s_e0, s_branches)))
            (Some (Inl (U.lcomp_of_comp (S.mk_Total U.ktype0))))
    in
    let t1_star =  U.arrow [S.mk_binder <| S.new_bv None p_type] (S.mk_Total U.ktype0) in
    M t1,
    mk (Tm_ascribed (s_e, (Inl t1_star, None), None)) ,
    mk (Tm_match (u_e0, u_branches))
  end else begin
    let s_branches = List.map close_branch s_branches in
    let u_branches = List.map close_branch u_branches in
    let t1_star = t1 in
    N t1,
    mk (Tm_ascribed (mk (Tm_match (s_e0, s_branches)), (Inl t1_star, None), None)),
    mk (Tm_match (u_e0, u_branches))
  end

and mk_let (env: env_) (binding: letbinding) (e2: term)
    (proceed: env_ -> term -> nm * term * term)
    (ensure_m: env_ -> term -> term * term * term) =
  let mk x = mk x None e2.pos in
  let e1 = binding.lbdef in
  // This is [let x = e1 in e2]. Open [x] in [e2].
  let x = BU.left binding.lbname in
  let x_binders = [ S.mk_binder x ] in
  let x_binders, e2 = SS.open_term x_binders e2 in
  begin match infer env e1 with
  | N t1, s_e1, u_e1 ->
      // BU.print1 "[debug] %s is NOT a monadic let-binding\n" (Print.lbname_to_string binding.lbname);
      // TODO : double-check  that correct env and lbeff are used
      let u_binding =
        if is_C t1
        then { binding with lbtyp = trans_F_ env t1 (SS.subst env.subst s_e1) }
        else binding
      in
      // Piggyback on the environment to carry our own special terms
      let env = { env with env = push_bv env.env ({ x with sort = t1 }) } in
      // Simple case: just a regular let-binding. We defer checks to e2.
      let nm_rec, s_e2, u_e2 = proceed env e2 in
      let s_binding = { binding with lbtyp = star_type' env binding.lbtyp } in
      nm_rec,
      mk (Tm_let ((false, [ { s_binding with lbdef = s_e1 } ]), SS.close x_binders s_e2)),
      mk (Tm_let ((false, [ { u_binding with lbdef = u_e1 } ]), SS.close x_binders u_e2))

  | M t1, s_e1, u_e1 ->
      // BU.print1 "[debug] %s IS a monadic let-binding\n" (Print.lbname_to_string binding.lbname);
      let u_binding = { binding with lbeff = Const.effect_PURE_lid ; lbtyp = t1 } in
      let env = { env with env = push_bv env.env ({ x with sort = t1 }) } in
      let t2, s_e2, u_e2 = ensure_m env e2 in
      // Now, generate the bind.
      // p: A* -> Type
      let p_type = mk_star_to_type mk env t2 in
      let p = S.gen_bv "p''" None p_type in
      // e2* p
      let s_e2 = mk (Tm_app (s_e2, [ S.bv_to_name p, S.as_implicit false ])) in
      // fun x -> s_e2* p; this takes care of closing [x].
      let s_e2 = U.abs x_binders s_e2 (Some (Inl (U.lcomp_of_comp (S.mk_Total U.ktype0)))) in
      // e1* (fun x -> e2* p)
      let body = mk (Tm_app (s_e1, [ s_e2, S.as_implicit false ])) in
      M t2,
      U.abs [ S.mk_binder p ] body (Some (Inl (U.lcomp_of_comp (S.mk_Total U.ktype0)))),
      mk (Tm_let ((false, [ { u_binding with lbdef = u_e1 } ]), SS.close x_binders u_e2))
  end


and check_n (env: env_) (e: term): typ * term * term =
  let mn = N (mk Tm_unknown None e.pos) in
  match check env e mn with
  | N t, s_e, u_e -> t, s_e, u_e
  | _ -> failwith "[check_n]: impossible"

and check_m (env: env_) (e: term): typ * term * term =
  let mn = M (mk Tm_unknown None e.pos) in
  match check env e mn with
  | M t, s_e, u_e -> t, s_e, u_e
  | _ -> failwith "[check_m]: impossible"

and comp_of_nm (nm: nm_): comp =
  match nm with
  | N t -> mk_Total t
  | M t -> mk_M t

and mk_M (t: typ): comp =
  mk_Comp ({
    comp_univs=[U_unknown];
    effect_name = Const.monadic_lid;
    result_typ = t;
    effect_args = [];
    flags = [CPS ; TOTAL]
  })

and type_of_comp t = U.comp_result t

// This function expects its argument [c] to be normalized and to satisfy [is_C c]
and trans_F_ (env: env_) (c: typ) (wp: term): term =
  if not (is_C c) then
    failwith "not a C";
  let mk x = mk x None c.pos in
  match (SS.compress c).n with
  | Tm_app (head, args) ->
      // It's a product, the only form of [Tm_app] allowed.
      let wp_head, wp_args = head_and_args wp in
      if not (List.length wp_args = List.length args) ||
         not (is_constructor wp_head (mk_tuple_data_lid (List.length wp_args) Range.dummyRange)) then
        failwith "mismatch";
      mk (Tm_app (head, List.map2 (fun (arg, q) (wp_arg, q') ->
        let print_implicit q = if S.is_implicit q then "implicit" else "explicit" in
        if q <> q' then BU.print2_warning "Incoherent implicit qualifiers %b %b" (print_implicit q) (print_implicit q') ;
        trans_F_ env arg wp_arg, q)
      args wp_args))
  | Tm_arrow (binders, comp) ->
      let binders = U.name_binders binders in
      let binders_orig, comp = open_comp binders comp in
      let bvs, binders = List.split (List.map (fun (bv, q) ->
        let h = bv.sort in
        if is_C h then
          let w' = S.gen_bv (bv.ppname.idText ^ "__w'") None (star_type' env h) in
          w', [ w', q; S.null_bv (trans_F_ env h (S.bv_to_name w')), q ]
        else
          let x = S.gen_bv (bv.ppname.idText ^ "__x") None (star_type' env h) in
          x, [ x, q ]
      ) binders_orig) in
      let binders = List.flatten binders in
      let comp = SS.subst_comp (U.rename_binders binders_orig (S.binders_of_list bvs)) comp in
      let app = mk (Tm_app (wp, List.map (fun bv -> S.bv_to_name bv, S.as_implicit false) bvs)) in
      let comp = trans_G env (type_of_comp comp) (is_monadic_comp comp) app in
      U.arrow binders comp
  | Tm_ascribed(e, _, _) ->
      (* TODO : find a way to recompute the corrected ascription *)
      trans_F_ env e wp
  | _ ->
      failwith "impossible trans_F_"

and trans_G (env: env_) (h: typ) (is_monadic: bool) (wp: typ): comp =
  let mk x = mk x None h.pos in
  if is_monadic then
    mk_Comp ({
      comp_univs = [U_unknown];
      effect_name = Const.effect_PURE_lid;
      result_typ = star_type' env h;
      effect_args = [ wp, S.as_implicit false ];
      flags = []
    })
  else
    mk_Total (trans_F_ env h wp)

// A helper --------------------------------------------------------------------

(* KM : why is there both NoDeltaSteps and UnfoldUntil Delta_constant ? *)
let n = N.normalize [ N.Beta; N.UnfoldUntil Delta_constant; N.NoDeltaSteps; N.Eager_unfolding; N.EraseUniverses ]

// Exported definitions -------------------------------------------------------

let star_type env t =
  star_type' env (n env.env t)

let star_expr env t =
  check_n env (n env.env t)

let trans_F (env: env_) (c: typ) (wp: term): term =
  trans_F_ env (n env.env c) (n env.env wp)
