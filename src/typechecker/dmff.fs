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

open FStar
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.Util
open FStar.Ident
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
module U  = FStar.Syntax.Util

// Synthesis of WPs from a partial effect definition (in F*) ------------------

let gen_wps_for_free
  env (binders: binders) (a: bv) (wp_a: term) tc_decl tc_term (ed: Syntax.eff_decl):
  _ * Syntax.eff_decl
=
  // [wp_a] has been type-checked and contains universe unification variables;
  // we want to re-use [wp_a] and make it re-generalize accordingly
  // let wp_a = N.normalize [N.Beta; N.EraseUniverses] env wp_a in
  let a = { a with sort = N.normalize [ N.EraseUniverses ] env a.sort } in

  // Debugging
  let d s = Util.print1 "\x1b[01;36m%s\x1b[00m\n" s in
  d "Elaborating extra WP combinators";
  Util.print1 "wp_a is: %s\n" (Print.term_to_string wp_a);

  let check env str t =
    if Env.debug env (Options.Other "ED") then begin
      d str;
      Util.print2 "Generated term for %s: %s\n" str (Print.term_to_string t);
      let t, { res_typ = res_typ }, _ = tc_term env t in
      let res_typ = N.normalize [ N.Beta; N.Inline; N.UnfoldUntil S.Delta_constant ] env res_typ in
      Util.print2 "Inferred type for %s: %s\n" str (Print.term_to_string res_typ)
    end
  in

  (* Consider the predicate transformer st_wp:
   *   let st_pre_h  (heap:Type)          = heap -> GTot Type0
   *   let st_post_h (heap:Type) (a:Type) = a -> heap -> GTot Type0
   *   let st_wp_h   (heap:Type) (a:Type) = st_post_h heap a -> Tot (st_pre_h heap)
   * after reduction we get:
   *   let st_wp_h (heap: Type) (a: Type) = (a -> heap -> GTot Type0) -> heap -> GTot Type0
   * we want:
   *   type st2_gctx (heap: Type) (a:Type) (t:Type) = (a -> heap -> GTot Type0) -> heap -> GTot t
   * we thus generate macros parameterized over [e] that build the right
   * context. [gamma] is the series of binders the precede the return type of
   * the context. *)
  let rec collect_binders (t : term) =
    match (compress t).n with
    | Tm_arrow (bs, comp) ->
        // TODO: dubious, assert no nested arrows
        let rest = match comp.n with
          | Total t -> t
          | _ -> failwith "wp_a contains non-Tot arrow"
        in
        bs @ (collect_binders rest)
    | Tm_type _ ->
        []
    | _ ->
        failwith "wp_a doesn't end in Type0" in

  let mk_lid name: lident =
    lid_of_path (path_of_text (text_of_lid ed.mname ^ "_" ^ name)) Range.dummyRange
  in

  let gamma = collect_binders wp_a in
  d (Util.format1 "Gamma is %s\n" (Print.binders_to_string ", " gamma));
  let unknown = S.tun in
  let mk x = mk x None Range.dummyRange in
  let register env lident def = TcUtil.register_toplevel_definition env tc_decl lident def in

  (* Some helpers. *)
  let binders_of_list = List.map (fun (t, b) -> t, S.as_implicit b) in
  let mk_all_implicit = List.map (fun t -> fst t, S.as_implicit true) in
  let args_of_binders = List.map (fun bv -> S.as_arg (S.bv_to_name (fst bv))) in

  let env, mk_ctx, mk_gctx =
    // Neither [ctx_def] or [gctx_def] take implicit arguments.
    let ctx_def, gctx_def =
      let mk f: term =
        let t = S.gen_bv "t" None Util.ktype in
        let body = U.arrow gamma (f (S.bv_to_name t)) in
        U.abs (binders @ [ S.mk_binder a; S.mk_binder t ]) body None
      in
      mk mk_Total,
      mk mk_GTotal
    in
    // Register these two top-level bindings in the environment
    let ctx_lid = mk_lid "ctx" in
    let env, ctx_fv = register env ctx_lid ctx_def in

    let gctx_lid = mk_lid "gctx" in
    let env, gctx_fv = register env gctx_lid gctx_def in

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
  let env, c_pure = register env (mk_lid "pure") c_pure in

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
  let env, c_app = register env (mk_lid "app") c_app in

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
  let env, c_lift1 = register env (mk_lid "lift1") c_lift1 in


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
    U.abs (binders @ binders_of_list [ a, true; t1, true; t2, true; t3, true; f, false; a1, false; a2, false ]) (
      U.mk_app c_app (List.map S.as_arg [
        U.mk_app c_app (List.map S.as_arg [
          U.mk_app c_pure (List.map S.as_arg [ S.bv_to_name f ]);
          S.bv_to_name a1 ]);
        S.bv_to_name a2 ])
    ) ret
  in
  let env, c_lift2 = register env (mk_lid "lift2") c_lift2 in

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
  let env, c_push = register env (mk_lid "push") c_push in

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
    let c = S.gen_bv "c" None U.ktype in
    U.abs (binders @ S.binders_of_list [ a; c ]) (
      let l_ite = fvar Const.ite_lid (S.Delta_unfoldable 2) None in
      U.ascribe (
        U.mk_app c_lift2 (List.map S.as_arg [
          U.mk_app l_ite [S.as_arg (S.bv_to_name c)]
        ])
      ) (Inr (mk_Total ((U.arrow [ S.null_binder wp_a; S.null_binder wp_a ] (mk_Total wp_a)))))
    ) ret_tot_wp_a
  in
  let env, wp_if_then_else = register env (mk_lid "wp_if_then_else") wp_if_then_else in
  let wp_if_then_else = mk_generic_app wp_if_then_else in

  (* val st2_assert_p : heap:Type ->a:Type -> q:Type0 -> st2_wp heap a ->
                       Tot (st2_wp heap a)
    let st2_assert_p heap a q wp = st2_app (st2_pure (l_and q)) wp *)
  let wp_assert =
    let q = S.gen_bv "q" None U.ktype in
    let wp = S.gen_bv "wp" None wp_a in
    let l_and = fvar Const.and_lid (S.Delta_unfoldable 1) None in
    let body =
      U.mk_app c_app (List.map S.as_arg [
        U.mk_app c_pure (List.map S.as_arg [
          U.mk_app l_and [S.as_arg (S.bv_to_name q)]]);
        S.bv_to_name wp])
    in
    U.abs (S.binders_of_list [ a; q; wp ]) body ret_tot_wp_a
  in
  check env "wp_assert" (U.abs binders wp_assert None);

  (* val st2_assume_p : heap:Type ->a:Type -> q:Type0 -> st2_wp heap a ->
                       Tot (st2_wp heap a)
    let st2_assume_p heap a q wp = st2_app (st2_pure (l_imp q)) wp *)
  let wp_assume =
    let q = S.gen_bv "q" None U.ktype in
    let wp = S.gen_bv "wp" None wp_a in
    let l_imp = fvar Const.imp_lid (S.Delta_unfoldable 1) None in
    let body =
      U.mk_app c_app (List.map S.as_arg [
        U.mk_app c_pure (List.map S.as_arg [
          U.mk_app l_imp [S.as_arg (S.bv_to_name q)]]);
        S.bv_to_name wp])
    in
    U.abs (S.binders_of_list [ a; q; wp ]) body ret_tot_wp_a
  in
  check env "wp_assume" (U.abs binders wp_assume None);

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
    U.abs (S.binders_of_list [ a; b; f ]) body ret_tot_wp_a
  in
  check env "wp_close" (U.abs binders wp_close None);

  let ret_tot_type0 = Some (Inl (U.lcomp_of_comp <| S.mk_Total U.ktype)) in
  let mk_forall (x: S.bv) (body: S.term): S.term =
    S.mk (Tm_app (U.tforall, [ S.as_arg (U.abs [ S.mk_binder x ] body ret_tot_type0)])) None Range.dummyRange
  in

  (* For each (target) type t, we define a binary relation in t called ≤_t.

      x ≤_t y            =def=       x = y      [t is base type]
      x ≤_Type0 y        =def=       x ==> y
      x ≤_{a->b} y       =def=   ∀a1 a2, a1 ≤_a a2 ==> x a1 ≤_b y a2
  *)
  (* Invariant: [x] and [y] have type [t] *)
  let rec mk_leq t x y =
    let t = N.normalize [ N.Beta; N.Inline; N.UnfoldUntil S.Delta_constant ] env t in
    match (SS.compress t).n with
    | Tm_type _ ->
        (* Util.print2 "type0, x=%s, y=%s\n" (Print.term_to_string x) (Print.term_to_string y); *)
        U.mk_imp x y
    | Tm_arrow ([ binder ], { n = GTotal b })
    | Tm_arrow ([ binder ], { n = Total b }) when S.is_null_binder binder ->
        let a = (fst binder).sort in
        (* Util.print2 "arrow, a=%s, b=%s\n" (Print.term_to_string a) (Print.term_to_string b); *)
        let a1 = S.gen_bv "a1" None a in
        let a2 = S.gen_bv "a2" None a in
        let body = U.mk_imp
          (mk_leq a (S.bv_to_name a1) (S.bv_to_name a2))
          (mk_leq b
            (U.mk_app x [ S.as_arg (S.bv_to_name a1) ])
            (U.mk_app y [ S.as_arg (S.bv_to_name a2) ]))
        in
        mk_forall a1 (mk_forall a2 body)
    | Tm_arrow (binder :: binders, comp) ->
        let t = { t with n = Tm_arrow ([ binder ], S.mk_Total (U.arrow binders comp)) } in
        mk_leq t x y
    | Tm_arrow _ ->
        failwith "unhandled arrow"
    | _ ->
        (* TODO: assert that this is a base type. *)
        (* Util.print2 "base, x=%s, y=%s\n" (Print.term_to_string x) (Print.term_to_string y); *)
        U.mk_eq t t x y
  in
  let stronger =
    let wp1 = S.gen_bv "wp1" None wp_a in
    let wp2 = S.gen_bv "wp2" None wp_a in
    let body = mk_leq wp_a (S.bv_to_name wp1) (S.bv_to_name wp2) in
    U.abs (binders @ binders_of_list [ a, true; wp1, false; wp2, false ]) body ret_tot_type0
  in
  let env, stronger = register env (mk_lid "stronger") stronger in

  let null_wp = snd ed.null_wp in

  (* val st2_trivial : heap:Type ->a:Type -> st2_wp heap a -> Tot Type0
    let st2_trivial heap a wp = st2_stronger heap a (st2_null_wp heap a) wp *)
  let wp_trivial =
    let wp = S.gen_bv "wp" None wp_a in
    let body = U.mk_app stronger (args_of_binders binders @ List.map S.as_arg [
      U.mk_app null_wp [ S.as_arg (S.bv_to_name a) ];
      S.bv_to_name wp
    ]) in
    U.abs (S.binders_of_list [ a; wp ]) body ret_tot_type0
  in
  check env "wp_trivial" (U.abs binders wp_trivial None);

  d "End Dijkstra monads for free";

  env, { ed with
    if_then_else = ([], wp_if_then_else);
    assert_p     = ([], wp_assert);
    assume_p     = ([], wp_assume);
    close_wp     = ([], wp_close);
    trivial      = ([], wp_trivial)
  }


// Some helpers for... --------------------------------------------------------

type env = {
  // The type-checking environment which we abuse to store our DMFF-style types
  // when entering a binder.
  env: FStar.TypeChecker.Env.env;
  // The top-level definitions that have been checked so far, along with their
  // type, represented as an F* type, but really, a type from the definition
  // language.
  definitions: list<(lid * typ)>;
  // The substitution from every [x: C] to its [x^w: C*].
  subst: list<subst_elt>;
  // Hack to avoid a dependency
  tc_const: sconst -> typ;
}

let empty env tc_const = {
  env = env;
  definitions = [];
  subst = [];
  tc_const = tc_const
}

type env_ = env

type nm = | N of typ | M of typ

type nm_ = nm

let nm_of_comp = function
  | Total t ->
      N t
  | Comp c when lid_equals c.effect_name Const.monadic_lid ->
      M c.result_typ
  | _ ->
      failwith "[nm_of_comp]: impossible"

let string_of_nm = function
  | N t -> Util.format1 "N[%s]" (Print.term_to_string t)
  | M t -> Util.format1 "M[%s]" (Print.term_to_string t)

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

// ... the _ and * transformations from the definition language to F* ---------

let rec mk_star_to_type mk env a =
  mk (Tm_arrow (
    [S.null_bv (star_type env a), S.as_implicit false],
    mk_Total Util.ktype0
  ))


// The *-transformation for types, purely syntactic. Has been enriched with the
// [Tm_abs] case to account for parameterized types

and star_type env t =
  let mk x = mk x None t.pos in
  let mk_star_to_type = mk_star_to_type mk in
  //Util.print1 "[debug]: star_type %s\n" (Print.term_to_string t);
  let normalize = N.normalize [ N.EraseUniverses; N.UnfoldUntil S.Delta_constant ] env.env in
  let t = normalize t in
  let t = SS.compress t in
  match t.n with
  | Tm_arrow (binders, _) ->
      // TODO: check that this is not a dependent arrow.
      let binders = List.map (fun (bv, aqual) ->
        { bv with sort = star_type env bv.sort }, aqual
      ) binders in
      begin match is_monadic_arrow t.n with
      | N hn ->
          // Simple case:
          //   (H_0  -> ... -> H_n)* = H_0* -> ... -> H_n*
          mk (Tm_arrow (binders, mk_Total (star_type env hn)))
      | M a ->
          // F*'s arrows are n-ary (and the intermediary arrows are pure), so the rule is:
          //   (H_0  -> ... -> H_n  -t-> A)* = H_0* -> ... -> H_n* -> (A* -> Type) -> Type
          mk (Tm_arrow (
            binders @ [ S.null_bv (mk_star_to_type env a), S.as_implicit false ],
            mk_Total Util.ktype0))
      end

  | Tm_app (head, args) ->
      // Sums and products. TODO: re-use the cache in [env] to not recompute
      // (st a)* every time.
      let is_valid_application head =
        match (SS.compress head).n with
        | Tm_fvar fv when (
          // TODO: implement a better check (non-dependent, user-defined data type)
          fv_eq_lid fv Const.option_lid ||
          fv_eq_lid fv Const.either_lid ||
          is_tuple_constructor (SS.compress head)
        ) ->
            true
        | Tm_uinst _ ->
            failwith "impossible"
        | _ ->
            false
      in
      if is_valid_application head then
        mk (Tm_app (head, List.map (fun (t, qual) -> star_type env t, qual) args))
      else
        raise (Err (Util.format1 "For now, only [either] and [option] are \
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
      let subst = SS.opening_of_binders binders in
      let repr = SS.subst subst repr in
      let env = { env with env = push_binders env.env binders } in
      let repr = star_type env repr in
      let repr = SS.close binders repr in
      mk (Tm_abs (binders, repr, something))

  | Tm_abs _
  | Tm_uinst _
  | Tm_constant _
  | Tm_refine _
  | Tm_match _
  | Tm_ascribed _
  | Tm_let _
  | Tm_uvar _
  | Tm_meta _
  | Tm_unknown ->
      raise (Err (Util.format1 "The following term is outside of the definition language: %s"
        (Print.term_to_string t)))

  | Tm_delayed _ ->
      failwith "impossible"


// Recording a new definition in our top-level environment --------------------

let star_definition env t f =
  // Making the assumption that the thing we're passed is a top-level name.
  match (SS.compress (N.normalize [ N.EraseUniverses ] env.env t)).n with
  | Tm_fvar { fv_name = lid } ->
      // Start back from the original [t]... can't re-normalize a term without
      // universes (because it is now ill-typed)
      let t = N.normalize [ N.UnfoldUntil Delta_constant; N.NoInline; N.EraseUniverses ] env.env t in
      Util.print1 "Recording definition of %s\n" (text_of_lid lid.v);
      let keep, ret = f env t in
      { env with definitions = (lid.v, keep) :: env.definitions }, ret
  | _ ->
      raise (Err (Util.format1 "Ill-formed definition: %s" (Print.term_to_string t)))

let star_type_definition env t =
  star_definition env t (fun env e -> let t = star_type env e in t, t)


// The bi-directional *-transformation and checker for expressions ------------

let is_monadic = function
  | None ->
      failwith "un-annotated lambda?!"
  | Some (Inl { eff_name = lid }) | Some (Inr lid) ->
      lid_equals lid Const.monadic_lid

// TODO: this function implements a (partial) check for the well-formedness of
// C-types...
// This function expects its argument [t] to be normalized.
let rec is_C (t: typ): bool =
  match (SS.compress t).n with
  | Tm_app (head, args) when Util.is_tuple_constructor head ->
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
  U.abs [ S.mk_binder p ] body None

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
  Util.print1 "[debug]: check %s\n" (Print.term_to_string e);
  let mk x = mk x None e.pos in
  // [s_e] as in "starred e"; [u_e] as in "underlined u" (per the paper)
  let return_if (rec_nm, s_e, u_e) =
    let check t1 t2 =
      if not (is_unknown t2.n) && not (Rel.is_trivial (Rel.teq env.env t1 t2)) then
        raise (Err (Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]"
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
        raise (Err (Util.format3
          "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
          (Print.term_to_string e)
          (Print.term_to_string t1)
          (Print.term_to_string t2)))

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
        (fun env e2 ->
          let strip_m = function
            | M t, s_e, u_e -> t, s_e, u_e
            | _ -> failwith "impossible"
          in
          match context_nm with
          | N t -> strip_m (check env e2 (M t))
          | M _ -> strip_m (check env e2 context_nm))

  | Tm_match (e0, branches) ->
      // This is similar to the [let] case above. The [match] checks that the
      // types of the branches work; it also demands that the scrutinee be a
      // non-monadic computation.
      mk_match env e0 branches (fun env body -> check env body context_nm)

  | Tm_meta (e, _)
  | Tm_uinst (e, _)
  | Tm_ascribed (e, _, _) ->
      check env e context_nm

  | Tm_let _ ->
      failwith (Util.format1 "[check]: Tm_let %s" (Print.term_to_string e))
  | Tm_type _ ->
      failwith "impossible (stratified)"
  | Tm_arrow _ ->
      failwith "impossible (stratified)"
  | Tm_refine _ ->
      failwith (Util.format1 "[check]: Tm_refine %s" (Print.term_to_string e))
  | Tm_uvar _ ->
      failwith (Util.format1 "[check]: Tm_uvar %s" (Print.term_to_string e))
  | Tm_delayed _ ->
      failwith "impossible (compressed)"
  | Tm_unknown ->
      failwith (Util.format1 "[check]: Tm_unknown %s" (Print.term_to_string e))


and infer (env: env) (e: term): nm * term * term =
  Util.print1 "[debug]: infer %s\n" (Print.term_to_string e);
  let mk x = mk x None e.pos in
  let normalize = N.normalize [ N.Beta; N.Inline; N.UnfoldUntil S.Delta_constant ] env.env in
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
        let sort = star_type env bv.sort in
        { bv with sort = sort }, qual
      ) binders in

      // For the _-translation, things are a little bit trickier. We need to
      // update the substitution, and one binder may turn into two binders.
      let env, u_binders = List.fold_left (fun (env, acc) (bv, qual) ->
        let c = normalize bv.sort in
        if is_C c then
          let xw = S.gen_bv (bv.ppname.idText ^ "^w") None (star_type env c) in
          let x = { bv with sort = trans_F env c (S.bv_to_name xw) } in
          let env = { env with subst = NT (bv, S.bv_to_name xw) :: env.subst } in
          env, S.mk_binder x :: S.mk_binder xw :: acc
        else
          let x = { bv with sort = star_type env bv.sort } in
          env, S.mk_binder x :: acc
      ) (env, []) binders in
      let u_binders = List.rev u_binders in

      let comp, s_body, u_body =
        let check_what = if is_monadic what then check_m else check_n in
        let t, s_body, u_body = check_what env body in
        comp_of_nm (if is_monadic what then M t else N t), s_body, u_body
      in

      // From [comp], the inferred computation type for the (original), return
      // the inferred type for the original term.
      let t =
        let binders = List.map (fun (bv, _) ->
          S.mk_binder (S.null_bv (normalize bv.sort))
        ) binders in
        let binders = close_binders binders in
        mk (Tm_arrow (binders, comp))
      in

      let s_body = close s_binders s_body in
      let s_binders = close_binders s_binders in
      let s_term = mk (Tm_abs (s_binders, s_body, what)) in

      let u_body = close u_binders u_body in
      let u_binders = close_binders u_binders in
      let u_term = mk (Tm_abs (u_binders, u_body, what)) in
      N t, s_term, u_term

  | Tm_fvar { fv_name = { v = lid } } ->
      begin match List.find (fun (lid', _) -> lid_equals lid lid') env.definitions with
      | Some (_, t) ->
          Util.print2 "[debug]: lookup %s hit %s\n" (text_of_lid lid) (Print.term_to_string t);
          N t, e, e
      | None ->
          let _, t = Env.lookup_lid env.env lid in
          let txt = text_of_lid lid in
          let allowed_prefixes = [ "Mktuple"; "Left"; "Right"; "Some"; "None" ] in
          Util.print2 "[debug]: lookup %s miss %s\n" txt (Print.term_to_string t);
          if List.existsb (fun s -> Util.starts_with txt ("Prims." ^ s)) allowed_prefixes then
            N t, e, e
          else
            raise (Err (Util.format1 "The %s constructor has not been whitelisted for the definition language" txt))
      end

  | Tm_app (head, args) ->
      let t_head, s_head, u_head = check_n env head in
      let t_head = normalize t_head in
      let is_arrow t = match (SS.compress t).n with | Tm_arrow _ -> true | _ -> false in
      // TODO: replace with Util.arrow_formals_comp
      let rec flatten t = match (SS.compress t).n with
        | Tm_arrow (binders, { n = Total t }) when is_arrow t ->
            let binders', comp = flatten t in
            binders @ binders', comp
        | Tm_arrow (binders, comp) ->
            binders, comp
        | _ ->
            raise (Err (Util.format1 "%s: not a function type" (Print.term_to_string t_head)))
      in
      let binders, comp = flatten t_head in
      Util.print1 "[debug] type of [head] is %s\n" (Print.term_to_string t_head);

      // Making the assumption here that [Tm_arrow (..., Tm_arrow ...)]
      // implies [is_M comp]. F* should be fixed if it's not the case.
      let n = List.length binders in
      let n' = List.length args in
      if List.length binders < List.length args then
        raise (Err (Util.format3 "The head of this application, after being applied to %s \
          arguments, is an effectful computation (leaving %s arguments to be \
          applied). Please let-bind the head applied to the %s first \
          arguments." (string_of_int n) (string_of_int (n' - n)) (string_of_int n)));

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
      Util.print1 "[debug]: final type of application is %s\n" (string_of_nm final_type);

      let s_args, u_args = List.split (List.map2 (fun (bv, _) (arg, q) ->
        // TODO: implement additional check that the arguments are T-free if
        // head is [Tm_fvar ...] with [Mktuple], [Left], etc.
        // Note: not enforcing the types of the arguments because 1) it has
        // been enforced by the main F* type-checker and 2) it's a hassle with
        // binders and stuff
        match (SS.compress (normalize bv.sort)).n with
        | Tm_type _ ->
            let arg = normalize arg, q in
            arg, [ arg ]
        | _ ->
            let _, s_arg, u_arg = check_n env arg in
            (s_arg, S.as_implicit false), (if is_C bv.sort then
              [ SS.subst env.subst s_arg, S.as_implicit false; u_arg, S.as_implicit false ]
            else
              [ u_arg, S.as_implicit false ])
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
      failwith (Util.format1 "[infer]: Tm_let %s" (Print.term_to_string e))
  | Tm_type _ ->
      failwith "impossible (stratified)"
  | Tm_arrow _ ->
      failwith "impossible (stratified)"
  | Tm_refine _ ->
      failwith (Util.format1 "[infer]: Tm_refine %s" (Print.term_to_string e))
  | Tm_uvar _ ->
      failwith (Util.format1 "[infer]: Tm_uvar %s" (Print.term_to_string e))
  | Tm_delayed _ ->
      failwith "impossible (compressed)"
  | Tm_unknown ->
      failwith (Util.format1 "[infer]: Tm_unknown %s" (Print.term_to_string e))

and mk_match env e0 branches f =
  let mk x = mk x None e0.pos in
  // TODO: automatically [bind] when the scrutinee is monadic?
  let _, s_e0, u_e0 = check_n env e0 in
  let nms, branches = List.split (List.map (fun b ->
    match open_branch b with
    | pat, None, body ->
        let env = { env with env = List.fold_left push_bv env.env (pat_bvs pat) } in
        let nm, s_body, u_body = f env body in
        nm, (pat, None, (s_body, u_body))
    | _ ->
        raise (Err ("No when clauses in the definition language"))
  ) branches) in
  let t1 = match List.hd nms with | M t1 | N t1 -> t1 in
  let has_m = List.existsb (function | M _ -> true | _ -> false) nms in
  let nms, s_branches, u_branches = List.unzip3 (List.map2 (fun nm (pat, guard, (s_body, u_body)) ->
    let check t t' =
      if not (Rel.is_trivial (Rel.teq env.env t' t)) then
        raise (Err ("[infer]: branches do not have the same type"))
    in
    match nm, has_m with
    | N t2, false
    | M t2, true ->
        check t2 t1;
        nm, (pat, guard, s_body), (pat, guard, u_body)
    | N t2, true ->
        check t2 t1;
        // TODO: we could re-generate the body of the branch with [check_m] and
        // have [return]s inserted at depth, rather than on the outside...
        M t2, (pat, guard, mk_return env t2 s_body), (pat, guard, u_body)
    | M _, false ->
        failwith "impossible"
  ) nms branches) in
  let s_branches = List.map close_branch s_branches in
  let u_branches = List.map close_branch u_branches in
  (if has_m then M t1 else N t1), mk (Tm_match (s_e0, s_branches)), mk (Tm_match (u_e0, u_branches))


and mk_let (env: env_) (binding: letbinding) (e2: term)
    (proceed: env_ -> term -> nm * term * term)
    (ensure_m: env_ -> term -> term * term * term) =
  let mk x = mk x None e2.pos in
  let e1 = binding.lbdef in
  // This is [let x = e1 in e2]. Open [x] in [e2].
  let x = Util.left binding.lbname in
  let x_binders = [ S.mk_binder x ] in
  let x_binders, e2 = SS.open_term x_binders e2 in
  begin match infer env e1 with
  | N t1, s_e1, u_e1 ->
      // Piggyback on the environment to carry our own special terms
      let env = { env with env = push_bv env.env ({ x with sort = t1 }) } in
      // Simple case: just a regular let-binding. We defer checks to e2.
      let nm_rec, s_e2, u_e2 = proceed env e2 in
      nm_rec,
      mk (Tm_let ((false, [ { binding with lbdef = s_e1 } ]), SS.close x_binders s_e2)),
      mk (Tm_let ((false, [ { binding with lbdef = u_e1 } ]), SS.close x_binders u_e2))

  | M t1, s_e1, u_e1 ->
      let env = { env with env = push_bv env.env ({ x with sort = t1 }) } in
      let t2, s_e2, u_e2 = ensure_m env e2 in
      // Now, generate the bind.
      // p: A* -> Type
      let p_type = mk_star_to_type mk env t2 in
      let p = S.gen_bv "p''" None p_type in
      // e2* p
      let s_e2 = mk (Tm_app (s_e2, [ S.bv_to_name p, S.as_implicit false ])) in
      // fun x -> s_e2* p; this takes care of closing [x].
      let s_e2 = U.abs x_binders s_e2 None in
      // e1* (fun x -> s_e2* p)
      let body = mk (Tm_app (s_e1, [ s_e2, S.as_implicit false ])) in
      M t2,
      U.abs [ S.mk_binder p ] body None,
      mk (Tm_let ((false, [ { binding with lbdef = u_e1 } ]), SS.close x_binders u_e2))
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
    effect_name = Const.monadic_lid;
    result_typ = t;
    effect_args = [];
    flags = []
  })

and type_of_comp t =
  match t.n with
  | Total t | GTotal t | Comp { result_typ = t } -> t

// This function expects its argument [c] to be normalized and to satisfy [is_C c]
and trans_F (env: env_) (c: typ) (wp: term): term =
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
      mk (Tm_app (head, List.map2 (fun (arg, _) (wp_arg, _) ->
        trans_F env arg wp_arg, S.as_implicit false)
      args wp_args))
  | Tm_arrow (binders, comp) ->
      let binders = open_binders binders in
      let binders, comp = open_comp binders comp in
      let bvs, binders = List.split (List.map (fun (bv, q) ->
        let h = bv.sort in
        if is_C h then
          let w' = S.gen_bv (bv.ppname.idText ^ "-w'") None (star_type env h) in
          w', [ S.mk_binder w'; S.null_binder (trans_F env h (S.bv_to_name bv)) ]
        else
          let x = S.gen_bv (bv.ppname.idText ^ "-x") None (star_type env h) in
          x, [ S.mk_binder x ]
      ) binders) in
      let binders = List.flatten binders in
      let app = mk (Tm_app (wp, List.map (fun bv -> S.bv_to_name bv, S.as_implicit false) bvs)) in
      let comp = trans_G env (type_of_comp comp) (is_monadic_comp comp) app in
      let comp = close_comp binders comp in
      let binders = close_binders binders in
      mk (Tm_arrow (binders, comp))
  | _ ->
      failwith "impossible trans_F"

and trans_G (env: env_) (h: typ) (is_monadic: bool) (wp: typ): comp =
  let mk x = mk x None h.pos in
  if is_monadic then
    mk_Comp ({
      effect_name = Const.effect_PURE_lid;
      result_typ = star_type env h;
      effect_args = [ wp, S.as_implicit false ];
      flags = []
    })
  else
    mk_Total (trans_F env h wp)


let star_expr_definition env t =
  star_definition env t (fun env e -> let t, s_e, s_u = check_n env e in t, (s_e, s_u))
