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

let gen_wps_for_free env binders a wp_a tc_term (ed: Syntax.eff_decl): Syntax.eff_decl =
  (* A series of macros and combinators to automatically build WP's. In these
   * definitions, both [binders] and [a] are opened. This means that macros
   * close over [binders] and [a], and this means that combinators do not expect
   * [binders] and [a] when applied. *)
  let normalize = N.normalize [ N.Beta; N.Inline; N.UnfoldUntil S.Delta_constant ] env in

  let d s = Util.print1 "\x1b[01;36m%s\x1b[00m\n" s in
  let normalize_and_make_binders_explicit tm =
    let tm = normalize tm in
    let rec visit_term tm =
      let n = match (SS.compress tm).n with
        | Tm_arrow (binders, comp) ->
            let comp = visit_comp comp in
            let binders = List.map visit_binder binders in
            Tm_arrow (binders, comp)
        | Tm_abs (binders, term, comp) ->
            let comp = visit_maybe_lcomp comp in
            let term = visit_term term in
            let binders = List.map visit_binder binders in
            Tm_abs (binders, term, comp)
        | _ ->
            tm.n
      in
      { tm with n = n }
    and visit_binder (bv, a) =
      { bv with sort = visit_term bv.sort }, S.as_implicit false
    and visit_maybe_lcomp lcomp =
      match lcomp with
      | Some (Inl lcomp) ->
          Some (Inl (U.lcomp_of_comp (visit_comp (lcomp.comp ()))))
      | comp ->
          comp
    and visit_comp comp =
      let n = match comp.n with
        | Total tm ->
            Total (visit_term tm)
        | GTotal tm ->
            GTotal (visit_term tm)
        | comp ->
            comp
      in
      { comp with n = n }
    and visit_args args =
      List.map (fun (tm, q) -> visit_term tm, q) args
    in
    visit_term tm
  in

  (* A debug / sanity check. *)
  let check str t =
    if Env.debug env (Options.Other "ED") then begin
      Util.print2 "Generated term for %s: %s\n" str (Print.term_to_string t);
      let t = normalize t in
      let t = SS.compress t in
      let e, { res_typ = res_typ }, _ = tc_term env t in
      Util.print2 "Inferred type for %s: %s\n" str (Print.term_to_string (normalize res_typ));
      Util.print2 "Elaborated term for %s: %s\n" str (Print.term_to_string (normalize e))
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
        let rest = match comp.n with
                   | Total t -> t
                   | _ -> failwith "wp_a contains non-Tot arrow" in
        bs @ (collect_binders rest)
    | Tm_type _ ->
        []
    | _ ->
        failwith "wp_a doesn't end in Type0" in

  let mk_ctx, mk_gctx, mk_gamma =
    let i = ref 0 in
    let wp_binders = collect_binders (normalize wp_a) in
    (fun t -> U.arrow wp_binders (mk_Total t)),
    (fun t -> U.arrow wp_binders (mk_GTotal t)),
    (fun () -> List.map (fun (bv, _) ->
          (* Note: just returning [wp_binders] here would be wrong, because the
           * identity of binders relies on the _physical equality_ of the [bv]
           * data structure. So, arguments passed to [mk_ctx] should never refer
           * to [wp_binders]; one way to enforce that is to generate fresh
           * binders whenever the client asks for it. *)
          i := !i + 1;
          S.gen_bv ("g" ^ string_of_int !i) None bv.sort
        ) wp_binders)
  in

  (* A variation where we can specify implicit parameters. *)
  let binders_of_list = List.map (fun (t, b) -> t, S.as_implicit b) in

  let implicit_binders_of_list = List.map (fun t -> t, S.as_implicit true) in

  let args_of_bv = List.map (fun bv -> S.as_arg (S.bv_to_name bv)) in

  (* val st2_pure : #heap:Type -> #a:Type -> #t:Type -> x:t ->
       Tot (st2_ctx heap a t)
     let st2_pure #heap #a #t x = fun _post _h -> x *)
  let c_pure =
    let t = S.gen_bv "t" None U.ktype in
    let x = S.gen_bv "x" None (S.bv_to_name t) in
    let ret = Some (Inl (U.lcomp_of_comp (mk_Total (mk_ctx (S.bv_to_name t))))) in
    let gamma = mk_gamma () in
    let body = U.abs (implicit_binders_of_list gamma) (S.bv_to_name x) ret in
    U.abs (binders_of_list [ t, true; x, false ]) body ret
  in
  check "pure" (U.abs (binders @ [ S.mk_binder a ]) c_pure None);

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
      let gamma = mk_gamma () in
      let gamma_as_args = args_of_bv gamma in
      let inner_body =
        U.mk_app
          (S.bv_to_name l)
          (gamma_as_args @ [ S.as_arg (U.mk_app (S.bv_to_name r) gamma_as_args)])
      in
      U.abs (implicit_binders_of_list gamma) inner_body ret
    in
    U.abs (binders_of_list [ t1, true; t2, true; l, false; r, false ]) outer_body ret
  in
  check "app" (U.abs (binders @ [ S.mk_binder a ]) c_app None);

  (* val st2_liftGA1 : #heap:Type -> #a:Type -> #t1:Type -> #t2:Type ->
                       f : (t1 -> GTot t2) ->
                       st2_gctx heap a t1 ->
                       Tot (st2_gctx heap a t2)
    let st2_liftGA1 #heap #a #t1 #t2 f a1 =
                    st2_app (st2_pure f) a1
  *)
  let unknown = mk Tm_unknown None Range.dummyRange in
  let c_lift1 =
    let t1 = S.gen_bv "t1" None U.ktype in
    let t2 = S.gen_bv "t2" None U.ktype in
    let t_f = U.arrow [ S.null_binder (S.bv_to_name t1) ] (S.mk_GTotal (S.bv_to_name t2)) in
    let f = S.gen_bv "f" None t_f in
    let a1 = S.gen_bv "a1" None (mk_gctx (S.bv_to_name t1)) in
    let ret = Some (Inl (U.lcomp_of_comp (mk_Total (mk_gctx (S.bv_to_name t2))))) in
    U.abs (binders_of_list [ t1, true; t2, true; f, false; a1, false ]) (
      U.mk_app c_app (List.map S.as_arg [
        unknown; unknown;
        U.mk_app c_pure (List.map S.as_arg [ unknown; S.bv_to_name f ]);
        S.bv_to_name a1 ])
    ) ret
  in
  check "lift1" (U.abs (binders @ [ S.mk_binder a ]) c_lift1 None);


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
    U.abs (binders_of_list [ t1, true; t2, true; t3, true; f, false; a1, false; a2, false ]) (
      U.mk_app c_app (List.map S.as_arg [
        unknown; unknown;
        U.mk_app c_app (List.map S.as_arg [
          unknown; unknown;
          U.mk_app c_pure (List.map S.as_arg [ unknown; S.bv_to_name f ]);
          S.bv_to_name a1 ]);
        S.bv_to_name a2 ])
    ) ret
  in
  check "lift2" (U.abs (binders @ [ S.mk_binder a ]) c_lift2 None);

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
    let gamma = mk_gamma () in
    let body = U.abs (S.binders_of_list gamma @ [ S.mk_binder e1 ]) (
      U.mk_app (S.bv_to_name f) (S.as_arg (S.bv_to_name e1) :: args_of_bv gamma)
    ) ret in
    U.abs (binders_of_list [ t1, true; t2, true; f, false ]) body ret
  in
  check "push" (U.abs (binders @ [ S.mk_binder a ]) c_push None);

  let ret_tot_wp_a = Some (Inl (U.lcomp_of_comp (mk_Total wp_a))) in

  (* val st2_if_then_else : heap:Type -> a:Type -> c:Type0 ->
                            st2_wp heap a -> st2_wp heap a ->
                            Tot (st2_wp heap a)
    let st2_if_then_else heap a c = st2_liftGA2 (l_ITE c) *)
  let wp_if_then_else =
    let c = S.gen_bv "c" None U.ktype in
    (* Note that this one *does* abstract over [a]. This is in line with the
     * expected shape of the combinator in the effect declaration. (But it does
     * not abstract over [binders]; [tc_eff_decl] will take care of closing
     * [binders]. *)
    U.abs (S.binders_of_list [ a; c ]) (
      let l_ite = fvar Const.ite_lid (S.Delta_unfoldable 2) None in
      U.mk_app c_lift2 (List.map S.as_arg [
        unknown; unknown; unknown;
        U.mk_app l_ite [S.as_arg (S.bv_to_name c)]
      ])
    ) ret_tot_wp_a
  in
  let wp_if_then_else = normalize_and_make_binders_explicit wp_if_then_else in
  check "wp_if_then_else" (U.abs binders wp_if_then_else None);

  (* val st2_assert_p : heap:Type ->a:Type -> q:Type0 -> st2_wp heap a ->
                       Tot (st2_wp heap a)
    let st2_assert_p heap a q wp = st2_app (st2_pure (l_and q)) wp *)
  let wp_assert =
    let q = S.gen_bv "q" None U.ktype0 in
    let wp = S.gen_bv "wp" None wp_a in
    let l_and = fvar Const.and_lid (S.Delta_unfoldable 1) None in
    let body =
      U.mk_app c_app (List.map S.as_arg [
        unknown; unknown;
        U.mk_app c_pure (List.map S.as_arg [
          unknown;
          U.mk_app l_and [S.as_arg (S.bv_to_name q)]]);
        S.bv_to_name wp])
    in
    U.abs (S.binders_of_list [ a; q; wp ]) body ret_tot_wp_a
  in
  let wp_assert = normalize_and_make_binders_explicit wp_assert in
  check "wp_assert" (U.abs binders wp_assert None);

  (* val st2_assume_p : heap:Type ->a:Type -> q:Type0 -> st2_wp heap a ->
                       Tot (st2_wp heap a)
    let st2_assume_p heap a q wp = st2_app (st2_pure (l_imp q)) wp *)
  let wp_assume =
    let q = S.gen_bv "q" None U.ktype0 in
    let wp = S.gen_bv "wp" None wp_a in
    let l_imp = fvar Const.imp_lid (S.Delta_unfoldable 1) None in
    let body =
      U.mk_app c_app (List.map S.as_arg [
        unknown; unknown;
        U.mk_app c_pure (List.map S.as_arg [
          unknown;
          U.mk_app l_imp [S.as_arg (S.bv_to_name q)]]);
        S.bv_to_name wp])
    in
    U.abs (S.binders_of_list [ a; q; wp ]) body ret_tot_wp_a
  in
  let wp_assume = normalize_and_make_binders_explicit wp_assume in
  check "wp_assume" (U.abs binders wp_assume None);

  let tforall = U.mk_app (S.mk_Tm_uinst U.tforall [ U_unknown ]) [ S.as_arg unknown ] in

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
        unknown; unknown;
        U.mk_app c_pure (List.map S.as_arg [
          unknown;
          tforall]);
        U.mk_app c_push (List.map S.as_arg [
          unknown; unknown;
          S.bv_to_name f])])
    in
    U.abs (S.binders_of_list [ a; b; f ]) body ret_tot_wp_a
  in
  let wp_close = normalize_and_make_binders_explicit wp_close in
  check "wp_close" (U.abs binders wp_close None);

  let ret_tot_type0 = Some (Inl (U.lcomp_of_comp <| S.mk_Total U.ktype0)) in
  let mk_forall (x: S.bv) (body: S.term): S.term =
    let tforall = U.mk_app (S.mk_Tm_uinst U.tforall [ U_unknown ]) [ S.as_arg x.sort ] in
    S.mk (Tm_app (tforall, [ S.as_arg (U.abs [ S.mk_binder x ] body ret_tot_type0)])) None Range.dummyRange
  in

  (* For each (target) type t, we define a binary relation in t called ≤_t.

      x ≤_t y            =def=       x = y      [t is base type]
      x ≤_Type0 y        =def=       x ==> y
      x ≤_{a->b} y       =def=   ∀a1 a2, a1 ≤_a a2 ==> x a1 ≤_b y a2
  *)
  (* Invariant: [x] and [y] have type [t] *)
  let rec mk_leq t x y =
    match (normalize (SS.compress t)).n with
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
    U.abs (S.binders_of_list [ wp1; wp2 ]) body ret_tot_type0
  in
  check "stronger" (U.abs (binders @ [ S.mk_binder a ]) stronger None);

  let null_wp = snd ed.null_wp in

  (* val st2_trivial : heap:Type ->a:Type -> st2_wp heap a -> Tot Type0
    let st2_trivial heap a wp = st2_stronger heap a (st2_null_wp heap a) wp *)
  let wp_trivial =
    let wp = S.gen_bv "wp" None wp_a in
    let body = U.mk_app stronger (List.map S.as_arg [
      U.mk_app null_wp [ S.as_arg (S.bv_to_name a) ];
      S.bv_to_name wp
    ]) in
    U.abs (S.binders_of_list [ a; wp ]) body ret_tot_type0
  in
  let wp_trivial = normalize_and_make_binders_explicit wp_trivial in
  check "wp_trivial" (U.abs binders wp_trivial None);

  { ed with
    if_then_else = ([], wp_if_then_else);
    assert_p     = ([], wp_assert);
    assume_p     = ([], wp_assume);
    close_wp     = ([], wp_close);
    trivial      = ([], wp_trivial)
  }


// Some helpers for... --------------------------------------------------------

type env = {
  env: FStar.TypeChecker.Env.env;
  definitions: list<(lid * typ)>;
}

let empty env = {
  env = env;
  definitions = []
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

let is_monadic_arrow n =
  match n with
  | Tm_arrow (_, { n = n}) ->
      nm_of_comp n
  | _ ->
      failwith "unexpected_argument: [is_monadic_arrow]"


// ... the _ and * transformations from the definition language to F* ---------

let rec mk_star_to_type mk env a =
  mk (Tm_arrow (
    [S.null_bv (star_type env a), S.as_implicit false],
    mk_Total Util.ktype
  ))


// The *-transformation for types, purely syntactic. Has been enriched with the
// [Tm_abs] case to account for parameterized types

and star_type env t =
  let mk x = mk x None t.pos in
  let mk_star_to_type = mk_star_to_type mk in
  //Util.print1 "[debug]: star_type %s\n" (Print.term_to_string t);
  let normalize = N.normalize [ (* N.Beta; N.Inline; *) N.UnfoldUntil S.Delta_constant ] env.env in
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
            mk_Total Util.ktype))
      end

  | Tm_app (head, args) ->
      // Sums and products. TODO: re-use the cache in [env] to not recompute
      // (st a)* every time.
      let rec is_valid_application head =
        match (SS.compress head).n with
        | Tm_fvar fv when (
          // TODO: implement a better check (non-dependent, user-defined data type)
          fv_eq_lid fv Const.option_lid ||
          fv_eq_lid fv Const.either_lid ||
          is_tuple_constructor (SS.compress head)
        ) ->
            true
        | Tm_uinst (head, _) ->
            is_valid_application head
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
  match (SS.compress t).n with
  | Tm_fvar { fv_name = lid } ->
      Util.print1 "Recording definition of %s\n" (text_of_lid lid.v);
      let store, ret =
        match lookup_definition (Unfold Delta_constant) env.env lid.v, lookup_lid env.env lid.v with
        | Some ([], e), ([], t) ->
            f env e
        | _ ->
            raise (Err ("Bad definition in [star_type_definition]"))
      in
      { env with definitions = (lid.v, store) :: env.definitions }, ret
  | Tm_uinst _ ->
      raise (Err "Ill-formed definition (hint: use Type0, not Type)")
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

// This function assumes [e] has been starred already and returns:
//   [fun (p: t* -> Type) -> p e
let mk_return env (t: typ) (e: term) =
  let mk x = mk x None e.pos in
  let p_type = mk_star_to_type mk env t in
  let p = S.gen_bv "p'" None p_type in
  let body = mk (Tm_app (S.bv_to_name p, [ e, S.as_implicit false ])) in
  U.abs [ S.mk_binder p ] body None

let is_unknown = function | Tm_unknown -> true | _ -> false

// [check] ensures that the sub-term is of the desired effect (N or M) _and_
// of the desired type. In case the type is [Tm_unknown], [check] skips the
// latter check. It always returns the desired effect and the desired type or,
// if it was unknown, the inferred type (pre star-transformation). Furthermore,
// it returns a starred version of the (elaborated) term.
let rec check (env: env) (e: term) (context_nm: nm): nm * term =
  Util.print1 "[debug]: check %s\n" (Print.term_to_string e);
  let mk x = mk x None e.pos in
  let return_if (rec_nm, e) =
    let check t1 t2 =
      if not (is_unknown t2.n) && not (Rel.is_trivial (Rel.teq env.env t1 t2)) then
        raise (Err (Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]"
          (Print.term_to_string e) (Print.term_to_string t1) (Print.term_to_string t2)))
    in
    match rec_nm, e, context_nm with
    | N t1, e, N t2
    | M t1, e, M t2 ->
        check t1 t2;
        rec_nm, e
    | N t1, e, M t2 ->
        check t1 t2;
        M t1, mk_return env t1 e
    | M _, _, N _ ->
        raise (Err ("[check]: got an effectful computation in lieu of a pure computation"))
  in

  match (SS.compress e).n with
  | Tm_bvar _
  | Tm_name _
  | Tm_fvar _
  | Tm_abs _
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
            | M t, e -> t, e
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
  | Tm_constant _ ->
      failwith (Util.format1 "[check]: Tm_constant %s" (Print.term_to_string e))
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


and infer (env: env) (e: term): nm * term =
  Util.print1 "[debug]: infer %s\n" (Print.term_to_string e);
  let mk x = mk x None e.pos in
  let normalize = N.normalize [ N.Beta; N.Inline; N.UnfoldUntil S.Delta_constant ] env.env in
  match (SS.compress e).n with
  | Tm_bvar bv ->
      failwith "I failed to open a binder... boo"

  | Tm_name bv ->
      N bv.sort, e

  | Tm_abs (binders, body, what) ->
      let binders = SS.open_binders binders in
      let subst = SS.opening_of_binders binders in
      let body = SS.subst subst body in
      let env = { env with env = push_binders env.env binders } in

      let binders = List.map (fun (bv, qual) ->
        let sort = star_type env bv.sort in
        { bv with sort = sort }, qual
      ) binders in
      let comp, body =
        let check_what = if is_monadic what then check_m else check_n in
        let t, body = check_what env body in
        comp_of_nm (if is_monadic what then M t else N t), body
      in

      let body = close binders body in
      let t =
        let binders = List.map (fun (bv, _) ->
          S.mk_binder (S.null_bv bv.sort)
        ) binders in
        let binders = close_binders binders in
        mk (Tm_arrow (binders, comp))
      in
      let binders = close_binders binders in
      N t, mk (Tm_abs (binders, body, what))

  | Tm_fvar { fv_name = { v = lid } } ->
      begin match List.find (fun (lid', _) -> lid_equals lid lid') env.definitions with
      | Some (_, t) ->
          Util.print2 "[debug]: lookup %s hit %s\n" (text_of_lid lid) (Print.term_to_string t);
          N t, e
      | None ->
          let _, t = Env.lookup_lid env.env lid in
          let txt = text_of_lid lid in
          let allowed_prefixes = [ "Mktuple"; "Left"; "Right"; "Some"; "None" ] in
          Util.print2 "[debug]: lookup %s miss %s\n" txt (Print.term_to_string t);
          if List.existsb (fun s -> Util.starts_with txt ("Prims." ^ s)) allowed_prefixes then
            N t, e
          else
            raise (Err (Util.format1 "The %s constructor has not been whitelisted for the definition language" txt))
      end

  | Tm_app (head, args) ->
      let t_head, head = check_n env head in
      let t_head = normalize t_head in
      Util.print1 "[debug] type of [head] is %s\n" (Print.term_to_string t_head);
      begin match (SS.compress t_head).n with
      | Tm_arrow (binders, comp) ->
          let binders, comp = SS.open_comp binders comp in
          // Return the starred argument (for elaboration) and a substitution to
          // apply on the computation to get the original return type
          let args, subst_elts = List.split (List.map2 (fun (bv, _) (arg, q) ->
            // TODO: implement additional check that the arguments are T-free if
            // head is [Tm_fvar ...] with [Mktuple], [Left], etc.
            // Note: not enforcing the types of the arguments because 1) it has
            // been enforced by the main F* type-checker and 2) it's a hassle with
            // binders and stuff
            let starred_arg = match (normalize (SS.compress bv.sort)).n with
              | Tm_type _ -> normalize arg
              | _ -> snd (check_n env arg)
            in
            (starred_arg, q), NT (bv, arg)
          ) binders args) in
          let comp = SS.subst_comp subst_elts comp in
          nm_of_comp comp.n, mk (Tm_app (head, args))
      | _ ->
          raise (Err (Util.format1 "%s: not a function type" (Print.term_to_string t_head)))
      end

  | Tm_let ((false, [ binding ]), e2) ->
      mk_let env binding e2 infer check_m

  | Tm_match (e0, branches) ->
      mk_match env e0 branches infer

  | Tm_uinst (e, _)
  | Tm_meta (e, _)
  | Tm_ascribed (e, _, _) ->
      infer env e

  | Tm_let _ ->
      failwith (Util.format1 "[infer]: Tm_let %s" (Print.term_to_string e))
  | Tm_constant _ ->
      failwith (Util.format1 "[infer]: Tm_constant %s" (Print.term_to_string e))
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
  // TODO: automatically [bind] when the scrutinee is monadic
  let _, e0 = check_n env e0 in
  let nms, branches = List.split (List.map (fun b ->
    match open_branch b with
    | pat, None, body ->
        let env = { env with env = List.fold_left push_bv env.env (pat_bvs pat) } in
        let nm, body = f env body in
        nm, (pat, None, body)
    | _ ->
        raise (Err ("No when clauses in the definition language"))
  ) branches) in
  let t1 = match List.hd nms with | M t1 | N t1 -> t1 in
  let has_m = List.existsb (function | M _ -> true | _ -> false) nms in
  let nms, branches = List.split (List.map2 (fun nm (pat, guard, body) ->
    let check t t' =
      if not (Rel.is_trivial (Rel.teq env.env t' t)) then
        raise (Err ("[infer]: branches do not have the same type"))
    in
    match nm, has_m with
    | N t2, false
    | M t2, true ->
        check t2 t1;
        nm, (pat, guard, body)
    | N t2, true ->
        check t2 t1;
        M t2, (pat, guard, mk_return env t2 body)
    | M _, false ->
        failwith "impossible"
  ) nms branches) in
  let branches = List.map close_branch branches in
  (if has_m then M t1 else N t1), mk (Tm_match (e0, branches))


and mk_let (env: env_) (binding: letbinding) (e2: term)
    (proceed: env_ -> term -> nm * term)
    (ensure_m: env_ -> term -> term * term) =
  let mk x = mk x None e2.pos in
  let e1 = binding.lbdef in
  // This is [let x = e1 in e2]. Open [x] in [e2].
  let x = Util.left binding.lbname in
  let x_binders = [ S.mk_binder x ] in
  let x_binders, e2 = SS.open_term x_binders e2 in
  begin match infer env e1 with
  | N t1, e1 ->
      let env = { env with env = push_bv env.env ({ x with sort = t1 }) } in
      // Simple case: just a regular let-binding. We defer checks to e2.
      let nm_rec, e2 = proceed env e2 in
      nm_rec, mk (Tm_let ((false, [ { binding with lbdef = e1 } ]), SS.close x_binders e2))
  | M t1, e1 ->
      let env = { env with env = push_bv env.env ({ x with sort = t1 }) } in
      let t2, e2 = ensure_m env e2 in
      // Now, generate the bind.
      // p: A* -> Type
      let p_type = mk_star_to_type mk env t2 in
      let p = S.gen_bv "p''" None p_type in
      // e2* p
      let e2 = mk (Tm_app (e2, [ S.bv_to_name p, S.as_implicit false ])) in
      // fun x -> e2* p; this takes care of closing [x].
      let e2 = U.abs x_binders e2 None in
      // e1* (fun x -> e2* p)
      let body = mk (Tm_app (e1, [ e2, S.as_implicit false ])) in
      M t2, U.abs [ S.mk_binder p ] body None
  end


and check_n (env: env_) (e: term): typ * term =
  let mn = N (mk Tm_unknown None e.pos) in
  match check env e mn with
  | N t, e -> t, e
  | _ -> failwith "[check_n]: impossible"

and check_m (env: env_) (e: term): typ * term =
  let mn = M (mk Tm_unknown None e.pos) in
  match check env e mn with
  | M t, e -> t, e
  | _ -> failwith "[check_m]: impossible"

and comp_of_nm (nm: nm_): comp =
  match nm with
  | N t -> mk_Total t
  | M t -> mk_M t

and mk_M (t: typ): comp =
  mk_Comp ({
    effect_name = Const.monadic_lid;
    result_typ = t;
    effect_args = [ t, S.as_implicit false ];
    flags = []
  })


let star_expr_definition env t =
  star_definition env t check_n
