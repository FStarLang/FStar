(*
   Copyright 2023 Microsoft Research

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

module Pulse.Checker.Base

module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing
module Metatheory = Pulse.Typing.Metatheory
module CP = Pulse.Checker.Pure
module RU = Pulse.RuntimeUtils
module FV = Pulse.Typing.FV
module P = Pulse.Syntax.Printer

open Pulse.Typing.Combinators
open Pulse.Typing.Metatheory

let debug (g:env) (f: unit -> T.Tac string) : T.Tac unit =
  if RU.debug_at_level (fstar_env g) "pulse.checker" then
    T.print (f())

let format_failed_goal (g:env) (ctxt:list term) (goal:list term) =
  let terms_to_strings (ts:list term)= T.map Pulse.Syntax.Printer.term_to_string ts in
  let numbered_list ss = 
       let _, s = T.fold_left (fun (i, acc) s -> (i+1, Printf.sprintf "%d. %s" i s :: acc)) (1, []) ss in
       String.concat "\n  " (List.rev s)
  in
  let format_terms (ts:list term) = numbered_list (terms_to_strings ts) in
  Printf.sprintf 
    "Failed to prove the following goals:\n  \
     %s\n\
     The remaining conjuncts in the separation logic context available for use are:\n  \
     %s\n\
     The typing context is:\n  \
     %s\n"
    (format_terms goal)
    (format_terms ctxt)
    (env_to_string g)


let mk_arrow ty t = RT.mk_arrow ty T.Q_Explicit t
let mk_abs ty t = RT.(mk_abs ty T.Q_Explicit t)

let intro_comp_typing (g:env) 
                      (c:comp_st)
                      (pre_typing:tot_typing g (comp_pre c) tm_slprop)
                      (i_typing:effect_annot_typing g (effect_annot_of_comp c))
                      (res_typing:universe_of g (comp_res c) (comp_u c))
                      (x:var { fresh_wrt x g (freevars (comp_post c)) })
                      (post_typing:tot_typing (push_binding g x ppname_default (comp_res c)) (open_term (comp_post c) x) tm_slprop)
  : T.Tac (comp_typing g c (universe_of_comp c))
  = let intro_st_comp_typing (st:st_comp { comp_u c == st.u /\
                                           comp_pre c == st.pre /\
                                           comp_res c == st.res /\
                                           comp_post c == st.post } )
      : T.Tac (st_comp_typing g st)
      = STC g st x res_typing pre_typing post_typing
    in
    match c with
    | C_ST st -> 
      let stc = intro_st_comp_typing st in
      CT_ST _ _ stc
    | C_STAtomic i obs st -> 
      let stc = intro_st_comp_typing st in
      CT_STAtomic _ i obs _ i_typing stc
    | C_STGhost i st -> 
      let stc = intro_st_comp_typing st in
      CT_STGhost _ i _ i_typing stc

irreducible
let post_typing_as_abstraction
  (#g:env) (#x:var) (#ty:term) (#t:term { fresh_wrt x g (freevars t) })
  (_:tot_typing (push_binding g x ppname_default ty) (open_term t x) tm_slprop)
  : FStar.Ghost.erased (RT.tot_typing (elab_env g) (mk_abs ty t) (mk_arrow ty tm_slprop))                                 
  = admit()

(* This should be in reflection typing *)
let fstar_equiv_preserves_typing
    (g:R.env) (t1 : R.term) (typ : R.term) (t2 : R.term)
    (eq : squash (T.equiv_token g t1 t2))
    (t1_typing : RT.tot_typing g t1 typ)
  : RT.tot_typing g t2 typ
  = admit()

let equiv_preserves_typing
    (g:env) (t1 : term) (typ : term) (t2 : term)
    (eq : squash (T.equiv_token (elab_env g) t1 t2))
    (t1_typing : typing g t1 T.E_Total typ)
  : typing g t2 T.E_Total typ
  = match t1_typing with
    | E pf -> E (fstar_equiv_preserves_typing _ t1 typ t2 eq pf)

let check_effect_annot (g:env) (e:effect_annot)
  : T.Tac (e':effect_annot { effect_annot_labels_match e e' } & effect_annot_typing g e') =
  let check_opens opens : T.Tac (e:term & typing g e T.E_Total tm_inames) =
    let (| opens, d |) = CP.check_term g opens T.E_Total tm_inames in
    let opens' =
      T.norm_well_typed_term
        (elab_env g)
        [primops; iota; zeta; delta_attr ["Pulse.Lib.Core.unfold_check_opens"]]
        opens
    in
    (| opens', equiv_preserves_typing _ _ _ _ () d |)
  in
  match e with
  | EffectAnnotSTT -> (| e, () |)
  | EffectAnnotGhost { opens } ->
    let (| opens, d |) = check_opens opens in
    (| EffectAnnotGhost { opens }, d |)
  | EffectAnnotAtomic { opens } ->
    let (| opens, d |) = check_opens opens in
    (| EffectAnnotAtomic { opens }, d |)
  | EffectAnnotAtomicOrGhost { opens } ->
    let (| opens, d |) = check_opens opens in
    (| EffectAnnotAtomicOrGhost { opens }, d |)

let intro_post_hint g effect_annot ret_ty_opt post =
  let x = fresh g in
  let ret_ty = 
      match ret_ty_opt with
      | None -> wr RT.unit_ty FStar.Range.range_0
      | Some t -> t
  in
  let ret_ty, _ = CP.instantiate_term_implicits g ret_ty None in
  let (| u, ty_typing |) = CP.check_universe g ret_ty in
  let (| post, post_typing |) = CP.check_slprop (push_binding g x ppname_default ret_ty) (open_term_nv post (v_as_nv x)) in 
  let post' = close_term post x in
  Pulse.Typing.FV.freevars_close_term post x 0;
  let (| effect_annot, effect_annot_typing |) = check_effect_annot g effect_annot in
  assume (open_term post' x == post);
  { g;
    effect_annot;
    effect_annot_typing;
    ret_ty; u; ty_typing;
    post=post';
    x; post_typing_src=post_typing;
    post_typing=post_typing_as_abstraction #_ #_ #_ #post' post_typing }

let comp_typing_as_effect_annot_typing (#g:env) (#c:comp_st) (ct:comp_typing_u g c)
: effect_annot_typing g (effect_annot_of_comp c)
= let _, iname_typing = Metatheory.comp_typing_inversion ct in
  match c with
  | C_ST _ -> ()
  | C_STGhost _ _
  | C_STAtomic _ _ _ -> iname_typing
  

let post_hint_from_comp_typing #g #c ct = 
  let st_comp_typing, _ = Metatheory.comp_typing_inversion ct in
  let (| ty_typing, pre_typing, x, post_typing |) = Metatheory.st_comp_typing_inversion st_comp_typing in
  let effect_annot_typing = comp_typing_as_effect_annot_typing ct in
  let p : post_hint_t = 
    { g;
      effect_annot=_;
      effect_annot_typing;
      ret_ty = comp_res c; u=comp_u c; 
      ty_typing=ty_typing;
      post=comp_post c;
      x;
      post_typing_src=post_typing;
      post_typing=post_typing_as_abstraction post_typing }
  in
  p

let comp_typing_from_post_hint
    (#g: env)
    (c: comp_st)
    (pre_typing: tot_typing g (comp_pre c) tm_slprop)
    (p:post_hint_for_env g { comp_post_matches_hint c (Some p) })
: T.Tac (comp_typing_u g c)
= let x = fresh g in
  if x `Set.mem` freevars p.post //exclude this
  then fail g None "Impossible: unexpected freevar in post, please file a bug-report"
  else let post_typing = post_hint_typing g p x in
       intro_comp_typing g c pre_typing
        post_typing.effect_annot_typing
        post_typing.ty_typing 
        x post_typing.post_typing


let extend_post_hint g p x tx conjunct conjunct_typing =
  let g' = push_binding g x ppname_default tx in
  let y = fresh g' in
  let g'' = push_binding g' y ppname_default p.ret_ty in
  let p_post_typing_src
    : tot_typing (push_binding p.g p.x ppname_default p.ret_ty)
                 (open_term p.post p.x) tm_slprop
    = p.post_typing_src
  in
  let p_post_typing_src''
    : tot_typing g'' (open_term p.post y) tm_slprop
    = RU.magic () //weaken, rename
  in
  let conjunct_typing'
    : tot_typing g' conjunct tm_slprop
    = conjunct_typing
  in
  let conjunct_typing''
    : tot_typing g'' (open_term conjunct y) tm_slprop
    = RU.magic () //weaken
  in
  let new_post = tm_star p.post conjunct in
  let new_post_typing
    : tot_typing g'' (open_term new_post y) tm_slprop
    = Pulse.Typing.star_typing p_post_typing_src'' conjunct_typing''
  in
  assume (fresh_wrt y g'' (freevars new_post));
  let new_post_abs_typing
    : Ghost.erased (RT.tot_typing (elab_env g'') (mk_abs p.ret_ty new_post) (mk_arrow p.ret_ty tm_slprop))
    = post_typing_as_abstraction new_post_typing
  in
  { p with
    g=g';
    post=new_post;
    x=y;
    post_typing_src=new_post_typing;
    post_typing=new_post_abs_typing }

let k_elab_unit (g:env) (ctxt:term)
  : continuation_elaborator g ctxt g ctxt
  = fun p r -> r

let k_elab_trans
  (#g0:env) (#g1:env { g1 `env_extends` g0 }) (#g2:env { g2 `env_extends` g1 }) (#ctxt0 #ctxt1 #ctxt2:term)
  (k0:continuation_elaborator g0 ctxt0 g1 ctxt1)
  (k1:continuation_elaborator g1 ctxt1 g2 ctxt2 { g1 `env_extends` g0})
   : continuation_elaborator g0 ctxt0 g2 ctxt2
   = fun post_hint res -> k0 post_hint (k1 post_hint res)

let comp_st_with_post (c:comp_st) (post:term)
  : c':comp_st { st_comp_of_comp c' == ({ st_comp_of_comp c with post} <: st_comp) } =
  match c with
  | C_ST st -> C_ST { st with post }
  | C_STGhost i st -> C_STGhost i { st with post }
  | C_STAtomic i obs st -> C_STAtomic i obs {st with post}

let ve_unit_r g (p:term) : slprop_equiv g (tm_star p tm_emp) p = 
  VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Unit _ _)

let st_equiv_trans (#g:env) (#c0 #c1 #c2:comp) (d01:st_equiv g c0 c1) (d12:st_equiv g c1 c2)
  : option (st_equiv g c0 c2)
  = 
    match d01 with
    | ST_SLPropEquiv _f _c0 _c1 x c0_pre_typing c0_res_typing c0_post_typing eq_res_01 eq_pre_01 eq_post_01 -> (
      let ST_SLPropEquiv _f _c1 _c2 y c1_pre_typing c1_res_typing c1_post_typing eq_res_12 eq_pre_12 eq_post_12 = d12 in
      if x = y && eq_tm (comp_res c0) (comp_res c1)
      then Some (
            ST_SLPropEquiv g c0 c2 x c0_pre_typing c0_res_typing c0_post_typing
              (RT.Rel_trans _ _ _ _ _ eq_res_01 eq_res_12)
              (VE_Trans _ _ _ _ eq_pre_01 eq_pre_12)
              (VE_Trans _ _ _ _ eq_post_01 eq_post_12)
      )
      else None
    )
    | ST_TotEquiv g t1 t2 u typing eq ->
      let ST_TotEquiv _g _t1 t3 _ _ eq' = d12 in
      let eq'' = Ghost.hide (RT.Rel_trans _ _ _ _ _ eq eq') in
      Some (ST_TotEquiv g t1 t3 u typing eq'')

let t_equiv #g #st #c (d:st_typing g st c) (#c':comp) (eq:st_equiv g c c')
  : st_typing g st c'
  = match d with
    | T_Equiv _ _ _ _ d0 eq' -> (
        match st_equiv_trans eq' eq with
        | None -> T_Equiv _ _ _ _ d eq
        | Some eq'' -> T_Equiv _ _ _ _ d0 eq''
    )
    | _ -> T_Equiv _ _ _ _ d eq

let st_equiv_post (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                  (post:term { freevars post `Set.subset` freevars (comp_post c)})
                  (veq: (x:var { fresh_wrt x g (freevars (comp_post c)) } ->
                         slprop_equiv (push_binding g x ppname_default (comp_res c)) 
                                     (open_term (comp_post c) x)
                                     (open_term post x)))
  : Dv (st_typing g t (comp_st_with_post c post))
  = if eq_tm post (comp_post c) then d
    else
      let c' = comp_st_with_post c post in
      let (| u_of, pre_typing, x, post_typing |) = Metatheory.(st_comp_typing_inversion (fst (comp_typing_inversion (st_typing_correctness d)))) in
      let veq = veq x in
      let st_equiv : st_equiv g c c' =
          ST_SLPropEquiv g c c' x pre_typing u_of post_typing (RT.Rel_refl _ _ _) (VE_Refl _ _) veq
      in
      t_equiv d st_equiv

let simplify_post (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                  (post:term { comp_post c == tm_star post tm_emp})
  : Dv (st_typing g t (comp_st_with_post c post))
  = st_equiv_post d post (fun x -> ve_unit_r (push_binding g x ppname_default (comp_res c)) (open_term post x))

let simplify_lemma (c:comp_st) (c':comp_st) (post_hint:option post_hint_t)
  : Lemma
    (requires
        comp_post_matches_hint c post_hint /\
        effect_annot_of_comp c == effect_annot_of_comp c' /\
        comp_res c' == comp_res c /\
        comp_u c' == comp_u c /\
        comp_post c' == tm_star (comp_post c) tm_emp)
    (ensures comp_post_matches_hint (comp_st_with_post c' (comp_post c)) post_hint /\
             comp_pre (comp_st_with_post c' (comp_post c)) == comp_pre c')
  = ()

let slprop_equiv_typing_bk (#g:env) (#ctxt:_) (ctxt_typing:tot_typing g ctxt tm_slprop)
                           (#p:_) (d:slprop_equiv g p ctxt)
  : tot_typing g p tm_slprop 
  = let _, bk = slprop_equiv_typing d in
    bk ctxt_typing

let comp_with_pre (c:comp_st) (pre:term) =
  match c with
  | C_ST st -> C_ST { st with pre }
  | C_STGhost i st -> C_STGhost i { st with pre }
  | C_STAtomic i obs st -> C_STAtomic i obs {st with pre}


let st_equiv_pre (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                 (pre:term)
                 (veq: slprop_equiv g (comp_pre c) pre)
  : Dv (st_typing g t (comp_with_pre c pre))
  = if eq_tm pre (comp_pre c) then d
    else
      let c' = comp_with_pre c pre in
      let (| u_of, pre_typing, x, post_typing |) =
        Metatheory.(st_comp_typing_inversion (fst (comp_typing_inversion (st_typing_correctness d)))) in
      let st_equiv : st_equiv g c c' =
          ST_SLPropEquiv g c c' x pre_typing u_of post_typing (RT.Rel_refl _ _ _) veq (VE_Refl _ _)
      in
      t_equiv d st_equiv


#push-options "--z3rlimit_factor 4 --ifuel 2 --fuel 0"
let k_elab_equiv_continuation (#g1:env) (#g2:env { g2 `env_extends` g1 }) (#ctxt #ctxt1 #ctxt2:term)
  (k:continuation_elaborator g1 ctxt g2 ctxt1)
  (d:slprop_equiv g2 ctxt1 ctxt2)
  : continuation_elaborator g1 ctxt g2 ctxt2 =
  fun post_hint res ->
    let (| st, c, st_d |) = res in
    let st_d : st_typing g2 st c = st_d in
    assert (comp_pre c == ctxt2);
    let st_d' : st_typing g2 st (comp_with_pre c ctxt1) = st_equiv_pre st_d _ (VE_Sym _ _ _ d) in
    k post_hint (| st, _, st_d' |)
#pop-options

let slprop_equiv_typing_fwd (#g:env) (#ctxt:_) (ctxt_typing:tot_typing g ctxt tm_slprop)
                           (#p:_) (d:slprop_equiv g ctxt p)
  : tot_typing g p tm_slprop 
  = let fwd, _ = slprop_equiv_typing d in
    fwd ctxt_typing

#push-options "--z3rlimit_factor 4 --ifuel 1 --fuel 0"
let k_elab_equiv_prefix
  (#g1:env) (#g2:env { g2 `env_extends` g1 }) (#ctxt1 #ctxt2 #ctxt:term)
  (k:continuation_elaborator g1 ctxt1 g2 ctxt)
  (d:slprop_equiv g1 ctxt1 ctxt2)
  : continuation_elaborator g1 ctxt2 g2 ctxt =
  fun post_hint res ->
  let framing_token : frame_for_req_in_ctxt g1 ctxt2 ctxt1 = 
  let d = VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Trans _ _ _ _ (VE_Unit _ _) d) in
    (| tm_emp, emp_typing, d |)
  in
  let res = k post_hint res in
  let (| st, c, st_d |) = res in
  assert (comp_pre c == ctxt1);
  (| _, _, st_equiv_pre st_d _ d |)
 #pop-options

let k_elab_equiv
  (#g1:env) (#g2:env { g2 `env_extends` g1 }) (#ctxt1 #ctxt1' #ctxt2 #ctxt2':term)                 
  (k:continuation_elaborator g1 ctxt1 g2 ctxt2)
  (d1:slprop_equiv g1 ctxt1 ctxt1')
  (d2:slprop_equiv g2 ctxt2 ctxt2')
  : continuation_elaborator g1 ctxt1' g2 ctxt2' =
  
  let k : continuation_elaborator g1 ctxt1 g2 ctxt2' =
    k_elab_equiv_continuation k d2 in
  let k : continuation_elaborator g1 ctxt1' g2 ctxt2' =
    k_elab_equiv_prefix k d1 in
  k

#push-options "--fuel 3 --ifuel 2 --split_queries no --z3rlimit_factor 20"
open Pulse.PP
let continuation_elaborator_with_bind (#g:env) (ctxt:term)
  (#c1:comp{stateful_comp c1})
  (#e1:st_term)
  (e1_typing:st_typing g e1 c1)
  (ctxt_pre1_typing:tot_typing g (tm_star ctxt (comp_pre c1)) tm_slprop)
  (x:nvar { None? (lookup g (snd x)) })
  : T.Tac (continuation_elaborator
             g
             (tm_star ctxt (comp_pre c1))
             (push_binding g (snd x) (fst x) (comp_res c1))
             (tm_star (open_term (comp_post c1) (snd x)) ctxt)) =

  let pre1 = comp_pre c1 in
  let res1 = comp_res c1 in
  let post1 = comp_post c1 in
  let ctxt_typing = star_typing_inversion_l ctxt_pre1_typing in
  // let p_prop = Metatheory.pure_typing_inversion pure_typing in
  let v_eq = VE_Comm g ctxt pre1 in
  let framing_token : frame_for_req_in_ctxt g (tm_star ctxt pre1) pre1 = 
    (| ctxt, ctxt_typing, VE_Comm g pre1 ctxt  |)
  in
  let (| c1, e1_typing |) =
    apply_frame ctxt_pre1_typing e1_typing framing_token in
  let (| u_of_1, pre_typing, _, _ |) =
    Metatheory.(st_comp_typing_inversion (fst <| comp_typing_inversion (st_typing_correctness e1_typing))) in
  let b = res1 in
  let ppname, x = x in
  let g' = push_binding g x ppname b in
  
  let post1_opened = open_term_nv post1 (v_as_nv x) in
  let k : continuation_elaborator g (tm_star ctxt pre1) g' (tm_star post1_opened ctxt) =
    fun post_hint res ->
    let (| e2, c2, e2_typing |) = res in
    assert (comp_post_matches_hint c2 post_hint);
    let e2_typing : st_typing g' e2 c2 = e2_typing in
    let e2_closed = close_st_term e2 x in
    assume (open_st_term e2_closed x == e2);
    assert (comp_pre c1 == (tm_star ctxt pre1));
    assert (comp_post c1 == tm_star post1 ctxt);
    assert (comp_pre c2 == tm_star post1_opened ctxt);
    assert (open_term (comp_post c1) x == tm_star post1_opened (open_term ctxt x));
    // ctxt is well-typed, hence ln
    assume (open_term ctxt x == ctxt);
    assert (open_term (comp_post c1) x == comp_pre c2);
    // we closed e2 with x
    assume (~ (x `Set.mem` freevars_st e2_closed));
    if x `Set.mem` freevars (comp_post c2)
    then fail g' None "Impossible: freevar clash when constructing continuation elaborator for bind, please file a bug-report"
    else (
      let t_typing, post_typing =
        Pulse.Typing.Combinators.bind_res_and_post_typing g c2 x post_hint in
      let g = push_context g "mk_bind" e1.range in
      // info_doc g None
      //   [prefix 4 1 (doc_of_string "mk_bind e1 = ") (doc_of_string (Pulse.Syntax.Printer.st_term_to_string e1));
      //    prefix 4 1 (doc_of_string "mk_bind c1 = ") (pp #comp c1);
      //    prefix 4 1 (doc_of_string "mk_bind e2 = ") (doc_of_string (Pulse.Syntax.Printer.st_term_to_string e2));
      //    prefix 4 1 (doc_of_string "mk_bind c2 = ") (pp #comp c2)]
      // ;
      let (| e, c, e_typing |) =
        Pulse.Typing.Combinators.mk_bind
          g (tm_star ctxt pre1) 
          e1 e2_closed c1 c2 (ppname, x) e1_typing
          u_of_1 
          e2_typing
          t_typing
          post_typing
          post_hint
      in
      (| e, c, e_typing |)
    )
  in
  k
#pop-options

module LN = Pulse.Typing.LN
#push-options "--z3rlimit_factor 8 --fuel 1 --ifuel 1"

let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b{y == x} = x

let st_comp_typing_with_post_hint 
      (#g:env) (#ctxt:_)
      (ctxt_typing:tot_typing g ctxt tm_slprop)
      (post_hint:post_hint_opt g { Some? post_hint })
      (c:comp_st { comp_pre c == ctxt /\ comp_post_matches_hint c post_hint })
: Dv (st_comp_typing g (st_comp_of_comp c))
= let st = st_comp_of_comp c in
  let Some ph = post_hint in
  let post_typing_src
    : tot_typing (push_binding ph.g ph.x ppname_default ph.ret_ty)
                 (open_term ph.post ph.x) tm_slprop
    = ph.post_typing_src
  in
  let x = fresh g in
  assume (fresh_wrt x g (freevars ph.post));
  assume (None? (lookup g ph.x));
  let post_typing_src
    : tot_typing (push_binding ph.g x ppname_default ph.ret_ty)
                 (open_term ph.post x) tm_slprop
    = if x = ph.x
      then post_typing_src
      else 
        let open Pulse.Typing.Metatheory.Base in
        let tt :
         tot_typing
            (push_binding ph.g x ppname_default ph.ret_ty)
            (subst_term (open_term ph.post ph.x) (renaming ph.x x))
            (subst_term tm_slprop (renaming ph.x x)) =
          tot_typing_renaming1 ph.g ph.x ph.ret_ty (open_term ph.post ph.x) tm_slprop post_typing_src x
        in
        assert (subst_term tm_slprop (renaming ph.x x) == tm_slprop);
        assume (subst_term (open_term ph.post ph.x) (renaming ph.x x) ==
                open_term ph.post x);
        coerce_eq tt ()
  in
  let post_typing_src
    : tot_typing (push_binding g x ppname_default ph.ret_ty)
                 (open_term ph.post x) tm_slprop
    = //weakening: TODO
      RU.magic ()
  in
  let ty_typing : universe_of ph.g st.res st.u = ph.ty_typing in
  let ty_typing : universe_of g st.res st.u =
    Pulse.Typing.Metatheory.tot_typing_weakening_standard ph.g ty_typing g
  in
  assert (st.res == ph.ret_ty);
  assert (st.post == ph.post);
  STC g st x ty_typing ctxt_typing post_typing_src

let continuation_elaborator_with_bind_fn (#g:env) (#ctxt:term)
  (ctxt_typing:tot_typing g ctxt tm_slprop)
  (#e1:st_term)
  (#c1:comp { C_Tot? c1 })
  (b:binder{b.binder_ty == comp_res c1})
  (e1_typing:st_typing g e1 c1)
  (x:nvar { None? (lookup g (snd x)) })
: T.Tac (continuation_elaborator
          g ctxt
          (push_binding g (snd x) ppname_default (comp_res c1)) ctxt)
= let t1 = comp_res c1 in
  assert ((push_binding g (snd x) (fst x) t1) `env_extends` g);
  fun post_hint (| e2, c2, d2 |) ->
    if None? post_hint then T.fail "bind_fn: expects the post_hint to be set";
    let ppname, x = x in
    let e2_closed = close_st_term e2 x in
    assume (open_st_term (close_st_term e2 x) x == e2);
    let e = wrst c2 (Tm_Bind {binder=b; head=e1; body=e2_closed}) in
    let (| u, c1_typing |) = Pulse.Typing.Metatheory.Base.st_typing_correctness_ctot e1_typing in
    let c2_typing : comp_typing g c2 (universe_of_comp c2) =
      match c2 with
      | C_ST st -> 
        let stc = st_comp_typing_with_post_hint ctxt_typing post_hint c2 in
        CT_ST _ _ stc
      
      | C_STAtomic i obs st -> 
        let stc = st_comp_typing_with_post_hint ctxt_typing post_hint c2 in
        let i_typing = CP.core_check_term g i T.E_Total tm_inames in
        CT_STAtomic _ _ obs _ i_typing stc

      | C_STGhost i st ->
        let i_typing = CP.core_check_term g i T.E_Total tm_inames in
        let stc = st_comp_typing_with_post_hint ctxt_typing post_hint c2 in
        CT_STGhost _ i _ i_typing stc
    in
    let d : st_typing g e c2 =
        T_BindFn g e1 e2_closed c1 c2 b x e1_typing u c1_typing d2 c2_typing
    in
    (| e, c2, d |)

let rec check_equiv_emp (g:env) (vp:term)
  : option (slprop_equiv g vp tm_emp)
  = match inspect_term vp with
    | Tm_Emp -> Some (VE_Refl _ _)
    | Tm_Star vp1 vp2 ->
      (match check_equiv_emp g vp1, check_equiv_emp g vp2 with
       | Some d1, Some d2 ->
         let d3 : slprop_equiv g (tm_star vp1 vp2) (tm_star tm_emp tm_emp)
           = VE_Ctxt _ _ _ _ _ d1 d2 in
         let d4 : slprop_equiv g (tm_star tm_emp tm_emp) tm_emp =
           VE_Unit _ _ in
         Some (VE_Trans _ _ _ _ d3 d4)
       | _, _ -> None)
     | _ -> None

let emp_inames_included (g:env) (i:term) (_:tot_typing g i tm_inames)
: prop_validity g (tm_inames_subset tm_emp_inames i)
= RU.magic()

let return_in_ctxt (g:env) (y:var) (y_ppname:ppname) (u:universe) (ty:term) (ctxt:slprop)
  (ty_typing:universe_of g ty u)
  (post_hint0:post_hint_opt g { Some? post_hint0 /\ checker_res_matches_post_hint g post_hint0 y ty ctxt})
: Div  (st_typing_in_ctxt g ctxt post_hint0)
       (requires lookup g y == Some ty)
       (ensures fun _ -> True)
= let Some post_hint = post_hint0 in
  let x = fresh g in
  assume (~ (x `Set.mem` freevars post_hint.post));
  let ctag =
    match post_hint.effect_annot with
    | EffectAnnotAtomic _ -> STT_Atomic
    | EffectAnnotGhost _ -> STT_Ghost
    | EffectAnnotAtomicOrGhost _ -> STT_Atomic
    | EffectAnnotSTT -> STT
  in
  let y_tm = tm_var {nm_index=y;nm_ppname=y_ppname} in
  let d = T_Return g ctag false u ty y_tm post_hint.post x ty_typing
    (RU.magic ())  // that null_var y is well typed at ty in g, we know since lookup g y == Some ty
    (RU.magic ())  // typing of (open post x) in (g, x) ... post_hint is well-typed, so should get
  in
  let t = wtag (Some ctag) (Tm_Return {expected_type=tm_unknown;insert_eq=false;term=y_tm}) in
  let c = comp_return ctag false u ty y_tm post_hint.post x in
  let d : st_typing g t c = d in
  assume (comp_u c == post_hint.u); // this u should follow from equality of t
  match c, post_hint.effect_annot with
  | C_STAtomic _ obs _, EffectAnnotAtomic { opens }
  | C_STAtomic _ obs _, EffectAnnotAtomicOrGhost { opens } ->
    assert (comp_inames c == tm_emp_inames);
    let pht = post_hint_typing g post_hint x in
    let validity = emp_inames_included g opens pht.effect_annot_typing in
    let d = T_Sub _ _ _ _ d (STS_AtomicInvs _ (st_comp_of_comp c) tm_emp_inames opens obs obs validity) in
    (| _, _, d |)
  | C_STGhost _ _, EffectAnnotGhost { opens }
  | C_STGhost _ _, EffectAnnotAtomicOrGhost { opens } ->
    assert (comp_inames c == tm_emp_inames);
    let pht = post_hint_typing g post_hint x in
    let validity = emp_inames_included g opens pht.effect_annot_typing in
    let d = T_Sub _ _ _ _ d (STS_GhostInvs _ (st_comp_of_comp c) tm_emp_inames opens validity) in
    (| _, _, d |)
  | _ -> 
    (| _, _, d |)

let match_comp_res_with_post_hint (#g:env) (#t:st_term) (#c:comp_st)
  (d:st_typing g t c)
  (post_hint:post_hint_opt g)
  : T.Tac (t':st_term &
           c':comp_st &
           st_typing g t' c') =

  match post_hint with
  | None -> (| t, c, d |)
  | Some { ret_ty } ->
    let cres = comp_res c in
    if eq_tm cres ret_ty
    then (| t, c, d |)
    else match Pulse.Checker.Pure.check_equiv g cres ret_ty with
         | None ->
           fail g (Some t.range)
             (Printf.sprintf "Could not prove equiv for computed type %s and expected type %s"
                (P.term_to_string cres)
                (P.term_to_string ret_ty))
         | Some tok ->
           let d_equiv
             : RT.equiv _ cres ret_ty =
             RT.Rel_eq_token _ _ _ (FStar.Squash.return_squash tok) in
           
           let c' = with_st_comp c {(st_comp_of_comp c) with res = ret_ty } in
           let (| cres_typing, cpre_typing, x, cpost_typing |) =
             st_comp_typing_inversion (fst <| comp_typing_inversion (st_typing_correctness d)) in

           let d_stequiv : st_equiv g c c' =
             ST_SLPropEquiv _ c c' _ cpre_typing cres_typing cpost_typing d_equiv (VE_Refl _ _) (VE_Refl _ _)
           in

           (| t, c', T_Equiv _ _ _ _ d d_stequiv |)

let apply_checker_result_k (#g:env) (#ctxt:slprop) (#post_hint:post_hint_for_env g)
  (r:checker_result_t g ctxt (Some post_hint))
  (res_ppname:ppname)
  : T.Tac (st_typing_in_ctxt g ctxt (Some post_hint)) =

  // TODO: FIXME add to checker result type?
  let (| y, g1, (| u_ty, ty_y, d_ty_y |), (| pre', _ |), k |) = r in

  let (| u_ty_y, d_ty_y |) = Pulse.Checker.Pure.check_universe g1 ty_y in

  let d : st_typing_in_ctxt g1 pre' (Some post_hint) =
    return_in_ctxt g1 y res_ppname u_ty_y ty_y pre' d_ty_y (Some post_hint) in

  k (Some post_hint) d

#push-options "--z3rlimit_factor 4 --fuel 0 --ifuel 1"
let checker_result_for_st_typing (#g:env) (#ctxt:slprop) (#post_hint:post_hint_opt g)
  (d:st_typing_in_ctxt g ctxt post_hint)
  (ppname:ppname)
  : T.Tac (checker_result_t g ctxt post_hint) =

  let (| t, c, d |) = d in
 
  let x = fresh g in

  let g' = push_binding g x ppname (comp_res c) in
  let ctxt' = open_term_nv (comp_post c) (ppname, x) in
  let k
    : continuation_elaborator
        g (tm_star tm_emp (comp_pre c))
        g' (tm_star ctxt' tm_emp) =
    continuation_elaborator_with_bind tm_emp d (RU.magic ()) (ppname, x) in
  let k
    : continuation_elaborator g (comp_pre c) g' ctxt' =
    k_elab_equiv k (RU.magic ()) (RU.magic ()) in

  let _ : squash (checker_res_matches_post_hint g post_hint x (comp_res c) ctxt') =
    match post_hint with
    | None -> ()
    | Some post_hint -> () in

  assert (g' `env_extends` g);

  let comp_res_typing, _, f =
    Metatheory.(st_comp_typing_inversion_cofinite (fst <| comp_typing_inversion (st_typing_correctness d))) in

  // RU.magic is the typing of comp_res in g'
  // weaken comp_res_typing

  assume (~ (x `Set.mem` freevars (comp_post c)));
  let tt : universe_of _ _ _ = RU.magic () in
  (| x, g', (| comp_u c, comp_res c, tt |), (| ctxt', f x |), k |)
#pop-options

module R = FStar.Reflection.V2

let readback_comp_res_as_comp (c:T.comp) : option comp =
  match c with
  | T.C_Total t -> (
    match readback_comp t with
    | None -> None
    | Some c -> Some c
  )
  | _ -> None

let rec is_stateful_arrow (g:env) (c:option comp) (args:list T.argv) (out:list T.argv)
  : T.Tac (option (list T.argv & T.argv))
  = let open R in
    match c with
    | None -> None
    | Some (C_ST _)
    | Some (C_STGhost _ _)
    | Some (C_STAtomic _ _ _) -> (
      match args, out with
      | [], hd::tl -> Some (List.rev tl, hd)
      | _ -> None //leftover or not enough args
    )

    | Some (C_Tot c_res) -> (
      let ht = T.inspect c_res in
      match ht with
      | T.Tv_Arrow b c -> (
        match args with
        | [] -> ( //no more args; check that only implicits remain, ending in an stateful comp  
          let bs, c = T.collect_arr_ln_bs c_res in
          if List.Tot.for_all (fun b -> R.Q_Implicit? (R.inspect_binder b).qual) bs
          then is_stateful_arrow g (readback_comp_res_as_comp (R.inspect_comp c)) [] out
          else None //too few args    
        )

        | (arg, qual)::args' -> ( //check that this arg qual matches the binder and recurse accordingly
          let bqual =
            (* Ignore equality qualifiers in the binder *)
            match b.qual with
            | Q_Equality -> Q_Explicit
            | q -> q
          in
          match bqual, qual with
          | T.Q_Meta _, T.Q_Implicit
          | T.Q_Implicit, T.Q_Implicit 
          | T.Q_Explicit, T.Q_Explicit ->  //consume this argument
            is_stateful_arrow g (readback_comp_res_as_comp c) args' ((arg, qual)::out)

          | T.Q_Meta _, T.Q_Explicit
          | T.Q_Implicit, T.Q_Explicit -> 
            //don't consume this argument
            is_stateful_arrow g (readback_comp_res_as_comp c) args out

          | _ -> None //incompatible qualifiers; bail
        )
      )
      | _ ->
        let c_res' = RU.whnf_lax (elab_env g) c_res in
        let ht = T.inspect c_res' in
        if T.Tv_Arrow? ht
        then (
          let c_res' = wr c_res' (T.range_of_term c_res') in
          is_stateful_arrow g (Some (C_Tot c_res')) args out
        )
        else None
    )

let checker_result_t_equiv_ctxt (g:env) (ctxt ctxt' : slprop)
  (post_hint:post_hint_opt g)
  (equiv : slprop_equiv g ctxt ctxt')
  (r : checker_result_t g ctxt post_hint)
: checker_result_t g ctxt' post_hint
= let (| x, g1, t, ctxt', k |) = r in
  (| x, g1, t, ctxt', k_elab_equiv k equiv (VE_Refl _ _) |)

module RU = Pulse.RuntimeUtils  
let is_stateful_application (g:env) (e:term) 
  : T.Tac (option st_term) =
  
  let head, args = T.collect_app_ln e in
  match RU.lax_check_term_with_unknown_universes (elab_env g) head with
  | None -> None
  | Some ht -> 
    let head_t = wr ht (T.range_of_term ht) in
    match is_stateful_arrow g (Some (C_Tot head_t)) args [] with 
    | None -> None
    | Some (applied_args, (last_arg, aqual))->
      let head = T.mk_app head applied_args in
      let head = wr head (T.range_of_term head) in
      let last_arg = wr last_arg (T.range_of_term last_arg) in
      let qual = 
        match aqual with
        | T.Q_Implicit -> Some Implicit
        | _ -> None
      in
      let st_app = Tm_STApp { head; arg=last_arg; arg_qual=qual} in
      let st_app = mk_term st_app (RU.range_of_term e) in
      Some st_app
    | _ -> None


let apply_conversion
      (#g:env) (#e:term) (#eff:_) (#t0:term)
      (d:typing g e eff t0)
      (#t1:term)
      (eq:Ghost.erased (RT.related (elab_env g) t0 RT.R_Eq t1))
  : typing g e eff t1
  = let d : RT.typing (elab_env g) e (eff, t0) = d._0 in
    let r : RT.related (elab_env g) t0 RT.R_Eq t1 = eq in
    let r  = RT.Rel_equiv _ _ _ RT.R_Sub r in
    let s : RT.sub_comp (elab_env g) (eff, t0) (eff, t1) = 
        RT.Relc_typ _ _ _ _ _ r
    in
    E (RT.T_Sub _ _ _ _ d s)

let norm_typing
      (g:env) (e:term) (eff:_) (t0:term)
      (d:typing g e eff t0)
      (steps:list norm_step)
  : T.Tac (t':term & typing g e eff t')
  = let u_t_typing : Ghost.erased (u:R.universe & RT.typing _ _ _) = 
      Pulse.Typing.Metatheory.Base.typing_correctness d._0
    in
    let (| t', t'_typing, related_t_t' |) =
      Pulse.RuntimeUtils.norm_well_typed_term (dsnd u_t_typing) steps
    in
    let d : typing g e eff t' = apply_conversion d related_t_t' in
    (| t', d |)

module TermEq = FStar.Reflection.TermEq
let norm_typing_inverse
      (g:env) (e:term) (eff:_) (t0:term)
      (d:typing g e eff t0)
      (t1:term)
      (#u:_)
      (d1:tot_typing g t1 (tm_type u))
      (steps:list norm_step)
  : T.Tac (option (typing g e eff t1))
  = let (| t1', t1'_typing, related_t1_t1' |) =
      let d1 = Ghost.hide d1._0 in
      Pulse.RuntimeUtils.norm_well_typed_term d1 steps
    in
    if TermEq.term_eq t0 t1'
    then (
      let related_t1'_t1 = Ghost.hide (RT.Rel_sym _ _ _ related_t1_t1') in
      Some (apply_conversion d related_t1'_t1)
    )
    else None


let norm_st_typing_inverse
      (#g:env) (#e:st_term) (#t0:term)
      (d:st_typing g e (C_Tot t0))
      (#u:_)
      (t1:term)
      (d1:tot_typing g t1 (tm_type u))
      (steps:list norm_step)
  : T.Tac (option (st_typing g e (C_Tot t1)))
  = let d1 
      : Ghost.erased (RT.tot_typing (elab_env g) t1 (RT.tm_type u))
      = Ghost.hide (coerce_eq d1._0 ())
    in
    let (| t1', t1'_typing, related_t1_t1' |) =
      Pulse.RuntimeUtils.norm_well_typed_term d1 steps
    in
    if TermEq.term_eq t0 t1'
    then (
      let t0_typing 
        : Ghost.erased (RT.tot_typing (elab_env g) t0 (RT.tm_type u)) =
        rt_equiv_typing #_ #_ #t0 related_t1_t1' d1
      in
      let eq
        : Ghost.erased (RT.equiv (elab_env g) t0 t1)
        = Ghost.hide (RT.Rel_sym _ _ _ related_t1_t1')
      in
      let steq : st_equiv g (C_Tot t0) (C_Tot t1) =
        ST_TotEquiv _ _ _ u (E (coerce_eq (Ghost.reveal t0_typing) ())) eq
      in
      Some (T_Equiv _ _ _ _ d steq)
    )
    else None
