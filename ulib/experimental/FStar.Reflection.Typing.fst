(*
   Copyright 2008-2023 Microsoft Research

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

module FStar.Reflection.Typing

(** This module defines a typing judgment for (parts of) the total
    fragment of F*. We are using it in the meta DSL framework as an
    official specification for the F* type system.

    We expect it to grow to cover more of the F* language.

    IT IS HIGHLY EXPERIMENTAL AND NOT YET READY TO USE.
  *)

open FStar.List.Tot
open FStar.Reflection.V2

module R = FStar.Reflection.V2
open FStar.Stubs.Tactics.V2.Builtins
open FStar.Stubs.Tactics.Types
open FStar.Tactics.Effect
module RTB = FStar.Reflection.Typing.Builtins

let inspect_pack = R.inspect_pack_inv
  
let inspect_pack_namedv = R.inspect_pack_namedv
let pack_inspect_namedv = R.pack_inspect_namedv

let inspect_pack_bv = R.inspect_pack_bv
let pack_inspect_bv = R.pack_inspect_bv

let inspect_pack_binder = R.inspect_pack_binder
let pack_inspect_binder = R.pack_inspect_binder

let inspect_pack_comp = R.inspect_pack_comp_inv
let pack_inspect_comp = R.pack_inspect_comp_inv

let inspect_pack_fv = R.inspect_pack_fv
let pack_inspect_fv = R.pack_inspect_fv

let inspect_pack_universe = R.inspect_pack_universe
let pack_inspect_universe = R.pack_inspect_universe

let inspect_pack_lb = R.inspect_pack_lb
let pack_inspect_lb = R.pack_inspect_lb

let inspect_pack_sigelt = R.inspect_pack_sigelt

let lookup_bvar (e:env) (x:int) : option term = magic ()

let lookup_fvar_uinst (e:R.env) (x:R.fv) (us:list R.universe)
  : option R.term = magic ()

let lookup_bvar_extend_env (g:env) (x y:var) (ty:term) = admit ()

let lookup_fvar_extend_env (g:env) (x:fv) (us:universes) (y:var) (ty:term) = admit ()



let open_with (t:term) (v:term) = RTB.open_with t v
let open_with_spec (t v:term) = admit ()
let open_term (t:term) (v:var) = RTB.open_term t v
let open_term_spec (t:term) (v:var) = admit ()
let close_term (t:term) (v:var) = RTB.close_term t v
let close_term_spec (t:term) (v:var) = admit ()
let rename (t:term) (x y:var)= RTB.rename t x y
let rename_spec (t:term) (x y:var) = admit ()

  
let bv_index_of_make_bv (n:nat) = ()
let namedv_uniq_of_make_namedv (n:nat) = ()

let bindings_ok_for_pat bnds pat = magic ()
let bindings_ok_pat_constant c = admit ()

let subtyping_token_renaming (g:env)
                             (bs0:bindings)
                             (bs1:bindings)
                             (x:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) x) })
                             (y:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) y) })
                             (t:term)
                             (t0 t1:term_spec)
                             (d:subtyping_token (extend_env_l g (bs1@(x,t)::bs0)) t0 t1) = magic ()

let subtyping_token_denote_equiv (g:env)
                                 (bs bs':bindings)
                                 (t0 t1:term_spec) = admit ()

let subtyping_token_weakening (g:env)
                              (bs0:bindings)
                              (bs1:bindings)
                              (x:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) x) })
                              (t:term)
                              (t0 t1:term_spec)
                              (d:subtyping_token (extend_env_l g (bs1@bs0)) t0 t1) = magic ()

let well_typed_terms_are_ln _ _ _ _ = admit ()

let type_correctness _ _ _ _ = admit ()



let equiv_arrow #g #e1 #e2 ty q x eq =
  assume (~ (x `Set.mem` (freevars_spec e1 `Set.union` freevars_spec e2)));
  let c1 = E_Total, e1 in
  let c2 = E_Total, e2 in
  Rel_arrow _ _ _ _ c1 c2 _ _ (Rel_refl _ _ _) (Relc_typ _ _ _ _ _ eq)

let equiv_abs_close #g #e1 #e2 ty q x eq =
  // TODO: the following can be the preconditions?
  //       or derived from equiv?
  assume (ln_spec' e1 (-1));
  assume (ln_spec' e2 (-1));
  // this should be a lemma
  assume (~ (x `Set.mem` (freevars_spec (subst_term_spec e1 [ NDs x 0 ]) `Set.union`
                          freevars_spec (subst_term_spec e2 [ NDs x 0 ]))));
  open_close_inverse'_spec 0 e1 x;
  open_close_inverse'_spec 0 e2 x;
  let eq
    : equiv (extend_env g x ty)
        (subst_term_spec
           (subst_term_spec e1 [ NDs x 0 ])
           (open_with_var_spec x 0))
        (subst_term_spec
           (subst_term_spec e2 [ NDs x 0 ])
           (open_with_var_spec x 0)) =
    eq in

  Rel_abs _ _ _ _ _ _ _ (Rel_refl _ _ _) eq


let if_complete_match (g:env) (t:term_spec) = magic()

let mkif
    (g:fstar_env)
    (scrutinee:term)
    (then_:term)
    (else_:term)
    (ty:term)
    (u_ty:universe_spec)
    (hyp:var { None? (lookup_bvar g hyp) /\
               ~(hyp `Set.mem` (freevars_spec (denote_term then_) `Set.union` freevars_spec (denote_term else_))) })
    (eff:tot_or_ghost)
    (ty_eff:tot_or_ghost)
    (ts : typing g (denote_term scrutinee) (eff, bool_ty))
    (tt : typing (extend_env g hyp (eq2 u_zero bool_ty_tm scrutinee true_bool_tm)) (denote_term then_) (eff, denote_term ty))
    (te : typing (extend_env g hyp (eq2 u_zero bool_ty_tm scrutinee false_bool_tm)) (denote_term else_) (eff, denote_term ty))
    (tr : typing g (denote_term ty) (ty_eff, tm_type u_ty))
: typing g (denote_term (mk_if scrutinee then_ else_)) (eff, denote_term ty)
= let brt = (Ps_Constant C_True, denote_term then_) in
  let bre = (Ps_Constant C_False, denote_term else_) in
  bindings_ok_pat_constant g C_True;
  bindings_ok_pat_constant g C_False;
  denote_pack_fvar bool_fv; // denote_term bool_ty_tm == bool_ty
  denote_pack_match scrutinee None [(Pat_Constant C_True, then_); (Pat_Constant C_False, else_)];
  let brty () : branches_typing g u_zero bool_ty_tm scrutinee (eff, denote_term ty) [brt; bre] [[]; []] =
    BT_S brt []
         (BO (Pat_Constant C_True) [] hyp (denote_term then_) () tt)
         _ _ (
      BT_S bre []
           (BO (Pat_Constant C_False) [] hyp (denote_term else_) () te)
           _ _
        BT_Nil)
  in
  T_Match g u_zero bool_ty_tm scrutinee E_Total (T_FVar g bool_fv) eff ts [brt; bre] (eff, denote_term ty)
    [[]; []]
    (MC_Tok g (denote_term scrutinee) (denote_term bool_ty_tm) _ _ (if_complete_match g (denote_term scrutinee)))
    (brty ())

let typing_to_token (#g:env) (#e:term_spec) (#c:comp_spec_typ) (_ : typing g e c) = magic()
