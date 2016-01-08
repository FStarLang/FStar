(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Constructive.fst FStar.Classical.fst FStar.FunctionalExtensionality.fst ../metatheory/stlc_strong_db_parsubst.fst ../metatheory/stlc_cbv_db_parsubst.fst
 --*)
module Bug194

open FStar.Constructive
open StlcStrongDbParSubst
open StlcCbvDbParSubst

type step : exp -> exp -> Type =
  | SBeta : t:typ ->
            e1:exp ->
            e2:exp{is_value e2} ->
            step (EApp (ELam t e1) e2) (subst (sub_beta e2) e1)
  | SApp1 : #e1:exp ->
            e2:exp ->
            #e1':exp ->
            step e1 e1' ->
            step (EApp e1 e2) (EApp e1' e2)
  | SApp2 : e1:exp{is_value e1} ->
            #e2:exp ->
            #e2':exp ->
            step e2 e2' ->
            step (EApp e1 e2) (EApp e1 e2')

kind Relation (a:Type) = a -> a -> Type
type multi (a:Type) (r:Relation a) : a -> a -> Type =
| Multi_refl : x:a -> multi a r x x
| Multi_step : x:a -> y:a -> z:a -> r x y -> multi a r y z -> multi a r x z
type steps : exp -> exp -> Type = fun x y -> multi exp step x y
type halts (e:exp) : Type = cexists (fun e' -> u:(steps e e'){is_value e'})

(* this has negative occurrence *)
(* type red : typ -> exp -> Type = *)
(* | R_arrow : t1:typ -> t2:typ -> #e:exp -> *)
(*             typing empty e (TArr t1 t2) -> *)
(*             halts e -> *)
(*             (e':exp -> red t1 e' -> Tot (red t2 (EApp e e'))) -> *)
(*             red (TArr t1 t2) e *)

assume type red : typ -> exp -> Type

assume val red_halts : #t:typ -> #e:exp -> red t e -> Tot (halts e)
(* let red_halts t e h = match h with R_arrow _ _ _ hh _ -> hh *)
                                                           
assume val red_typable_empty : #t:typ -> #e:exp -> red t e -> Tot (typing empty e t)
(* let red_typable_empty t e h = match h with | R_arrow k1 k2 ht k3 k4 -> ht *)

type ered (t : typ) (e : exp) = e':exp -> step e e' -> Tot (red t e')

assume val red_exp_closed : #t:typ -> e:exp{not (is_value e)} ->
                     typing empty e t ->
                     ered t e ->
                     Tot (red t e)

val red_beta : t1:typ -> t2:typ -> x:var -> e:exp ->
               typing (extend_gen x t1 empty) e t2 ->
               (e' : exp -> red t1 e' -> Tot (red t2 (subst (sub_beta_gen x e') e))) ->
               e' : exp -> red t1 e' -> Tot (red t2 (EApp (ELam t1 e) e'))
let red_beta t1 t2 x e ty_t2 f e' red_e' =
  let ExIntro v steps_ev = red_halts red_e' in
  let rec induction (ter: steps e v) (* : Tot (red t2 (EApp (ELam t1 e) e'))*) =
    (match ter with
     | Multi_step same_e' e'' same_v step_e'e'' mult_e''v -> 
	red_exp_closed (EApp (ELam t1 e) e') (TyApp (TyLam t1 ty_t2) (red_typable_empty red_e')) (fun e' (step_ee': step e e') -> magic())
     | Multi_refl same_e' -> magic()
    )
  in
  induction steps_ev
