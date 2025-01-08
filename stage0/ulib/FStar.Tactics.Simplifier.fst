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
module FStar.Tactics.Simplifier

open FStar.Tactics.V2
open FStar.Reflection.V2.Formula
open FStar.Reflection.Const

(* A correct-by-construction logical simplifier
 *
 * No calling `norm [simpl]`, that's cheating!
 *)

val lem_iff_refl : #a:Type -> Lemma (a <==> a)
let lem_iff_refl #a = ()

val lem_iff_trans : #a:Type -> #b:Type -> #c:Type -> squash (a <==> b) -> squash (b <==> c)
                                                            -> Lemma (a <==> c)
let lem_iff_trans #a #b #c _ _ = ()

let tiff () : Tac unit =
    apply_lemma (`lem_iff_refl)

let step () : Tac unit =
    apply_lemma (`lem_iff_trans)

val lem_true_and_p : #p:Type -> Lemma ((True /\ p) <==> p)
let lem_true_and_p #p = ()

val lem_p_and_true : #p:Type -> Lemma ((p /\ True) <==> p)
let lem_p_and_true #p = ()

val lem_false_and_p : #p:Type -> Lemma ((False /\ p) <==> False)
let lem_false_and_p #p = ()

val lem_p_and_false : #p:Type -> Lemma ((p /\ False) <==> False)
let lem_p_and_false #p = ()

val lem_true_or_p : #p:Type -> Lemma ((True \/ p) <==> True)
let lem_true_or_p #p = ()

val lem_p_or_true : #p:Type -> Lemma ((p \/ True) <==> True)
let lem_p_or_true #p = ()

val lem_false_or_p : #p:Type -> Lemma ((False \/ p) <==> p)
let lem_false_or_p #p = ()

val lem_p_or_false : #p:Type -> Lemma ((p \/ False) <==> p)
let lem_p_or_false #p = ()

val lem_true_imp_p : #p:Type -> Lemma ((True ==> p) <==> p)
let lem_true_imp_p #p = ()

val lem_p_imp_true : #p:Type -> Lemma ((p ==> True) <==> True)
let lem_p_imp_true #p = ()

val lem_false_imp_p : #p:Type -> Lemma ((False ==> p) <==> True)
let lem_false_imp_p #p = ()

val lem_fa_true : #a:Type -> Lemma ((forall (x:a). True) <==> True)
let lem_fa_true #a = ()

val lem_fa_false : #a:Type -> (x:a) -> Lemma ((forall (x:a). False) <==> False)
let lem_fa_false #a x = ()

val lem_ex_false : #a:Type -> Lemma ((exists (x:a). False) <==> False)
let lem_ex_false #a = ()

val lem_ex_true : #a:Type -> (x:a) -> Lemma ((exists (x:a). True) <==> True)
let lem_ex_true #a x = ()

val lem_neg_false : unit -> Lemma (~False <==> True)
let lem_neg_false () = ()

val lem_neg_true : unit -> Lemma (~True <==> False)
let lem_neg_true () = ()

val lem_true_iff_p : #p:Type -> Lemma ((True <==> p) <==> p)
let lem_true_iff_p #p = ()

val lem_false_iff_p : #p:Type -> Lemma ((False <==> p) <==> ~p)
let lem_false_iff_p #p = ()

val lem_p_iff_true : #p:Type -> Lemma ((p <==> True) <==> p)
let lem_p_iff_true #p = ()

val lem_p_iff_false : #p:Type -> Lemma ((p <==> False) <==> ~p)
let lem_p_iff_false #p = ()

val and_cong (#p #q #p' #q' : Type) : squash (p <==> p') ->
                                      squash (q <==> q') ->
                                      Lemma ((p /\ q) <==> (p' /\ q'))
let and_cong #p #q #p' #q' _ _ = ()

val or_cong (#p #q #p' #q' : Type) : squash (p <==> p') ->
                                     squash (q <==> q') ->
                                     Lemma ((p \/ q) <==> (p' \/ q'))
let or_cong #p #q #p' #q' _ _ = ()

val imp_cong (#p #q #p' #q' : Type) : squash (p <==> p') ->
                                      squash (q <==> q') ->
                                      Lemma ((p ==> q) <==> (p' ==> q'))
let imp_cong #p #q #p' #q' _ _ = ()

val fa_cong (#a : Type) (#p #q : a -> Type) :
    (x:a -> squash (p x <==> q x)) ->
    Lemma ((forall (x:a). p x) <==> (forall (x:a). q x))
let fa_cong #a #p #q f =
  assert ((forall (x:a). p x) <==> (forall (x:a). q x)) by (
    split();
    let do1 () : Tac unit =
      let _ = l_intros () in
      let t = quote f in
      let x = nth_var (-1) in
      let bb = pose (mk_e_app t [binding_to_term x]) in
      ()
    in
    iseq [do1; do1]
  )

val ex_cong (#a : Type) (#p #q : a -> Type) :
    (x:a -> squash (p x <==> q x)) ->
    Lemma ((exists (x:a). p x) <==> (exists (x:a). q x))
let ex_cong #a #p #q f =
  assert ((exists (x:a). p x) <==> (exists (x:a). q x)) by (assume_safe (fun () ->
    split();
    let do1 () : Tac unit =
      let [ex] = l_intros () in
      let (b, pf) = elim_exists (binding_to_term ex) in
      let t = quote f in
      let bb = pose (mk_e_app t [binding_to_term b]) in
      ()
    in
    iseq [do1; do1]
  ))

val neg_cong (#p #q:Type) : squash (p <==> q) -> Lemma (~p <==> ~q)
let neg_cong #p #q _ = ()

val iff_cong (#p #p' #q #q' : Type) : squash (p <==> p') -> squash (q <==> q') -> Lemma ((p <==> q) <==> (p' <==> q'))
let iff_cong #p #p' #q #q' _ _ = ()

// Absolutely hideous, do something about normalization
val is_true : term -> Tac bool
let is_true t =
    begin match term_as_formula' t with
    | True_ -> true
    | _ -> begin match inspect t with
           | Tv_App l r ->
            begin match inspect l with
            | Tv_Abs b t ->
                begin match term_as_formula' t with
                | True_ -> true
                | _ -> false
                end
            | _ -> false
            end
           | _ -> false
           end
    end

val is_false : term -> Tac bool
let is_false t =
    begin match term_as_formula' t with
    | False_ -> true
    | _ -> begin match inspect t with
           | Tv_App l r ->
            begin match inspect l with
            | Tv_Abs b t ->
                begin match term_as_formula' t with
                | False_ -> true
                | _ -> false
                end
            | _ -> false
            end
           | _ -> false
           end
    end

val inhabit : unit -> Tac unit
let inhabit () =
    let t = cur_goal () in
    match inspect t with
    | Tv_FVar fv ->
        let qn = inspect_fv fv in
             if qn = int_lid  then exact (`42)
        else if qn = bool_lid then exact (`true)
        else if qn = unit_lid then exact (`())
        else fail ""
    | _ -> fail ""

val simplify_point : unit -> Tac unit
val recurse : unit -> Tac unit

let rec simplify_point () =
    recurse ();
    norm [];
    let g = cur_goal () in
    let f = term_as_formula g in
    match f with
    | Iff l r ->
        begin match term_as_formula' l with
        | And p q ->
                 if is_true p  then apply_lemma (`lem_true_and_p)
            else if is_true q  then apply_lemma (`lem_p_and_true)
            else if is_false p then apply_lemma (`lem_false_and_p)
            else if is_false q then apply_lemma (`lem_p_and_false)
            else tiff ()

        | Or p q ->
                 if is_true p  then apply_lemma (`lem_true_or_p)
            else if is_true q  then apply_lemma (`lem_p_or_true)
            else if is_false p then apply_lemma (`lem_false_or_p)
            else if is_false q then apply_lemma (`lem_p_or_false)
            else tiff ()

        | Implies p q ->
                 if is_true p  then apply_lemma (`lem_true_imp_p)
            else if is_true q  then apply_lemma (`lem_p_imp_true)
            else if is_false p then apply_lemma (`lem_false_imp_p)
            else tiff ()

        | Forall _b _sort p ->
                 if is_true p  then apply_lemma (`lem_fa_true)
            else if is_false p then or_else (fun () -> apply_lemma (`lem_fa_false); inhabit ()) tiff
            else tiff ()

        | Exists _b _sort p ->
                 if is_false p then apply_lemma (`lem_ex_false)
            else if is_true  p then or_else (fun () -> apply_lemma (`lem_ex_true); inhabit ()) tiff
            else tiff ()

        | Not p ->
                 if is_true p  then apply_lemma (`lem_neg_true)
            else if is_false p then apply_lemma (`lem_neg_false)
            else tiff ()

        | Iff p q ->
            // After applying the lemma, we might still have more simpl to do,
            // so add an intermediate step.
            step ();
                 if is_true p  then apply_lemma (`lem_true_iff_p)
            else if is_true q  then apply_lemma (`lem_p_iff_true)
            else if is_false p then apply_lemma (`lem_false_iff_p)
            else if is_false q then apply_lemma (`lem_p_iff_false)
            else tiff ();
            simplify_point ()

        | _ -> tiff ()
        end
    | _ -> fail "simplify_point: failed precondition: goal should be `g <==> ?u`"

and recurse () : Tac unit =
    step ();
    norm [];
    let g = cur_goal () in
    let f = term_as_formula g in
    match f with
    | Iff l r ->
        begin match term_as_formula' l with
        | And _ _ ->
            seq (fun () -> apply_lemma (`and_cong)) simplify_point

        | Or _ _ ->
            seq (fun () -> apply_lemma (`or_cong)) simplify_point

        | Implies _ _ ->
            seq (fun () -> apply_lemma (`imp_cong)) simplify_point

        | Forall _ _ _ ->
            apply_lemma (`fa_cong);
            let _ = intro () in
            simplify_point ()

        | Exists _ _ _ ->
            apply_lemma (`ex_cong);
            let _ = intro () in
            simplify_point ()

        | Not _ ->
            apply_lemma (`neg_cong);
            simplify_point ()

        | Iff _ _ ->
            seq (fun () -> apply_lemma (`iff_cong)) simplify_point

        | _ -> tiff ()
        end
    | _ -> fail "recurse: failed precondition: goal should be `g <==> ?u`"

val equiv : #p:Type -> #q:Type -> squash (p <==> q) -> squash q -> Lemma p
let equiv #p #q _ _ = ()

let simplify () : Tac unit =
    apply_lemma (`equiv);
    simplify_point ()
