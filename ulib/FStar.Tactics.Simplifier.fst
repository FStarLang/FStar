module FStar.Tactics.Simplifier

open FStar.Tactics
open FStar.Reflection.Syntax
open FStar.Reflection.Formula

(* A correct-by-construction logical simplifier
 *
 * No calling `norm [simpl]`, that's cheating!
 *)

val lem_iff_refl : #a:Type -> Lemma (a <==> a)
let lem_iff_refl #a = ()

val lem_iff_trans : #a:Type -> #b:Type -> #c:Type -> squash (a <==> b) -> squash (b <==> c)
                                                            -> Lemma (a <==> c)
let lem_iff_trans #a #b #c _ _ = ()

let tiff : tactic unit =
    apply_lemma (quote lem_iff_refl)

let step : tactic unit =
    apply_lemma (quote lem_iff_trans)

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
let fa_cong #a #p #q f = admit() //fix, this should certainly be provable

val ex_cong (#a : Type) (#p #q : a -> Type) :
    (x:a -> squash (p x <==> q x)) ->
    Lemma ((exists (x:a). p x) <==> (exists (x:a). q x))
let ex_cong #a #p #q f = admit() //fix, this should certainly be provable

val neg_cong (#p #q:Type) : squash (p <==> q) -> Lemma (~p <==> ~q)
let neg_cong #p #q _ = ()

val iff_cong (#p #p' #q #q' : Type) : squash (p <==> p') -> squash (q <==> q') -> Lemma ((p <==> q) <==> (p' <==> q'))
let iff_cong #p #p' #q #q' _ _ = ()

// Absolutely hideous, do something about normalization
val is_true : term -> bool
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

val is_false : term -> bool
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

val inhabit : tactic unit
let inhabit =
    t <-- cur_goal;
    match inspect t with
    | Tv_FVar fv ->
        let qn = inspect_fv fv in
             if qn = int_lid then exact (quote 42)
        else if qn = bool_lid then exact (quote true)
        else if qn = unit_lid then exact (quote ())
        else fail ""
    | _ -> fail ""

val simplify_point : unit -> Tac unit
val recurse : unit -> Tac unit

let rec simplify_point = fun () -> (
    (* dump "1 ALIVE";; *)
    recurse;;
    norm [];;
    g <-- cur_goal;
    let f = term_as_formula g in
    (* print ("1 g = " ^ term_to_string g);; *)
    (* print ("1 f = " ^ formula_to_string f);; *)
    match f with
    | Iff l r ->
        begin match term_as_formula' l with
        | And p q ->
                 if is_true p then apply_lemma (quote lem_true_and_p)
            else if is_true q then apply_lemma (quote lem_p_and_true)
            else if is_false p then apply_lemma (quote lem_false_and_p)
            else if is_false q then apply_lemma (quote lem_p_and_false)
            else tiff

        | Or p q ->
                 if is_true p then apply_lemma (quote lem_true_or_p)
            else if is_true q then apply_lemma (quote lem_p_or_true)
            else if is_false p then apply_lemma (quote lem_false_or_p)
            else if is_false q then apply_lemma (quote lem_p_or_false)
            else tiff

        | Implies p q ->
                 if is_true p then apply_lemma (quote lem_true_imp_p)
            else if is_true q then apply_lemma (quote lem_p_imp_true)
            else if is_false p then apply_lemma (quote lem_false_imp_p)
            else tiff

        | Forall b p ->
                 if is_true p then apply_lemma (quote lem_fa_true)
            else if is_false p then or_else (apply_lemma (quote lem_fa_false);; inhabit) tiff
            else tiff

        | Exists b p ->
                 if is_false p then apply_lemma (quote lem_ex_false)
            else if is_true  p then or_else (apply_lemma (quote lem_ex_true);; inhabit) tiff
            else tiff

        | Not p ->
                 if is_true p then apply_lemma (quote lem_neg_true)
            else if is_false p then apply_lemma (quote lem_neg_false)
            else tiff

        | Iff p q ->
            // After applying the lemma, we might still have more simpl to do,
            // so add an intermediate step.
            step;;
                 if is_true p then apply_lemma (quote lem_true_iff_p)
            else if is_true q then apply_lemma (quote lem_p_iff_true)
            else if is_false p then apply_lemma (quote lem_false_iff_p)
            else if is_false q then apply_lemma (quote lem_p_iff_false)
            else tiff;;
            simplify_point

        | _ -> tiff
        end
    | _ -> fail "simplify_point: failed precondition: goal should be `g <==> ?u`"
) ()
and recurse : unit -> Tac unit = fun () -> (
    (* dump "2 ALIVE";; *)
    step;;
    norm [];;
    g <-- cur_goal;
    let f = term_as_formula g in
    (* print ("2 g = " ^ term_to_string g);; *)
    (* print ("2 f = " ^ formula_to_string f);; *)
    match f with
    | Iff l r ->
        begin match term_as_formula' l with
        | And _ _ ->
            seq (apply_lemma (quote and_cong)) simplify_point

        | Or _ _ ->
            seq (apply_lemma (quote or_cong)) simplify_point

        | Implies _ _ ->
            seq (apply_lemma (quote imp_cong)) simplify_point

        | Forall _ _ ->
            apply_lemma (quote fa_cong);;
            intro;;
            simplify_point

        | Exists _ _ ->
            apply_lemma (quote ex_cong);;
            intro;;
            simplify_point

        | Not _ ->
            apply_lemma (quote neg_cong);;
            simplify_point

        | Iff _ _ ->
            seq (apply_lemma (quote iff_cong)) simplify_point

        | _ -> tiff
        end
    | _ -> fail "recurse: failed precondition: goal should be `g <==> ?u`"
) ()

val equiv : #p:Type -> #q:Type -> squash (p <==> q) -> squash q -> Lemma p
let equiv #p #q _ _ = ()

let simplify : tactic unit =
    apply_lemma (quote equiv);;
    simplify_point
