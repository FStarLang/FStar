module FStar.Tactics.Simplifier

open FStar.Tactics

(* A correct-by-construction logical simplifier
 *
 * No calling `norm [Simpl]`, that's cheating!
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
            else tiff

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

        | _ -> tiff
        end
    | _ -> fail "recurse: failed precondition: goal should be `g <==> ?u`"
) ()

val equiv : #p:Type -> #q:Type -> squash (p <==> q) -> squash q -> Lemma p
let equiv #p #q _ _ = ()

let simplify : tactic unit =
    apply_lemma (quote equiv);;
    simplify_point
