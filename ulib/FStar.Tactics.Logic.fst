module FStar.Tactics.Logic

open FStar.Tactics.Effect
open FStar.Tactics.Builtins
open FStar.Tactics.Derived
open FStar.Reflection
open FStar.Reflection.Types

private val revert_squash : (#a:Type) -> (#b : (a -> Type)) ->
                            (squash (forall (x:a). b x)) ->
                            x:a -> squash (b x)
let revert_squash #a #b s x = ()

let l_revert : tactic unit =
    revert;;
    apply (quote_lid ["FStar";"Tactics";"Logic";"revert_squash"])

let rec l_revert_all (bs:binders) : tactic unit =
    match bs with
    | [] -> return ()
    | _::tl -> l_revert;;
               l_revert_all tl

private val fa_intro_lem : (#a:Type) -> (#p : (a -> Type)) ->
                           (x:a -> squash (p x)) ->
                           Lemma (forall (x:a). p x)
let fa_intro_lem #a #p f = FStar.Classical.forall_intro #a #p (fun x -> f x <: Lemma (p x))

let forall_intro : tactic binder =
    g <-- cur_goal;
    match term_as_formula g with
    | Forall _ _ -> (
        apply_lemma (quote_lid ["FStar";"Tactics";"Logic";"fa_intro_lem"]);;
        intro)
    | _ ->
        fail "not a forall"

let forall_intros : tactic binders = repeat1 forall_intro

private val split_lem : (#a:Type) -> (#b:Type) ->
                        squash a -> squash b -> Lemma (a /\ b)
let split_lem #a #b sa sb = ()

let split : tactic unit =
    g <-- cur_goal;
    match term_as_formula g with
    | And _ _ ->
        apply_lemma (quote_lid ["FStar";"Tactics";"Logic";"split_lem"])
    | _ ->
        fail "not a conjunction"

private val imp_intro_lem : (#a:Type) -> (#b : Type) ->
                            (a -> squash b) ->
                            Lemma (a ==> b)
let imp_intro_lem #a #b f = FStar.Classical.impl_intro #a #b (fun x -> f x <: Lemma b)

let implies_intro : tactic binder =
    g <-- cur_goal;
    match term_as_formula g with
    | Implies _ _ -> (
        apply_lemma (quote_lid ["FStar";"Tactics";"Logic";"imp_intro_lem"]);;
        b <-- intro;
        return b
        )
    | _ ->
        fail "not an implication"

let implies_intros : tactic binders = repeat1 implies_intro

let rec visit (callback:tactic unit) () : Tac unit =
    focus (or_else callback
                   (g <-- cur_goal;
                    match term_as_formula g with
                    | Forall b phi ->
                        binders <-- forall_intros;
                        seq (visit callback) (
                            l_revert_all binders
                        )
                    | And p q ->
                        seq split (
                            visit callback;;
                            return ()
                        )
                    | Implies p q ->
                        implies_intro;;
                        seq (visit callback)
                            l_revert
                    | _ ->
                        or_else trivial smt
                   )
          ) ()

// Need to thunk it like to this for proper handling of non-termination.
// (not doing it would still work, because of issue #1017, but should not)
let rec simplify_eq_implication (u:unit) : Tac unit = (
    e <-- cur_env;
    g <-- cur_goal;
    r <-- destruct_equality_implication g;
    match r with
    | None ->
        fail "Not an equality implication"
    | Some (_, rhs) ->
        eq_h <-- implies_intro; // G, eq_h:x=e |- P
        rewrite eq_h;; // G, eq_h:x=e |- P[e/x]
        clear_top;; // G |- P[e/x]
        visit simplify_eq_implication) ()

let rewrite_all_equalities : tactic unit =
    visit (simplify_eq_implication)

// See comment on `simplify_eq_implication`
let rec unfold_definition_and_simplify_eq' (tm:term) (u:unit) : Tac unit = (
    g <-- cur_goal;
    match term_as_formula g with
    | App hd arg ->
        if term_eq hd tm
        then trivial
        else return ()
    | _ -> begin
        r <-- destruct_equality_implication g;
        match r with
        | None -> fail "Not an equality implication"
        | Some (_, rhs) ->
            eq_h <-- implies_intro;
            rewrite eq_h;;
            clear_top;;
            visit (unfold_definition_and_simplify_eq' tm)
        end) ()

let unfold_definition_and_simplify_eq (tm:tactic term) : tactic unit =
    tm' <-- tm;
    unfold_definition_and_simplify_eq' tm'

private val vbind : (#p:Type) -> (#q:Type) -> squash p -> (p -> squash q) -> Lemma q
let vbind #p #q sq f = FStar.Squash.bind_squash sq f

let unsquash (t:term) : tactic term =
    v <-- quote_lid ["FStar";"Tactics";"Logic";"vbind"];
    apply_lemma (return (mk_e_app v [t]));;
    b <-- intro;
    return (pack (Tv_Var b))

let squash_intro : tactic unit =
    apply (quote_lid ["FStar";"Squash";"return_squash"])

private val or_ind : (#p:Type) -> (#q:Type) -> (#phi:Type) ->
                     (p \/ q) ->
                     (squash (p ==> phi)) ->
                     (squash (q ==> phi)) ->
                     Lemma phi
let or_ind #p #q #phi o l r = ()

let cases_or (o:term) : tactic unit =
    oi <-- quote_lid ["FStar";"Tactics";"Logic";"or_ind"];
    apply_lemma (return (mk_e_app oi [o]))

private val bool_ind : (b:bool) -> (phi:Type) -> (squash (b == true  ==> phi)) ->
                                                 (squash (b == false ==> phi)) ->
                                                 Lemma phi
let bool_ind b phi l r = ()

let cases_bool (b:term) : tactic unit =
    bi <-- quote_lid ["FStar";"Tactics";"Logic";"bool_ind"];
    seq (apply_lemma (return (mk_e_app bi [b])))
        (trytac (b <-- implies_intro; rewrite b;; clear_top);; idtac)

private val or_intro_1 : (#p:Type) -> (#q:Type) -> squash p -> Lemma (p \/ q)
let or_intro_1 #p #q _ = ()

private val or_intro_2 : (#p:Type) -> (#q:Type) -> squash q -> Lemma (p \/ q)
let or_intro_2 #p #q _ = ()

let left : tactic unit =
    apply_lemma (quote_lid ["FStar";"Tactics";"Logic";"or_intro_1"])

let right : tactic unit =
    apply_lemma (quote_lid ["FStar";"Tactics";"Logic";"or_intro_2"])

private val __and_elim : (#p:Type) -> (#q:Type) -> (#phi:Type) ->
                              (p /\ q) ->
                              squash (p ==> q ==> phi) ->
                              Lemma phi
let __and_elim #p #q #phi p_and_q f = ()

let and_elim (t : term) : tactic unit =
    ae <-- quote_lid ["FStar";"Tactics";"Logic";"__and_elim"];
    apply_lemma (return (mk_e_app ae [t]))
