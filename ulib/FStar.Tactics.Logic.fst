module FStar.Tactics.Logic

open FStar.Tactics.Effect
open FStar.Tactics.Builtins
open FStar.Tactics.Derived
open FStar.Reflection
open FStar.Reflection.Types

private val revert_squash : (a:Type) -> (b : (a -> Type)) ->
                            (squash (forall (x:a). b x)) ->
                            x:a -> squash (b x)
let revert_squash a b s x = ()

let term_of_binder b = pack (Tv_Var b)
let apply_term t ts = List.Tot.fold_left (fun t1 t2 -> pack (Tv_App t1 (t2, Q_Explicit))) t ts
let apply_args t args = List.Tot.fold_left (fun t1 arg -> pack (Tv_App t1 arg)) t args

private
let build_named_revert_squash_type (s:string) : term =
  let a = fresh_binder (Some "a") (pack (Tv_Type ())) in
  let x = fresh_binder (Some s) (pack (Tv_Var a)) in
  let b = fresh_binder (Some "b") (pack (Tv_Arrow x (pack (Tv_Type ())))) in
  let result = pack (Tv_App (term_of_binder b) (term_of_binder x, Q_Explicit)) in
  let squash_app t = pack (Tv_App (pack (Tv_FVar (pack_fv squash_qn))) (t, Q_Explicit)) in
  let for_all = pack (Tv_FVar (pack_fv forall_qn)) in
  let forallfml =
  squash_app (apply_args for_all [term_of_binder a, Q_Implicit ; pack (Tv_Abs x result), Q_Explicit ])
  in
  let forall_binder = fresh_binder None forallfml in
  let arr0 = pack (Tv_Arrow x (squash_app result)) in
  pack (Tv_Arrow a (pack (Tv_Arrow b (pack (Tv_Arrow forall_binder arr0)))))

private
let id (a:Type) (x:a) : a = x

private
let named_revert_squash (s:string) : tactic term =
  id <-- quote_lid ["FStar";"Tactics";"Logic";"id"] ;
  t <-- quote_lid ["FStar";"Tactics";"Logic";"revert_squash"] ;
  return (apply_term id [build_named_revert_squash_type s ; t])

let l_revert : tactic unit =
    g <-- cur_env ;
    let bs = binders_of_env g in
    let i = List.Tot.length bs - 1 in
    b <-- if i >= 0 then return (List.Tot.index bs i) else fail "Nothing in context" ;
    revert;;
    apply (named_revert_squash (inspect_bv b))

let rec l_revert_all (bs:binders) : tactic unit =
    match bs with
    | [] -> return ()
    | _::tl -> l_revert;;
               l_revert_all tl

private val fa_intro_lem : (#a:Type) -> (#b : (a -> Type)) ->
                           (x:a -> squash (b x)) ->
                           squash (forall (x:a). b x)
let fa_intro_lem #a #b f = FStar.Squash.(return_squash (squash_double_arrow (return_squash f)))

let forall_intro : tactic binder =
    g <-- cur_goal;
    match term_as_formula g with
    | Forall b _ -> (
        apply (quote_lid ["FStar";"Tactics";"Logic";"fa_intro_lem"]);;
        intro_named (Some (inspect_bv b)))
    | _ ->
        fail "not a forall"

let forall_intros : tactic binders = repeat1 forall_intro

private val split_lem : (#a:Type) -> (#b:Type) ->
                        squash a -> squash b -> squash (a /\ b)
let split_lem #a #b sa sb = ()

let split : tactic unit =
    g <-- cur_goal;
    match term_as_formula g with
    | And _ _ ->
        apply (quote_lid ["FStar";"Tactics";"Logic";"split_lem"])
    | _ ->
        fail "not a conjunction"

private val revert_squash_impl (#a #b:Type) : (squash (a ==> b)) -> a -> squash b
let revert_squash_impl #a #b s x = ()

let implies_revert : tactic unit =
  revert ;;
  apply (quote_lid ["FStar" ; "Tactics" ; "Logic" ; "revert_squash_impl"])

private val imp_intro_lem : (#a:Type) -> (#b : Type) ->
                            (a -> squash b) ->
                            squash (a ==> b)
let imp_intro_lem #a #b f = FStar.Squash.(return_squash (squash_double_arrow (return_squash f)))

let implies_intro : tactic binder =
    g <-- cur_goal;
    match term_as_formula g with
    | Implies _ _ -> (
        apply (quote_lid ["FStar";"Tactics";"Logic";"imp_intro_lem"]);;
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
        clear;; // G |- P[e/x]
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
            clear;;
            visit (unfold_definition_and_simplify_eq' tm)
        end) ()

let unfold_definition_and_simplify_eq (tm:tactic term) : tactic unit =
    tm' <-- tm;
    unfold_definition_and_simplify_eq' tm'

private val vbind : (#p:Type) -> (#q:Type) -> squash p -> (p -> squash q) -> squash q
let vbind #p #q sq f = FStar.Squash.bind_squash sq f

let unsquash (t:term) : tactic term =
    v <-- quote_lid ["FStar";"Tactics";"Logic";"vbind"];
    apply (return (mk_e_app v [t]));;
    b <-- intro;
    return (pack (Tv_Var b))

let squash_intro : tactic unit =
    apply (quote_lid ["FStar";"Squash";"return_squash"])

private val or_ind : (#p:Type) -> (#q:Type) -> (#phi:Type) ->
                     (p \/ q) ->
                     (squash (p ==> phi)) ->
                     (squash (q ==> phi)) ->
                     squash phi
let or_ind #p #q #phi o l r = ()

let cases_or (o:term) : tactic unit =
    oi <-- quote_lid ["FStar";"Tactics";"Logic";"or_ind"];
    apply (return (mk_e_app oi [o]))

private val bool_ind : (b:bool) -> (phi:Type) -> (squash (b == true  ==> phi)) ->
                                                 (squash (b == false ==> phi)) ->
                                                 squash phi
let bool_ind b phi l r = ()

let cases_bool (b:term) : tactic unit =
    bi <-- quote_lid ["FStar";"Tactics";"Logic";"bool_ind"];
    seq (apply (return (mk_e_app bi [b])))
        (trytac (b <-- implies_intro; rewrite b;; clear);; idtac)

private val or_intro_1 : (#p:Type) -> (#q:Type) -> squash p -> squash (p \/ q)
let or_intro_1 #p #q _ = ()

private val or_intro_2 : (#p:Type) -> (#q:Type) -> squash q -> squash (p \/ q)
let or_intro_2 #p #q _ = ()

let left : tactic unit =
    apply (quote_lid ["FStar";"Tactics";"Logic";"or_intro_1"])

let right : tactic unit =
    apply (quote_lid ["FStar";"Tactics";"Logic";"or_intro_2"])

private val __and_elim : (#p:Type) -> (#q:Type) -> (#phi:Type) ->
                              (p /\ q) ->
                              squash (p ==> q ==> phi) ->
                              squash phi
let __and_elim #p #q #phi p_and_q f = ()

let and_elim (t : term) : tactic unit =
    ae <-- quote_lid ["FStar";"Tactics";"Logic";"__and_elim"];
    apply (return (mk_e_app ae [t]))
