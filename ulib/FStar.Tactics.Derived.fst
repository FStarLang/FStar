module FStar.Tactics.Derived

open FStar.Reflection
open FStar.Tactics.Effect
open FStar.Tactics.Builtins

(* Monadic helpers, could be made generic for do notation? *)

val liftM1' : ('a -> tactic 'b) -> (tactic 'a -> tactic 'b)
let liftM1' f ma = a <-- ma;
                   f a

val liftM1 : ('a -> 'b) -> (tactic 'a -> tactic 'b)
let liftM1 f = liftM1' (fun x -> return (f x))

val liftM2' : ('a -> 'b -> tactic 'c) -> (tactic 'a -> tactic 'b -> tactic 'c)
let liftM2' f ma mb = a <-- ma;
                      b <-- mb;
                      f a b

val liftM2 : ('a -> 'b -> 'c) -> (tactic 'a -> tactic 'b -> tactic 'c)
let liftM2 f = liftM2' (fun x y -> return (f x y))

let idtac : tactic unit = return ()

(* Fix combinator, so we need not expose the TAC effect (c.f. 1017) *)
val fix : #a:Type -> (tactic a -> tactic a) -> unit -> Tac a
let rec fix #a ff (u:unit) = ff (fix #a ff) ()

val fix1 : #a:Type -> #b:Type -> ((b -> tactic a) -> (b -> tactic a)) -> b -> unit -> Tac a
let rec fix1 #a #b ff x (u:unit) = ff (fix1 #a #b ff) x ()

(* working around #885 *)
let __fail (a:Type) (msg:string) : __tac a = fun s0 -> Failed #a msg s0
let fail (#a:Type) (msg:string) : tactic a = fun () -> TAC?.reflect (__fail a msg)

// Never fails
let trytac (#a:Type) (t : tactic a) : tactic (option a) = fun () ->
    TAC?.reflect (fun ps -> match reify_tactic t ps with
                            | Success a ps' -> Success (Some a) ps'
                            | Failed _ _ -> Success None ps)

let or_else (#a:Type) (t1 : tactic a) (t2 : tactic a) : tactic a =
    r <-- trytac t1;
    (match r with
    | Some x -> return x
    | None -> t2)

let rec repeat (#a:Type) (t : tactic a) () : Tac (list a) =
    (r <-- trytac t;
    match r with
    | None -> return []
    | Some x -> (xs <-- repeat t;
                 return (x::xs))) ()

let rec repeatseq (#a:Type) (t : tactic a) () : Tac unit =
    (trytac (seq (t;; return ()) (repeatseq t));; return ()) ()

let simpl : tactic unit = norm [Simpl; Primops]
let whnf  : tactic unit = norm [WHNF; Primops]

let rec revert_all (bs:binders) : tactic unit =
    match bs with
    | [] -> return ()
    | _::tl -> revert;;
               revert_all tl

private val revert_squash : (#a:Type) -> (#b : (a -> Type)) ->
                            (squash (forall (x:a). b x)) ->
                            PURE (x:a -> squash (b x)) (fun p -> forall x. p x)
let revert_squash #a #b s = admit()

let l_revert : tactic unit =
    revert;;
    apply (quote revert_squash)

let rec l_revert_all (bs:binders) : tactic unit =
    match bs with
    | [] -> return ()
    | _::tl -> l_revert;;
               l_revert_all tl

let cur_goal : tactic goal =
  ps <-- get;
  let goals, _ = ps in
  match goals with
  | [] -> fail "No more goals"
  | hd::_ -> return hd

let destruct_equality_implication (t:term) : tactic (option (formula * term)) =
    match term_as_formula t with
    | Implies lhs rhs ->
        let lhs = term_as_formula' lhs in
        begin match lhs with
        | Comp Eq _ _ _ -> return (Some (lhs, rhs))
        | _ -> return None
        end
    | _ -> return None

private val fa_intro_lem : (#a:Type) -> (#b : (a -> Type)) ->
                           (x:a -> squash (b x)) ->
                           squash (forall (x:a). b x)
let fa_intro_lem #a #b f = admit()

let forall_intro : tactic binder =
    egw <-- cur_goal;
    let (_, g), _ = egw in
    match term_as_formula g with
    | Forall _ _ -> (
        apply (quote fa_intro_lem);;
        intro)
    | _ ->
        fail "not a forall"

let forall_intros : tactic binders = repeat forall_intro

private val split_lem : (#a:Type) -> (#b:Type) ->
                        squash a -> squash b -> squash (a /\ b)
let split_lem #a #b sa sb = ()

let split : tactic unit =
    egw <-- cur_goal;
    let (_, g), _ = egw in
    match term_as_formula g with
    | And _ _ ->
        apply (quote split_lem)
    | _ ->
        fail "not a conjunction"

private val imp_intro_lem : (#a:Type) -> (#b : Type) ->
                            (a -> squash b) ->
                            squash (a ==> b)
let imp_intro_lem #a #b f = admit()

let implies_intro : tactic binder =
    egw <-- cur_goal;
    let (_, g), _ = egw in
    match term_as_formula g with
    | Implies _ _ -> (
        apply (quote imp_intro_lem);;
        b <-- intro;
        return b
        )
    | _ ->
        fail "not an implication"

let implies_intros : tactic binders = repeat implies_intro

let rec visit (callback:tactic unit) () : Tac unit =
    focus (or_else callback
                   (dump "IN VISIT";;
                    eg <-- cur_goal;
                    let (e, g), _ = eg in
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
                        or_else trivial (smt ())
                   )
          ) ()

// Need to thunk it like to this for proper handling of non-termination.
// (not doing it would still work, because of issue #1017, but should not)
let rec simplify_eq_implication (u:unit) : Tac unit = (
    g <-- cur_goal;
    let (context, goal_t), _ = g in // G |- x=e ==> P
    r <-- destruct_equality_implication goal_t;
    match r with
    | None ->
        fail "Not an equality implication"
    | Some (_, rhs) ->
        eq_h <-- implies_intro; // G, eq_h:x=e |- P
        rewrite eq_h;; // G, eq_h:x=e |- P[e/x]
        clear;; // G |- P[e/x]
        visit simplify_eq_implication) ()

let rec try_rewrite_equality (x:term) (bs:binders) : tactic unit =
    match bs with
    | [] -> return ()
    | x_t::bs ->
        begin match term_as_formula' (type_of_binder x_t) with
        | Comp Eq _ y _ ->
            if term_eq x y
            then rewrite x_t
            else try_rewrite_equality x bs
        | _ ->
            try_rewrite_equality x bs
        end

let rec rewrite_all_context_equalities (bs:binders) : tactic unit =
    match bs with
    | [] ->
        return ()
    | x_t::bs ->
        begin (match term_as_formula' (type_of_binder x_t) with
        | Comp Eq _ lhs _ ->
            begin match inspect lhs with
            | Tv_Var _ -> rewrite x_t
            | _ -> idtac
            end
        | _ -> idtac);;
        rewrite_all_context_equalities bs
        end

let rewrite_eqs_from_context : tactic unit =
    g <-- cur_goal;
    let (context, _), _ = g in
    rewrite_all_context_equalities (binders_of_env context)

let rewrite_equality (x:tactic term) : tactic unit =
    g <-- cur_goal;
    let (context, _), _ = g in
    t <-- x;
    try_rewrite_equality t (binders_of_env context)

let rewrite_all_equalities : tactic unit =
    visit (simplify_eq_implication)

// See comment on `simplify_eq_implication`
let rec unfold_definition_and_simplify_eq' (tm:term) (u:unit) : Tac unit = (
    g <-- cur_goal;
    let (_, goal_t), _ = g in
    match term_as_formula goal_t with
    | App hd arg ->
        if term_eq hd tm
        then trivial
        else return ()
    | _ -> begin
        r <-- destruct_equality_implication goal_t;
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

private let bool_ext (b:bool) : unit -> Lemma (b == true \/ b == false) = fun () -> ()

(* let cases_bool (b:bool) : tactic unit = *)
(*     lemt <-- quote (bool_ext b); *)
(*     p <-- get_lemma lemt; *)
(*     p <-- unsquash p; *)
(*     seq (cases p;; return ()) rewrite_eqs_from_context // TODO: overkill, we want to only rewrite each case *)

let unfold_point (t:term) : tactic unit =
    eg <-- cur_goal;
    let (e, g), _ = eg in
    let f = term_as_formula g in
    match f with
    | Comp Eq _ l r ->
        if term_eq l t
        then (norm [Delta];; trefl)
        else trefl
    | _ ->
        fail "impossible"

let unfold_def (t:term) : tactic unit =
    pointwise (unfold_point t)
