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

private val __cut : (#b:Type) -> (a:Type) -> (a -> b) -> a -> b
let __cut #b a f x = f x

let tcut (t:term) : tactic binder =
    qq <-- quote __cut;
    let tt = pack (Tv_App qq t) in
    apply (return tt);;
    intro

let rec revert_all (bs:binders) : tactic unit =
    match bs with
    | [] -> return ()
    | _::tl -> revert;;
               revert_all tl

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
