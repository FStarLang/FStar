module FStar.Tactics.Derived

open FStar.Reflection
open FStar.Reflection.Types
open FStar.Tactics.Result
open FStar.Tactics.Effect
open FStar.Tactics.Builtins

let fresh_uvar o =
    e <-- cur_env;
    uvar_env e o

let quote_lid (ns:name) : tactic term =
    let t = pack (Tv_FVar (pack_fv ns)) in
    return t

let norm_term (s : list norm_step) (t : term) : tactic term =
    e <-- cur_env;
    norm_term_env e s t

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

val mapM : ('a -> tactic 'b) -> list 'a -> tactic (list 'b)
let rec mapM f l = match l with
               | [] -> return []
               | x::xs -> (y <-- f x;
                           ys <-- mapM f xs;
                           return (y::ys))

let idtac : tactic unit = return ()

let guard (b : bool) : tactic unit =
    if b
    then return ()
    else fail "guard failed"

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

let repeat1 (#a:Type) (t : tactic a) : tactic (list a) =
    x <-- t;
    xs <-- repeat t;
    return (x::xs)

let rec repeatseq (#a:Type) (t : tactic a) () : Tac unit =
    (trytac (seq (t;; return ()) (repeatseq t));; return ()) ()

let simpl : tactic unit = norm [simplify; primops]
let whnf  : tactic unit = norm [weak; hnf; primops]

let intros : tactic (list binder) = repeat intro

private val __cut : (a:Type) -> (b:Type) -> (a -> b) -> a -> b
private let __cut a b f x = f x

let tcut (t:term) : tactic binder =
    qq <-- quote_lid ["FStar";"Tactics";"Derived";"__cut"];
    let tt = pack (Tv_App qq (t, Q_Explicit)) in
    apply (return tt);;
    intro

let rec revert_all (bs:binders) : tactic unit =
    match bs with
    | [] -> return ()
    | _::tl -> revert;;
               revert_all tl

let assumption : tactic unit =
    e <-- cur_env;
    let rec aux (bs : binders) =
        match bs with
        | [] -> fail "no assumption matches goal"
        | b::bs ->
            let t = pack (Tv_Var b) in
            or_else (exact (return t)) (aux bs)
    in
    aux (binders_of_env e)

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
        begin match term_as_formula (type_of_binder x_t) with
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
        begin (match term_as_formula (type_of_binder x_t) with
        | Comp Eq _ lhs _ ->
            begin match inspect lhs with
            | Tv_Var _ -> rewrite x_t
            | _ -> idtac
            end
        | _ -> idtac);;
        rewrite_all_context_equalities bs
        end

let rewrite_eqs_from_context : tactic unit =
    e <-- cur_env;
    rewrite_all_context_equalities (binders_of_env e)

let rewrite_equality (x:tactic term) : tactic unit =
    e <-- cur_env;
    t <-- x;
    try_rewrite_equality t (binders_of_env e)

let unfold_point (t:term) : tactic unit =
    e <-- cur_env;
    g <-- cur_goal;
    let f = term_as_formula g in
    match f with
    | Comp Eq _ l r ->
        if term_eq l t
        then (norm [delta];; trefl)
        else trefl
    | _ ->
        fail "impossible"

let unfold_def (t:term) : tactic unit =
    pointwise (unfold_point t)

let grewrite' (t1 t2 eq : term) : tactic unit =
    g <-- cur_goal;
    match term_as_formula g with
    | Comp Eq _ l _ ->
        if term_eq l t1
        then exact (return eq)
        else trefl
    | _ ->
        fail "impossible"

let mk_squash (t : term) : term =
    let sq : term = pack (Tv_FVar (pack_fv squash_qn)) in
    mk_e_app sq [t]

let mk_sq_eq (t1 t2 : term) : term =
    let eq : term = pack (Tv_FVar (pack_fv eq2_qn)) in
    mk_squash (mk_e_app eq [t1; t2])

let grewrite (t1 t2 : term) : tactic unit =
    e <-- tcut (mk_sq_eq t1 t2);
    pointwise (grewrite' t1 t2 (pack (Tv_Var e)))

let focus (f : tactic 'a) : tactic 'a =
    res <-- divide 1 f idtac;
    return (fst res)

let rec iseq (ts : list (tactic unit)) : tactic unit =
    match ts with
    | t::ts ->
        divide 1 t (iseq ts);;
        return ()
    | [] -> return ()

private val __witness : (#a:Type) -> (x:a) -> (#p:(a -> Type)) -> squash (p x) -> squash (l_Exists p)
private let __witness #a x #p _ = ()

let witness (t : tactic term) : tactic unit =
    apply_raw (quote __witness);;
    exact t

private val push1 : (#p:Type) -> (#q:Type) ->
                        squash (p ==> q) ->
                        squash p ->
                        squash q
private let push1 #p #q f u = ()

(*
 * Some easier applying, which should prevent frustation
 * (or cause more when it doesn't do what you wanted to)
 *)
val apply_squash_or_lem : d:nat -> term -> Tot (tactic unit) (decreases d)
let rec apply_squash_or_lem d t =
    // This terminates because of the fuel, but we could just expand into Tac and diverge
    if d <= 0 then fail "mapply: out of fuel" else begin
    g <-- cur_goal;
    ty <-- tc t;
    let tys, c = collect_arr ty in
    match inspect_comp c with
    | C_Lemma pre post ->
       begin
       (* What I would really like to do here is unify `mk_squash post` and the goal,
        * but it didn't work on a first try, so just doing this for now *)
       r <-- trytac (apply_lemma (return t));
       match r with
       | Some _ -> return () // Success
       | None ->
           post <-- norm_term [] post;
           (* Is the lemma an implication? We can try to intro *)
           match term_as_formula' post with
           | Implies p q ->
               apply (quote push1);;
               apply_squash_or_lem (d-1) t

           | _ ->
               fail "mapply: can't apply (1)"
       end
    | C_Total rt ->
       begin match unsquash rt with
       (* If the function returns a squash, just apply it, since our goals are squashed *)
       | Some _ -> apply (return t)
       (* If not, we can try to introduce the squash ourselves first *)
       | None ->
           apply (quote FStar.Squash.return_squash);;
           apply (return t)
       end
    | _ -> fail "mapply: can't apply (2)"
    end

(* `m` is for `magic` *)
let mapply (t : tactic term) : tactic unit =
    tt <-- t;
    apply_squash_or_lem 10 tt

private
let dump_admit a : tactic unit =
  clear_top;; // gets rid of the unit binder
  dump1 "Admitting goal";;
  g <-- cur_goal;
  gg <-- unquote #Type g;
  exact (quote #gg (magic ()))

assume val admit_goal : #a:Type -> unit ->
    Pure a (requires (by_tactic (dump_admit a) a))
           (ensures (fun _ -> False))
