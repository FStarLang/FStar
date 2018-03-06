module FStar.Tactics.Derived

open FStar.Reflection
open FStar.Reflection.Formula
open FStar.Tactics.Effect
open FStar.Tactics.Builtins

val map: ('a -> Tac 'b) -> list 'a -> Tac (list 'b)
let rec map f x = match x with
  | [] -> []
  | a::tl -> f a::map f tl

// TODO: maybe we can increase a counter on each call
let fresh_binder t = fresh_binder_named "x" t

(** [exact e] will solve a goal [Gamma |- w : t] if [e] has type exactly
[t] in [Gamma]. Also, [e] needs to unift with [w], but this will almost
always be the case since [w] is usually a uvar. *)
let exact (t : term) : Tac unit =
    t_exact false true t

(** Like [exact], but allows for the term [e] to have a type [t] only
under some guard [g], adding the guard as a goal. *)
let exact_guard (t : term) : Tac unit =
    t_exact false false t

let fresh_uvar o =
    let e = cur_env () in
    uvar_env e o

let norm_term (s : list norm_step) (t : term) : Tac term =
    let e = cur_env () in
    norm_term_env e s t

let idtac () : Tac unit = ()

let guard (b : bool) : Tac unit =
    if b
    then ()
    else fail "guard failed"

let or_else (#a:Type) (t1 : unit -> Tac a) (t2 : unit -> Tac a) : Tac a =
    match trytac t1 with
    | Some x -> x
    | None -> t2 ()

let rec repeat (#a:Type) (t : unit -> Tac a) : Tac (list a) =
    match trytac t with
    | None -> []
    | Some x -> let xs = repeat t in x::xs

let repeat1 (#a:Type) (t : unit -> Tac a) : Tac (list a) =
    let x = t () in
    x :: repeat t

let discard (tau : unit -> Tac 'a) : unit -> Tac unit =
    fun () -> let _ = tau () in ()

// TODO: do we want some value of this?
let rec repeatseq (#a:Type) (t : unit -> Tac a) : Tac unit =
    let _ = trytac (fun () -> (discard t) `seq` (discard (fun () -> repeatseq t))) in ()

private
let admit1' () : Tac unit =
    exact (`(magic ()))

let admit1 () : Tac unit =
    print "Warning: Admitting goal";
    admit1' ()

let admit_all () : Tac unit =
    print "Warning: Admitting all goals";
    let _ = repeat admit1' in
    ()

let skip_guard () : Tac unit =
    if is_guard ()
    then smt ()
    else fail ""

let guards_to_smt () : Tac unit =
    let _ = repeat skip_guard in
    ()

let simpl () : Tac unit = norm [simplify; primops]
let whnf  () : Tac unit = norm [weak; hnf; primops]

let intros () : Tac (list binder) = repeat intro

private val __cut : (a:Type) -> (b:Type) -> (a -> b) -> a -> b
private let __cut a b f x = f x

let tcut (t:term) : Tac binder =
    let tt = pack (Tv_App (`__cut) (t, Q_Explicit)) in
    apply tt;
    intro ()

let rec revert_all (bs:binders) : Tac unit =
    match bs with
    | [] -> ()
    | _::tl -> revert ();
               revert_all tl

// Cannot define this inside `assumption` due to #1091
private
let rec __assumption_aux (bs : binders) : Tac unit =
    match bs with
    | [] ->
        fail "no assumption matches goal"
    | b::bs ->
        let t = pack (Tv_Var b) in
        or_else (fun () -> exact t) (fun () -> __assumption_aux bs)

let assumption () : Tac unit =
    __assumption_aux (binders_of_env (cur_env ()))

let destruct_equality_implication (t:term) : Tac (option (formula * term)) =
    match term_as_formula t with
    | Implies lhs rhs ->
        let lhs = term_as_formula' lhs in
        begin match lhs with
        | Comp (Eq _) _ _ -> Some (lhs, rhs)
        | _ -> None
        end
    | _ -> None

let rec try_rewrite_equality (x:term) (bs:binders) : Tac unit =
    match bs with
    | [] -> ()
    | x_t::bs ->
        begin match term_as_formula (type_of_binder x_t) with
        | Comp (Eq _) y _ ->
            if term_eq x y
            then rewrite x_t
            else try_rewrite_equality x bs
        | _ ->
            try_rewrite_equality x bs
        end

let rec rewrite_all_context_equalities (bs:binders) : Tac unit =
    match bs with
    | [] -> ()
    | x_t::bs -> begin
        begin match term_as_formula (type_of_binder x_t) with
        | Comp (Eq _) lhs _ ->
            begin match inspect lhs with
            | Tv_Var _ -> rewrite x_t
            | _ -> ()
            end
        | _ -> () end;
        rewrite_all_context_equalities bs
    end

let rewrite_eqs_from_context () : Tac unit =
    rewrite_all_context_equalities (binders_of_env (cur_env ()))

let rewrite_equality (t:term) : Tac unit =
    try_rewrite_equality t (binders_of_env (cur_env ()))

let unfold_point (t:term) : Tac unit =
    let g : term = cur_goal () in
    match term_as_formula g with
    | Comp (Eq _) l r ->
        if term_eq l t
        then (norm [delta]; trefl ())
        else trefl ()
    | _ ->
        fail "impossible"

let unfold_def (t:term) : Tac unit =
    pointwise (fun () -> unfold_point t)

let grewrite' (t1 t2 eq : term) : Tac unit =
    let g = cur_goal () in
    match term_as_formula g with
    | Comp (Eq _) l _ ->
        if term_eq l t1
        then exact eq
        else trefl ()
    | _ ->
        fail "impossible"

let mk_squash (t : term) : term =
    let sq : term = pack (Tv_FVar (pack_fv squash_qn)) in
    mk_e_app sq [t]

let mk_sq_eq (t1 t2 : term) : term =
    let eq : term = pack (Tv_FVar (pack_fv eq2_qn)) in
    mk_squash (mk_e_app eq [t1; t2])

let grewrite (t1 t2 : term) : Tac unit =
    let e = tcut (mk_sq_eq t1 t2) in
    pointwise (fun () -> grewrite' t1 t2 (pack (Tv_Var e)))

let focus (f : unit -> Tac 'a) : Tac 'a =
    let res, _ = divide 1 f idtac in
    res

let rec iseq (ts : list (unit -> Tac unit)) : Tac unit =
    match ts with
    | t::ts -> let _ = divide 1 t (fun () -> iseq ts) in ()
    | []    -> ()

private val __witness : (#a:Type) -> (x:a) -> (#p:(a -> Type)) -> squash (p x) -> squash (l_Exists p)
private let __witness #a x #p _ = ()

let witness (t : term) : Tac unit =
    apply_raw (`__witness);
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
val apply_squash_or_lem : d:nat -> term -> Tac unit
let rec apply_squash_or_lem d t =
    // This terminates because of the fuel, but we could just expand into Tac and diverge
    if d <= 0 then fail "mapply: out of fuel" else begin
    let g = cur_goal () in
    let ty = tc t in
    let tys, c = collect_arr ty in
    match inspect_comp c with
    | C_Lemma pre post ->
       begin
       (* What I would really like to do here is unify `mk_squash post` and the goal,
        * but it didn't work on a first try, so just doing this for now *)
       match trytac (fun () -> apply_lemma t) with
       | Some _ -> () // Success
       | None ->
           let post = norm_term [] post in
           (* Is the lemma an implication? We can try to intro *)
           match term_as_formula' post with
           | Implies p q ->
               apply (`push1);
               apply_squash_or_lem (d-1) t

           | _ ->
               fail "mapply: can't apply (1)"
       end
    | C_Total rt ->
       begin match unsquash rt with
       (* If the function returns a squash, just apply it, since our goals are squashed *)
       | Some _ -> apply t
       (* If not, we can try to introduce the squash ourselves first *)
       | None ->
           apply (`FStar.Squash.return_squash);
           apply t
       end
    | _ -> fail "mapply: can't apply (2)"
    end

(* `m` is for `magic` *)
let mapply (t : term) : Tac unit =
    apply_squash_or_lem 10 t

private
let dump_admit () : Tac unit =
  clear_top (); // gets rid of the unit binder
  admit1 ()

assume val admit_goal : #a:Type -> unit ->
    Pure a (requires (by_tactic dump_admit a))
           (ensures (fun _ -> False))
