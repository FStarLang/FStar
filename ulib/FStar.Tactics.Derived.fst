module FStar.Tactics.Derived

open FStar.Reflection
open FStar.Reflection.Formula
open FStar.Tactics.Types
open FStar.Tactics.Effect
open FStar.Tactics.Builtins
open FStar.Tactics.Util
module L = FStar.List.Tot

(** Set the guard policy only locally, without affecting calling code *)
let with_policy pol (f : unit -> Tac 'a) : Tac 'a =
    let old_pol = get_guard_policy () in
    set_guard_policy pol;
    let r = f () in
    set_guard_policy old_pol;
    r

(** [exact e] will solve a goal [Gamma |- w : t] if [e] has type exactly
[t] in [Gamma]. Also, [e] needs to unift with [w], but this will almost
always be the case since [w] is usually a uvar. *)
let exact (t : term) : Tac unit =
    with_policy SMT (fun () -> t_exact false t)

(** Like [exact], but allows for the term [e] to have a type [t] only
under some guard [g], adding the guard as a goal. *)
let exact_guard (t : term) : Tac unit =
    with_policy Goal (fun () -> t_exact false t)

let cur_module () : Tac (list string) =
    moduleof (cur_env ())

let focus (f : unit -> Tac 'a) : Tac 'a =
    let res, _ = divide 1 f (fun () -> ()) in
    res

let rec repeatn (#a:Type) (n : int) (t : unit -> Tac a) : Tac (list a) =
    if n = 0
    then []
    else let x = t () in
         let xs = repeatn (n - 1) t in
         x :: xs

let fresh_uvar (o : option typ) : Tac term =
    let e = cur_env () in
    uvar_env e o

let unify t1 t2 =
    let e = cur_env () in
    unify_env e t1 t2

let exact_args (qs : list aqualv) (t : term) : Tac unit =
    focus (fun () ->
        let n = List.length qs in
        let uvs = repeatn n (fun () -> fresh_uvar None) in
        let t' = mk_app t (zip uvs qs) in
        exact t';
        iter (fun uv -> if is_uvar uv
                        then unshelve uv
                        else ()) (L.rev uvs)
    )

let exact_n (n : int) (t : term) : Tac unit =
    exact_args (repeatn n (fun () -> Q_Explicit)) t

let fresh_bv t =
    (* These bvs are fresh anyway through a separate counter,
     * but adding the integer allows for more readable code when
     * generating code *)
    let i = fresh () in
    fresh_bv_named ("x" ^ string_of_int i) t

let fresh_binder_named nm t =
    mk_binder (fresh_bv_named nm t)

let fresh_binder t =
    (* See comment in fresh_bv *)
    let i = fresh () in
    fresh_binder_named ("x" ^ string_of_int i) t

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

let rec first (ts : list (unit -> Tac 'a)) : Tac 'a =
    match ts with
    | [] -> fail "no tactics to try"
    | [t] -> t ()
    | t::ts -> or_else t (fun () -> first ts)

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

let admit1 () : Tac unit =
    tadmit ()

let admit_all () : Tac unit =
    let _ = repeat tadmit in
    ()

let skip_guard () : Tac unit =
    if is_guard ()
    then smt ()
    else fail ""

let guards_to_smt () : Tac unit =
    let _ = repeat skip_guard in
    ()

let simpl   () : Tac unit = norm [simplify; primops]
let whnf    () : Tac unit = norm [weak; hnf; primops]
let compute () : Tac unit = norm [primops; iota; delta; zeta]

let intros () : Tac (list binder) = repeat intro

let intros' () = let _ = intros () in ()
let destruct tm = let _ = t_destruct tm in ()
let destruct_intros tm = seq (fun () -> let _ = t_destruct tm in ()) intros'

private val __cut : (a:Type) -> (b:Type) -> (a -> b) -> a -> b
private let __cut a b f x = f x

let tcut (t:term) : Tac binder =
    let g = cur_goal () in
    let tt = mk_e_app (`__cut) [t; g] in
    apply tt;
    intro ()

let pose (t:term) : Tac binder =
    apply (`__cut);
    flip ();
    exact t;
    let _ = trytac flip in // maybe we have less than 2 goals now
    intro ()

let intro_as (s:string) : Tac binder =
    let b = intro () in
    rename_to b s;
    b

let pose_as (s:string) (t:term) : Tac binder =
    let b = pose t in
    rename_to b s;
    b

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
        let t = pack_ln (Tv_Var (bv_of_binder b)) in
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
            begin match inspect_ln lhs with
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

let unfold_def (t:term) : Tac unit =
    match inspect t with
    | Tv_FVar fv ->
        let n = String.concat "." (inspect_fv fv) in
        norm [delta_fully [n]]
    | _ -> fail "unfold_def: term is not a fv"

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
    let sq : term = pack_ln (Tv_FVar (pack_fv squash_qn)) in
    mk_e_app sq [t]

let mk_sq_eq (t1 t2 : term) : term =
    let eq : term = pack_ln (Tv_FVar (pack_fv eq2_qn)) in
    mk_squash (mk_e_app eq [t1; t2])

let grewrite (t1 t2 : term) : Tac unit =
    let e = tcut (mk_sq_eq t1 t2) in
    pointwise (fun () -> grewrite' t1 t2 (pack_ln (Tv_Var (bv_of_binder e))))



let rec iseq (ts : list (unit -> Tac unit)) : Tac unit =
    match ts with
    | t::ts -> let _ = divide 1 t (fun () -> iseq ts) in ()
    | []    -> ()

private val __witness : (#a:Type) -> (x:a) -> (#p:(a -> Type)) -> squash (p x) -> squash (l_Exists p)
private let __witness #a x #p _ =
  let id (a:Type) = a in
  let x : squash (exists x. id (p x)) = () in //an indirection to tickle the SMT encoding
  x

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
    // Fuel cutoff, just in case.
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
    | C_Total rt _ ->
       begin match unsquash rt with
       (* If the function returns a squash, just apply it, since our goals are squashed *)
       | Some _ -> apply_lemma t
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

let change_with t1 t2 =
    focus (fun () ->
        grewrite t1 t2;
        iseq [idtac; trivial]
    )

private val conv : #x:Type -> #y:Type -> squash (y == x) -> x -> y
private let conv #x #y eq w = w

let change_sq t1 =
    change (mk_e_app (`squash) [t1])

let finish_by (t : unit -> Tac 'a) : Tac 'a =
    let x = t () in
    or_else qed (fun () -> fail "finish_by: not finished");
    x

let solve_then #a #b (t1 : unit -> Tac a) (t2 : a -> Tac b) : Tac b =
    dup ();
    let x = focus (fun () -> finish_by t1) in
    let y = t2 x in
    trefl ();
    y

let add_elem (t : unit -> Tac 'a) : Tac 'a = focus (fun () ->
    apply (`Cons);
    focus (fun () ->
      let x = t () in
      qed ();
      x
    )
  )

(* Some syntax utility functions *)
let bv_to_term (bv : bv) : Tac term = pack (Tv_Var bv)
let binder_to_term (b : binder) : Tac term = let bv, _ = inspect_binder b in bv_to_term bv

(*
 * Specialize a function by partially evaluating it
 * For example:
 *   let rec foo (l:list int) (x:int) :St int =
       match l with
       | [] -> x
       | hd::tl -> x + foo tl x

     let f :int -> St int = synth_by_tactic (specialize (foo [1; 2]) [%`foo])

 * would make the definition of f as x + x + x
 *
 * f is the term that needs to be specialized
 * l is the list of names to be delta-ed
 *)
let specialize (#a:Type) (f:a) (l:list string) :unit -> Tac unit
  = fun () -> solve_then (fun () -> exact (quote f)) (fun () -> norm [delta_only l; iota; zeta])
