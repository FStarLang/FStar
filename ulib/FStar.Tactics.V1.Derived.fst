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
module FStar.Tactics.V1.Derived

open FStar.Reflection.V1
open FStar.Reflection.V1.Formula
open FStar.Tactics.Effect
open FStar.Stubs.Tactics.Types
open FStar.Stubs.Tactics.Result
open FStar.Tactics.Util
open FStar.Stubs.Tactics.V1.Builtins
open FStar.Tactics.V1.SyntaxHelpers
open FStar.Stubs.VConfig
include FStar.Tactics.Names

module L = FStar.List.Tot.Base
module V = FStar.Tactics.Visit
private let (@) = L.op_At

let name_of_bv (bv : bv) : Tac string =
    unseal ((inspect_bv bv).bv_ppname)

let bv_to_string (bv : bv) : Tac string =
    (* Could also print type...? *)
    name_of_bv bv

let name_of_binder (b : binder) : Tac string =
    name_of_bv (bv_of_binder b)

let binder_to_string (b : binder) : Tac string =
    bv_to_string (bv_of_binder b) //TODO: print aqual, attributes

exception Goal_not_trivial

let goals () : Tac (list goal) = goals_of (get ())
let smt_goals () : Tac (list goal) = smt_goals_of (get ())

let fail (#a:Type) (m:string)
  : TAC a (fun ps post -> post (Failed (TacticFailure (mkmsg m, None)) ps))
  = raise #a (TacticFailure (mkmsg m, None))

let fail_silently (#a:Type) (m:string)
  : TAC a (fun _ post -> forall ps. post (Failed (TacticFailure (mkmsg m, None)) ps))
  = set_urgency 0;
    raise #a (TacticFailure (mkmsg m, None))

(** Return the current *goal*, not its type. (Ignores SMT goals) *)
let _cur_goal () : Tac goal =
    match goals () with
    | []   -> fail "no more goals"
    | g::_ -> g

(** [cur_env] returns the current goal's environment *)
let cur_env () : Tac env = goal_env (_cur_goal ())

(** [cur_goal] returns the current goal's type *)
let cur_goal () : Tac typ = goal_type (_cur_goal ())

(** [cur_witness] returns the current goal's witness *)
let cur_witness () : Tac term = goal_witness (_cur_goal ())

(** [cur_goal_safe] will always return the current goal, without failing.
It must be statically verified that there indeed is a goal in order to
call it. *)
let cur_goal_safe () : TacH goal (requires (fun ps -> ~(goals_of ps == [])))
                                 (ensures (fun ps0 r -> exists g. r == Success g ps0))
 = match goals_of (get ()) with
   | g :: _ -> g

(** [cur_binders] returns the list of binders in the current goal. *)
let cur_binders () : Tac binders =
    binders_of_env (cur_env ())

(** Set the guard policy only locally, without affecting calling code *)
let with_policy pol (f : unit -> Tac 'a) : Tac 'a =
    let old_pol = get_guard_policy () in
    set_guard_policy pol;
    let r = f () in
    set_guard_policy old_pol;
    r

(** [exact e] will solve a goal [Gamma |- w : t] if [e] has type exactly
[t] in [Gamma]. *)
let exact (t : term) : Tac unit =
    with_policy SMT (fun () -> t_exact true false t)

(** [exact_with_ref e] will solve a goal [Gamma |- w : t] if [e] has
type [t'] where [t'] is a subtype of [t] in [Gamma]. This is a more
flexible variant of [exact]. *)
let exact_with_ref (t : term) : Tac unit =
    with_policy SMT (fun () -> t_exact true true t)

let trivial () : Tac unit =
  norm [iota; zeta; reify_; delta; primops; simplify; unmeta];
  let g = cur_goal () in
  match term_as_formula g with
  | True_ -> exact (`())
  | _ -> raise Goal_not_trivial

(* Another hook to just run a tactic without goals, just by reusing `with_tactic` *)
let run_tactic (t:unit -> Tac unit)
  : Pure unit
         (requires (set_range_of (with_tactic (fun () -> trivial (); t ()) (squash True)) (range_of t)))
         (ensures (fun _ -> True))
  = ()

(** Ignore the current goal. If left unproven, this will fail after
the tactic finishes. *)
let dismiss () : Tac unit =
    match goals () with
    | [] -> fail "dismiss: no more goals"
    | _::gs -> set_goals gs

(** Flip the order of the first two goals. *)
let flip () : Tac unit =
    let gs = goals () in
    match goals () with
    | [] | [_]   -> fail "flip: less than two goals"
    | g1::g2::gs -> set_goals (g2::g1::gs)

(** Succeed if there are no more goals left, and fail otherwise. *)
let qed () : Tac unit =
    match goals () with
    | [] -> ()
    | _ -> fail "qed: not done!"

(** [debug str] is similar to [print str], but will only print the message
if [--debug Tac] is on. *)
let debug (m:string) : Tac unit =
    if debugging () then print m

(** [smt] will mark the current goal for being solved through the SMT.
This does not immediately run the SMT: it just dumps the goal in the
SMT bin. Note, if you dump a proof-relevant goal there, the engine will
later raise an error. *)
let smt () : Tac unit =
    match goals (), smt_goals () with
    | [], _ -> fail "smt: no active goals"
    | g::gs, gs' ->
        begin
        set_goals gs;
        set_smt_goals (g :: gs')
        end

let idtac () : Tac unit = ()

(** Push the current goal to the back. *)
let later () : Tac unit =
    match goals () with
    | g::gs -> set_goals (gs @ [g])
    | _ -> fail "later: no goals"

(** [apply f] will attempt to produce a solution to the goal by an application
of [f] to any amount of arguments (which need to be solved as further goals).
The amount of arguments introduced is the least such that [f a_i] unifies
with the goal's type. *)
let apply (t : term) : Tac unit =
    t_apply true false false t

let apply_noinst (t : term) : Tac unit =
    t_apply true true false t

(** [apply_lemma l] will solve a goal of type [squash phi] when [l] is a
Lemma ensuring [phi]. The arguments to [l] and its requires clause are
introduced as new goals. As a small optimization, [unit] arguments are
discharged by the engine. Just a thin wrapper around [t_apply_lemma]. *)
let apply_lemma (t : term) : Tac unit =
    t_apply_lemma false false t

(** See docs for [t_trefl] *)
let trefl () : Tac unit =
  t_trefl false

(** See docs for [t_trefl] *)
let trefl_guard () : Tac unit =
  t_trefl true

(** See docs for [t_commute_applied_match] *)
let commute_applied_match () : Tac unit =
  t_commute_applied_match ()

(** Similar to [apply_lemma], but will not instantiate uvars in the
goal while applying. *)
let apply_lemma_noinst (t : term) : Tac unit =
    t_apply_lemma true false t

let apply_lemma_rw (t : term) : Tac unit =
    t_apply_lemma false true t

(** [apply_raw f] is like [apply], but will ask for all arguments
regardless of whether they appear free in further goals. See the
explanation in [t_apply]. *)
let apply_raw (t : term) : Tac unit =
    t_apply false false false t

(** Like [exact], but allows for the term [e] to have a type [t] only
under some guard [g], adding the guard as a goal. *)
let exact_guard (t : term) : Tac unit =
    with_policy Goal (fun () -> t_exact true false t)

(** (TODO: explain better) When running [pointwise tau] For every
subterm [t'] of the goal's type [t], the engine will build a goal [Gamma
|= t' == ?u] and run [tau] on it. When the tactic proves the goal,
the engine will rewrite [t'] for [?u] in the original goal type. This
is done for every subterm, bottom-up. This allows to recurse over an
unknown goal type. By inspecting the goal, the [tau] can then decide
what to do (to not do anything, use [trefl]). *)
let t_pointwise (d:direction) (tau : unit -> Tac unit) : Tac unit =
  let ctrl (t:term) : Tac (bool & ctrl_flag) =
    true, Continue
  in
  let rw () : Tac unit =
    tau ()
  in
  ctrl_rewrite d ctrl rw

(** [topdown_rewrite ctrl rw] is used to rewrite those sub-terms [t]
    of the goal on which [fst (ctrl t)] returns true.

    On each such sub-term, [rw] is presented with an equality of goal
    of the form [Gamma |= t == ?u]. When [rw] proves the goal,
    the engine will rewrite [t] for [?u] in the original goal
    type.

    The goal formula is traversed top-down and the traversal can be
    controlled by [snd (ctrl t)]:

    When [snd (ctrl t) = 0], the traversal continues down through the
    position in the goal term.

    When [snd (ctrl t) = 1], the traversal continues to the next
    sub-tree of the goal.

    When [snd (ctrl t) = 2], no more rewrites are performed in the
    goal.
*)
let topdown_rewrite (ctrl : term -> Tac (bool & int))
                    (rw:unit -> Tac unit) : Tac unit
  = let ctrl' (t:term) : Tac (bool & ctrl_flag) =
      let b, i = ctrl t in
      let f =
        match i with
        | 0 -> Continue
        | 1 -> Skip
        | 2 -> Abort
        | _ -> fail "topdown_rewrite: bad value from ctrl"
      in
      b, f
    in
    ctrl_rewrite TopDown ctrl' rw

let pointwise  (tau : unit -> Tac unit) : Tac unit = t_pointwise BottomUp tau
let pointwise' (tau : unit -> Tac unit) : Tac unit = t_pointwise TopDown  tau

let cur_module () : Tac name =
    moduleof (top_env ())

let open_modules () : Tac (list name) =
    env_open_modules (top_env ())

let fresh_uvar (o : option typ) : Tac term =
    let e = cur_env () in
    uvar_env e o

let unify (t1 t2 : term) : Tac bool =
    let e = cur_env () in
    unify_env e t1 t2

let unify_guard (t1 t2 : term) : Tac bool =
    let e = cur_env () in
    unify_guard_env e t1 t2

let tmatch (t1 t2 : term) : Tac bool =
    let e = cur_env () in
    match_env e t1 t2

(** [divide n t1 t2] will split the current set of goals into the [n]
first ones, and the rest. It then runs [t1] on the first set, and [t2]
on the second, returning both results (and concatenating remaining goals). *)
let divide (n:int) (l : unit -> Tac 'a) (r : unit -> Tac 'b) : Tac ('a & 'b) =
    if n < 0 then
      fail "divide: negative n";
    let gs, sgs = goals (), smt_goals () in
    let gs1, gs2 = List.Tot.Base.splitAt n gs in

    set_goals gs1; set_smt_goals [];
    let x = l () in
    let gsl, sgsl = goals (), smt_goals () in

    set_goals gs2; set_smt_goals [];
    let y = r () in
    let gsr, sgsr = goals (), smt_goals () in

    set_goals (gsl @ gsr); set_smt_goals (sgs @ sgsl @ sgsr);
    (x, y)

let rec iseq (ts : list (unit -> Tac unit)) : Tac unit =
    match ts with
    | t::ts -> let _ = divide 1 t (fun () -> iseq ts) in ()
    | []    -> ()

(** [focus t] runs [t ()] on the current active goal, hiding all others
and restoring them at the end. *)
let focus (t : unit -> Tac 'a) : Tac 'a =
    match goals () with
    | [] -> fail "focus: no goals"
    | g::gs ->
        let sgs = smt_goals () in
        set_goals [g]; set_smt_goals [];
        let x = t () in
        set_goals (goals () @ gs); set_smt_goals (smt_goals () @ sgs);
        x

(** Similar to [dump], but only dumping the current goal. *)
let dump1 (m : string) = focus (fun () -> dump m)

let rec mapAll (t : unit -> Tac 'a) : Tac (list 'a) =
    match goals () with
    | [] -> []
    | _::_ -> let (h, t) = divide 1 t (fun () -> mapAll t) in h::t

let rec iterAll (t : unit -> Tac unit) : Tac unit =
    (* Could use mapAll, but why even build that list *)
    match goals () with
    | [] -> ()
    | _::_ -> let _ = divide 1 t (fun () -> iterAll t) in ()

let iterAllSMT (t : unit -> Tac unit) : Tac unit =
    let gs, sgs = goals (), smt_goals () in
    set_goals sgs;
    set_smt_goals [];
    iterAll t;
    let gs', sgs' = goals (), smt_goals () in
    set_goals gs;
    set_smt_goals (gs'@sgs')

(** Runs tactic [t1] on the current goal, and then tactic [t2] on *each*
subgoal produced by [t1]. Each invocation of [t2] runs on a proofstate
with a single goal (they're "focused"). *)
let seq (f : unit -> Tac unit) (g : unit -> Tac unit) : Tac unit =
    focus (fun () -> f (); iterAll g)

let exact_args (qs : list aqualv) (t : term) : Tac unit =
    focus (fun () ->
        let n = List.Tot.Base.length qs in
        let uvs = repeatn n (fun () -> fresh_uvar None) in
        let t' = mk_app t (zip uvs qs) in
        exact t';
        iter (fun uv -> if is_uvar uv
                        then unshelve uv
                        else ()) (L.rev uvs)
    )

let exact_n (n : int) (t : term) : Tac unit =
    exact_args (repeatn n (fun () -> Q_Explicit)) t

(** [ngoals ()] returns the number of goals *)
let ngoals () : Tac int = List.Tot.Base.length (goals ())

(** [ngoals_smt ()] returns the number of SMT goals *)
let ngoals_smt () : Tac int = List.Tot.Base.length (smt_goals ())

(* Create a fresh bound variable (bv), using a generic name. See also
[fresh_bv_named]. *)
let fresh_bv () : Tac bv =
    (* These bvs are fresh anyway through a separate counter,
     * but adding the integer allows for more readability when
     * generating code *)
    let i = fresh () in
    fresh_bv_named ("x" ^ string_of_int i)

let fresh_binder_named nm t : Tac binder =
    mk_binder (fresh_bv_named nm) t

let fresh_binder t : Tac binder =
    (* See comment in fresh_bv *)
    let i = fresh () in
    fresh_binder_named ("x" ^ string_of_int i) t

let fresh_implicit_binder_named nm t : Tac binder =
    mk_implicit_binder (fresh_bv_named nm) t

let fresh_implicit_binder t : Tac binder =
    (* See comment in fresh_bv *)
    let i = fresh () in
    fresh_implicit_binder_named ("x" ^ string_of_int i) t

let guard (b : bool) : TacH unit (requires (fun _ -> True))
                                 (ensures (fun ps r -> if b
                                                       then Success? r /\ Success?.ps r == ps
                                                       else Failed? r))
        (* ^ the proofstate on failure is not exactly equal (has the psc set) *)
    =
    if not b then
        fail "guard failed"
    else ()

let try_with (f : unit -> Tac 'a) (h : exn -> Tac 'a) : Tac 'a =
    match catch f with
    | Inl e -> h e
    | Inr x -> x

let trytac (t : unit -> Tac 'a) : Tac (option 'a) =
    try Some (t ())
    with
    | _ -> None

let or_else (#a:Type) (t1 : unit -> Tac a) (t2 : unit -> Tac a) : Tac a =
    try t1 ()
    with | _ -> t2 ()

val (<|>) : (unit -> Tac 'a) ->
            (unit -> Tac 'a) ->
            (unit -> Tac 'a)
let (<|>) t1 t2 = fun () -> or_else t1 t2

let first (ts : list (unit -> Tac 'a)) : Tac 'a =
    L.fold_right (<|>) ts (fun () -> fail "no tactics to try") ()

let rec repeat (#a:Type) (t : unit -> Tac a) : Tac (list a) =
    match catch t with
    | Inl _ -> []
    | Inr x -> x :: repeat t

let repeat1 (#a:Type) (t : unit -> Tac a) : Tac (list a) =
    t () :: repeat t

let repeat' (f : unit -> Tac 'a) : Tac unit =
    let _ = repeat f in ()

let norm_term (s : list norm_step) (t : term) : Tac term =
    let e =
        try cur_env ()
        with | _ -> top_env ()
    in
    norm_term_env e s t

(** Join all of the SMT goals into one. This helps when all of them are
expected to be similar, and therefore easier to prove at once by the SMT
solver. TODO: would be nice to try to join them in a more meaningful
way, as the order can matter. *)
let join_all_smt_goals () =
  let gs, sgs = goals (), smt_goals () in
  set_smt_goals [];
  set_goals sgs;
  repeat' join;
  let sgs' = goals () in // should be a single one
  set_goals gs;
  set_smt_goals sgs'

let discard (tau : unit -> Tac 'a) : unit -> Tac unit =
    fun () -> let _ = tau () in ()

// TODO: do we want some value out of this?
let rec repeatseq (#a:Type) (t : unit -> Tac a) : Tac unit =
    let _ = trytac (fun () -> (discard t) `seq` (discard (fun () -> repeatseq t))) in ()

let tadmit () = tadmit_t (`())

let admit1 () : Tac unit =
    tadmit ()

let admit_all () : Tac unit =
    let _ = repeat tadmit in
    ()

(** [is_guard] returns whether the current goal arose from a typechecking guard *)
let is_guard () : Tac bool =
    Stubs.Tactics.Types.is_guard (_cur_goal ())

let skip_guard () : Tac unit =
    if is_guard ()
    then smt ()
    else fail ""

let guards_to_smt () : Tac unit =
    let _ = repeat skip_guard in
    ()

let simpl   () : Tac unit = norm [simplify; primops]
let whnf    () : Tac unit = norm [weak; hnf; primops; delta]
let compute () : Tac unit = norm [primops; iota; delta; zeta]

let intros () : Tac (list binder) = repeat intro

let intros' () : Tac unit = let _ = intros () in ()
let destruct tm : Tac unit = let _ = t_destruct tm in ()
let destruct_intros tm : Tac unit = seq (fun () -> let _ = t_destruct tm in ()) intros'

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
    intro ()

let intro_as (s:string) : Tac binder =
    let b = intro () in
    rename_to b s

let pose_as (s:string) (t:term) : Tac binder =
    let b = pose t in
    rename_to b s

let for_each_binder (f : binder -> Tac 'a) : Tac (list 'a) =
    map f (cur_binders ())

let rec revert_all (bs:binders) : Tac unit =
    match bs with
    | [] -> ()
    | _::tl -> revert ();
               revert_all tl

(* Some syntax utility functions *)
let bv_to_term (bv : bv) : Tac term = pack (Tv_Var bv)

[@@coercion]
let binder_to_term (b : binder) : Tac term =
  let bview = inspect_binder b in
  bv_to_term bview.binder_bv

let binder_sort (b : binder) : Tac typ =
  (inspect_binder b).binder_sort

// Cannot define this inside `assumption` due to #1091
private
let rec __assumption_aux (bs : binders) : Tac unit =
    match bs with
    | [] ->
        fail "no assumption matches goal"
    | b::bs ->
        let t = binder_to_term b in
        try exact t with | _ ->
        try (apply (`FStar.Squash.return_squash);
             exact t) with | _ ->
        __assumption_aux bs

let assumption () : Tac unit =
    __assumption_aux (cur_binders ())

let destruct_equality_implication (t:term) : Tac (option (formula & term)) =
    match term_as_formula t with
    | Implies lhs rhs ->
        let lhs = term_as_formula' lhs in
        begin match lhs with
        | Comp (Eq _) _ _ -> Some (lhs, rhs)
        | _ -> None
        end
    | _ -> None

private
let __eq_sym #t (a b : t) : Lemma ((a == b) == (b == a)) =
  FStar.PropositionalExtensionality.apply (a==b) (b==a)

(** Like [rewrite], but works with equalities [v == e] and [e == v] *)
let rewrite' (b:binder) : Tac unit =
    ((fun () -> rewrite b)
     <|> (fun () -> binder_retype b;
                    apply_lemma (`__eq_sym);
                    rewrite b)
     <|> (fun () -> fail "rewrite' failed"))
    ()

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
        (try rewrite x_t with | _ -> ());
        rewrite_all_context_equalities bs
    end

let rewrite_eqs_from_context () : Tac unit =
    rewrite_all_context_equalities (cur_binders ())

let rewrite_equality (t:term) : Tac unit =
    try_rewrite_equality t (cur_binders ())

let unfold_def (t:term) : Tac unit =
    match inspect t with
    | Tv_FVar fv ->
        let n = implode_qn (inspect_fv fv) in
        norm [delta_fully [n]]
    | _ -> fail "unfold_def: term is not a fv"

(** Rewrites left-to-right, and bottom-up, given a set of lemmas stating
equalities. The lemmas need to prove *propositional* equalities, that
is, using [==]. *)
let l_to_r (lems:list term) : Tac unit =
    let first_or_trefl () : Tac unit =
        fold_left (fun k l () ->
                    (fun () -> apply_lemma_rw l)
                    `or_else` k)
                  trefl lems () in
    pointwise first_or_trefl

let mk_squash (t : term) : term =
    let sq : term = pack_ln (Tv_FVar (pack_fv squash_qn)) in
    mk_e_app sq [t]

let mk_sq_eq (t1 t2 : term) : term =
    let eq : term = pack_ln (Tv_FVar (pack_fv eq2_qn)) in
    mk_squash (mk_e_app eq [t1; t2])

(** Rewrites all appearances of a term [t1] in the goal into [t2].
Creates a new goal for [t1 == t2]. *)
let grewrite (t1 t2 : term) : Tac unit =
    let e = tcut (mk_sq_eq t1 t2) in
    let e = pack_ln (Tv_Var (bv_of_binder e)) in
    pointwise (fun () ->
      (* If the LHS is a uvar, do nothing, so we do not instantiate it. *)
      let is_uvar =
        match term_as_formula (cur_goal()) with
        | Comp (Eq _) lhs rhs ->
          (match inspect_ln lhs with
           | Tv_Uvar _ _ -> true
           | _ -> false)
        | _ -> false
      in
      if is_uvar
      then trefl ()
      else try exact e with | _ -> trefl ())

private
let __un_sq_eq (#a:Type) (x y : a) (_ : (x == y)) : Lemma (x == y) = ()

(** A wrapper to [grewrite] which takes a binder of an equality type *)
let grewrite_eq (b:binder) : Tac unit =
  match term_as_formula (type_of_binder b) with
  | Comp (Eq _) l r ->
    grewrite l r;
    iseq [idtac; (fun () -> exact (binder_to_term b))]
  | _ ->
    begin match term_as_formula' (type_of_binder b) with
    | Comp (Eq _) l r ->
      grewrite l r;
      iseq [idtac; (fun () -> apply_lemma (`__un_sq_eq);
                              exact (binder_to_term b))]
    | _ ->
      fail "grewrite_eq: binder type is not an equality"
    end

private val push1 : (#p:Type) -> (#q:Type) ->
                        squash (p ==> q) ->
                        squash p ->
                        squash q
private let push1 #p #q f u = ()

private val push1' : (#p:Type) -> (#q:Type) ->
                         (p ==> q) ->
                         squash p ->
                         squash q
private let push1' #p #q f u = ()

(*
 * Some easier applying, which should prevent frustration
 * (or cause more when it doesn't do what you wanted to)
 *)
val apply_squash_or_lem : d:nat -> term -> Tac unit
let rec apply_squash_or_lem d t =
    (* Before anything, try a vanilla apply and apply_lemma *)
    try apply t with | _ ->
    try apply (`FStar.Squash.return_squash); apply t with | _ ->
    try apply_lemma t with | _ ->

    // Fuel cutoff, just in case.
    if d <= 0 then fail "mapply: out of fuel" else begin

    let ty = tc (cur_env ()) t in
    let tys, c = collect_arr ty in
    match inspect_comp c with
    | C_Lemma pre post _ ->
       begin
       let post = `((`#post) ()) in (* unthunk *)
       let post = norm_term [] post in
       (* Is the lemma an implication? We can try to intro *)
       match term_as_formula' post with
       | Implies p q ->
           apply_lemma (`push1);
           apply_squash_or_lem (d-1) t

       | _ ->
           fail "mapply: can't apply (1)"
       end
    | C_Total rt ->
       begin match unsquash_term rt with
       (* If the function returns a squash, just apply it, since our goals are squashed *)
       | Some rt ->
        // DUPLICATED, refactor!
         begin
         let rt = norm_term [] rt in
         (* Is the lemma an implication? We can try to intro *)
         match term_as_formula' rt with
         | Implies p q ->
             apply_lemma (`push1);
             apply_squash_or_lem (d-1) t

         | _ ->
             fail "mapply: can't apply (1)"
         end

       (* If not, we can try to introduce the squash ourselves first *)
       | None ->
        // DUPLICATED, refactor!
         begin
         let rt = norm_term [] rt in
         (* Is the lemma an implication? We can try to intro *)
         match term_as_formula' rt with
         | Implies p q ->
             apply_lemma (`push1);
             apply_squash_or_lem (d-1) t

         | _ ->
             apply (`FStar.Squash.return_squash);
             apply t
         end
       end
    | _ -> fail "mapply: can't apply (2)"
    end

(* `m` is for `magic` *)
let mapply (t : term) : Tac unit =
    apply_squash_or_lem 10 t


private
let admit_dump_t () : Tac unit =
  dump "Admitting";
  apply (`admit)

val admit_dump : #a:Type -> (#[admit_dump_t ()] x : (unit -> Admit a)) -> unit -> Admit a
let admit_dump #a #x () = x ()

private
let magic_dump_t () : Tac unit =
  dump "Admitting";
  apply (`magic);
  exact (`());
  ()

val magic_dump : #a:Type -> (#[magic_dump_t ()] x : a) -> unit -> Tot a
let magic_dump #a #x () = x

let change_with t1 t2 : Tac unit =
    focus (fun () ->
        grewrite t1 t2;
        iseq [idtac; trivial]
    )

let change_sq (t1 : term) : Tac unit =
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

let tlabel (l:string) =
    match goals () with
    | [] -> fail "tlabel: no goals"
    | h::t ->
        set_goals (set_label l h :: t)

let tlabel' (l:string) =
    match goals () with
    | [] -> fail "tlabel': no goals"
    | h::t ->
        let h = set_label (l ^ get_label h) h in
        set_goals (h :: t)

let focus_all () : Tac unit =
    set_goals (goals () @ smt_goals ());
    set_smt_goals []

private
let rec extract_nth (n:nat) (l : list 'a) : option ('a & list 'a) =
  match n, l with
  | _, [] -> None
  | 0, hd::tl -> Some (hd, tl)
  | _, hd::tl -> begin
    match extract_nth (n-1) tl with
    | Some (hd', tl') -> Some (hd', hd::tl')
    | None -> None
  end

let bump_nth (n:pos) : Tac unit =
  // n-1 since goal numbering begins at 1
  match extract_nth (n - 1) (goals ()) with
  | None -> fail "bump_nth: not that many goals"
  | Some (h, t) -> set_goals (h :: t)

let rec destruct_list (t : term) : Tac (list term) =
    let head, args = collect_app t in
    match inspect_ln head, args with
    | Tv_FVar fv, [(a1, Q_Explicit); (a2, Q_Explicit)]
    | Tv_FVar fv, [(_, Q_Implicit); (a1, Q_Explicit); (a2, Q_Explicit)] ->
      if inspect_fv fv = cons_qn
      then a1 :: destruct_list a2
      else raise NotAListLiteral
    | Tv_FVar fv, _ ->
      if inspect_fv fv = nil_qn
      then []
      else raise NotAListLiteral
    | _ ->
      raise NotAListLiteral

private let get_match_body () : Tac term =
  match unsquash_term (cur_goal ()) with
  | None -> fail ""
  | Some t -> match inspect_unascribe t with
             | Tv_Match sc _ _ -> sc
             | _ -> fail "Goal is not a match"

private let rec last (x : list 'a) : Tac 'a =
    match x with
    | [] -> fail "last: empty list"
    | [x] -> x
    | _::xs -> last xs

(** When the goal is [match e with | p1 -> e1 ... | pn -> en],
destruct it into [n] goals for each possible case, including an
hypothesis for [e] matching the corresponding pattern. *)
let branch_on_match () : Tac unit =
    focus (fun () ->
      let x = get_match_body () in
      let _ = t_destruct x in
      iterAll (fun () ->
        let bs = repeat intro in
        let b = last bs in (* this one is the equality *)
        grewrite_eq b;
        norm [iota])
    )

(** When the argument [i] is non-negative, [nth_binder] grabs the nth
binder in the current goal. When it is negative, it grabs the (-i-1)th
binder counting from the end of the goal. That is, [nth_binder (-1)]
will return the last binder, [nth_binder (-2)] the second to last, and
so on. *)
let nth_binder (i:int) : Tac binder =
  let bs = cur_binders () in
  let k : int = if i >= 0 then i else List.Tot.Base.length bs + i in
  let k : nat = if k < 0 then fail "not enough binders" else k in
  match List.Tot.Base.nth bs k with
  | None -> fail "not enough binders"
  | Some b -> b

(** [mk_abs [x1; ...; xn] t] returns the term [fun x1 ... xn -> t] *)
let rec mk_abs (args : list binder) (t : term) : Tac term (decreases args) =
  match args with
  | [] -> t
  | a :: args' ->
    let t' = mk_abs args' t in
    pack (Tv_Abs a t')

(** [string_to_term_with_lb [(id1, t1); ...; (idn, tn)] e s] parses
[s] as a term in environment [e] augmented with bindings
[id1, t1], ..., [idn, tn]. *)
let string_to_term_with_lb
  (letbindings: list (string & term))
  (e: env) (t: string): Tac term
  = let unk = pack_ln Tv_Unknown in
    let e, lb_bvs = fold_left (fun (e, lb_bvs) (i, v) ->
        let e, bv = push_bv_dsenv e i in
        e, (v,bv)::lb_bvs
      ) (e, []) letbindings in
    let t = string_to_term e t in
    fold_left (fun t (i, bv) -> pack (Tv_Let false [] bv unk i t)) t lb_bvs

private
val lem_trans : (#a:Type) -> (#x:a) -> (#z:a) -> (#y:a) ->
                    squash (x == y) -> squash (y == z) -> Lemma (x == z)
private
let lem_trans #a #x #z #y e1 e2 = ()

(** Transivity of equality: reduce [x == z] to [x == ?u] and [?u == z].  *)
let trans () : Tac unit = apply_lemma (`lem_trans)
