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
module FStar.Tactics.V2.Logic

open FStar.Reflection.V2
open FStar.Reflection.V2.Formula
open FStar.Tactics.Effect
open FStar.Stubs.Tactics.V2.Builtins
open FStar.Tactics.V2.Derived
open FStar.Tactics.V2.SyntaxCoercions
open FStar.Tactics.NamedView
open FStar.Tactics.Util

open FStar.Tactics.V1.Logic.Lemmas

private
let term_eq = FStar.Reflection.TermEq.Simple.term_eq

(** Revert an introduced binder as a forall. *)
let l_revert () : Tac unit =
    revert ();
    apply (`revert_squash)

(** Repeated [l_revert]. *)
let rec l_revert_all (bs:list binding) : Tac unit =
    match bs with
    | []    -> ()
    | _::tl -> begin l_revert (); l_revert_all tl end

(** Introduce a forall. *)
let forall_intro () : Tac binding =
    apply_lemma (`fa_intro_lem);
    intro ()

(** Introduce a forall, with some given name. *)
let forall_intro_as (s:string) : Tac binding =
    apply_lemma (`fa_intro_lem);
    intro_as s

(** Repeated [forall_intro]. *)
let forall_intros () : Tac (list binding) = repeat1 forall_intro

(** Split a conjunction into two goals. *)
let split () : Tac unit =
    try apply_lemma (`split_lem)
    with | _ -> fail "Could not split goal"

(** Introduce an implication. *)
let implies_intro () : Tac binding =
    apply_lemma (`imp_intro_lem);
    intro ()

let implies_intro_as (s:string) : Tac binding =
    apply_lemma (`imp_intro_lem);
    intro_as s

(** Repeated [implies_intro]. *)
let implies_intros () : Tac (list binding) = repeat1 implies_intro

(** "Logical" intro: introduce a forall or an implication. *)
let l_intro () = forall_intro `or_else` implies_intro

(** Repeated [l]. *)
let l_intros () = repeat l_intro

let squash_intro () : Tac unit =
    apply (`FStar.Squash.return_squash)

let l_exact (t:term) =
    try exact t with
    | _ -> (squash_intro (); exact t)

// FIXME: should this take a binding? It's less general...
// but usually what we want. Coercions could help.
let hyp (x:namedv) : Tac unit = l_exact (namedv_to_term x)

let pose_lemma (t : term) : Tac binding =
  let c = tcc (cur_env ()) t in
  let pre, post =
    match c with
    | C_Lemma pre post _ -> pre, post
    | _ -> fail ""
  in
  let post = `((`#post) ()) in (* unthunk *)
  let post = norm_term [] post in
  (* If the precondition is trivial, do not cut by it *)
  match term_as_formula' pre with
  | True_ ->
    pose (`(__lemma_to_squash #(`#pre) #(`#post) () (fun () -> (`#t))))
  | _ ->
    let reqb = tcut (`squash (`#pre)) in

    let b = pose (`(__lemma_to_squash #(`#pre) #(`#post) (`#(reqb <: term)) (fun () -> (`#t)))) in
    flip ();
    ignore (trytac trivial);
    b

let explode () : Tac unit =
    ignore (
    repeatseq (fun () -> first [(fun () -> ignore (l_intro ()));
                                (fun () -> ignore (split ()))]))

let rec visit (callback:unit -> Tac unit) : Tac unit =
    focus (fun () ->
            or_else callback
                   (fun () ->
                    let g = cur_goal () in
                    match term_as_formula g with
                    | Forall _b _sort _phi ->
                        let binders = forall_intros () in
                        seq (fun () -> visit callback) (fun () -> l_revert_all binders)
                    | And p q ->
                        seq split (fun () -> visit callback)
                    | Implies p q ->
                        let _ = implies_intro () in
                        seq (fun () -> visit callback) l_revert
                    | _ ->
                        ()
                   )
          )

let rec simplify_eq_implication () : Tac unit =
    let e = cur_env () in
    let g = cur_goal () in
    let r = destruct_equality_implication g in
    match r with
    | None ->
        fail "Not an equality implication"
    | Some (_, rhs) ->
        let eq_h = implies_intro () in // G, eq_h:x=e |- P
        rewrite eq_h; // G, eq_h:x=e |- P[e/x]
        clear_top (); // G |- P[e/x]
        visit simplify_eq_implication

let rewrite_all_equalities () : Tac unit =
    visit simplify_eq_implication

let rec unfold_definition_and_simplify_eq (tm:term) : Tac unit =
    let g = cur_goal () in
    match term_as_formula g with
    | App hd arg ->
        if term_eq hd tm
        then trivial ()
        else ()
    | _ -> begin
        let r = destruct_equality_implication g in
        match r with
        | None -> fail "Not an equality implication"
        | Some (_, rhs) ->
            let eq_h = implies_intro () in
            rewrite eq_h;
            clear_top ();
            visit (fun () -> unfold_definition_and_simplify_eq tm)
        end

(** A tactic to unsquash a hypothesis. Perhaps you are looking
for [unsquash_term].

Pre:
  goal =
    G |- e : squash s
    t : squash r

Post:
    G, x:r |- e : squash s
    `x` is returned as a term
*)
let unsquash (t : term) : Tac term =
    let v = `vbind in
    apply_lemma (mk_e_app v [t]);
    let b = intro () in
    pack (Tv_Var b)

let cases_or (o:term) : Tac unit =
    apply_lemma (mk_e_app (`or_ind) [o])

let cases_bool (b:term) : Tac unit =
    let bi = `bool_ind in
    seq (fun () -> apply_lemma (mk_e_app bi [b]))
        (fun () -> let _ = trytac (fun () -> let b = implies_intro () in rewrite b; clear_top ()) in ())

let left () : Tac unit =
    apply_lemma (`or_intro_1)

let right () : Tac unit =
    apply_lemma (`or_intro_2)

let and_elim (t : term) : Tac unit =
    begin
     try apply_lemma (`(__and_elim (`#t)))
     with | _ -> apply_lemma (`(__and_elim' (`#t)))
    end

let destruct_and (t : term) : Tac (binding & binding) =
    and_elim t;
    (implies_intro (), implies_intro ())

let witness (t : term) : Tac unit =
    apply_raw (`__witness);
    exact t

(* returns witness and proof as binders *)
let elim_exists (t : term) : Tac (binding & binding) =
  apply_lemma (`(__elim_exists' (`#(t))));
  let x = intro () in
  let pf = intro () in
  (x, pf)

let instantiate (fa : term) (x : term) : Tac binding =
    try pose (`__forall_inst_sq (`#fa) (`#x)) with | _ ->
    try pose (`__forall_inst (`#fa) (`#x)) with | _ ->
    fail "could not instantiate"

let instantiate_as (fa : term) (x : term) (s : string) : Tac binding =
    let b = instantiate fa x in
    rename_to b s

let rec sk_binder' (acc:list binding) (b:binding) : Tac (list binding & binding) =
  focus (fun () ->
    try
      apply_lemma (`(sklem0 (`#b)));
      if ngoals () <> 1 then fail "no";
      clear b;
      let bx = forall_intro () in
      let b' = implies_intro () in
      sk_binder' (bx::acc) b' (* We might have introduced a new existential, so possibly recurse *)
    with | _ -> (acc, b) (* If the above failed, just return *)
  )

(* Skolemizes a given binder for an existential, returning the introduced new binders
 * and the skolemized formula. *)
let sk_binder b = sk_binder' [] b

let skolem () =
  let bs = vars_of_env (cur_env ()) in
  map sk_binder bs

let easy_fill () =
    let _ = repeat intro in
    (* If the goal is `a -> Lemma b`, intro will fail, try to use this switch *)
    let _ = trytac (fun () -> apply (`lemma_from_squash); intro ()) in
    smt ()

let easy #a #x = x

(** Add a lemma into the local context, quantified for all arguments.
Only works for lemmas with up to 3 arguments for now. It is expected
that `t` is a top-level name, this has not been battle-tested for other
kinds of terms. *)
let using_lemma (t : term) : Tac binding =
  try pose_lemma (`(lem1_fa (`#t))) with | _ ->
  try pose_lemma (`(lem2_fa (`#t))) with | _ ->
  try pose_lemma (`(lem3_fa (`#t))) with | _ ->
  fail "using_lemma: failed to instantiate"
