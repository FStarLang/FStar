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
module FStar.Tactics.Logic

open FStar.Tactics.Effect
open FStar.Tactics.Builtins
open FStar.Tactics.Derived
open FStar.Tactics.Util
open FStar.Reflection
open FStar.Reflection.Formula

(** Returns the current goal as a [formula]. *)
let cur_formula () : Tac formula = term_as_formula (cur_goal ())

private val revert_squash : (#a:Type) -> (#b : (a -> Type)) ->
                            (squash (forall (x:a). b x)) ->
                            x:a -> squash (b x)
let revert_squash #a #b s x = let x : (_:unit{forall x. b x}) = s in ()

(** Revert an introduced binder as a forall. *)
let l_revert () : Tac unit =
    revert ();
    apply (`revert_squash)

(** Repeated [l_revert]. *)
let rec l_revert_all (bs:binders) : Tac unit =
    match bs with
    | []    -> ()
    | _::tl -> begin l_revert (); l_revert_all tl end

private let fa_intro_lem (#a:Type) (#p:a -> Type) (f:(x:a -> squash (p x))) : Lemma (forall (x:a). p x) =
  FStar.Classical.lemma_forall_intro_gtot
    ((fun x -> FStar.IndefiniteDescription.elim_squash (f x)) <: (x:a -> GTot (p x)))

(** Introduce a forall. *)
let forall_intro () : Tac binder =
    apply_lemma (`fa_intro_lem);
    intro ()

(** Introduce a forall, with some given name. *)
let forall_intro_as (s:string) : Tac binder =
    apply_lemma (`fa_intro_lem);
    intro_as s

(** Repeated [forall_intro]. *)
let forall_intros () : Tac binders = repeat1 forall_intro

private val split_lem : (#a:Type) -> (#b:Type) ->
                        squash a -> squash b -> Lemma (a /\ b)
let split_lem #a #b sa sb = ()

(** Split a conjunction into two goals. *)
let split () : Tac unit =
    try apply_lemma (`split_lem)
    with | _ -> fail "Could not split goal"

private val imp_intro_lem : (#a:Type) -> (#b : Type) ->
                            (a -> squash b) ->
                            Lemma (a ==> b)
let imp_intro_lem #a #b f =
  FStar.Classical.give_witness (FStar.Classical.arrow_to_impl (fun (x:squash a) -> FStar.Squash.bind_squash x f))

(** Introduce an implication. *)
let implies_intro () : Tac binder =
    apply_lemma (`imp_intro_lem);
    intro ()

let implies_intro_as (s:string) : Tac binder =
    apply_lemma (`imp_intro_lem);
    intro_as s

(** Repeated [implies_intro]. *)
let implies_intros () : Tac binders = repeat1 implies_intro

(** "Logical" intro: introduce a forall or an implication. *)
let l_intro () = forall_intro `or_else` implies_intro

(** Repeated [l]. *)
let l_intros () = repeat l_intro

let squash_intro () : Tac unit =
    apply (`FStar.Squash.return_squash)

let l_exact (t:term) =
    try exact t with
    | _ -> (squash_intro (); exact t)

let hyp (b:binder) : Tac unit = l_exact (binder_to_term b)

private
let __lemma_to_squash #req #ens (_ : squash req) (h : (unit -> Lemma (requires req) (ensures ens))) : squash ens =
  h ()

let pose_lemma (t : term) : Tac binder =
  let c = tcc (cur_env ()) t in
  let pre, post =
    match inspect_comp c with
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

    let b = pose (`(__lemma_to_squash #(`#pre) #(`#post) (`#(binder_to_term reqb)) (fun () -> (`#t)))) in
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
                    | Forall b phi ->
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

private val vbind : (#p:Type) -> (#q:Type) -> squash p -> (p -> squash q) -> Lemma q
let vbind #p #q sq f = FStar.Classical.give_witness_from_squash (FStar.Squash.bind_squash sq f)

(** A tactic to unsquash a hypothesis. Perhaps you are looking
for [unsquash_term]. *)
let unsquash (t:term) : Tac term =
    let v = `vbind in
    apply_lemma (mk_e_app v [t]);
    let b = intro () in
    pack_ln (Tv_Var (bv_of_binder b))

private val or_ind : (#p:Type) -> (#q:Type) -> (#phi:Type) ->
                     (p \/ q) ->
                     (squash (p ==> phi)) ->
                     (squash (q ==> phi)) ->
                     Lemma phi
let or_ind #p #q #phi o l r = ()

let cases_or (o:term) : Tac unit =
    apply_lemma (mk_e_app (`or_ind) [o])

private val bool_ind : (b:bool) -> (phi:Type) -> (squash (b == true  ==> phi)) ->
                                                 (squash (b == false ==> phi)) ->
                                                 Lemma phi
let bool_ind b phi l r = ()

let cases_bool (b:term) : Tac unit =
    let bi = `bool_ind in
    seq (fun () -> apply_lemma (mk_e_app bi [b]))
        (fun () -> let _ = trytac (fun () -> let b = implies_intro () in rewrite b; clear_top ()) in ())

private val or_intro_1 : (#p:Type) -> (#q:Type) -> squash p -> Lemma (p \/ q)
let or_intro_1 #p #q _ = ()

private val or_intro_2 : (#p:Type) -> (#q:Type) -> squash q -> Lemma (p \/ q)
let or_intro_2 #p #q _ = ()

let left () : Tac unit =
    apply_lemma (`or_intro_1)

let right () : Tac unit =
    apply_lemma (`or_intro_2)

private val __and_elim : (#p:Type) -> (#q:Type) -> (#phi:Type) ->
                              (p /\ q) ->
                              squash (p ==> q ==> phi) ->
                              Lemma phi
let __and_elim #p #q #phi p_and_q f = ()

private val __and_elim' : (#p:Type) -> (#q:Type) -> (#phi:Type) ->
                              squash (p /\ q) ->
                              squash (p ==> q ==> phi) ->
                              Lemma phi
let __and_elim' #p #q #phi p_and_q f = ()

let and_elim (t : term) : Tac unit =
    begin
     try apply_lemma (`(__and_elim (`#t)))
     with | _ -> apply_lemma (`(__and_elim' (`#t)))
    end

let destruct_and (t : term) : Tac (binder * binder) =
    and_elim t;
    (implies_intro (), implies_intro ())

private val __witness : (#a:Type) -> (x:a) -> (#p:(a -> Type)) -> squash (p x) -> squash (exists (x:a). p x)
private let __witness #a x #p _ = ()

let witness (t : term) : Tac unit =
    apply_raw (`__witness);
    exact t

private
let __elim_exists' #t (#pred : t -> Type0) #goal (h : (exists x. pred x))
                          (k : (x:t -> pred x -> squash goal)) : squash goal =
  FStar.Squash.bind_squash #(x:t & pred x) h (fun (|x, pf|) -> k x pf)

(* returns witness and proof as binders *)
let elim_exists (t : term) : Tac (binder & binder) =
  apply_lemma (`(__elim_exists' (`#(t))));
  let x = intro () in
  let pf = intro () in
  (x, pf)

private
let __forall_inst #t (#pred : t -> Type0) (h : (forall x. pred x)) (x : t) : squash (pred x) =
    ()

(* GM: annoying that this doesn't just work by SMT *)
private
let __forall_inst_sq #t (#pred : t -> Type0) (h : squash (forall x. pred x)) (x : t) : squash (pred x) =
    FStar.Squash.bind_squash h (fun (f : (forall x. pred x)) -> __forall_inst f x)

let instantiate (fa : term) (x : term) : Tac binder =
    try pose (`__forall_inst_sq (`#fa) (`#x)) with | _ ->
    try pose (`__forall_inst (`#fa) (`#x)) with | _ ->
    fail "could not instantiate"

let instantiate_as (fa : term) (x : term) (s : string) : Tac binder =
    let b = instantiate fa x in
    rename_to b s

private
let sklem0 (#a:Type) (#p : a -> Type0) ($v : (exists (x:a). p x)) (phi:Type0) :
  Lemma (requires (forall x. p x ==> phi))
        (ensures phi) = ()

private
let rec sk_binder' (acc:binders) (b:binder) : Tac (binders * binder) =
  focus (fun () ->
    try
      apply_lemma (`(sklem0 (`#(binder_to_term b))));
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
  let bs = binders_of_env (cur_env ()) in
  map sk_binder bs

private
val lemma_from_squash : #a:Type -> #b:(a -> Type) -> (x:a -> squash (b x)) -> x:a -> Lemma (b x)
private
let lemma_from_squash #a #b f x = let _ = f x in assert (b x)

private
let easy_fill () =
    let _ = repeat intro in
    (* If the goal is `a -> Lemma b`, intro will fail, try to use this switch *)
    let _ = trytac (fun () -> apply (`lemma_from_squash); intro ()) in
    smt ()

val easy : #a:Type -> (#[easy_fill ()] _ : a) -> a
let easy #a #x = x

private
let lem1_fa #a #pre #post
  ($lem : (x:a -> Lemma (requires pre x) (ensures post x))) :
  Lemma (forall (x:a). pre x ==> post x) =
  let l' x : Lemma (pre x ==> post x) =
    Classical.move_requires lem x
  in
  Classical.forall_intro l'

private
let lem2_fa #a #b #pre #post
  ($lem : (x:a -> y:b -> Lemma (requires pre x y) (ensures post x y))) :
  Lemma (forall (x:a) (y:b). pre x y ==> post x y) =
  let l' x y : Lemma (pre x y ==> post x y) =
    Classical.move_requires (lem x) y
  in
  Classical.forall_intro_2 l'

private
let lem3_fa #a #b #c #pre #post
  ($lem : (x:a -> y:b -> z:c -> Lemma (requires pre x y z) (ensures post x y z))) :
  Lemma (forall (x:a) (y:b) (z:c). pre x y z ==> post x y z) =
  let l' x y z : Lemma (pre x y z ==> post x y z) =
    Classical.move_requires (lem x y) z
  in
  Classical.forall_intro_3 l'

(** Add a lemma into the local context, quantified for all arguments.
Only works for lemmas with up to 3 arguments for now. It is expected
that `t` is a top-level name, this has not been battle-tested for other
kinds of terms. *)
let using_lemma (t : term) : Tac binder =
  try pose_lemma (`(lem1_fa (`#t))) with | _ ->
  try pose_lemma (`(lem2_fa (`#t))) with | _ ->
  try pose_lemma (`(lem3_fa (`#t))) with | _ ->
  fail #binder "using_lemma: failed to instantiate"
