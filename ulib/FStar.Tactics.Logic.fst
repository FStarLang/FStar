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

let cur_formula () : Tac formula = term_as_formula (cur_goal ())

private val revert_squash : (#a:Type) -> (#b : (a -> Type)) ->
                            (squash (forall (x:a). b x)) ->
                            x:a -> squash (b x)
let revert_squash #a #b s x = let x : (_:unit{forall x. b x}) = s in ()

let l_revert () : Tac unit =
    revert ();
    apply (`revert_squash)

let rec l_revert_all (bs:binders) : Tac unit =
    match bs with
    | []    -> ()
    | _::tl -> begin l_revert (); l_revert_all tl end

private val fa_intro_lem : (#a:Type) -> (#p : (a -> Type)) ->
                           (x:a -> squash (p x)) ->
                           Lemma (forall (x:a). p x)
let fa_intro_lem #a #p f = FStar.Classical.lemma_forall_intro_gtot (fun x -> (f x) <: GTot (squash (p x)))

let forall_intro () : Tac binder =
    apply_lemma (`fa_intro_lem);
    intro ()

let forall_intro_as (s:string) : Tac binder =
    apply_lemma (`fa_intro_lem);
    intro_as s

let forall_intros () : Tac binders = repeat1 forall_intro

private val split_lem : (#a:Type) -> (#b:Type) ->
                        squash a -> squash b -> Lemma (a /\ b)
let split_lem #a #b sa sb = ()

let split () : Tac unit =
    try apply_lemma (`split_lem)
    with | _ -> fail "Could not split goal"

private val imp_intro_lem : (#a:Type) -> (#b : Type) ->
                            (a -> squash b) ->
                            Lemma (a ==> b)
let imp_intro_lem #a #b f =
  FStar.Classical.give_witness (FStar.Classical.arrow_to_impl (fun (x:squash a) -> FStar.Squash.bind_squash x f))

let implies_intro () : Tac binder =
    apply_lemma (`imp_intro_lem);
    intro ()

let implies_intros () : Tac binders = repeat1 implies_intro

let l_intro () = forall_intro `or_else` implies_intro
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
    | C_Lemma pre post -> pre, post
    | _ -> fail ""
  in
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

private val __witness : (#a:Type) -> (x:a) -> (#p:(a -> Type)) -> squash (p x) -> squash (l_Exists p)
private let __witness #a x #p _ =
  let x : squash (exists x. p x) = () in
  x

let witness (t : term) : Tac unit =
    apply_raw (`__witness);
    exact t

private
let __elim_exists' #t (#pred : t -> Type0) #goal (h : (exists x. pred x))
                          (k : (x:t -> pred x -> squash goal)) : squash goal =
  FStar.Squash.bind_squash h (fun (|x, pf|) -> k x pf)

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
