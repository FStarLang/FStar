(*
   Copyright 2020 Microsoft Research

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

module Steel.Preorder
open FStar.PCM
open FStar.Preorder

/// This module explores the connection between PCM and preorders. More specifically, we show here
/// that any PCM induces a preorder relation, characterized by frame-preservation for any updates.
///
/// Furthermore, we also consider the reverse relationship where we derive a PCM for any preorder,
/// by taking as elements of the PCM the trace of all the states of the element.

(**** PCM to preoder *)

(**
  PCM [p] induces the preorder [q] if for any frame preserving update of [x] to [y],
  the argument and result of the frame preserving update are related by q
*)
let induces_preorder (#a:Type u#a) (p:pcm a) (q:preorder a) =
  forall (x y:a) (f:frame_preserving_upd p x y) (v:a).
    p.refine v ==> compatible p x v ==> q v (f v)


(**
  We can define a canonical preorder from any PCM by taking the quantified conjunction over all the
  preorders [q] induced by this PCM.
*)
let preorder_of_pcm (#a:Type u#a) (p:pcm a) : preorder a =
  fun x y -> forall (q:preorder a). induces_preorder p q ==> q x y

let frame_preserving_upd_is_preorder_preserving (#a:Type u#a) (p:pcm a)
  (x y:a) (f:frame_preserving_upd p x y)
  (v_old:a{p.refine v_old /\ compatible p x v_old})
  : Lemma ((preorder_of_pcm p) v_old (f v_old))
  = ()

(**
  This canonical preorder enjoys the nice property that it preserves fact stability of any
  induced preorder
*)
let stability (#a: Type u#a) (fact:a -> prop) (q:preorder a) (p:pcm a)
  : Lemma
    (requires stable fact q /\
              induces_preorder p q)
    (ensures  stable fact (preorder_of_pcm p))
  = ()

let stable_compatiblity (#a:Type u#a) (fact: a -> prop) (p:pcm a) (v v0 v1:a)
  : Lemma
    (requires
      stable fact (preorder_of_pcm p) /\
      p.refine v0 /\
      fact v0 /\
      p.refine v1 /\
      frame_preserving p v v1 /\
      compatible p v v0)
    (ensures
      fact v1)
  = let f : frame_preserving_upd p v v1 = frame_preserving_val_to_fp_upd p v v1 in
    frame_preserving_upd_is_preorder_preserving p v v1 f v0


(**** Preorder to PCM *)

(***** Building the preorder *)

(**
  This predicate tells that the list [l] can represent a trace of elements whose evolution is
  compatible with the preorder [q]
*)
let rec qhistory #a (q:preorder a) (l:list a) =
  match l with
  | []
  | [_] -> True
  | x::y::tl -> y `q` x /\ qhistory q (y::tl)

(** The history of a preorder is the type of all the traces compatible with that preorder *)
let hist (#a: Type u#a) (q:preorder a) = l:list a{qhistory q l}

(** Two compatible traces can extend each other *)
let rec extends' (#a: Type u#a) (#q:preorder a) (h0 h1:hist q) =
  h0 == h1 \/ (Cons? h0 /\ extends' (Cons?.tl h0) h1)

(** This extension relation is transitive *)
let rec extends_trans #a (#q:preorder a) (x y z:hist q)
  : Lemma (x `extends'` y /\ y `extends'` z ==> x `extends'` z)
          [SMTPat (x `extends'` y);
           SMTPat (y `extends'` z)]
  = match x with
    | [] -> ()
    | _::tl -> extends_trans tl y z

(** And it is also reflexive, so extensibility on traces is a preorder on traces *)
let extends (#a: Type u#a) (#q:preorder a) : preorder (hist q) = extends'

module L = FStar.List.Tot

(** If [h0] extends by [h1], then the length of [h0] is superior *)
let rec extends_length_eq (#a: Type u#a) (#q:preorder a) (h0 h1:hist q)
  : Lemma (ensures (extends h0 h1 ==> h0 == h1 \/ L.length h0 > L.length h1))
          [SMTPat (extends h0 h1)]
  = match h0 with
    | [] -> ()
    | hd::tl -> extends_length_eq tl h1

(**
  We build our relation of composability for traces by reflexing the extension to ensure
  symmetry
*)
let p_composable (#a: Type u#a) (q:preorder a) : symrel (hist q) =
    fun x y -> extends x y \/ extends y x

(** The operation for the PCM is to return the full trace of two extensible traces *)
let p_op (#a: Type u#a) (q:preorder a) (x:hist q) (y:hist q{p_composable q x y}) : hist q =
  if L.length x >= L.length y
  then x
  else if L.length x = L.length y
  then (assert (x == y); x)
  else y

(** The operation actually implements extension  *)
let p_op_extends (#a: Type u#a) (q:preorder a) (x:hist q) (y:hist q{p_composable q x y})
  : Lemma (ensures (p_op q x y `extends` x /\
                    p_op q x y `extends` y /\
                    (p_op q x y == x \/ p_op q x y == y)))
          [SMTPat (p_op q x y)]
  = extends_length_eq x y;
    extends_length_eq y x

(** And the empty trace is the unit element *)
let rec p_op_nil (#a: Type u#a) (q:preorder a) (x:hist q)
  : Lemma (ensures (p_composable q x [] /\ p_op q x [] == x))
          [SMTPat (p_composable q x [])]
  = match x with
    | [] -> ()
    | _::tl -> p_op_nil q tl

(** We can finally define our PCM with these operations *)
let p (#a: Type u#a) (q:preorder a) : pcm' (hist q) = {
  composable = p_composable q;
  op = p_op q;
  one = []
}

(** Composability is commutative *)
let comm (#a: Type u#a) (q:preorder a) (x y:hist q)
  : Lemma (requires p_composable q x y)
          (ensures p_composable q y x)
  = ()

(** As well as the compose operation *)
let comm_op (#a: Type u#a) (q:preorder a) (x:hist q) (y:hist q{p_composable q x y})
  : Lemma (p_op q x y == p_op q y x)
  = extends_length_eq x y;
    extends_length_eq y x

(** If [z] extends [x] and [y], then [x] and [y] are extending one or another *)
let rec extends_disjunction (#a: Type u#a) (#q:preorder a) (x y z:hist q)
  : Lemma (z `extends` x /\ z `extends` y ==> x `extends` y \/ y `extends` x)
          [SMTPat (z `extends` x);
           SMTPat (z `extends` y)]
  = match z with
    | [] -> ()
    | _::tl -> extends_disjunction x y tl

(** If [x] extends [y], then the two heads of the traces are still related by the preorder *)
let rec extends_related_head (#a: Type u#a) (#q:preorder a) (x y:hist q)
  : Lemma
    (ensures
      x `extends` y /\
      Cons? x /\
      Cons? y ==> Cons?.hd y `q` Cons?.hd x)
    [SMTPat (x `extends` y)]
  = match x with
    | [] -> ()
    | _::tl -> extends_related_head tl y

(** Finally, we can have our fully-fledged PCM from the preorder *)
let pcm_of_preorder (#a: Type u#a) (q:preorder a) : pcm (hist q) = {
  p = p q;
  comm = comm_op q;
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun _ -> True)
}

(***** Using the preorder *)

(**
  We check that the preorder derived from the PCM derived from the preorder
  satisfies the same properties as the original preorder. Here, we get back history
  extension from frame-preserving updates.
*)
let frame_preserving_q_aux (#a : Type u#a) (q:preorder a) (x y:hist q) (z:hist q)
  : Lemma (requires (frame_preserving (pcm_of_preorder q) x y /\ compatible (pcm_of_preorder q) x z))
          (ensures (y `extends` z))
  = ()

(** A non-empty history *)
let vhist (#a: Type u#a) (q:preorder a) = h:hist q{Cons? h}

(** Get the current value from an history *)
let curval (#a: Type u#a) (#q:preorder a) (v:vhist q) = Cons?.hd v

(**
  Given a frame-preserving update from [x] to [y]
  for any value of resource [z] (compatible with [x])
  the new value [y] advances the history [z] in a preorder respecting manner
*)
let frame_preserving_q (#a: Type u#a) (q:preorder a) (x y:vhist q)
  : Lemma (requires frame_preserving (pcm_of_preorder q) x y)
          (ensures (forall (z:hist q). compatible (pcm_of_preorder q) x z ==> curval z `q` curval y))
  = ()

(** Still given a frame-preserving update from [x] to [y], this update extends the history *)
let frame_preserving_extends (#a: Type u#a) (q:preorder a) (x y:vhist q)
  : Lemma (requires frame_preserving (pcm_of_preorder q) x y)
          (ensures (forall (z:hist q). compatible (pcm_of_preorder q) x z ==> y `extends` z))
  = ()

(** Helper function that flips a preoder *)
let flip (#a: Type u#a) (p:preorder a) : preorder a = fun x y -> p y x

(**
  What is the preorder induced from the PCM induced by preorder [q]? It turns out that
  it is the flipped of [q], reversed extension.
*)
let frame_preserving_extends2 (#a: Type u#a) (q:preorder a) (x y:hist q)
  : Lemma (requires frame_preserving (pcm_of_preorder q) x y)
          (ensures (forall (z:hist q). compatible (pcm_of_preorder q) x z ==> z `flip extends` y))
          [SMTPat (frame_preserving (pcm_of_preorder q) x y)]
  = ()

#push-options "--warn_error -271"
let pcm_of_preorder_induces_extends (#a: Type u#a) (q:preorder a)
  : Lemma (induces_preorder (pcm_of_preorder q) (flip extends))
  = let fp_full (x y:hist q) (f:frame_preserving_upd (pcm_of_preorder q) x y) (v:hist q)
      : Lemma (requires compatible (pcm_of_preorder q) x v)
              (ensures extends (f v) v)
              [SMTPat ()]
      = assert (composable (pcm_of_preorder q) x v) in
    ()
#pop-options

let extend_history (#a:Type u#a) (#q:preorder a) (h0:vhist q) (v:a{q (curval h0) v})
  : h1:vhist q{h1 `extends` h0}
  = v :: h0

let property (a:Type)
  = a -> prop

let stable_property (#a:Type) (pcm:pcm a)
  = fact:property a {
       FStar.Preorder.stable fact (preorder_of_pcm pcm)
    }

let fact_valid_compat (#a:Type) (#pcm:pcm a)
                      (fact:stable_property pcm)
                      (v:a)
  = forall z. compatible pcm v z ==> fact z

open Steel.FractionalPermission
open FStar.Real

noeq
type history (a:Type) (p:preorder a) =
  | Witnessed : hist p -> history a p
  | Current : h:vhist p -> f:perm -> history a p

let hval_tot #a #p (h:history a p{Current? h}) : a =
  match h with
  | Current h _ -> curval h

let hval #a #p (h:history a p{Current? h}) : Ghost.erased a =
  hval_tot h

let hperm #a #p (h:history a p{Current? h}) : perm =
  match h with
  | Current _ f -> f

let history_composable #a #p
  : symrel (history a p)
  = fun h0 h1 ->
    match h0, h1 with
    | Witnessed h0, Witnessed h1 ->
      p_composable p h0 h1
    | Witnessed h0, Current h1 f
    | Current h1 f, Witnessed h0 ->
      extends #a #p h1 h0
    | Current h0 f0, Current h1 f1 ->
      h0 == h1 /\
      (sum_perm f0 f1).v <=. one

let history_compose #a #p (h0:history a p) (h1:history a p{history_composable h0 h1})
  : history a p
  = match h0, h1 with
    | Witnessed h0, Witnessed h1 ->
      Witnessed (p_op p h0 h1)
    | Current h0 f, Witnessed h1
    | Witnessed h1, Current h0 f ->
      Current (p_op p h1 h0) f
    | Current h0 f0, Current _ f1 ->
      Current h0 (sum_perm f0 f1)

let unit_history #a #p : history a p = Witnessed []

let lem_is_unit #a #p (x:history a p)
  : Lemma (history_composable x unit_history /\
           history_compose x unit_history == x)
  = match x with
    | Witnessed h -> ()
    | Current h _ ->
      assert (forall (h:hist p). p_composable p h []);
      assert (forall (h:hist p). p_op p h [] == h);
      assert (forall (h:vhist p). extends #a #p h []);
      assert (h =!= []);
      assert (extends #a #p h [])
#push-options "--z3rlimit_factor 2"
let assoc_l #a #p (x y:history a p)
                  (z:history a p{history_composable y z /\
                                 history_composable x (history_compose y z)})
  : Lemma (history_composable x y /\
           history_composable (history_compose x y) z /\
           history_compose (history_compose x y) z ==
           history_compose x (history_compose y z))
  = ()


let assoc_r #a #p (x y:history a p)
                  (z:history a p{history_composable x y /\
                                 history_composable (history_compose x y) z})
  : Lemma (history_composable y z /\
           history_composable x (history_compose y z) /\
           history_compose (history_compose x y) z ==
           history_compose x (history_compose y z))
  = ()
#pop-options

let pcm_history #a #p : pcm (history a p) = {
  p = {
         composable = history_composable;
         op = history_compose;
         one = unit_history
      };
  comm = (fun _ _ -> ());
  assoc = assoc_l;
  assoc_r = assoc_r;
  is_unit = lem_is_unit;
  refine = (fun _ -> True);
}

let pcm_history_preorder #a #p : preorder (history a p) =
  fun h0 h1 ->
    match h0, h1 with
    | Witnessed vh0, Witnessed vh1
    | Current vh0 _, Witnessed vh1
    | Witnessed vh0, Current vh1 _
    | Current vh0 _, Current vh1 _ ->
      vh1 `extends` vh0

#push-options "--z3rlimit_factor 8 --ifuel 1 --fuel 0 --warn_error -271"
let pcm_history_induces_preorder #a #p
  : Lemma (induces_preorder (pcm_history #a #p)
                              (pcm_history_preorder #a #p))
  = let aux (x y:history a p)
            (f:frame_preserving_upd (pcm_history #a #p) x y)
            (v:history a p)
      : Lemma
          (requires compatible (pcm_history #a #p) x v)
          (ensures (pcm_history_preorder #a #p) v (f v))
          [SMTPat ()]
      = let pcm = pcm_history #a #p in
        let v1 = f v in
        match x, v, v1 with
        | Witnessed _, Witnessed _, Witnessed _ ->
          assert (composable pcm x v)
        | Current _ _, Witnessed _, Witnessed _ -> ()
        | Witnessed _, Current _ _, Witnessed _ -> ()
        | Witnessed _, Witnessed _, Current _ _ ->
          assert (composable pcm x v)
        | Current _ _, Witnessed _, Current _ _ -> ()
        | Witnessed _, Current _ _, Current _ _ -> ()
        | Current hx _, Current hv _, Witnessed _
        | Current hx _, Current hv _, Current _ _ ->
          let frame = FStar.IndefiniteDescription.indefinite_description_ghost
            (history a p) (fun frame -> composable pcm x frame /\ op pcm frame x == v) in
          match frame with
          | Current hf _ -> ()
          | Witnessed hf ->
            assert (extends hx hf);
            assert (hx == hv);
            assert (composable pcm x (Witnessed hv))
    in
    ()
#pop-options

let extend_history' #a #p (h0:history a p{Current? h0})
                         (v:a{p (hval h0) v})
 : history a p
 = let Current h f = h0 in
   Current (v :: h) f

let extend_history'_is_frame_preserving #a #p
                                       (h0:history a p{Current? h0 /\ hperm h0 == full_perm})
                                       (v:a{p (hval h0) v})
  : Lemma (frame_preserving pcm_history h0 (extend_history' h0 v))
  = ()

let history_val #a #p (h:history a p) (v:Ghost.erased a) (f:perm)
  : prop
  = Current? h /\ hval h == v /\ hperm h == f /\ f.v <=. one

let split_current #a #p (h:history a p { Current? h /\ (Current?.f h).v <=. one  })
  : half:history a p {
    Current? h /\
    composable pcm_history half half /\
    op pcm_history half half  == h /\
    Current?.h half == Current?.h h /\
    history_val half (hval h) (Current?.f half)
  }
  = let Current v p = h in
    assert_spinoff (sum_perm (half_perm p) (half_perm p) == p);
    Current v (half_perm p)

let lift_fact #a #p (f:property a)
  : property (history a p)
  = fun history ->
      match history with
      | Witnessed h -> Cons? h /\ f (Cons?.hd h)
      | Current h _ -> f (hval history)

let lift_fact_is_stable #a #p (f:property a{FStar.Preorder.stable f p})
  : Lemma (FStar.Preorder.stable #(history a p)
                                 (lift_fact f)
                                 (preorder_of_pcm pcm_history))
  = assert (FStar.Preorder.stable #(history a p) (lift_fact f) pcm_history_preorder);
    pcm_history_induces_preorder #a #p;
    stability #(history a p) (lift_fact f) pcm_history_preorder pcm_history

