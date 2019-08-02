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
module BinaryTreesEnumeration

open FStar.List

(*
 * AR: 11/29: hoisting it cf. recursive guards
 *)
type prod_with_sum (n:nat) = p:(nat & nat){fst p + snd p == n}

abstract val pairs_with_sum' : m:nat -> n:nat -> list (prod_with_sum (m + n))
abstract let rec pairs_with_sum' m n =
  (m, n) ::
    (if m = 0
     then []
     else pairs_with_sum' (m - 1) (n + 1))

let pairs_with_sum (n: nat) : list (prod_with_sum n) =
  pairs_with_sum' n 0

let product #a #b (l1: list a) (l2: list b) =
  List.Tot.concatMap (fun x1 -> List.Tot.map (fun x2 -> (x1, x2)) l2) l1

type bin_tree =
| Leaf
| Branch of bin_tree * bin_tree

let rec size bt : nat =
  match bt with
  | Leaf -> 0
  | Branch(l, r) -> 1 + size l + size r

type bt_with_size (n:nat) = t:bin_tree{size t == n}

(*> * Why do I need type annotations on [concatMap] and [map]?
    * When I reduce this definition I see that the lambda desugared to a match
      with 4 arguments (not 2). Why?
    * I had to eta-expand [Branch]; why?  Is it because there's a implicit cast
      from [bintree] to [bt: bin_tree{size bt == s}]?  If so, why is it not
      enough to add a coercion [Branch <: _ -> bt: bin_tree{size bt == s}]? *)
let rec trees_of_size (s: nat) : list (bt_with_size s) =
  if s = 0 then
    [Leaf]
  else
    List.Tot.concatMap #(prod_with_sum (s - 1))
      (fun (s1, s2) ->
       List.Tot.map #((bt_with_size s1) * (bt_with_size s2))
                    #(bt_with_size s)
         (fun (t1, t2) -> Branch (t1, t2))
         (product (trees_of_size s1) (trees_of_size s2)))
      (pairs_with_sum (s - 1))

(*> * Why do I need to re-state the goal as an [assert]?
    * Why do I need to re-state the lemma as an [assert]? *)
abstract let rec pws'_complete (m d n: nat) :
  Lemma (List.memP (m, n + d) (pairs_with_sum' (m + d) n)) =
    if d = 0 then ()
    else begin
      assert (m + d <> 0);
      pws'_complete m (d - 1) (n + 1);
      assert (List.memP (m, (n + 1) + (d - 1)) (pairs_with_sum' (m + (d - 1)) (n + 1)));
      assert (List.memP (m, n + d) (pairs_with_sum' (m + d) n))
    end

(*> Why do I need to explicitly unfold [pairs_with_sum]? *)
let pws_complete (m n: nat) :
  Lemma (List.memP (m, n) (pairs_with_sum (m + n))) =
    assert (pairs_with_sum (m + n) == pairs_with_sum' (m + n) 0);
    pws'_complete m n 0

(*> Should this be in the standard library? *)
let rec concatMap_flatten_map #a #b (f:a -> list b) l :
  Lemma (List.Tot.concatMap f l == List.Tot.flatten (List.Tot.map f l)) =
    match l with
    | [] -> ()
    | h :: t -> concatMap_flatten_map f t

(** This is Coq's [in_split] *)
(*> * Should this be in the stdlib?
    * I see why [assert false] doesn't work in the [[]] branch of the match
      (there's no contradiction unless the implication is taken into account)?
      Is there a lightweight way to make it explicit that we're proving [False ==> …]
      in that branch? I'm thinking of an equivalent of Coq's [intro; exfalso;
      assumption].
    * Is it worth writing it with two exists instead of a single exist on a pair?
    * Why do I need anything from 'classical'?  Is it because memP uses a
      classical [or]?
    * Why is [or_elim]'s 2nd argument implicit?
    * Does F* do induction automatically? I expected I'd have to supply
      [memP_append x t] explicitly to [exist_elim].  If I wanted to do that,
      would I have to use [get_proof] + [bind_squash]? *)

(* NS: June 07, 2017
   The previous "proof" here was relying on a bug revealed by issue #1071
   It had unresolved unification variables in a recursive function,
   so the proof wasn't actually complete. 
   So, this is a revised proof ... still in an overly explicit, 
   rather unsatisfactory style.

   This version may answer some of the questions above. *)

(* These utilities are better moved to the squash library *)
let bind = FStar.Squash.bind_squash
let return = FStar.Squash.return_squash
let pure_as_squash (#a:Type) 
                   (#p:_)
                   (#q:_)
                   ($f:(x:a -> Lemma (requires (p x)) (ensures (q x))))
                   (x:a{p x})
                   : squash (q x)
                   = f x
let rec memP_append_aux #a (x: a) (l: list a) :
  Lemma
    (requires (List.memP x l))
    (ensures (exists (l12: (list a * list a)). l == fst l12 @ x :: snd l12))
    =  let goal = exists l12. l == fst l12 @ x :: snd l12 in
       let x : squash goal =
         match l with
         | [] -> ()
         | h :: t ->
           let pf : squash (x == h \/ List.memP x t) = () in
           p <-- FStar.Squash.join_squash pf ;
           match p with 
           | Left x_eq_h -> 
             let l12 = [], t in
             assert (l == (fst l12) @ (x :: snd l12)) //trigger
           | Right mem_x_t -> 
             FStar.Classical.exists_elim 
                 goal
                 (pure_as_squash (memP_append_aux x) t)
                 (fun l12' -> 
                   let l12 = h::fst l12', snd l12' in
                   assert (l == (fst l12) @ (x :: snd l12))) //trigger
       in
       FStar.Squash.give_proof x

let memP_append #a (x: a) (l: list a) :
  Lemma
    (ensures (List.memP x l ==>
              (exists (l12: (list a * list a)). l == (fst l12) @ (x :: (snd l12))))) =
  FStar.Classical.move_requires (memP_append_aux x) l

(*> * Should this be in the stdlib? *)
let rec flatten_app #a (l1 l2: list (list a)) :
  Lemma (flatten (l1 @ l2) == flatten l1 @ flatten l2) =
    match l1 with
    | [] -> ()
    | h :: t -> flatten_app t l2;
              append_assoc h (flatten t) (flatten l2)

(*> * Should this be in the stdlib? *)
let rec memP_app_intro_l #a x (l1 l2: list a) :
  Lemma (memP x l1 ==> memP x (l1 @ l2)) =
    match l1 with
    | [] -> ()
    | h :: t -> memP_app_intro_l x t l2

(*> * Should this be in the stdlib? *)
let rec memP_app_intro_r #a x (l1 l2: list a) :
  Lemma (memP x l2 ==> memP x (l1 @ l2)) =
    match l1 with
    | [] -> ()
    | h :: t -> memP_app_intro_r x t l2

(*> * What's the right way to prove this? The code below is messy because…
      - … it repeats types all over the place.  Is there a way to get a bit more
        inference?
      - … it manages a context explicitly, using calls to [arrow_to_impl] to get
        concrete references to proofs.  These references (as well as the calls
        to [impl_to_arrow] and [bind_squash]) are used to construct the explicit
        proof that exist_elim asks for (without the [arrow_to_impl]s I can only
        prove [… ==> exists …], not [exists …].  What's the right way to do
        this?
      - … it lists arguments to each [memP_app] explicitly (in Coq I'd use
        apply, and it'd pick the right arguments by unifying with the goal).
        Is there a way around this?
      - … it's slow (multiple seconds), although the proof seems entirely
        explicit. *)
let memP_flatten_intro #a (x: a) (l: list a) (ls: list (list a)) :
  Lemma (List.memP x l ==>
         List.memP l ls ==>
         List.memP x (List.Tot.flatten ls)) =
    FStar.Classical.arrow_to_impl
      #(List.memP x l)
      #(List.memP l ls ==>
        List.memP x (List.Tot.flatten ls))
      (fun memP_x_l_proof ->
         FStar.Classical.arrow_to_impl
           #(List.memP l ls)
           #(List.memP x (List.Tot.flatten ls))
           (fun memP_l_ls_proof ->
              memP_append x l;
              FStar.Squash.bind_squash
                (FStar.Squash.get_proof (List.memP x l ==>
                                         (exists l12. l == (fst l12) @ (x :: (snd l12)))))
                (fun memP_x_l_split ->
                   let l_split_pr = FStar.Classical.impl_to_arrow
                                      #(List.memP x l)
                                      #(exists l12. l == (fst l12) @ (x :: (snd l12)))
                                      memP_x_l_split memP_x_l_proof in
                   FStar.Classical.exists_elim
                     (List.memP x (List.Tot.flatten ls))
                     #_
                     #(fun l12 -> l == (fst l12) @ (x :: (snd l12)))
                     l_split_pr
                     (fun l12 -> memP_append l ls;
                              FStar.Squash.bind_squash
                                (FStar.Squash.get_proof (List.memP l ls ==>
                                                         (exists ls12. ls == (fst ls12) @ (l :: (snd ls12)))))
                                (fun memP_l_ls_split ->
                                   let ls_split_pr = FStar.Classical.impl_to_arrow
                                                      #(List.memP l ls)
                                                      #(exists ls12. ls == (fst ls12) @ (l :: (snd ls12)))
                                                      memP_l_ls_split memP_l_ls_proof in
                                   FStar.Classical.exists_elim
                                     (List.memP x (List.Tot.flatten ls))
                                     #_
                                     #(fun ls12 -> ls == (fst ls12) @ (l :: (snd ls12)))
                                     ls_split_pr
                                     (fun ls12 ->
                                        let (l1, l2) = l12 in
                                        let (ls1, ls2) = ls12 in
                                        flatten_app ls1 (l :: ls2);
                                        memP_app_intro_r x (flatten ls1) ((l1 @ x :: l2) @ flatten ls2);
                                        memP_app_intro_l x (l1 @ x :: l2) (flatten ls2);
                                        memP_app_intro_r x l1 (x :: l2)))))))

let memP_concatMap_intro #a #b (x: a) (y: b) (f:a -> list b) (l: list a) :
  Lemma (List.memP x l ==>
         List.memP y (f x) ==>
         List.memP y (List.Tot.concatMap f l)) =
    concatMap_flatten_map f l;
    memP_map_intro f x l;
    memP_flatten_intro y (f x) (List.Tot.map f l)

(*> * This code used to include [assert]s instead of [:>] to re-state the goal.
      Is there a technique similar to Coq's [intro] that would allow me to only
      re-state the conclusions of the lemmas, instead of having to repeat
      redundant premises?
    * The let-bindings make the code more succinct, but also harder to read. How
      can I get rid of them without cluttering the rest of the proof with many
      copies of the same function?  Can I infer them by unifying with the
      current “goal”? *)
let product_complete (#a #b: Type) (l1: list a) (l2: list b) x1 x2 :
  Lemma (List.memP x1 l1 ==>
         List.memP x2 l2 ==>
         List.memP (x1, x2) (product #a l1 l2)) =
    let x = (x1, x2) in
    let f2 x1 = fun x2 -> (x1, x2) in
    let f1 = fun x1 -> List.Tot.map (f2 x1) l2 in
    let l = f1 x1 in
    let ls = List.Tot.map f1 l1 in
    assert (product l1 l2 == List.Tot.concatMap f1 l1);

    memP_map_intro (f2 x1) x2 l2
      <: Lemma (List.memP x2 l2 ==> List.memP x l);

    memP_map_intro f1 x1 l1
      <: Lemma (List.memP x1 l1 ==> List.memP l ls);

    memP_concatMap_intro x1 (x1, x2) f1 l1
      <: Lemma (List.memP x1 l1 ==>
                List.memP (x1, x2) (f1 x1) ==>
                List.memP (x1, x2) (List.Tot.concatMap f1 l1))

abstract let unfold_tos (s: nat) :
  Lemma (trees_of_size s ==
         (if s = 0 then
            [Leaf]
          else
            List.Tot.concatMap #(prod_with_sum (s - 1))
              (fun (s1, s2) ->
               List.Tot.map #(bt_with_size s1 * bt_with_size s2)
                            #(bt_with_size s)
                 (fun (t1, t2) -> Branch (t1, t2))
                 (product (trees_of_size s1) (trees_of_size s2)))
              (pairs_with_sum (s - 1)))) =
  assert_norm (trees_of_size s ==
               (if s = 0 then
                  [Leaf]
                else
                  List.Tot.concatMap #(prod_with_sum (s - 1))
                    (fun (s1, s2) ->
                     List.Tot.map #(bt_with_size s1 * bt_with_size s2)
                                  #(bt_with_size s)
                       (fun (t1, t2) -> Branch (t1, t2))
                       (product (trees_of_size s1) (trees_of_size s2)))
                    (pairs_with_sum (s - 1))))

(*> The error message if I omit this isn't the best.
    Could the resource exhaustion be detected and reported? *)
#set-options "--z3rlimit 40 --initial_fuel 1 --max_fuel 1"

(*> I ran into a few problems while writing this proof:
    - I had trouble supplying the right arguments for each lemma: In Coq I can just
      use [apply] and the arguments are inferred using unification.  Is there
      something similar in F*?
    - Just seeing the lemma calls made it hard to remember which facts were
      available at each point in the proof, so I wrote [assert]s to get visual
      feedback.  In previous proofs I used [<:] to write these annotations, but
      here I had to use explicit [assert]s ([<:] and [assert_norm] broke type
      inference).  The problem is that these asserts are rather costly (they
      make the proof slower).  Is there a way around this?
    - The proof does require one intermediate assert (see below) which just
      seems to be a restatement of the result of a call to a lemma.  Is there a
      way to omit it? *)
let rec tos_complete (bt0: bin_tree) :
  Lemma (List.memP bt0 (trees_of_size (size bt0))) =
    match bt0 with
    | Leaf -> ()
    | Branch(t1, t2) ->
      let s = size bt0 in
      let s1 = size t1 in
      let s2 = size t2 in
      let trees1 = trees_of_size s1 in
      let trees2 = trees_of_size s2 in

      tos_complete t1;
      (* assert (List.memP t1 trees1); *)

      tos_complete t2;
      (* assert (List.memP t2 trees2); *)

      product_complete trees1 trees2 t1 t2;
      (* assert (List.memP (t1, t2) (product trees1 trees2)); *)

      memP_map_intro #(bt_with_size s1 * bt_with_size s2)
        (fun (t1, t2) -> Branch (t1, t2) <: (bt_with_size s))
        (t1, t2)
        (product trees1 trees2);
      (* assert (List.memP (Branch (t1, t2)) *)
      (*                   (List.Tot.map #((t1: bin_tree{size t1 == s1}) * (t2: bin_tree{size t2 == s2})) *)
      (*                      (fun (t1, t2) -> Branch (t1, t2) <: (bt: bin_tree{size bt == s})) *)
      (*                      (product trees1 trees2))); *)

      pws_complete s1 s2;
      (*> Why do I need this intermediate assert? *)
      assert (List.memP (s1, s2) (pairs_with_sum (s1 + s2)));
      (* assert (List.memP (s1, s2) (pairs_with_sum (s - 1))); *)

      memP_concatMap_intro
        #(prod_with_sum (s - 1))
        (s1, s2)
        (Branch (t1, t2))
        (fun (s1, s2) ->
         List.Tot.map #(bt_with_size s1 * bt_with_size s2)
                      #(bt_with_size s)
           (fun (t1, t2) -> Branch (t1, t2))
           (product (trees_of_size s1) (trees_of_size s2)))
        (pairs_with_sum (s - 1));

      unfold_tos s
