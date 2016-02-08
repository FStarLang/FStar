module IFC.IFC

(* We model a simple IFC Type system *)
open FStar.Comp
open FStar.Heap
open FStar.Relational

(****************************** Preliminaries ******************************)

(* We model labels with different levels as integers *)


(* A top label that is higher than all other labels *)
let top = 1000

(* A bottom label that is lower than all other labels *)
let bot = - top

type label = l:int{bot <= l /\ l <= top}

(* Label of the attacker *)
assume val alpha : label

(* A global labeling function (assigns a label to every reference) *)
assume val label_fun : ref int -> Tot label

(* A reference can be observed by the attacker if its label is not higher than
   alpha *)
let attacker_observable x = label_fun x <= alpha

(* We have alpha equivalence when two heaps are equal for all references that
  have a label <= alpha and thus are observable by the attacker *)
type a_equiv (h1:double heap) = 
  (forall (x:ref int). attacker_observable x 
                       ==> sel (R.l h1) x = sel (R.r h1) x)

(* Function to create new labeled references *)
assume val new_labeled_int : l:label -> x:ref int{label_fun x = l}

let tu = twice ()

let max l1 l2 = if l1 <= l2 then l2 else l1
let min l1 l2 = if l1 <= l2 then l1 else l2


(**************************** Typing Judgements ****************************)

(* typing judgement  e : l
   - Expressions do not modify the heap
   - If we have alpha equivalence on the input heaps, then the results must be
     equal if the expression label is lower than or equal to alpha *)
type ni_exp (l:label) =
              double unit ->
              ST2 (double int)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 r h2 -> equal (R.l h1) (R.l h2)
                                         /\ equal (R.r h1) (R.r h2)
                                         /\ (a_equiv h1
                                            ==> (if l <= alpha then
                                                  R.l r = R.r r
                                                else
                                                  true))))

(* typing judgement  l |- c
   - references with a label below l are not modified
   - alpha equivalence on input heaps implies alpha equivalence on output
     heaps *)
type ni_com (l:label) =
              double unit ->
              ST2 (double unit)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 _ h2 -> (forall (y:ref int).
                                              label_fun y < l
                                              ==> sel (R.l h1) y = sel (R.l h2) y
                                               /\ sel (R.r h1) y = sel (R.r h2) y)
                                         /\ (a_equiv h1 ==> a_equiv h2)))

(* We define noninterference for a program as noninterference for commands with
   the label bottom *)
type ni = ni_com bot

(* This is needed due to typing problems with #377 *)
val convert_exp : l:label
               -> =e:(double unit
                 -> ST2 (double int)
                        (requires (fun h2 -> True))
                        (ensures  (fun h1 r h2 -> equal (R.l h1) (R.l h2)
                                               /\ equal (R.r h1) (R.r h2)
                                               /\ (a_equiv h1
                                                  ==> (if l <= alpha then
                                                        R.l r = R.r r
                                                      else
                                                        true))))) -> Tot (ni_exp l)
let convert_exp l e tu = e tu


val convert_com : l:label 
              ->  =e:(double unit ->
                  ST2 (double unit)
                      (requires (fun h2 -> True))
                      (ensures  (fun h1 _ h2 -> (forall (y:ref int).
                                                  label_fun y < l
                                                  ==> sel (R.l h1) y = sel (R.l h2) y
                                                   /\ sel (R.r h1) y = sel (R.r h2) y)
                                             /\ (a_equiv h1 ==> a_equiv h2)))) -> Tot (ni_com l)

let convert_com l c tu = c tu


(*********************** Typing Rules for Expressions **********************)

(* Subtyping rule for expression labels

         e : l1   l1 <= l2
         -----------------
             e : l2
*)
val sub_exp : l1:label -> l2:label{l1 <= l2} -> =e1:(ni_exp l1) -> Tot (ni_exp l2)
let sub_exp _ _ e1 tu = e1 tu

(* Typing rule for dereferencing

         label_fun(r) = l
         ----------------
             !r : l
*)
val deref_exp : r:ref int -> Tot (ni_exp (label_fun r)) 
let deref_exp r tu = compose2_self read (twice r) 
(* Typing rule for Int constants

         i : int
         -------
         i : bot
*)
val const_exp : int -> Tot (ni_exp bot)
let const_exp i tu = twice i

(* Typing rule for binary operators (we write the rule only for "+", but other
   binarry operators work analogously

          e1 : l   e2 : l
          ---------------
           e1 + e2  : l
*)
val bin_op_exp : l:label -> =e1:(ni_exp l) -> =e2:(ni_exp l)
(*            -> Tot (ni_exp l) *)
(* This is the above line inlined due to bug #377 ... *)
           -> double unit
           -> ST2 (double int)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 r h2 -> equal (R.l h1) (R.l h2)
                                         /\ equal (R.r h1) (R.r h2)
                                         /\ (a_equiv h1
                                            ==> (if l <= alpha then
                                                  R.l r = R.r r
                                                else
                                                  true))))
let bin_op_exp _ e1 e2 tu = compose2_self (fun (a, b) -> a + b) (pair_rel (e1 tu) (e2 tu))


(************************ Typing Rules for Commands ************************)

(* Subtyping rule for commands

         l1 |- c   l2 <= l1
         ------------------
              l2 |- c
*)
val sub_com : l1:label -> l2:label{l2 <= l1} -> =c1:(ni_com l1) -> Tot (ni_com l2)
let sub_com _ _ c1 tu = c1 tu

(* Typing rule for assignment
         e : l'      label_fun(r) = l'      l' >= l
         ------------------------------------------
                       l |- r := e
*)
val assign_com : r:ref int -> =e:ni_exp (label_fun r)
(*              -> Tot (ni_com (label_fun r) *)
(* This is the above line inlined due to bug #377 ... *)
          ->  double unit ->
              ST2 (double unit)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 _ h2 -> (forall (y:ref int).
                                              label_fun y < label_fun r
                                              ==> sel (R.l h1) y = sel (R.l h2) y
                                               /\ sel (R.r h1) y = sel (R.r h2) y)
                                         /\ (a_equiv h1 ==> a_equiv h2)))
let assign_com r e tu = compose2_self (write r) (e tu)

(* Sequencing rule for commands

         l |- c1    l |- c2
         ------------------
            l |- c1; c2
*)
val seq_com : l:label -> =c1:(ni_com l) -> =c2:(ni_com l)
(*             -> Tot(ni_com l) *)
(* This is the above line inlined due to bug #377 ... *)
          ->  double unit ->
              ST2 (double unit)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 _ h2 -> (forall (y:ref int).
                                              label_fun y < l
                                              ==> sel (R.l h1) y = sel (R.l h2) y
                                               /\ sel (R.r h1) y = sel (R.r h2) y)
                                         /\ (a_equiv h1 ==> a_equiv h2)))
let seq_com _ c1 c2 tu = let _ = c1 tu in c2 tu


(* Conditional rule for commands

         e : l     l |- ct      l |- cf
         ------------------------------
         l |- if e <> 0 then ct else cf
*)
val cond_com : l:label -> =e:(ni_exp l) -> =ct:(ni_com l) -> =cf:(ni_com l)
            -> Tot (ni_com l)
let cond_com _ e ct cf tu  = match e tu with
                             | R 0 0 -> cf tu
                             | R 0 _ -> cross cf ct
                             | R _ 0 -> cross ct cf
                             | R _ _ -> ct tu
                             


(* Typing rule for Skip

         -----------
         top |- skip
*)
val skip_com : ni_com top
let skip_com tu = tu

(* Loop case of a while loop *)
val loop_loop : l:label -> =e:(ni_exp l) -> =c:(ni_com l)
(*        -> Tot (ni_com l) *)
(* This fails because of bug #379 *)
           -> double unit ->
              ST2 (double unit)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 _ h2 -> (forall (y:ref int).
                                              label_fun y < l
                                              ==> sel (R.l h1) y = sel (R.l h2) y
                                               /\ sel (R.r h1) y = sel (R.r h2) y)
                                         /\ (a_equiv h1 ==> a_equiv h2)))

(* While rule for commands

         e : l               l |- c
         --------------------------
         l |- while (e <> 0) do {c}
*)
val loop_com : l:label -> =e:(ni_exp l) -> =c:(ni_com l)
(*            -> Tot (ni_com l) *)
(* This fails because of bug #379 *)
           -> double unit ->
              ST2 (double unit)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 _ h2 -> (forall (y:ref int).
                                              label_fun y < l
                                              ==> sel (R.l h1) y = sel (R.l h2) y
                                               /\ sel (R.r h1) y = sel (R.r h2) y)
                                         /\ (a_equiv h1 ==> a_equiv h2)))
let rec loop_com l e c tu =
                  match e tu with
                 | R 0 0 -> skip_com tu
                 | R 0 _ -> cross skip_com (loop_loop l e c)
                 | R _ 0 -> cross (loop_loop l e c) skip_com
                 | R _ _ -> loop_loop l e c tu
and loop_loop l e c tu = let _ = c tu in loop_com l e c tu


(****************************** IFC_Examples ******************************)

