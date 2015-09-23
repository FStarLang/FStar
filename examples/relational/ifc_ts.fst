(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 15;
    other-files:set.fsi heap.fst st.fst all.fst st2.fst noninterference.fst
  --*)

module IFC

(* We model a simple IFC Type system *)
open FStar.Comp
open FStar.Heap
open FStar.Relational

(****************************** Preliminaries ******************************)

(* We model labels with different levels as integers *)


(* A top label that is lower than all other lables *)
let top = 1000

(* A bottom label that is lower than all other lables *)
let bot = - top

type label = l:int{bot <= l /\ l <= top}

(* Label of the attacker *)
assume val alpha : label


(* A global labeling function (assigns a label to every reference) *)
assume val label_fun : ref int -> Tot label

(* A reference can be observed bu the attacker if its label is not higher than
   alpha *)
let attacker_observable x = label_fun x <= alpha

(* We have alpha equivalence when two heaps are equal for all references that
  have a label <= alpha and thus are observable by the attacker *)
type a_equiv (h1:double heap) = (forall (x:ref int). attacker_observable x 
                                                   ==> sel (R.l h1) x = sel (R.r h1) x) 

(* Function to create new labeled references *)
assume val new_labeled_int : l:label -> x:ref int{label_fun x = l}


(**************************** Typing Judgements ****************************)

(* typing judgement  e : l 
   - Expressions do not modify the heap 
   - If we have alpha equivalence on the input heaps, then the results must be
     equal if the expression label is lower than or equal to alpha *)
type ni_exp (l:label) =
              unit -> 
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
              unit -> 
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


(*********************** Typing Rules for Expressions **********************)

(* Subtyping rule for expression labels 

         e : l1   l1 <= l2
         -----------------
             e : l2
*)
val sub_exp : l1:label -> l2:label{l1 <= l2} -> =e1:(ni_exp l1) -> Tot (ni_exp l2)
let sub_exp _ _ e1 () = e1 ()

(* Typing rule for dereferencing

         label_fun(r) = l
         ----------------
             !r : l
*)
val deref_exp : r:ref int 
(*            -> Tot (ni_exp (label_fun r)) *)
(* This is the above line inlined due to bug #377 ... *)
           -> unit 
           -> ST2 (double int)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 res h2 -> equal (R.l h1) (R.l h2)
                                           /\ equal (R.r h1) (R.r h2)
                                           /\ (a_equiv h1
                                              ==> (if (label_fun r) <= alpha then 
                                                    R.l res = R.r res
                                                  else 
                                                  true))))
let deref_exp r () = compose2_self read (twice r)

(* Typing rule for Int constants

         i : int 
         -------
         i : bot 
*)
val const_exp : int -> Tot (ni_exp bot)
let const_exp i () = twice i

(* Typing rule for binary operators (we write the rule only for "+", but other
   binarry operators work analogously
 
          e1 : l   e2 : l 
          ---------------
           e1 + e2  : l2
*)
val bin_op_exp : l:label -> =e1:(ni_exp l) -> =e2:(ni_exp l) 
(*            -> Tot (ni_exp l) *)
(* This is the above line inlined due to bug #377 ... *)
           -> unit 
           -> ST2 (double int)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 r h2 -> equal (R.l h1) (R.l h2)
                                         /\ equal (R.r h1) (R.r h2)
                                         /\ (a_equiv h1
                                            ==> (if l <= alpha then 
                                                  R.l r = R.r r 
                                                else 
                                                  true))))
let bin_op_exp _ e1 e2 () = compose2_self (fun (a, b) -> a + b) (pair_rel (e1 ()) (e2 ()))


(************************ Typing Rules for Commands ************************)

(* Subtyping rule for commands

         l1 |- c   l2 <= l1
         ------------------
              l2 |- c 
*)
val sub_com : l1 : label -> l2:label{l2 <= l1} -> =c1:(ni_com l1) -> Tot (ni_com l2)
let sub_com _ _ c1 () = c1 () 

(* Typing rule for assignment 
         e : l'      label_fun(r) = l'      l' >= l
         ------------------------------------------
                       l |- r := e 
*)
val assign_com : l:label -> l':label{l' >= l} -> r:ref int{label_fun r = l'} -> =e:ni_exp l' 
(*              -> Tot (ni_com l) *)
(* This is the above line inlined due to bug #377 ... *)
          ->  unit -> 
              ST2 (double unit)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 _ h2 -> (forall (y:ref int). 
                                              label_fun y < l 
                                              ==> sel (R.l h1) y = sel (R.l h2) y
                                               /\ sel (R.r h1) y = sel (R.r h2) y)
                                         /\ (a_equiv h1 ==> a_equiv h2)))
let assign_com _ _ r e () = compose2_self (write r) (e ())

(* Sequencing rule for commands

         l |- c1    l |- c2
         ------------------
            l |- c1; c2 
*)
val seq_com : l:label -> =c1:(ni_com l) -> =c2:(ni_com l) 
(*             -> Tot(ni_com l) *)
(* This is the above line inlined due to bug #377 ... *)
          ->  unit -> 
              ST2 (double unit)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 _ h2 -> (forall (y:ref int). 
                                              label_fun y < l 
                                              ==> sel (R.l h1) y = sel (R.l h2) y
                                               /\ sel (R.r h1) y = sel (R.r h2) y)
                                         /\ (a_equiv h1 ==> a_equiv h2)))
let seq_com _ c1 c2 () = let _ = c1 () in c2 ()

(* This is used for cross cases (TODO: is this sound?)*)
assume val cross : #p:(heap2 -> heap2 -> Type) 
                -> #q:(heap2 -> heap2 -> Type) 
                -> =c1:(unit -> ST2 (double unit) (requires (fun h -> True)) (ensures (fun h1 _ h2 -> p h1 h2))) 
                -> =c2:(unit -> ST2 (double unit) (requires (fun h -> True)) (ensures (fun h1 _ h2 -> q h1 h2))) 
                -> ST2 (double unit) (requires (fun h -> True)) 
                                     (ensures (fun h1 _ h2 -> (exists (h2l:heap) (h2r:heap). p h1 (R (R.l h2) (h2r)) 
                                                                                          /\ q h1 (R h2l (R.r h2)))))

(* Conditional rule for commands

         e : l     l |- ct      l |- cf    
         ------------------------------
         l |- if e <> 0 then ct else cf
*)
  val cond : l:label -> =e:(ni_exp l) -> =ct:(ni_com l) -> =cf:(ni_com l) 
           -> Tot (ni_com l)
let cond _ e ct cf ()  = match e () with 
                         | R 0 0 -> cf ()
                         | R 0 _ -> cross cf ct
                         | R _ 0 -> cross ct cf 
                         | R _ _ -> ct ()

(* Typing rule for Skip

         -----------
         top |- skip
*)
val skip : ni_com top
let skip () = twice ()

(* Loop case of a while loop *)
val loop_loop : l:label -> =e:(ni_exp l) -> =c:(ni_com l) 
(*        -> Tot (ni_com l) *)
(* This fails because of bug #379 *)
           -> unit -> 
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
           -> unit -> 
              ST2 (double unit)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 _ h2 -> (forall (y:ref int). 
                                              label_fun y < l 
                                              ==> sel (R.l h1) y = sel (R.l h2) y
                                               /\ sel (R.r h1) y = sel (R.r h2) y)
                                         /\ (a_equiv h1 ==> a_equiv h2)))
let rec loop_com l e c () = 
                  match e () with 
                 | R 0 0 -> skip ()
                 | R 0 _ -> cross skip (loop_loop l e c)
                 | R _ 0 -> cross (loop_loop l e c) skip
                 | R _ _ -> loop_loop l e c ()
and loop_loop l e c () = let _ = c () in loop_com l e c ()



(****************************** IFC_Examples ******************************)

module IFC_Example1 
open Distinct 
open IFC
open FStar.Comp
open FStar.Relational

(* Fails iff label b > label a *)
let a = new_labeled_int 1
let b = new_labeled_int 0

assume Distinct : distinct2 a b

let test () = (if !b <> 0 then
                 a := 1
               else
                 a := 2);
               b := 0

(* Brute Force Approach *)
val test_ni : ni
let test_ni _ = compose2_self test (twice ())

(* Following the typing derivation *)

(* !b : 0 *)
val ni_exp_deref_b : ni_exp 0
let ni_exp_deref_b () = (deref_exp b) ()

(* 1 : bot *)
val ni_exp_1 : ni_exp bot
let ni_exp_1 () = (const_exp 1) ()

(* 1 : 1 *)
val ni_exp_1' : ni_exp 1
let ni_exp_1' = sub_exp bot 1 ni_exp_1

(* 0 |- a := 1 *)
val ni_com_a_1: ni_com 0
let ni_com_a_1 () = (assign_com 0 1 a ni_exp_1') ()

(* 2 : bot *)
val ni_exp_2 : ni_exp bot
let ni_exp_2 () = (const_exp  2) ()

(* 2 : 1 *)
val ni_exp_2' : ni_exp 1
let ni_exp_2' = sub_exp bot 1 ni_exp_2

(* 0 |- a := 2 *)
val ni_com_a_2: ni_com 0
let ni_com_a_2 () = (assign_com 0 1 a ni_exp_2') ()

(* 0 |- if (!b <> 0) then a := 1 else a := 2 *)
val ni_com_cond : ni_com 0 
let ni_com_cond = cond 0 ni_exp_deref_b ni_com_a_1 ni_com_a_2

(* bot |- if (!b <> 0) then a := 1 else a := 2 *)
val ni_com_cond' : ni_com bot
let ni_com_cond' = sub_com 0 bot ni_com_cond

(* 2 : bot *)
val ni_exp_0 : ni_exp bot
let ni_exp_0 () = (const_exp 0) ()

(* 2 : 0 *)
val ni_exp_0' : ni_exp 0
let ni_exp_0' = sub_exp bot 0 ni_exp_0

(* bot |- b := 0 *)
val ni_com_b : ni_com bot
let ni_com_b () = (assign_com bot 0 b ni_exp_0') ()

(* bot |- if (!b <> 0) then a := 1 else a := 2; b := 0 *)
val ni_com_seq : ni_com bot
let ni_com_seq () = (seq_com bot ni_com_cond' ni_com_b) ()

(* Noninterference result for the complete program *)
val ni_programm : ni
let ni_programm () = ni_com_seq ()



module IFC_Example3
open IFC
open FStar.Comp
open FStar.Relational
open Distinct

assume val la : label
assume val lb : lb:label{lb <= la}
assume val lc : lc:label{lc <= la}

let a = new_labeled_int la
let b = new_labeled_int lb
let c = new_labeled_int lc

assume Distinct : distinct3 a b c

let test () = a:= !b + !c

(* Brute Force Approach *)
val test_ni : ni
let test_ni _ = compose2_self test (twice ())

(* Following the typing derivation *)

(* !b : lb *)
val ni_exp_deref_b : ni_exp lb
let ni_exp_deref_b () = (deref_exp b) ()

(* !b : la *)
val ni_exp_deref_b' : ni_exp la
let ni_exp_deref_b' () = (sub_exp lb la ni_exp_deref_b) ()

(* !c : lc *)
val ni_exp_deref_c : ni_exp lc
let ni_exp_deref_c () = (deref_exp c) ()

(* !c : la *)
val ni_exp_deref_c' : ni_exp la
let ni_exp_deref_c' () = (sub_exp lc la ni_exp_deref_c) ()

(* !b + !c : la *)
val ni_exp_a : ni_exp la
let ni_exp_a () = (bin_op_exp la ni_exp_deref_b' ni_exp_deref_c') ()

(* bot |- a := !b + !c *)
val ni_com_a: ni_com bot 
let ni_com_a () = (assign_com bot la a ni_exp_a) ()

(* Noninterference result for the complete program *)
val ni_program : ni
let ni_program () = ni_com_a () 


module IFC_Example5
open IFC
open FStar.Comp
open FStar.Relational
open FStar.Heap
open Distinct

assume val la : label
assume val lb : lb:label{lb >= la}
assume val lc : lc:label

let a = new_labeled_int la
let b = new_labeled_int lb
let c = new_labeled_int lc

assume Distinct : distinct3 a b c

(* This val-declaration is necessary (otherwise: FStar does not infer ST, but ALL) *)
val loop : unit -> ST unit (requires (fun _ -> True))
                           (ensures  (fun h r h' -> ((sel h a) = 0 ==> equal h h')
                                                 /\ ((sel h a) <> 0  ==> equal h' (upd (upd h b ((sel h b) + (sel h a))) a 0))))
let rec loop () = if !a <> 0 then (a := !a + -1; b := !b + 1; loop ())

let test () = loop ();
              c := 0

(* Brute Force Approach *)
val test_ni : ni
let test_ni _ = compose2_self test (twice ())

(* Following the typing derivation *)

(* !a : la *)
val ni_exp_deref_a : ni_exp la
let ni_exp_deref_a () = (deref_exp a) ()

(* -1 : bot *)
val ni_exp__1 : ni_exp bot
let ni_exp__1 () = (const_exp (-1)) ()

(* -1 : la *)
val ni_exp__1a : ni_exp la
let ni_exp__1a () = (sub_exp bot la ni_exp__1) ()

(* !a + -1 : la *)
val ni_exp_a : ni_exp la
let ni_exp_a () = (bin_op_exp la ni_exp_deref_a ni_exp__1a) ()

(* la |- a := !a + -1  *)
val ni_com_a : ni_com la
let ni_com_a () = (assign_com la la a ni_exp_a) ()

(* !b : lb *)
val ni_exp_deref_b : ni_exp lb
let ni_exp_deref_b () = (deref_exp b) ()

(* 1 : bot *)
val ni_exp_1 : ni_exp bot
let ni_exp_1 () = (const_exp 1) ()

(* 1 : lb *)
val ni_exp_1b : ni_exp lb
let ni_exp_1b () = (sub_exp bot lb ni_exp_1) ()

(* !b + 1 : lb *)
val ni_exp_b : ni_exp lb
let ni_exp_b () = (bin_op_exp lb ni_exp_deref_b ni_exp_1b) ()

(* la |- !b + 1 *)
val ni_com_b : ni_com la
let ni_com_b () = (assign_com la lb b ni_exp_b) ()

(* la |- a := !a + -1; b := !b + 1 *)
val ni_com_loop_body : ni_com la
let ni_com_loop_body () = (seq_com la ni_com_a ni_com_b) ()

(* la |- while !a <> 0 {a := !a + -1; b := !b + 1} *)
val ni_com_loop : ni_com la
let ni_com_loop () = (loop_com la ni_exp_deref_a ni_com_loop_body) ()

(* bot |- while !a <> 0 {a := !a + -1; b := !b + 1} *)
val ni_com_loop' : ni_com bot
let ni_com_loop' () = (sub_com la bot ni_com_loop) ()

(* 0 : bot *)
val ni_exp_0 : ni_exp bot
let ni_exp_0 () = (const_exp 0) ()

(* 0 : lc *)
val ni_exp_0' : ni_exp lc
let ni_exp_0' () = (sub_exp bot lc ni_exp_0) ()

(* bot |- c := 0 *)
val ni_com_c : ni_com bot
let ni_com_c () = (assign_com bot lc c ni_exp_0') ()

(* Noninterference for the complete program *)
val ni_program : ni 
let ni_program () = (seq_com bot ni_com_loop' ni_com_c) ()
