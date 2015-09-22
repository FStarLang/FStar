(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 15;
    other-files:set.fsi heap.fst st.fst all.fst st2.fst
  --*)

module IFC

open FStar.Comp
open FStar.Heap
open FStar.Relational

(* We model labels with different levels as integers *)
type label = int

(* Label of the attacker *)
assume val alpha : label
assume val bot : bot:label{forall (l:label). bot <= l}

(* Labeling function (assigns a label to every reference) *)
assume val label_fun : ref int -> Tot label

(* A reference can be observed bu the attacker if its label is not higher than
   alpha *)
let attacker_observable x = label_fun x <= alpha

type alpha_equiv (h1:double heap) = (forall (x:ref int). attacker_observable x 
                                                   ==> sel (R.l h1) x = sel (R.r h1) x) 

(* typing jugdement  e : l *)
type ni_exp (l:label) =
              unit -> 
              ST2 (double int)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 r h2 -> alpha_equiv h1
                                          ==>(equal (R.l h1) (R.l h2)
                                            /\equal (R.r h1) (R.r h2)
                                            /\ (if l <= alpha then 
                                                 R.l r = R.r r 
                                               else 
                                                 true))))

type com (l:label) = unit 
                    -> ST unit 
                       (requires (fun h -> True))
                       (ensures  (fun h1 r h2 ->
                                       (forall (y:ref int). 
                                        label_fun y <= l 
                                        ==> sel h1 y = sel h2 y)))


(* typing jugdement  l |- c *)
type ni_com (l:label) =
              unit -> 
              ST2 (double unit)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 _ h2 -> alpha_equiv h1
                                            ==> (alpha_equiv h2
                                             /\ (forall (y:ref int). 
                                                label_fun y <= l 
                                                ==> sel (R.l h1) y = sel (R.l h2) y
                                                 /\ sel (R.r h1) y = sel (R.r h2) y))))

(*
val test : l:label -> com l -> Tot (ni_com l)
let test _ c = fun () -> compose2_self c (twice ())
*)


(* Subtyping rule for expression labels 

         e : l1   l1 <= l2
         -----------------
             e : l2
*)
val sub_exp : l1:label -> l2:label{l1 <= l2} -> e1:(ni_exp l1) -> Tot (ni_exp l2)
let sub_exp _ _ e1 = fun () -> e1 ()

(* Typing rule for dereferencing

         label_fun(r) = l
         ----------------
             !r : l
*)
val ref_exp : r:ref int 
(*            -> Tot (ni_exp (label_fun r)) *)
(* This is the above line inlined due to bug #377 ... *)
           -> Tot (unit -> ST2 (double int) 
                           (requires (fun _ -> True))
                  (ensures  (fun h1 res h2 -> alpha_equiv h1 
                                          ==>(equal (R.l h1) (R.l h2)
                                            /\equal (R.r h1) (R.r h2)
                                            /\ (if (label_fun r) <= alpha then 
                                                 R.l res = R.r res 
                                               else 
                                                 true)))))
let ref_exp r = fun () -> compose2_self (fun () -> (!r)) (twice ())

(* Typing rule for Int constants

         i : int 
         -------
         i : bot 
*)
val const_exp : int -> Tot (ni_exp bot)
let const_exp i = fun () -> twice i



(* Typing rule for binary operators 
 
          e1 : l   e2 : l 
          ---------------
           e1 + e2  : l2
*)
val expr : l:label -> e1:(ni_exp l) -> e2:(ni_exp l) 
(*            -> Tot (ni_exp l) *)
(* This is the above line inlined due to bug #377 ... *)
           -> Tot (unit -> ST2 (double int) 
                           (requires (fun _ -> True))
                  (ensures  (fun h1 r h2 -> alpha_equiv h1 
                                          ==>(equal (R.l h1) (R.l h2)
                                            /\equal (R.r h1) (R.r h2)
                                            /\ (if l <= alpha then 
                                                 R.l r = R.r r 
                                               else 
                                                 true)))))
let expr _ e1 e2 = (fun () -> compose2_self (fun (a, b) -> a + b) (pair_rel (e1 ()) (e2 ())))

(* Subtyping rule for commands

         l1 |- c   l2 <= l1
         ------------------
              l2 |- c 
*)
val sub_comp : l1 : label -> l2:label{l2 <= l1} -> c1:(ni_com l1) -> Tot (ni_com l2)
let sub_comp _ _ c1 = fun () -> c1 () 


(* Rule for assignment 
         e : l'      label_fun(r) = l'      l' > l
         ------------------------------------------
                       l |- r := e 
*)
val assign : l:label -> l':label{l' > l} -> r:ref int{label_fun r = l'} -> e:ni_exp l' 
       //      -> Tot (ni_com l)
(* This is the above line inlined due to bug #377 ... *)
       -> Tot (unit -> 
              ST2 (double unit)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 _ h2 -> alpha_equiv h1
                                            ==> (alpha_equiv h2
                                             /\ (forall (y:ref int). 
                                                label_fun y <= l 
                                                ==> sel (R.l h1) y = sel (R.l h2) y
                                                 /\ sel (R.r h1) y = sel (R.r h2) y))))) 
let assign _ _ r e = fun () -> compose2_self (fun x -> r := x) (e ())



(* Sequencing rule for commands

         l |- c1    l |- c2
         ------------------
            l |- c1; c2 
*)
val seq : l:label -> c1:(ni_com l) -> c2:(ni_com l) 
(*             -> Tot(ni_com l) *)
(* This is the above line inlined due to bug #377 ... *)
       -> Tot (unit -> 
              ST2 (double unit)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 _ h2 -> alpha_equiv h1
                                            ==> (alpha_equiv h2
                                             /\ (forall (y:ref int). 
                                                label_fun y <= l 
                                                ==> sel (R.l h1) y = sel (R.l h2) y
                                                 /\ sel (R.r h1) y = sel (R.r h2) y))))) 
let seq _ c1 c2 = (fun () -> let _ = c1 () in c2 ())



(* This is used for cross cases (TODO: is this sound?)*)
assume val cross : #p:(heap2 -> heap2 -> Type) 
                -> #q:(heap2 -> heap2 -> Type) 
                -> =c1:(unit -> ST2 (double unit) (requires (fun h -> True)) (ensures (fun h1 _ h2 -> p h1 h2))) 
                -> =c2:(unit -> ST2 (double unit) (requires (fun h -> True)) (ensures (fun h1 _ h2 -> q h1 h2))) 
                -> ST2 (double unit) (requires (fun h -> True)) (ensures (fun h1 _ h2 -> (exists (h2l:heap) (h2r:heap). p h1 (R (R.l h2) (h2r)) 
                                                                                                                     /\ q h1 (R h2l (R.r h2)) )))

(* Conditional rule for commands

         e : l     l |- ct     l |- cf    
         -----------------------------
           l |- if e then ct else cf
*)
val cond : l:label -> e:(ni_exp l) -> ct:(ni_com l) -> cf:(ni_com l) 
           -> Tot (ni_com l)
let cond _ e ct cf = (fun () -> match e () with 
                     | R 0 0 -> cf ()
                     | R 0 _ -> cross cf ct
                     | R _ 0 -> cross ct cf 
                     | R _ _ -> ct ())




val skip : unit -> ST2 (double unit) (requires (fun h -> True)) (ensures (fun h1 _ h2 -> equal (R.l h1) (R.l h2) /\ equal (R.r h1) (R.r h2)))
let skip () = twice ()

val loop_loop : l:label -> e:(ni_exp l) -> c:(ni_com l) 
     //  -> Tot (ni_com l)
(* This fails because of bug #379 *)
       -> unit -> 
              ST2 (double unit)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 _ h2 -> alpha_equiv h1
                                            ==> (alpha_equiv h2
                                             /\ (forall (y:ref int). 
                                                label_fun y <= l 
                                                ==> sel (R.l h1) y = sel (R.l h2) y
                                                 /\ sel (R.r h1) y = sel (R.r h2) y))))

(* While rule for commands

         e : l        l |- c
         -------------------
         l |- wihle e do {c}
*)
val loop : l:label -> e:(ni_exp l) -> c:(ni_com l) 
          // -> Tot (ni_com l)
(* This fails because of bug #379 *)
       -> unit -> 
              ST2 (double unit)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 _ h2 -> alpha_equiv h1
                                            ==> (alpha_equiv h2
                                             /\ (forall (y:ref int). 
                                                label_fun y <= l 
                                                ==> sel (R.l h1) y = sel (R.l h2) y
                                                 /\ sel (R.r h1) y = sel (R.r h2) y))))
let rec loop l e c = 
                (fun () -> match e () with 
                 | R 0 0 -> twice ()
                 | R 0 _ -> cross skip (loop_loop l e c)
                 | R _ 0 -> cross (loop_loop l e c) skip
                 | R _ _ -> loop_loop l e c ())
and loop_loop l e c = fun () -> let _ = c () in loop l e c ()

