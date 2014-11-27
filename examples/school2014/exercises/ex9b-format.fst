module Format
open Prims.PURE
open String
open Array

type message = seq byte
type msg (l:nat) = m:message{length m==l}

(* ----- two lemmas on array append *) 

(* Here's a small proof that append is injective. 
   To use this property, you have to explicitly call 
   append_inj yourself (with an implicit first arg) *)

val append_inj: #l:nat
               -> b1:msg l -> b2:message
               -> c1:msg l -> c2:message{append b1 b2==append c1 c2}
               -> Lemma (ensures (Equal b1 c1 /\ Equal b2 c2))
let rec append_inj l b1 b2 c1 c2 = match l with
  | 0 -> ()
  | _ -> append_inj #(l - 1) (slice b1 1 l) b2 (slice c1 1 l) c2

(* The same proof again, 
   But, if you give it a "Lemma" type the solver 
   will use the lemma as needed to prove other goals. *)

val append_inj_lemma: b1:message -> b2:message
                   -> c1:message -> c2:message
                   -> Lemma (requires (length b1==length c1 /\ append b1 b2==append c1 c2))
                            (ensures (Equal b1 c1 /\ Equal b2 c2))
                            (decreases (length b1))
                            [SMTPat (append b1 b2); SMTPat (append c1 c2)] 

let rec append_inj_lemma b1 b2 c1 c2 =
  let l = length b1 in 
  match l with
  | _ -> admit() (* prove this lemma *)

              
