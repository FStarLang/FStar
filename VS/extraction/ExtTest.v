Inductive isEven : nat -> Type :=
| ev0 : isEven 0
| evSS : forall n:nat, isEven n -> isEven (S (S n)).

Check isEven.

Definition anEvenNumber : sigT isEven.
exists 0. constructor.
Defined.


Recursive Extraction anEvenNumber.


(** The result of this computation cannot depend on h, because one cannot analyse (destruct) a Type
   in any computation .*)
Definition hello  (h: nat -> Type) : nat := 0.

(** So it makes sense that it got truncated, as predicted by the algorithm in the thesis *)
Recursive Extraction hello.


(** Just to makes sure that Coq is doing an unused argument analysis.*)
Definition hello2  (h: nat -> nat) : nat := 0.

(** the unused argument did not get removed in this case. It has a type whose members can potentially be used
  in computations. Again this is what the algorithm in the thesis predicts *)
Recursive Extraction hello2.


(* homogenous, but non-type parameter *)

Inductive isEven2 : nat -> Type :=
| ev02 : isEven2 0
| evSS2 : forall n:nat, isEven2 n -> isEven2 n.

(* nat gets removed *)
Recursive Extraction isEven2.

(* sanity check *)
Inductive isEven3 : Type -> Type :=
| ev03 : isEven3 nat
| evSS3 : forall n:nat, isEven3 nat -> isEven3 nat.

(* the dummy type argument does not get removed*)
Recursive Extraction isEven3.




