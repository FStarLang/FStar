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
Recursive Extraction nat.

(* sanity check *)
Inductive isEven3 : Type -> Type :=
| ev03 : isEven3 nat
| evSS3 : forall n:nat, isEven3 nat -> isEven3 nat.

(* the dummy type argument does not get removed*)
Recursive Extraction isEven3.



Definition f := (fun (A:Type) (x:A) => x) nat 0.

Recursive Extraction f.

Definition fb (b:bool) := (if b then (fun (A:Type) (x:A) => x) else (fun (A:Type) (x:A)=>x) ) nat 0.
Definition fc (b:bool) := (if b then (fun (A:Type) (x:A) (y:A) => x) else (fun (A:Type) (x:A) (y:A) =>y) ) nat 0 1.

Recursive Extraction fb fc.

Definition idvar := fun X:Type => X -> X.

Definition idtype := forall (X:Type), X -> X.

Check idvar.
Check idtype.

Definition id : idtype := fun X x => x. 


Definition idu : unit -> idtype := fun u X x => x. 

Extract Inductive unit => unit [ "()" ].

Recursive Extraction idvar idtype id idu.


Inductive  poly (x : nat -> Type) :=
| Poly :  forall (n:nat), x n -> poly x.

Inductive vec (A:Type) : nat -> Type :=
| vnil : vec A 0
| vcons : forall n, A -> (vec A n) -> (vec A (S n)).


Definition polyvec := poly (vec nat).


Inductive  poly2 (x : Type -> Type) : Type :=
     | Poly2 :  forall (t:Type), x t -> poly2 x.


Definition polylist := poly2 list.


Definition listalias (A:Type) := list A.

Definition polylistalias := poly2 (listalias).

Definition polylistnat : polylist.
  exists nat. exact (cons 1 nil).
Defined.


Definition polylistbool : polylist.
  exists bool. exact (cons true nil).
Defined.



Recursive Extraction polylistnat polylistbool polylistalias.


Inductive  poly3 (x : Type -> Type) : Type :=
     | Poly3 :  x nat -> poly3 x.

Recursive Extraction polyvec polylist poly3.

Definition poly3list : Type := poly3 list.

Recursive Extraction poly3list poly2.

Definition vecn := vec nat.
Definition vecn' := fun n => vec nat n.

Recursive Extraction vecn vecn'.

Inductive naryTree (T:Type) (n:nat) :=
| leaf : naryTree T n
| node : vec (naryTree T n) n -> (naryTree T n).


Definition binaryTree (T:Type) := naryTree T 2.

Recursive Extraction naryTree binaryTree.
 
Definition consalias := cons.
Definition cons0  := cons 0.

Recursive Extraction consalias cons0.


(* Coq's extraction seems to ignore the effectful OCaml reaslization of variables*)


Variable effectfulIncr : nat -> nat.

Definition someNat : nat :=
let _ : Prop := (effectfulIncr 0 = effectfulIncr (S 0)) in 0.

Recursive Extraction someNat. (*the call to effectfulIncr vanishes*)

(*Can Prop be extracted as unit? It seems odd because Props may be uninhabited. 
  It seems OCaml does not have any uninhabited type.
  But that oddness might not matter as far as results(and possibly effects) of computation are concerned *)


Definition pair (a:Type) (a':Type) := prod a a'.

Recursive Extraction pair.

Inductive void := .
Recursive Extraction void.