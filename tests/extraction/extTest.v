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


Inductive list3 : Type -> Type :=
| Nil3 : forall (a:Type), list3 a
| Cons3 : forall (a:Type), a -> list3 a -> list3 (prod a a).


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


(*
Looks like Haskell is more general. type vars need not be of type type.
Here is an example from 
http://learnyouahaskell.com/making-our-own-types-and-typeclasses#kinds-and-some-type-foo

data Frank a b  = Frank {frankField :: b a} deriving (Show)  

However, Coq's extraction does not yet take advantage of that, because the core of extraction
is independent of these differences in target dialects


Extraction Language Haskell.
Recursive Extraction polylist.

*)


(*
Infact, the example above (Haskell extraction of polylist) seems to indicate an orthogonal bug in extraction 
from Coq to Haskell. 
In OCaml, the argument to list is Obj.t, which makes sense.
However, in Haskell. the argument is unit, which can cause type errors later on, similar to
the errors observed in ROSCoq:

https://github.com/aa755/ROSCoq/commit/972ed9d26ac642499e60098cf0510ee9b6e0d3ea#diff-f9928ac6597fcd7e0cfbf7e9da0cdba9L2376
*)



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


(*Can Prop be extracted as unit? It seems odd because Props may be uninhabited. 
  It seems OCaml does not have any uninhabited type.
  But that oddness might not matter as far as results(and possibly effects) of computation are concerned *)


Definition pair (a:Type) (a':Type) := prod a a'.

Recursive Extraction pair.

Inductive void := .
Recursive Extraction void.

Inductive erased (T:Type) : Prop := 
| hide : T -> erased T.



Definition unhide {T :Type} {R:Prop} (g : erased T) (f: T -> R) : R.
  destruct g.
  apply f. assumption.
Defined.

Definition pi1 (a:nat) (b:nat) (c: erased nat) : nat := a.


Recursive Extraction pi1.



Definition elift1 {T R :Type} (f: T -> R) (g : erased T) : erased R.
  destruct g. apply hide.
  apply f. assumption.
Defined.


Definition GS : (erased nat) -> erased nat :=
(elift1 S).


Inductive listOfSize {C:Type} : (list C) -> (erased nat) -> Prop :=
| lsnil : listOfSize nil (hide _ 0)
| lscons : forall (l: list C) (c:C) (n: erased nat), listOfSize l n -> (listOfSize (c::l) (GS n)) .

Definition sizedList (C:Type): Type := {size : erased nat & {l : list C | listOfSize l size}}.


Definition aSizedList : sizedList nat.
  exists (GS (hide _ 0)).
  exists (cons 1 nil).
  constructor. constructor.
Defined.

Recursive Extraction aSizedList.
 
(* Coq's extraction seems to ignore the effectful OCaml realization of variables*)


Variable effectfulIncr : nat -> nat.

Definition someNat (n:nat) : nat :=
let _ := hide _ (effectfulIncr n) in n.


Recursive Extraction someNat. (*the call to effectfulIncr vanishes*)
