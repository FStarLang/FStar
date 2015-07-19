(* extracting the type of constructor O
([], MLTY_Named ([],(["Test"], "nnat"))) *)

(* extracting the type of constructor S
([],
 MLTY_Fun
   (MLTY_Named ([],(["Test"], "nnat")),MayErase,
    MLTY_Named ([],(["Test"], "nnat")))) *)


 (*needed to coerce expression 
 MLE_Fun
  ([(("_1_788", 0), Some (MLTY_Named ([],(["Prims"], "unit"))));
    (("x", 0), Some (MLTY_Var ("a", 0)))],MLE_Var ("x", 0)) 
 of type 
 MLTY_Fun
  (MLTY_Var ("a", 0),MayErase,
   MLTY_Fun (MLTY_Named ([],(["Prims"], "unit")),MayErase,MLTY_Var ("a", 0))) 
 to type 
 MLTY_Fun
  (MLTY_Named ([],(["Prims"], "unit")),Keep,
   MLTY_Fun (MLTY_Var ("a", 0),Keep,MLTY_Var ("a", 0))) *) 


 (*needed to coerce expression 
 MLE_Fun
  ([(("_1_788", 0), Some (MLTY_Named ([],(["Prims"], "unit"))));
    (("x", 0), Some MLTY_Top)],MLE_Var ("x", 0)) 
 of type 
 MLTY_Fun
  (MLTY_Top,MayErase,
   MLTY_Fun (MLTY_Named ([],(["Prims"], "unit")),MayErase,MLTY_Top)) 
 to type 
 MLTY_Fun
  (MLTY_Named ([],(["Prims"], "unit")),Keep,MLTY_Fun (MLTY_Top,Keep,MLTY_Top)) *) 

(* extracting the type of constructor Pair
([("'a", 0); ("'b", 0)],
 MLTY_Fun
   (MLTY_Var ("'a", 0),MayErase,
    MLTY_Fun
      (MLTY_Var ("'b", 0),MayErase,
       MLTY_Named ([MLTY_Var ("'a", 0); MLTY_Var ("'b", 0)],(["Test"], "prod"))))) *)

(* extracting the type of constructor Nil
([("'a", 0)], MLTY_Named ([MLTY_Var ("'a", 0)],(["Test"], "list"))) *)

(* extracting the type of constructor Cons
([("'a", 0)],
 MLTY_Fun
   (MLTY_Var ("'a", 0),MayErase,
    MLTY_Fun
      (MLTY_Named ([MLTY_Var ("'a", 0)],(["Test"], "list")),MayErase,
       MLTY_Named ([MLTY_Var ("'a", 0)],(["Test"], "list"))))) *)


 (*needed to coerce expression 
 MLE_Name (["Test"], "O") 
 of type 
 MLTY_Named ([],(["Test"], "nnat")) 
 to type 
 MLTY_Top *) 


 (*needed to coerce expression 
 MLE_Var ("tll", 0) 
 of type 
 MLTY_Named ([MLTY_Named ([],(["Test"], "nnat"))],(["Test"], "list")) 
 to type 
 MLTY_Named ([MLTY_Top],(["Test"], "list")) *) 


 (*needed to coerce expression 
 MLE_Fun
  ([(("tll", 0),
     Some (MLTY_Named ([MLTY_Named ([],(["Test"], "nnat"))],(["Test"], "list"))))],
   MLE_App
     (MLE_Name (["Test"], "Cons"),
      [MLE_Coerce
         (MLE_Name (["Test"], "O"),MLTY_Named ([],(["Test"], "nnat")),MLTY_Top);
       MLE_Coerce
         (MLE_Var ("tll", 0),
          MLTY_Named ([MLTY_Named ([],(["Test"], "nnat"))],(["Test"], "list")),
          MLTY_Named ([MLTY_Top],(["Test"], "list")))])) 
 of type 
 MLTY_Fun
  (MLTY_Named ([MLTY_Named ([],(["Test"], "nnat"))],(["Test"], "list")),Keep,
   MLTY_Named ([MLTY_Top],(["Test"], "list"))) 
 to type 
 MLTY_Fun
  (MLTY_Named ([MLTY_Named ([],(["Test"], "nnat"))],(["Test"], "list")),Keep,
   MLTY_Named ([MLTY_Named ([],(["Test"], "nnat"))],(["Test"], "list"))) *) 

(* extracting the type of constructor Nil2
([("'a", 0); ("'b", 0)],
 MLTY_Named ([MLTY_Var ("'a", 0); MLTY_Var ("'b", 0)],(["Test"], "list2"))) *)

(* extracting the type of constructor Cons2
([("'a", 0); ("'b", 0)],
 MLTY_Fun
   (MLTY_Var ("'a", 0),MayErase,
    MLTY_Fun
      (MLTY_Var ("'b", 0),MayErase,
       MLTY_Fun
         (MLTY_Named
            ([MLTY_Var ("'a", 0); MLTY_Var ("'b", 0)],(["Test"], "list2")),
          MayErase,
          MLTY_Named
            ([MLTY_Var ("'a", 0); MLTY_Var ("'b", 0)],(["Test"], "list2")))))) *)

(* extracting the type of constructor Any
([],
 MLTY_Fun
   (MLTY_Named ([],([], "unit")),MayErase,
    MLTY_Fun (MLTY_Top,MayErase,MLTY_Named ([],(["Test"], "any"))))) *)

(* extracting the type of constructor Nil2p
([("'a", 0)], MLTY_Named ([MLTY_Var ("'a", 0)],(["Test"], "list2p"))) *)

(* extracting the type of constructor Cons2p
([("'a", 0)],
 MLTY_Fun
   (MLTY_Var ("'a", 0),MayErase,
    MLTY_Fun
      (MLTY_Named
         ([MLTY_Named
             ([MLTY_Var ("'a", 0); MLTY_Var ("'a", 0)],(["Test"], "prod"))],
          (["Test"], "list2p")),MayErase,
       MLTY_Named ([MLTY_Var ("'a", 0)],(["Test"], "list2p"))))) *)

(* extracting the type of constructor Nil3
([],
 MLTY_Fun
   (MLTY_Named ([],([], "unit")),MayErase,
    MLTY_Named ([MLTY_Top],(["Test"], "list3")))) *)

(* extracting the type of constructor Cons3
([],
 MLTY_Fun
   (MLTY_Named ([],([], "unit")),MayErase,
    MLTY_Fun
      (MLTY_Top,MayErase,
       MLTY_Fun
         (MLTY_Named ([MLTY_Top],(["Test"], "list3")),MayErase,
          MLTY_Named
            ([MLTY_Named ([MLTY_Top; MLTY_Top],(["Test"], "prod"))],
             (["Test"], "list3")))))) *)

(* extracting the type of constructor Poly
([("'x", 0)],
 MLTY_Fun
   (MLTY_Named ([],(["Test"], "nnat")),MayErase,
    MLTY_Fun
      (MLTY_Var ("'x", 0),MayErase,
       MLTY_Named ([MLTY_Var ("'x", 0)],(["Test"], "poly"))))) *)

(* extracting the type of constructor Poly2
([("'x", 0)],
 MLTY_Fun
   (MLTY_Named ([],([], "unit")),MayErase,
    MLTY_Fun
      (MLTY_Var ("'x", 0),MayErase,
       MLTY_Named ([MLTY_Var ("'x", 0)],(["Test"], "poly2"))))) *)

(* extracting the type of constructor Nill
([("'a", 0)],
 MLTY_Named
   ([MLTY_Var ("'a", 0); MLTY_Named ([],([], "unit"))],(["Test"], "vec"))) *)

(* extracting the type of constructor Conss
([("'a", 0)],
 MLTY_Fun
   (MLTY_Named ([],(["Test"], "nnat")),MayErase,
    MLTY_Fun
      (MLTY_Var ("'a", 0),MayErase,
       MLTY_Fun
         (MLTY_Named
            ([MLTY_Var ("'a", 0); MLTY_Named ([],([], "unit"))],
             (["Test"], "vec")),MayErase,
          MLTY_Named
            ([MLTY_Var ("'a", 0); MLTY_Named ([],([], "unit"))],
             (["Test"], "vec")))))) *)

(* extracting the type of constructor Leaf
([("'t", 0); ("'n", 0)],
 MLTY_Named
   ([MLTY_Var ("'t", 0); MLTY_Named ([],([], "unit"))],(["Test"], "naryTree"))) *)

(* extracting the type of constructor Node
([("'t", 0); ("'n", 0)],
 MLTY_Fun
   (MLTY_Named
      ([MLTY_Named
          ([MLTY_Var ("'t", 0); MLTY_Named ([],([], "unit"))],
           (["Test"], "naryTree")); MLTY_Named ([],([], "unit"))],
       (["Test"], "vec")),MayErase,
    MLTY_Named
      ([MLTY_Var ("'t", 0); MLTY_Named ([],([], "unit"))],(["Test"], "naryTree")))) *)

Gen Code: Test

type nnat =
| O
| S of Test.nnat

let idnat = (fun x -> x)

let idnat2 = (fun x -> x)

let id = (Obj.magic (fun _1_788 x -> x))

let idp = (Obj.magic (fun _1_788 x -> x))

let add1 = (fun a -> (Test.l__S a))

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a Test.list

let prepend0 = (Obj.magic (fun tll -> (Test.l__Cons (Obj.magic Test.l__O) (Obj.magic tll))))

type ('a, 'b) list2 =
| Nil2
| Cons2 of 'a * 'b * ('a, 'b) Test.list2

type any =
| Any of unit * Obj.t

type distr_pair =
(unit  ->  Obj.t  ->  Obj.t)  ->  (Test.nnat, Test.nnat Test.list) Test.prod

type 'a list2p =
| Nil2p
| Cons2p of 'a * ('a, 'a) Test.prod Test.list2p

type 'dummyV1 list3 =
| Nil3 of unit
| Cons3 of unit * Obj.t * Obj.t Test.list3

type 'x poly =
| Poly of Test.nnat * 'x

type 'x poly2 =
| Poly2 of unit * 'x

type 'x sch =
'x  ->  'x

type sch1 =
Obj.t  ->  Obj.t

type sch3 =
Obj.t  ->  Obj.t

type 'x sch3param =
'x  ->  'x

type idt =
unit  ->  Obj.t  ->  Obj.t

type ('a, 'dummyV1) vec =
| Nill
| Conss of Test.nnat * 'a * ('a, unit) Test.vec

type vecn1 =
(Test.nnat, unit) Test.vec

type ('t, 'n) naryTree =
| Leaf
| Node of (('t, unit) Test.naryTree, unit) Test.vec

type 't binaryTree =
('t, unit) Test.naryTree

type polyvec =
(Test.nnat, unit) Test.vec Test.poly

type polylist =
Obj.t Test.list Test.poly2

type 'a listalias =
'a Test.list

type polylistalias =
Obj.t Test.listalias Test.poly2




