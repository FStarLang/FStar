(*--build-config
  other-files: FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.List.fst
  --*)



(*
fstar extTest.fst --codegen OCaml > Test.ml ; sed -i '$d;/kdhvljkdshalfkhclklkdnfsnydufnysdkyfnklsnykweyacklnyrecynrncrewanyu/d' Test.ml ; ocamlc Test.ml
*)
module Test
open All
type prod 'a 'b =
| Pair : pfst:'a -> psnd:'b -> (prod 'a 'b)

let ffst = Pair.pfst

let idlist (x:list int) = x//Cons 0 x

type nnat =
| O : nnat
| S : nnat -> nnat

let idnat = fun (x:nnat) -> x
let idnat2 (x:nnat) = x

(* do the F* ASTs of id and idp' look different at all?
  No. It seems that the F* AST does not even have a place to store the
  binders appearing before '=''.
  It seems that there is such a place in the ML AST.

  We should try move the head lambdas in the body of a let to the LHS of '=''
  This is what Coq seems to be doing.

  NS: I disagree. Let bindings bind a value, period.
      Their RHS can be any value, including a lambda.
  *)
let id : a:Type -> a -> a = fun x -> x

let idp (a:Type) = fun x -> x (*x does not have type a, it has a type ?uvar a*)
let idp' (a:Type) = fun (x:a) -> x

let add1 (a : nnat) = (S a)
let add2 = S //test eta expansion of data
let eval_order (effectful:string -> string)
               (f:string -> string -> string) =
    f (effectful "first") "second"

let prev = function
  | O -> O
  | S n -> n

val add : nnat -> nnat -> Tot nnat
let rec add a b
= match a with
| O -> b
| S a' -> S (add a' b)

(*
type list (a:Type) =
  | Nil  : list a
  | Cons : hd:a -> tl:list a -> list a
*)

let prepend0 (tll : list nnat) = (Cons O tll)

type list2 'a  (b:Type) =
  | Nil2  : list2 'a b
  | Cons2 : hd:'a -> hd2:b ->  tl:list2 'a b -> list2 'a b

(*Sec 3.1.4 *)
type any =
| Any : a:Type -> a -> any

(* "It is known that fun f → (f O, f true) is untypable in ML. And there again, no simple
adaptation into an equivalent typable code " *)
type distr_pair = (x:Type -> x -> Tot x) -> (prod nnat  (list nnat))

(*Sec 3.3.4*)
type list2p 'a  =
  | Nil2p  : list2p 'a
  | Cons2p : hd:'a  ->  tl:list2p (prod 'a 'a)  -> list2p 'a

type list3 : Type -> Type =
| Nil3 : (a:Type) -> list3 a
| Cons3 :  (a:Type) -> a -> list3 a -> list3 (prod a a)


type  poly (x : nnat -> Type)  =
| Poly :  n:nnat -> x n -> poly x

(*
type  poly2 (x : Type -> Type)  =
| Poly2 : t:Type -> x t -> poly2 x
*)

(*The type sections (new paragraph in the thesis)*)
type sch (x:Type) =  (x ->  Tot x)

(*like Coq, we move lambdas in the body to the left of '=' *)
type sch1 : (Type  ->  Type) = fun (x:Type) ->  (x ->  Tot x)

(*this extracts to his preferred choice: 'x -> 'x . See below*)
type sch3 : (nnat  ->  Type) -> Type  = fun (x:(nnat  ->  Type)) ->  (x O) ->  Tot (x (S O))

(* Manual moving of lambdas to LHS of '=', now it extracts to his second (preferred) option.
   We now do this moving automatically.
 *)
type sch3param (x:(nnat  ->  Type))  =  (x O) ->  Tot (x (S O))

type idt =  (x:Type) ->  (x ->  Tot x)

type vec (a:Type) : nnat -> Type =
| Nill : vec a O
| Conss : n:nnat -> a ->  (vec a n) -> vec a (S n)

type vecn1 = vec nnat (S O)

type naryTree (t:Type) (n:nnat) =
| Leaf : naryTree t n
| Node : vec (naryTree t n) n -> (naryTree t n)


val two : nnat
let two = (S (S O))

type binaryTree (t:Type) = naryTree t two

val binLeaf : naryTree nnat two
let binLeaf = Leaf

val binNode : naryTree nnat two
let binNode = Node (Conss (S O) binLeaf (Conss O binLeaf Nill))

type polyvec = poly (vec nnat)

(* This is even more complicated. what does Coq do about it?
   What it does is similar to the above case. Instead of applying unit (to vec),
   it applies  Obj.t (to list).

  Perhaps the general theme is that we retain type parameters, even
    if they have type other than Type.
  Indeed, while translating type type abbreviations or inductive types,
  we just copy the list of binders and dont even look at the types of binders.

  Of course, after the translation, all binders have type Type.
  So, one has to be careful while instantiating those binders.
  In particular, one has to apply more arguments before instantiating.
  If the arguments are terms, unit should usually work, because
  term-dependencies are removed in type definitions.

  In case the arguments are types, Obj.t seems to be the only thing that
  can be cooked from thin air, and it is what Coq seems to be doing.
  Is this mentioned somewhere in the thesis?

  All this seems a bit arbitrary, although is perhaps inspired by some
  use cases in Coq, and haa been heavily tested (in Coq).
  Yet, Why is this the right way, conceptually?

  Our current implementation makes these same choices as Coq's.
*)
(*
type polylist = poly2 (list)
*)
type listalias 'a = list 'a

(*
type polylistalias = poly2 (listalias)
*)

type evenlist (a:Type) =
  | ENil  : evenlist a
  | ECons : hd:a -> tl:oddlist a -> evenlist a
and oddlist (a:Type) =
  | OCons : hd:a -> tl:evenlist a -> oddlist a

type isEven : nnat -> Type  =
  | Ev0  : isEven O
  | EvSOdd : n:nnat -> isOdd n -> isEven (S n)
and isOdd : nnat -> Type =
  | OddSEven : n:nnat -> isEven n -> isOdd (S n)

  type node =
      { frequency: int;
        next: node;
        zero_child: ref node;
        one_child: node;
        symbol: int;
        code: string;
      }


val ev2 :  (isEven (S (S O)))
let ev2 = EvSOdd (S O) (OddSEven O Ev0)

(*the 2 types below are not erased to unit.
structural erasure is done later,
when it wont mess up with extraction/ML-typechecking of expressions*)
type someLemmaStatement = nnat -> nnat -> Tot unit
type trivialLemmaSatement = n:nnat -> m:nnat -> Lemma (add n m == add m n)

(*this gets erased*)
val add0Comm :  n:nnat -> Lemma (add n O == add O n)
let rec add0Comm n =
match n with
| O -> ()
| S n' -> add0Comm n'


(*this gets erased*)
val add0CommUse :  n:nnat -> Tot unit
let add0CommUse n = add0Comm n (*why does this typecheck after extraction? add0Comm is not a function after erasure*)
(*Perhaps the environment stores the unerased ML type of add0Comm?*)
(*If not, we should do structural erasure after all  modules have been extracted?*)

val add0CommUse2 :  n:nnat -> Tot nnat
let add0CommUse2 n = let x = add0Comm (S n) in n

val unitAsNat : unit -> Tot nnat
let unitAsNat u = O

(*this example also works fine. Indeed (add0Comm (S n) gets replaced by ()
  during term erasure*)
val add0CommUse3 :  n:nnat -> Tot nnat
let add0CommUse3 n = unitAsNat (add0Comm (S n))

val add0CommAlias :  n:nnat -> Tot unit
let add0CommAlias = add0Comm  (*why does this typecheck after extraction? add0Comm is not a function after erasure*)


val mult2 : a:nnat -> b:nnat -> Tot nnat
let rec mult2 a b =
match a with
| O -> O
| S a' -> add b (mult2 a' b)


type capture (a:Type) 'a = 'a*a

(*
type bTree (t:Type)=
| BLeaf : ldata:t -> bTree t
| BNode : left:(bTree t) -> right:(bTree t) -> bTree t

val leftmostLeaf : t:Type ->  (bTree t) -> t
let rec leftmostLeaf 't bt =
match bt with
| BLeaf d -> d
| BNode l r -> leftmostLeaf 't l
*)
