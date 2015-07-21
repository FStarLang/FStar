(*--build-config
  --*)

(*
fstar extTest.fst --codegen OCaml-experimental > Test.ml ; sed -i '1d;$d;s/Test.l__//g;s/Test.//g;s/Prims.//g;/kdhvljkdshalfkhclklkdnfsnydufnysdkyfnklsnykweyacklnyrecynrncrewanyu/d' Test.ml ; ocamlc Test.ml
*)
module Test

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

let rec add (a : nnat) (b : nnat) = match a with
| O -> b
| S a' -> S (add a' b)


type prod 'a 'b =
| Pair : fst:'a -> snd:'b -> (prod 'a 'b)

type list (a:Type) =
  | Nil  : list a
  | Cons : hd:a -> tl:list a -> list a

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

type  poly2 (x : Type -> Type)  =
| Poly2 :  t:Type -> x t -> poly2 x


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


type binaryTree (t:Type) = naryTree t (S (S O))

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
type polylist = poly2 (list)

type listalias 'a = list 'a

type polylistalias = poly2 (listalias)

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

val ev2 :  (isEven (S (S O)))
let ev2 = EvSOdd (S O) (OddSEven O Ev0)

(* val evDouble : (n:nnat) -> isEven (add n n) *)

(*
type someLemmaStatement = nat -> nat -> Tot unit
*)
