(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Test1

let idlist (x:list int) = x//Cons 0 x

type nnat =
| O : nnat
| S : nnat -> nnat

val isPositive : nnat -> Tot bool
let isPositive  = S?

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


type prod 'a 'b =
| Pair : fst:'a -> snd:'b -> (prod 'a 'b)

type list (a:Type) =
  | Nil  : list a
  | Cons : hd:a -> tl:list a -> list a

let prepend0 (tll : list nnat) = (Cons O tll)

type list2 'a  (b:Type) =
  | Nil2  : list2 'a b
  | Cons2 : hd:'a -> hd2:b ->  tl:list2 'a b -> list2 'a b

(* "It is known that fun f → (f O, f true) is untypable in ML. And there again, no simple
adaptation into an equivalent typable code " *)
type distr_pair = (x:Type -> x -> Tot x) -> (prod nnat  (list nnat))

(*Sec 3.3.4*)
type list2p 'a  =
  | Nil2p  : list2p 'a
  | Cons2p : hd:'a  ->  tl:list2p (prod 'a 'a)  -> list2p 'a




(*The type sections (new paragraph in the thesis)*)
type sch (x:Type) =  (x ->  Tot x)


(* Manual moving of lambdas to LHS of '=', now it extracts to his second (preferred) option.
   We now do this moving automatically.
 *)
type sch3param (x:(nnat  ->  Type))  =  (x O) ->  Tot (x (S O))

type idt =  (x:Type) ->  (x ->  Tot x)




(* This is even more complicated. what does Coq do about it?
   What it does is similar to the above case. Instead of applying unit (to vec),
   it applies  Obj.t (to list).

  Perhaps the general theme is that we retain type parameters, even
    if they have type other than Type.
  Indeed, while translating type type abbreviations or inductive types,
  we just copy the list of binders and don't even look at the types of binders.

  Of course, after the translation, all binders have type Type.
  So, one has to be careful while instantiating those binders.
  In particular, one has to apply more arguments before instantiating.
  If the arguments are terms, unit should usually work, because
  term-dependencies are removed in type definitions.

  In case the arguments are types, Obj.t seems to be the only thing that
  can be cooked from thin air, and it is what Coq seems to be doing.
  Is this mentioned somewhere in the thesis?

  All this seems a bit arbitrary, although is perhaps inspired by some
  use cases in Coq, and has been heavily tested (in Coq).
  Yet, Why is this the right way, conceptually?

  Our current implementation makes these same choices as Coq's.
*)

type listalias 'a = list 'a


type evenlist (a:Type) =
  | ENil  : evenlist a
  | ECons : hd:a -> tl:oddlist a -> evenlist a
and oddlist (a:Type) =
  | OCons : hd:a -> tl:evenlist a -> oddlist a

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
