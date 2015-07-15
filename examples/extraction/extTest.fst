(*--build-config
  --*)

(*fstar extTest.fst --codegen OCaml > Test.ml ; sed '$d' Test.ml > temp ; cp temp Test.ml ; ocamlc Test.ml*)
module Test

type nnat =
| O : nnat
| S : nnat -> nnat

type prod 'a 'b =
| Pair : fst:'a -> snd:'b -> (prod 'a 'b)

type list (a:Type) =
  | Nil  : list a
  | Cons : hd:a -> tl:list a -> list a

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


(*The type sections (new paragraph in the thesis)*)
type sch (x:Type) =  (x ->  Tot x)

(*type lambdas in a definitions should be moved leftward and made a definition *)
type sch1 : (Type  ->  Type) = fun (x:Type) ->  (x ->  Tot x)

(*again, too this differs from both options presented in the thesis. *)
type sch3 : (nnat  ->  Type) -> Type  = fun (x:(nnat  ->  Type)) ->  (x O) ->  Tot (x (S O))

(* manual parametrization, now it extracts to his second (preferred) option *)
type sch3param (x:(nnat  ->  Type))  =  (x O) ->  Tot (x (S O))


(*things that dont work:*)

type idt =  (x:Type) ->  (x ->  Tot x)


(*
Minor changes are required to make it work.
The idea is that nnat becomes unit.
Inuitively, vec now becomes a union of all members of the family *)

type vec (a:Type) : nnat -> Type =
| Nill : vec a O
| Conss : n:nnat -> a ->  (vec a n) -> vec a (S n)

type vecn1 = vec nnat (S O)
