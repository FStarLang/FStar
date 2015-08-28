(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module Util

type TT :: P = 
  | True : TT

type fix2 :: 'a1::* => 'a2::('a1 => *) => 'b1::* => 'b2::('b1 => *) => * = 
  | MkFix2 : 'a1::* -> 'a2::('a1 => *) 
             -> 'b1::* -> 'b2::('b1 => *) 
             -> (fix2 'a1 'a2 'b1 'b2 -> x:'a1 -> 'a2 x) 
             -> (fix2 'a1 'a2 'b1 'b2 -> x:'b1 -> 'b2 x) 
             -> fix2 'a1 'a2 'b1 'b2
    
type tup :: 'a::* => 'b::* => * = 
  | Tup : 'a -> 'b -> tup 'a 'b

val fst : ('a * 'b) -> 'a
let fst x = match x with 
  | (x, y) -> x

val snd : ('a * 'b) -> 'b
let snd x = match x with 
  | (x, y) -> y
  
(* TODO: Implementation of exhaustiveness checks is incomplete. 
         I document infeasible cases that we can't currently prove 
         with calls to these functions. *)
val impos : string -> 'a 
let impos x = raise (strcat "Impossible: " x)

val __todo : string -> 'a
let __todo x = raise (strcat "TODO: " x)

val strcat3: string -> string -> string -> string
let strcat3 s1 s2 s3 = strcat s1 (strcat s2 s3)

val tostr: 'a -> string 
let tostr x = string_of_any_for_coq x

type Eq :: 'a::* => 'a => 'a => P = 
  | Refl_eq : 'a::* -> x:'a -> Eq 'a x x

type Either :: * => * => * =
  | InlS : 'a -> Either 'a 'b
  | InrS : 'b -> Either 'a 'b

type Disj :: P => P => P = 
  | Inl : 'a::P -> 'b::P -> 'a -> Disj 'a 'b
  | Inr : 'a::P -> 'b::P -> 'b -> Disj 'a 'b

type DisjStar :: P => P => * = 
  | InlStar : 'a::P -> 'b::P -> 'a -> DisjStar 'a 'b
  | InrStar : 'a::P -> 'b::P -> 'b -> DisjStar 'a 'b

type EqReln :: 'ctx::* => 'a::* => ('ctx => 'a => 'a => P) => 'ctx => 'a => 'a => P =
  | EQ_Refl : 'ctx::* -> 'a::* -> 'Base::('ctx => 'a => 'a => P)
             -> G:'ctx -> x:'a 
             -> EqReln 'ctx 'a 'Base G x x 

  | EQ_Sym : 'ctx::* -> 'a::* -> 'Base::('ctx => 'a => 'a => P)
             -> G:'ctx -> x:'a -> y:'a
             -> EqReln 'ctx 'a 'Base G x y
             -> EqReln 'ctx 'a 'Base G y x

  | EQ_Trans : 'ctx::* -> 'a::* -> 'Base::('ctx => 'a => 'a => P)
             -> G:'ctx -> x:'a -> y:'a -> z:'a
             -> EqReln 'ctx 'a 'Base G x y
             -> EqReln 'ctx 'a 'Base G y z
             -> EqReln 'ctx 'a 'Base G x z

  | EQ_Base : 'ctx::* -> 'a::* -> 'Base::('ctx => 'a => 'a => P)
             -> G:'ctx -> x:'a -> y:'a 
             -> 'Base G x y 
             -> EqReln 'ctx 'a 'Base G x y

type mu :: 'a::* => ('a => *) => * =
   | MkMu : 'a::* -> 'b::('a => *)
         -> (mu 'a 'b -> x:'a -> 'b x)
         -> mu 'a 'b

val nyi : string -> 'a
let nyi x = raise (strcat "not yet implemented: " x)

type seq :: * => * = list
(* type seq 'a :: _ = list 'a *)

val fold_left2_opt : ('env -> 'a -> 'b -> option 'env) -> option 'env -> list 'a -> list 'b -> option 'env
let rec fold_left2_opt f envOpt l1 l2 = match envOpt with 
  | None -> None
  | Some env -> 
      match l1, l2 with 
        | [], [] -> envOpt
        | (x::tl1), (y::tl2) -> 
            fold_left2_opt f (f env x y) tl1 tl2
        | _ -> raise "fold_left2: unequal length lists"

type Zip :: 'a::* => 'b::* => ('a => 'b => P) => list 'a => list 'b => P = 
   | Zip_Nil : 'a::* -> 'b::* -> 'Q::('a => 'b => P) 
             -> Zip 'a 'b 'Q [] []

   | Zip_Cons: 'a::* -> 'b::* -> 'Q::('a => 'b => P)
             -> l1:list 'a -> l2:list 'b 
             -> x:'a -> y:'b 
             -> Zip 'a 'b 'Q l1 l2
             -> 'Q x y
             -> Zip 'a 'b 'Q (x::l1) (y::l2)

(* TODO: Remove the let rec as below? *)
val zip_p: 'a::* -> 'b::* -> 'Q::('a => 'b => P)
      -> f:(x:'a -> y:'b -> optionP ('Q x y))
      -> l1:list 'a
      -> l2:list 'b
      -> optionP (Zip 'a 'b 'Q l1 l2)
let rec zip_p f l1 l2 = match l1, l2 with
  | [],[] -> SomeP (Zip_Nil<'a,'b,'Q>)
  | (x1::tl1), (x2::tl2) ->
      match zip_p<'a,'b,'Q> f tl1 tl2, f x1 x2 with
        | (SomeP pf_tl), SomeP pf_hd -> SomeP (Zip_Cons<'a,'b,'Q> tl1 tl2 x1 x2 pf_tl pf_hd)
        | _ -> NoneP



val map_p: 'a::* -> 'b::* -> 'Q::('a => 'b => P)
      -> f:(x:'a -> (y:'b * 'Q x y))
      -> l1:list 'a
      -> (l2:list 'b * Zip 'a 'b 'Q l1 l2)
let rec map_p f l1 = match l1 with
  | [] -> [], Zip_Nil<'a,'b,'Q>
  | x::tlx ->
      let y, pfHd = f x in
      let tly, pfTl = map_p<'a,'b,'Q> f tlx in
        (y::tly), Zip_Cons<'a,'b,'Q> tlx tly x y pfTl pfHd
end

(* ******************************************************************************** *)

module FiniteSet
open Util

type Mem :: 'a::* => 'a => seq 'a => P =
   | Mem_hd : 'a::* -> x:'a -> tl:seq 'a -> Mem x (x::tl)
   | Mem_tl : 'a::* -> x:'a -> y:'a -> tl:seq 'a
            -> Mem x tl -> Mem x (y::tl)

type NotMem :: 'a::* => 'a => seq 'a => P =
   | NotMem_nil : 'a::* -> x:'a -> NotMem x []
   | NotMem_tl : 'a::* -> x:'a -> y:'a -> tl:seq 'a
            -> dummy:(Eq true true){x<>y}
            -> NotMem x tl
            -> NotMem x (y::tl)

type Disjoint :: 'a::* => seq 'a => seq 'a => P =
   | Disjoint_nil : l:seq 'a -> Disjoint [] l
   | Disjoint_cons : x:'a -> xs:seq 'a -> ys:seq 'a
                   -> Disjoint xs ys
                   -> NotMem x ys
                   -> Disjoint (x::xs) ys

type Distinct :: 'a::* => seq 'a => P =
   | Distinct_nil : 'a::* -> Distinct 'a []
   | Distinct_cons : 'a::* -> hd:'a -> tl:seq 'a
                   -> NotMem 'a hd tl
                   -> Distinct 'a tl
                   -> Distinct (hd::tl)

val decideMem: x:'a -> l:seq 'a -> DisjStar (Mem x l) (NotMem x l)
let rec decideMem x l = match l with
  | [] -> InrStar (NotMem_nil x)
  | hd::tl ->
      if (hd=x)
      then InlStar (Mem_hd x tl )
      else (match decideMem x tl with
              | InlStar pf_mem_tl -> InlStar (Mem_tl x hd tl pf_mem_tl)
              | InrStar pf_notmem_tl -> InrStar (NotMem_tl x hd tl (Refl_eq true) pf_notmem_tl))

val checkDisjoint : xs:seq 'a -> ys:seq 'a -> optionP (Disjoint xs ys)
let rec checkDisjoint xs ys = match xs with
  | [] -> SomeP (Disjoint_nil ys)
  | x::tl ->
      match decideMem x ys with
        | InlStar _ -> NoneP
        | InrStar pf_notmem ->
            match checkDisjoint tl ys with
              | NoneP -> NoneP
              | SomeP pf -> SomeP (Disjoint_cons x tl ys pf pf_notmem)

val checkDistinct: l:seq 'a -> optionP (Distinct l)
let rec checkDistinct l = match l with
  | [] -> SomeP (Distinct_nil)
  | hd::tl ->
      match checkDistinct tl with
        | NoneP -> NoneP
        | SomeP pf_tl ->
            match decideMem hd tl with
              | InlStar _ -> NoneP
              | InrStar pf_hd -> SomeP (Distinct_cons hd tl pf_hd pf_tl)

val checkDistinctCache: i_tl:seq 'a -> Distinct i_tl -> i:seq 'a -> optionP (Distinct i)
let rec checkDistinctCache i_tl ditl i =
  if i_tl = i then SomeP (ditl)
  else match i with
    | hd::tl -> match checkDistinctCache i_tl ditl tl with
        | NoneP -> NoneP
        | SomeP di_tl ->
            match decideMem hd tl with
              | InlStar _ -> NoneP
              | InrStar nm -> SomeP (Distinct_cons hd tl nm di_tl)
                  
val mem_pf: x:'a -> l:seq 'a -> optionP (Mem x l)
let rec mem_pf x l = match l with
  | [] -> NoneP
  | hd::tl ->
      if (hd=x)
      then SomeP (Mem_hd x tl )
      else (match mem_pf x tl with
              | NoneP -> NoneP
              | SomeP pftl -> SomeP (Mem_tl x hd tl pftl))


val mem: x:'a -> seq 'a -> bool
let rec mem x = function
  | hd::tl -> if hd=x then true else mem x tl
  | [] -> false

val find : 'a::* -> 'P::('a => P)
         -> f:(x:'a -> optionP ('P x))
         -> l:seq 'a
         -> option (x:'a * 'P x * Mem x l)
let rec find f l = match l with
  | [] -> None
  | hd::tl ->
      match f hd with
        | SomeP p -> Some (hd, p, Mem_hd hd tl)
        | NoneP ->
            match find f tl with
              | None -> None
              | Some ((x, p, mtl)) -> Some(x, p, Mem_tl x hd tl mtl)

val concat : seq 'a -> seq 'a -> seq 'a
let rec concat l1 l2 = match l1 with
  | [] -> l2
  | hd::tl -> hd::(concat tl l2)

type Append :: 'a::* => seq 'a => seq 'a => seq 'a => P =
  | Append_Nil : 'a::* -> l:seq 'a -> Append 'a [] l l
  | Append_Cons : 'a::* -> x:'a -> tl:seq 'a -> l2:seq 'a -> tl_l2:seq 'a
               -> Append 'a tl l2 tl_l2
               -> Append 'a (x::tl) l2 (x::tl_l2)

type Flatten :: 'a::* => list (list 'a) => list 'a => P =
  | Flatten_Nil : 'a::* -> Flatten 'a [] []
  | Flatten_Cons : 'a::* -> hds:list 'a -> tls:list (list 'a) -> tl:list 'a -> hds_tl:list 'a
                 -> Flatten 'a tls tl
                 -> Append 'a hds tl hds_tl
                 -> Flatten 'a (hds::tls) hds_tl

val append_pf : 'a::* -> l1:seq 'a -> l2:seq 'a -> (l3:seq 'a * Append l1 l2 l3)
let rec append_pf l1 l2 = match l1 with
  | [] -> (l2, Append_Nil l2)
  | hd::tl ->
      let tl_l2, pf_tl = append_pf tl l2 in
        ((hd::tl_l2), Append_Cons hd tl l2 tl_l2 pf_tl)

val flatten_pf: 'a::* -> l1: list (list 'a) -> (l2: list 'a * Flatten l1 l2)
let rec flatten_pf l1 = match l1 with
  | [] -> ([], Flatten_Nil)
  | hds::tls ->
      let tl, pf_tl = flatten_pf tls in
      let hds_tl, pf_ap = append_pf hds tl in
        (hds_tl, Flatten_Cons hds tls tl hds_tl pf_tl pf_ap)

val extendZip: 'a::* -> 'b::* -> 'Q::('a => 'b => P)
              -> tl1:seq 'a -> tl2:seq 'b -> Zip 'a 'b 'Q tl1 tl2
              -> l1:seq 'a -> (x:'a -> (y:'b * 'Q x y))
              -> option (pfx:seq 'b * out:seq 'b * Append pfx tl2 out * Zip 'a 'b 'Q l1 out)
let rec extendZip tl1 tl2 z l1 f =
  if l1=tl1
  then Some ([], tl2, Append_Nil tl2, z)
  else
    match l1 with
      | [] -> None
      | hd1::l1_tl->
          let hd2, pfQ = f hd1 in
            (match extendZip tl1 tl2 z l1_tl f with
               | None -> None
               | Some((l2_pfx, out_tl, apf, z_tl)) ->
                   Some ((hd2::l2_pfx), (hd2::out_tl),
                         Append_Cons hd2 l2_pfx tl2 out_tl apf,
                         Zip_Cons<'a,'b,'Q> l1_tl out_tl hd1 hd2 z_tl pfQ))

type Partition :: 'a::* => seq 'a => seq 'a => seq 'a => P =
  | Part_Admit : l1:seq 'a -> l2:seq 'a -> l3:seq 'a -> Partition l1 l2 l3

and Perm :: 'a::* => seq 'a => seq 'a => P =
  | Perm_Refl : 'a::* -> l:seq 'a -> Perm 'a l l

  | Perm_Sym  : 'a::* -> l1:seq 'a -> l2:seq 'a -> Perm 'a l1 l2 -> Perm 'a l2 l1

  | Perm_Trans : 'a::* -> l1:seq 'a -> l2:seq 'a -> l3:seq 'a
               -> Perm 'a l1 l2 -> Perm 'a l2 l3
               -> Perm 'a l1 l3

  | Perm_Cons : 'a::* -> x:'a -> tl1:seq 'a -> tl2:seq 'a
              -> Perm 'a tl1 tl2
              -> tl2_pfx:seq 'a -> tl2_sfx:seq 'a -> Partition 'a tl2 tl2_pfx tl2_sfx
              -> tl2x:seq 'a -> Append 'a tl2_pfx (x::tl2_sfx) tl2x
              -> Perm 'a (x::tl1) tl2x

(* Need this wrapper in places to allow cross-universe
   elimination at the expense of losing totality guarantees *)
type W :: P => * =
  | MkW : 'a::P -> 'a -> W 'a

val partitionUnconsL : x:'a -> a:seq 'a -> a1:seq 'a -> a2:seq 'a
                    -> Partition (x::a) (x::a1) a2
                    -> Partition a a1 a2
let partitionUnconsL x a a1 a2 p = Part_Admit a a1 a2

val partitionUnconsR : x:'a -> a:seq 'a -> a1:seq 'a -> a2:seq 'a
                    -> Partition (x::a) a1 (x::a2)
                    -> Partition a a1 a2
let partitionUnconsR x a a1 a2 p = Part_Admit a a1 a2


type fixpn ('a::*) :: _ = (fix2 (seq 'a) (fun (l:seq 'a) => Perm [] l -> W (Eq l []))
                                (seq 'a) (fun (l:seq 'a) => Perm l [] -> W (Eq l [])))

val permNil1: l:seq 'a -> Perm [] l -> W (Eq l [])
let permNil1 l p =
  match l with
    | [] -> MkW (Refl_eq l)
    | _ -> raise "Impos1"

val permNil2: l:seq 'a -> Perm l [] -> W (Eq l [])
let permNil2 l p =
  match l with
    | [] -> MkW (Refl_eq l)
    | _ -> raise "Impos2"

(* val permNil1': fixpn 'a -> l:seq 'a -> Perm [] l -> W (Eq l []) *)
(* val permNil2': fixpn 'a -> l:seq 'a -> Perm l [] -> W (Eq l []) *)
(* let permNil1' f l p =  *)
(*   match f with  *)
(*     | MkFix2 permNil1'' permNil2'' ->  *)
(*         match p with  *)
(*           | Perm_Refl _ -> MkW (Refl_eq l) *)
(*           | Perm_Sym _l _nil p' -> permNil2'' f l p' *)
(*           | Perm_Trans l1 l2 l3 p12 p23 ->  *)
(*               (match permNil1'' f l2 p12 with *)
(*                  | MkW (Refl_eq _) -> permNil1'' f l3 p23) *)

(* let permNil2' f l p = *)
(*   match f with  *)
(*     | MkFix2 permNil1'' permNil2'' ->  *)
(*         match p with  *)
(*           | Perm_Refl _ -> MkW (Refl_eq l) *)
(*           | Perm_Sym _nil _nil p' -> permNil1'' f l p' *)
(*           | Perm_Trans l1 l2 l3 p12 p23 ->  *)
(*               (match permNil2'' f l2 p23 with *)
(*                  | MkW (Refl_eq _) -> permNil2'' f l1 p12) *)


(* val permNil1: l:seq 'a -> Perm [] l -> W (Eq l []) *)
(* val permNil2: l:seq 'a -> Perm l [] -> W (Eq l []) *)
(* let permNil1 l p =  *)
(*   permNil1' (MkFix2 permNil1' permNil2') l p *)
(* let permNil2 l p =  *)
(*   permNil2' (MkFix2 permNil1' permNil2') l p *)

val partitionUnNil : l1:seq 'a -> l2:seq 'a -> Partition [] l1 l2
                   -> (Eq l1 [] * Eq l2 [])
let rec partitionUnNil l1 l2 pnil =
  match l1, l2 with
    | [], [] -> (Refl_eq l1, Refl_eq l2)
    | _ -> raise "impos3"

val findPartition : x:'a -> l:seq 'a -> option (pfx:seq 'a * sfx:seq 'a * Partition 'a l pfx (x::sfx))
let rec findPartition x l = match l with
  | [] -> None
  | hd::tl ->
      if hd=x
      then
        let pf = Part_Admit l [] (x::tl) in
          Some ([], tl, pf)
      else
        match findPartition x tl with
          | None -> None
          | Some ((tl_pfx, tl_sfx, pf)) ->
              Some ((hd::tl_pfx), tl_sfx, Part_Admit l (hd::tl_pfx) (x::tl_sfx))

val findPerm' : x:'a -> l:seq 'a -> option (l':seq 'a * Perm l (x::l'))
let rec findPerm' x l = match l with
  | [] -> None
  | hd::tl ->
      if hd=x
      then Some (tl, Perm_Refl l)
      else
        match findPerm' x tl with
          | None -> None
          | Some ((tl', perm_tl_xtl')) ->
              let l' = hd::tl' in
                (* perm_tl: Perm tl (x::tl') *)
                (* Initial Goal: Perm (hd::tl) (x::hd::tl') *)
                (* Goal: Partition (hd::tl) [x] (hd::tl') *)
              let part_tl'_nil = Part_Admit tl' [] tl' in
              let part_xtl' = Part_Admit (x::tl') [x] tl' in
                (* part_xtl' : Partition (x::tl') [x] tl' *)
              let hd_tl' = (hd::tl') in
              let pf_append = Append_Cons x [] hd_tl' hd_tl' (Append_Nil hd_tl') in
              let x_hd_tl' = x::hd_tl' in
              let pf_perm = Perm_Cons hd tl (x::tl') perm_tl_xtl' [x] tl' part_xtl' x_hd_tl' pf_append in
                (* pf_perm: Perm (hd::tl) (x::hd::tl') *)
                Some (hd_tl', pf_perm)

val findPerm : x:'a -> l:seq 'a -> option (l':seq 'a * Partition l [x] l')
let rec findPerm x l =
  match findPerm' x l with
    | None -> None
    | Some((l', pf_perm)) -> (* pf_perm : Perm l (x::l') *)
        (* Goal: Partition l [x] l' *)
        (* Initial goal: Partition (x::l') [x] l' *)
        let goal = Part_Admit l [x] l' in
          Some (l', goal)

val mergePartition: l:seq 'a -> l1:seq 'a -> l2:seq 'a -> Partition 'a l l1 l2
                 -> l2_1:seq 'a -> l2_2:seq 'a -> Partition 'a l2 l2_1 l2_2
                 -> (l1_l2_1:seq 'a * Partition l l1_l2_1 l2_2 * Partition l1_l2_1 l1 l2_1)
let rec mergePartition l l1 l2 pf12 l2_1 l2_2 pf2_12 =
  let l1_l2_1 = concat l1 l2_1 in
    (l1_l2_1, Part_Admit l l1_l2_1 l2_2, Part_Admit l1_l2_1 l1 l2_1)

val partAllL: l:seq 'a -> Partition 'a l l []
let partAllL l = Part_Admit l l []

val partAllR: l:seq 'a -> Partition 'a l [] l
let partAllR l = Part_Admit l [] l

val partConsL: x:'a -> tl:seq 'a -> l:seq 'a -> r:seq 'a
              -> Partition 'a tl l r
              -> Partition 'a (x::tl) (x::l) r
let partConsL x tl l r p = Part_Admit (x::tl) (x::l) r

val partConsR : 'a::* -> x:'a -> tl:seq 'a -> l:seq 'a -> r:seq 'a
              -> Partition 'a tl l r
              -> Partition 'a (x::tl) l (x::r)
let partConsR x tl l r p = Part_Admit (x::tl) l (x::r)

val partPerm1 : 'a::* -> l1:seq 'a -> l2:seq 'a -> pfx:seq 'a -> sfx:seq 'a
              -> Perm 'a l1 l2
              -> Partition 'a l1 pfx sfx
              -> Partition 'a l2 pfx sfx

let partPerm1 l1 l2 pfx sfx perm p = Part_Admit l2 pfx sfx

val partPerm2 : 'a::* -> l:seq 'a -> pfx1:seq 'a -> pfx2:seq 'a -> sfx:seq 'a
              -> Perm 'a pfx1 pfx2
              -> Partition 'a l pfx1 sfx
              -> Partition 'a l pfx2 sfx

let partPerm2 l pfx1 pfx2 sfx perm p = Part_Admit l pfx2 sfx

val partPerm3 : 'a::* -> l:seq 'a -> pfx:seq 'a -> sfx1:seq 'a -> sfx2:seq 'a
              -> Perm 'a sfx1 sfx2
              -> Partition 'a l pfx sfx1
              -> Partition 'a l pfx sfx2
let partPerm3 l pfx sfx1 sfx2 perm p = Part_Admit l pfx sfx2

val partUnconsL : x:'a -> a:seq 'a -> a1:seq 'a -> a2:seq 'a
                  -> Partition (x::a) (x::a1) a2
                  -> Partition a a1 a2
let partUnconsL x a a1 a2 p = Part_Admit a a1 a2

val partUnconsR : x:'a -> a:seq 'a -> a1:seq 'a -> a2:seq 'a
                  -> Partition (x::a) a1 (x::a2)
                  -> Partition a a1 a2
let partUnconsR x a a1 a2 p = Part_Admit a a1 a2
end

(* ******************************************************************************** *)

module Terms
open Util

(* Core AST, imported from FS_Terms.v *)
type bvar    = string
type tyname  = string
type vlname  = string
type cname   = string
type iname   = string
type boxname = string
type name    = string (* a catch-all for the various names *)

type gvar :: * => *(* P *) =
   | GV_Bound : bvar -> gvar 'a
   | GV_Free : 'a::* -> 'a -> gvar 'a

type pattern = (* :: P = *)
   | MkPattern : cname -> seq bvar -> seq bvar -> pattern

type basekind = (* :: P = *)
   | BK_Comp  : basekind
   | BK_Prop  : basekind
   | BK_Erase : basekind
   | BK_Afn   : basekind

type kind =(* :: P = *)
  | K_Base  : basekind -> kind
  | K_ProdK : bvar -> kind -> kind -> kind
  | K_ProdT : bvar -> typ -> kind -> kind

and typ = (* :: P  = *)
  | T_Var   : gvar tyname -> typ
  | T_Unit  : typ
  | T_Ind   : iname -> typ
  | T_VApp  : typ -> value -> typ
  | T_App   : typ -> typ -> typ
  | T_Prod  : bvar -> typ -> typ -> typ
  | T_ProdK : bvar -> kind -> typ -> typ
  | T_Ref   : bvar -> typ -> typ -> typ
  | T_Lam   : bvar -> typ -> typ -> typ
  | T_Afn   : typ -> typ
  | T_Ascribe : typ -> kind -> typ

and value = (* :: P = *)
  | V_Var   : gvar vlname -> value
  | V_Unit  : value
  | V_Fun   : bvar  -> typ -> expr -> value
  | V_FunT  : bvar  -> kind -> expr -> value
  | V_Boxed : boxname -> value -> value
  | V_Const : cname -> seq typ -> seq value -> value
  | V_Ascribe : value -> typ -> value
    
and expr =  (* :: P = *)
  | E_Value  : value -> expr
  | E_App    : expr -> value -> expr
  | E_TApp   : expr -> typ -> expr
  | E_LetIn  : bvar -> expr -> expr -> expr
  | E_Match  : value -> pattern -> expr -> expr -> expr
  | E_Assume : typ -> expr
  | E_Ascribe : expr -> typ -> expr

(* A datatype for mutual recursion over exp/value/typ/kind *)
type fix :: (kind => *) => (typ => *) => (value => *) => (expr => *) => * =
  | MkFix : 'a::(kind  => *)
         -> 'b::(typ   => *)
         -> 'c::(value => *)
         -> 'd::(expr  => *)
         -> (fix 'a 'b 'c 'd  -> k:kind     -> 'a k)
         -> (fix 'a 'b 'c 'd  -> t:typ      -> 'b t)
         -> (fix 'a 'b 'c 'd  -> v:value    -> 'c v)
         -> (fix 'a 'b 'c 'd  -> e:expr     -> 'd e)
         -> fix 'a 'b 'c 'd

type CurryT :: expr => seq typ => expr => P =
  | CurryT_nil  : e:expr -> CurryT e [] e
  | CurryT_cons : e:expr -> t:typ -> ts:seq typ -> e':expr
                -> CurryT (E_TApp e t) ts e'
                -> CurryT e (t::ts) e'

type CurryV :: expr => seq value => expr => P =
  | CurryV_nil  : e:expr -> CurryV e [] e
  | CurryV_cons : e:expr -> v:value -> vs:seq value -> e':expr
                -> CurryV (E_App e v) vs e'
                -> CurryV e (v::vs) e'

type AsTyp :: _ = (fun (a:bvar) (t:typ) => Eq t (T_Var (GV_Bound a)))
type AsTyps :: _ = Zip bvar typ AsTyp
val asTyps : al:seq bvar -> (tl:seq typ * AsTyps al tl)
let asTyps al = map_p<bvar, typ, AsTyp> (fun a -> let t = (T_Var (GV_Bound a)) in (t, Refl_eq t)) al


type AsVal :: _ = (fun (a:bvar) (v:value) => Eq v (V_Var (GV_Bound a)))
type AsVals :: _ = Zip bvar value AsVal
val asVals : xl:seq bvar -> (vl:seq value * AsVals xl vl)
let asVals xl = map_p<bvar, value, AsVal> (fun x -> let v = (V_Var (GV_Bound x)) in (v, Refl_eq v)) xl

(* TODO: write this using fold_left? *)
type ct :: _ = fun (e:expr) => (ts:seq typ   -> (e':expr * CurryT e ts e'))
type cv :: _ = fun (e:expr) => (vs:seq value -> (e':expr * CurryV e vs e'))

private val curryt' : mu expr ct -> e:expr -> ct e
let curryt' f e ts =
  match f with MkMu curryt' ->
    match ts with
      | [] -> e, CurryT_nil e
      | hd::tl ->
          let eres, pf_tl = curryt' f (E_TApp e hd) tl  in
            eres, CurryT_cons e hd tl eres pf_tl

private val curryv' : mu expr cv -> e:expr -> cv e
let curryv' f e vs =
  match f with MkMu curryv' ->
    match vs with
      | [] -> e, CurryV_nil e
      | hd::tl ->
          let eres, pf_tl = curryv' f (E_App e hd) tl  in
            eres, CurryV_cons e hd tl eres pf_tl

val curryt : e:expr -> ct e
let curryt e ts = curryt' (MkMu curryt') e ts

val curryv : e:expr -> cv e
let curryv e vs = curryv' (MkMu curryv') e vs

val pr : string -> unit
let pr s = print_string s; ()

val print_list: sep:string -> ('a -> unit) -> list 'a -> unit
let rec print_list sep f l = match l with
  | [] -> ()
  | hd::tl -> f hd; pr sep; print_list sep f tl

let print_pattern p = match p with
  | MkPattern x ts xs ->
      pr x;
      print_list " " (fun x -> pr "'"; pr x; ()) ts;
      print_list " " pr xs

(* val print_typ : typ -> unit *)
(* val print_kind : kind -> unit *)
(* val print_value : value -> unit *)
(* val print_expr : expr -> unit *)
(* let rec print_typ t = match t with  *)
(*   | T_Var (GV_Bound f) -> pr "'"; pr f *)
(*   | T_Var (GV_Free f) -> pr f *)
(*   | T_Ind x -> pr x *)
(*   | T_VApp t v -> pr "("; print_typ t; print_value v; pr ")" *)
(*   | T_App t1 t2 -> pr "("; print_typ t1; pr " "; print_typ t2; pr ")" *)
(*   | T_Prod x t1 t2 ->  *)
(*       pr x;  *)
(*       pr ":";  *)
(*       print_typ t1; *)
(*       pr " -> "; *)
(*       print_typ t2  *)
(*  | T_ProdK a k t ->  *)
(*       pr "'";  *)
(*       pr a;  *)
(*       pr "::";  *)
(*       print_kind k; *)
(*       pr " -> "; *)
(*       print_typ t *)

(*   | T_Ref x t phi ->  *)
(*       pr x;  *)
(*       pr ":";  *)
(*       print_typ t; *)
(*       pr "{"; *)
(*       print_typ phi; *)
(*       pr "}" *)

(*   | T_Lam x t t' ->  *)
(*       pr "fun (";  *)
(*       pr x; *)
(*       pr ":";  *)
(*       print_typ t; *)
(*       pr ")";  *)
(*       pr "->"; *)
(*       print_typ t' *)

(*   | T_Afn t -> pr "!"; print_typ t *)

(*   | T_Ascribe t k -> pr "("; print_typ t; pr "::"; print_kind k; pr ")" *)

(* and print_kind k = match k with  *)
(*   | K_Base (BK_Comp)  -> pr "*" *)
(*   | K_Base (BK_Prop)  -> pr "P" *)
(*   | K_Base (BK_Afn)   -> pr "A" *)
(*   | K_Base (BK_Erase) -> pr "E" *)
(*   | K_ProdK a k k' ->  *)
(*       pr "'";  *)
(*       pr a;  *)
(*       pr "::";  *)
(*       print_kind k; *)
(*       pr " => "; *)
(*       print_kind k' *)
(*   | K_ProdT x t k ->  *)
(*       pr x;  *)
(*       pr ":";  *)
(*       print_typ t; *)
(*       pr " => "; *)
(*       print_kind k *)

(* and print_value v = match v with  *)
(*   | V_Var (GV_Bound f) -> pr f *)
(*   | V_Var (GV_Free f) -> pr f *)
(*   | V_Fun x t e ->  *)
(*       pr "fun (";  *)
(*       pr x; *)
(*       pr ":";  *)
(*       print_typ t; *)
(*       pr ")";  *)
(*       pr "->"; *)
(*       print_expr e *)


(*   | V_FunT a k e -> *)
(*       pr "fun ('";  *)
(*       pr a; *)
(*       pr "::";  *)
(*       print_kind k; *)
(*       pr ")";  *)
(*       pr "->"; *)
(*       print_expr e *)

(*   | V_Boxed b v -> pr "box("; pr b; pr ", "; print_value v; pr ")" *)

(*   | V_Const c ts vs ->  *)
(*       pr c;  *)
(*       print_list ", " print_typ ts;  *)
(*       print_list ", " print_value vs *)

(*   | V_Ascribe v t -> pr "("; print_value v; pr ":"; print_typ t; pr ")" *)
    
(* and print_expr e =  match e with *)
(*   | E_Value v -> print_value v *)
(*   | E_App e v -> pr "("; print_expr e; pr " "; print_value v; pr ")" *)
(*   | E_TApp e t -> pr "("; print_expr e; pr " "; print_typ t; pr ")" *)
(*   | E_LetIn x e1 e2 -> pr "let "; pr x; pr " = "; print_expr e1; pr " in "; print_expr e2 *)
(*   | E_Match v p e1 e2 ->  *)
(*       pr "match "; print_value v; pr " with "; print_pattern p; pr " -> "; print_expr e1; pr " else "; print_expr e2 *)
(*   | E_Assume t ->  *)
(*       pr "assume "; print_typ t *)
(*   | E_Ascribe e t -> pr "("; print_expr e; pr ":"; print_typ t; pr ")" *)

end

(* ******************************************************************************** *)

module Env
open Util
open FiniteSet
open Terms

type constructor = (* :: P = *)
  | MkConstructor : cname -> typ -> constructor

type ikind =(* :: P = *)
  | MkIKind : iname -> kind -> ikind

type inductive =  (* :: P = *)
  | MkIndType : seq ikind -> seq constructor -> inductive

type icompartment = seq inductive

type fvbinding = (* :: P = *)
  | FV_VlName : vlname -> typ -> fvbinding
  | FV_TyName : tyname -> kind -> fvbinding

type environment = seq fvbinding

type locbinding =  (* :: P = *)
  | LB_BvarTy   : bvar -> typ -> locbinding
  | LB_BvarKind : bvar -> kind -> locbinding
  | LB_VlEq     : value -> value -> locbinding
  | LB_TyEq     : typ -> typ -> locbinding

type bindings = seq locbinding

type ICompBinds_I :: icompartment => iname => kind => P =
  | ICompBinds_ind : I:icompartment -> i:iname -> k:kind
                   -> is:seq ikind
                   -> ds:seq constructor
                   -> Mem (MkIndType is ds) I
                   -> Mem (MkIKind i k) is
                   -> ICompBinds_I I i k

type ICompBinds_C :: icompartment => cname => typ => P =
  | ICompBinds_dcon : I:icompartment -> d:cname -> t:typ
                     -> is:seq ikind
                     -> ds:seq constructor
                     -> Mem (MkIndType is ds) I
                     -> Mem (MkConstructor d t) ds
                     -> ICompBinds_C I d t

type VlNames :: environment => seq vlname => P =
   | VLN_Nil : VlNames [] []
   | VLN_ConsV : G:environment -> v:vlname -> t:typ -> names:seq vlname
              -> VlNames G names
              -> VlNames ((FV_VlName v t)::G) (v::names)
   | VLN_ConsT : G:environment -> a:tyname -> k:kind -> names:seq vlname
              -> VlNames G names
              -> VlNames ((FV_TyName a k)::G) names

type TyNames :: environment => seq tyname => P =
   | TYN_Nil : TyNames [] []
   | TYN_ConsV : G:environment -> v:vlname -> t:typ -> names:seq tyname
              -> TyNames G names
              -> TyNames ((FV_VlName v t)::G) names
   | TYN_ConsT : G:environment -> a:tyname -> k:kind -> names:seq tyname
              -> TyNames G names
              -> TyNames ((FV_TyName a k)::G) (a::names)

type BindingBvars :: bindings => seq bvar => P =
   | BB_Nil : BindingBvars [] []
   | BB_BVT : B:bindings -> x:bvar -> t:typ -> xs:seq bvar
            -> BindingBvars B xs
            -> BindingBvars ((LB_BvarTy x t)::B) (x::xs)
   | BB_BTK : B:bindings -> a:bvar -> k:kind -> xs:seq bvar
            -> BindingBvars B xs
            -> BindingBvars ((LB_BvarKind a k)::B) (a::xs)
   | BB_VlEq : B:bindings -> v1:value -> v2:value -> xs:seq bvar
            -> BindingBvars B xs
            -> BindingBvars ((LB_VlEq v1 v2)::B) xs
   | BB_TyEq : B:bindings -> t1:typ -> t2:typ -> xs:seq bvar
            -> BindingBvars B xs
            -> BindingBvars ((LB_TyEq t1 t2)::B) xs


val lookup_iname : i:icompartment -> j:name -> option (k:kind * ICompBinds_I i j k)
let rec lookup_iname i j = match i with
  | [] -> None
  | (MkIndType is ds)::tl ->
      let fopt = find<ikind, (fun (i:ikind) => TT)> (fun x -> match x with
                                                         | MkIKind j' k' when j=j' -> SomeP True
                                                         | _ -> NoneP) is in
        match fopt with
          | None ->
              (match lookup_iname tl j with
                 | Some ((k, (ICompBinds_ind _tl _j _k is' ds' mtl mis))) ->
                     let m = Mem_tl (MkIndType is' ds') (MkIndType is ds) tl mtl in
                     let binds = ICompBinds_ind i j k is' ds' m mis in
                       Some (k, binds)
                 | None -> None)
          | Some (((MkIKind j' k), _, mis)) ->
              (if j=j'
               then
                 let binds = ICompBinds_ind i j k is ds (Mem_hd (MkIndType is ds) tl) mis in
                   Some (k, binds)
               else None)
                
private val lookup_constr: s:seq constructor -> d:cname -> option (t:typ * Mem (MkConstructor d t) s)
let rec lookup_constr s d = match s with
  | [] -> None
  | hd::tl ->
      match hd with
        | MkConstructor d' t when d=d' -> Some (t, Mem_hd hd tl)
        | _ ->
            match lookup_constr tl d with
              | None -> None
              | Some ((t, pf)) -> Some (t, Mem_tl (MkConstructor d t) hd tl pf)

val lookup_dcon : I:icompartment -> d:cname -> option (t:typ * ICompBinds_C I d t)
let rec lookup_dcon i d = match i with
  | [] -> None
  | (MkIndType is ds)::tl ->
      match lookup_constr ds d with
        | None ->
            (match lookup_dcon tl d with
               | None -> None
               | Some ((t, ICompBinds_dcon _tl _d _t is' ds' mem_is' mem_ds')) ->
                   Some (t, ICompBinds_dcon i d t is' ds' (Mem_tl (MkIndType is' ds') (MkIndType is ds) tl mem_is') mem_ds'))
        | Some ((t, pf)) -> Some (t, ICompBinds_dcon i d t is ds (Mem_hd (MkIndType is ds) tl) pf)

type ex :: 'a::* => 'b::('a => P) => P =
  | MkEx1 : b:fvbinding
         -> x:vlname
         -> t:typ
         -> (Eq b (FV_VlName x t))
         -> ex typ (fun (t:typ) => Eq b (FV_VlName x t))

  | MkEx2 : b:fvbinding
          -> x:tyname
          -> k:kind
          -> (Eq b (FV_TyName x k))
          -> ex kind (fun (k:kind) => (Eq b (FV_TyName x k)))

  | MkEx3 : i:inductive
          -> iks:seq ikind
          -> ds:seq constructor
          -> (Eq i (MkIndType iks ds))
          -> ex (seq constructor) (fun (ds:seq constructor) => Eq i (MkIndType iks ds))

  | MkEx4 : i:inductive
          -> ds:seq constructor
          -> iks:seq ikind
          -> (Eq i (MkIndType iks ds))
          -> ex (seq ikind) (fun (iks:seq ikind) => Eq i (MkIndType iks ds))

  | MkEx5 : ik:ikind
          -> i:iname
          -> k:kind
          -> (Eq ik (MkIKind i k))
          -> ex kind (fun (k:kind) => Eq ik (MkIKind i k))

  | MkEx6 : c:constructor
          -> cn:cname
          -> t:typ
          -> (Eq c (MkConstructor cn t))
          -> ex typ (fun (t:typ) => (Eq c (MkConstructor cn t)))

  | MkEx7 : b:locbinding
           -> a:bvar
           -> ta:typ
           -> (Eq b (LB_TyEq (T_Var (GV_Bound a)) ta))
           -> ex typ (fun (ta:typ) => Eq b (LB_TyEq (T_Var (GV_Bound a)) ta))

  | MkEx8 :  b:locbinding
          -> a:bvar
          -> va:value
          -> (Eq b (LB_VlEq (V_Var (GV_Bound a)) va))
          -> ex value (fun (va:value) => Eq b (LB_VlEq (V_Var (GV_Bound a)) va))

  | MkEx9: i:inductive
         -> iks:seq ikind
         -> ds:seq constructor
         -> (Eq i (MkIndType iks ds))
         -> ex (seq constructor) (fun (ds:seq constructor) => Eq i (MkIndType iks ds))

  | MkEx10: i:inductive
         -> ds:seq constructor
         -> iks:seq ikind
         -> (Eq i (MkIndType iks ds))
         -> ex (seq ikind) (fun (iks:seq ikind) => Eq i (MkIndType iks ds))

            
type exists_vl :: _ = (fun (x:vlname) (b:fvbinding) => (ex typ (fun (t:typ) => Eq b (FV_VlName x t))))
val vlEq: x:vlname -> b:fvbinding -> optionP (exists_vl x b)
let vlEq x b = match b with
  | FV_VlName x' t when x=x' -> SomeP (MkEx1 b x t (Refl_eq b))
  | _ -> NoneP

type exists_ty :: _ = (fun (x:tyname) (b:fvbinding) => (ex kind (fun (k:kind) => Eq b (FV_TyName x k))))
val tyEq: x:tyname -> b:fvbinding -> optionP (exists_ty x b)
let tyEq x b = match b with
  | FV_TyName x' k when x=x' -> SomeP (MkEx2 b x k (Refl_eq b))
  | _ -> NoneP

val lookup_vlname : F:environment -> x:vlname -> option (t:typ * Mem (FV_VlName x t) F)
let lookup_vlname f x =
  match find<fvbinding, (exists_vl x)> (vlEq x) f with
    | Some (((FV_VlName x' t), _, pf_mem)) when x=x' -> (* TODO: just destruct the MkEx proof *)
        Some (t, pf_mem)
    | _ -> None

val lookup_tyname : F:environment -> x:tyname -> option (k:kind * Mem (FV_TyName x k) F)
let lookup_tyname f x =
  match find<fvbinding, (exists_ty x)> (tyEq x) f with
    | Some (((FV_TyName x' k), _, pf_mem)) when x=x' -> (* TODO: just destruct the MkEx proof *)
        Some (k, pf_mem)
    | _ -> None

val lookup_ty   : G:bindings -> x:bvar -> option (t:typ * Mem (LB_BvarTy x t) G)
let rec lookup_ty g x = match g with
  | [] -> None
  | hd::tl ->
      match hd with
        | LB_BvarTy(x', t) when x=x' ->
            Some (t, Mem_hd hd tl)
        | _ ->
            match lookup_ty tl x with
              | None -> None
              | Some ((t, mtl)) -> Some (t, Mem_tl (LB_BvarTy x t) hd tl mtl)


val lookup_kind : G:bindings -> x:bvar -> option (k:kind * Mem (LB_BvarKind x k) G)
let rec lookup_kind g x = match g with
  | [] -> None
  | hd::tl ->
      match hd with
        | LB_BvarKind(x', k) when x=x' ->
            Some (k, Mem_hd hd tl)
        | _ ->
            match lookup_kind tl x with
              | None -> None
              | Some ((k, mtl)) -> Some (k, Mem_tl (LB_BvarKind x k) hd tl mtl)

type ValueEq :: _ =
    EqReln bindings value (fun (G:bindings) (x:value) (y:value) => Mem (LB_VlEq x y) G)

type TypeEq :: _ =
    EqReln bindings typ (fun (G:bindings) (x:typ) (y:typ) => Mem (LB_TyEq x y) G)

val is_value_eq : G:bindings -> v1:value -> v2:value -> optionP (ValueEq G v1 v2)
let is_value_eq g v1 v2 = raise "NYI is_value_eq"

val is_typ_eq   : G:bindings -> t1:typ -> t2:typ -> optionP (TypeEq G t1 t2)
let is_typ_eq g t1 t2 = raise "NYI is_value_eq"

end


(* ******************************************************************************** *)
module FreeNames
open Util
open FiniteSet
open Terms

type vsortT =
  | TermNameT : vsortT
  | TypeNameT : vsortT

type bname = tup bvar vsortT
type bnames = seq bname

type AsTypeName :: bvar => bname => P =
   | MkAsTypeName : x:bvar -> AsTypeName x (Tup x TypeNameT)
type AsTypeNames :: _ = Zip bvar bname AsTypeName

type AsTermName :: bvar => bname => P =
   | MkAsTermName : x:bvar -> AsTermName x (Tup x TermNameT)
type AsTermNames :: _ = Zip bvar bname AsTermName

val asTypeName : x:bvar -> (y:bname * AsTypeName x y)
let asTypeName (x:bvar) = ((Tup x TypeNameT), MkAsTypeName x)

val asTermName : x:bvar -> (y:bname * AsTermName x y)
let asTermName (x:bvar) = ((Tup x TermNameT), MkAsTermName x)

type FreeBvarsK' :: bnames => bnames => kind => bnames => P =
   | FBK_Base  : bound:bnames -> accum:bnames -> b:basekind
              -> FreeBvarsK' bound accum (K_Base b) accum

   | FBK_ProdK : bound:bnames -> accum:bnames -> a:bvar -> k1:kind -> k2:kind
                -> accum':bnames -> out:bnames
                -> FreeBvarsK' bound accum k1 accum'
                -> FreeBvarsK' ((Tup a TypeNameT)::bound) accum' k2 out
                -> FreeBvarsK' bound accum (K_ProdK a k1 k2) out

   | FBK_ProdT : bound:bnames -> accum:bnames -> a:bvar -> t1:typ -> k2:kind
                -> accum':bnames -> out:bnames
                -> FreeBvarsT' bound accum t1 accum'
                -> FreeBvarsK' ((Tup a TermNameT)::bound) accum' k2 out
                -> FreeBvarsK' bound accum (K_ProdT a t1 k2) out

and FreeBvarsT' :: bnames => bnames => typ => bnames => P =
   | FBT_Var1 : bound:bnames -> accum:bnames -> a:bvar
             -> NotMem (Tup a TypeNameT) bound
             -> FreeBvarsT' bound accum (T_Var (GV_Bound a)) ((Tup a TypeNameT)::accum)

   | FBT_Var2 : bound:bnames -> accum:bnames -> a:bvar
             -> Mem (Tup a TypeNameT) bound
             -> FreeBvarsT' bound accum (T_Var (GV_Bound a)) accum

   | FBT_FVar : bound:bnames -> accum:bnames -> a:tyname
             -> FreeBvarsT' bound accum (T_Var (GV_Free a)) accum

   | FBT_Unit : bound:bnames -> accum:bnames
             -> FreeBvarsT' bound accum T_Unit accum

   | FBT_Ind : bound:bnames -> accum:bnames -> i:iname
             -> FreeBvarsT' bound accum (T_Ind i) accum

   | FBT_VApp : bound:bnames -> accum:bnames -> t:typ -> v:value
             -> accum_t:bnames
             -> out:bnames
             -> FreeBvarsT' bound accum t accum_t
             -> FreeBvarsV' bound accum_t v out
             -> FreeBvarsT' bound accum (T_VApp t v) out

   | FBT_App : bound:bnames -> accum:bnames -> t1:typ -> t2:typ
             -> accum_t1:bnames
             -> out:bnames
             -> FreeBvarsT' bound accum t1 accum_t1
             -> FreeBvarsT' bound accum_t1 t2 out
             -> FreeBvarsT' bound accum (T_App t1 t2) out

   | FBT_Prod : bound:bnames -> accum:bnames -> x:bvar -> t1:typ -> t2:typ
             -> accum_t1:bnames -> out:bnames
             -> FreeBvarsT' bound accum t1 accum_t1
             -> FreeBvarsT' ((Tup x TermNameT)::bound) accum_t1 t2 out
             -> FreeBvarsT' bound accum (T_Prod x t1 t2) out

   | FBT_ProdK : bound:bnames -> accum:bnames -> x:bvar -> k1:kind -> t2:typ
             -> accum_k1:bnames
             -> out:bnames
             -> FreeBvarsK' bound accum k1 accum_k1
             -> FreeBvarsT' ((Tup x TypeNameT)::bound) accum_k1 t2 out
             -> FreeBvarsT' bound accum (T_ProdK x k1 t2) out

   | FBT_Ref : bound:bnames -> accum:bnames -> x:bvar -> t1:typ -> t2:typ
             -> accum_t1:bnames
             -> out:bnames
             -> FreeBvarsT' bound accum t1 accum_t1
             -> FreeBvarsT' ((Tup x TermNameT)::bound) accum_t1 t2 out
             -> FreeBvarsT' bound accum (T_Ref x t1 t2) out

   | FBT_Lam : bound:bnames -> accum:bnames -> x:bvar -> t1:typ -> t2:typ
             -> accum_t1:bnames
             -> out:bnames
             -> FreeBvarsT' bound accum t1 accum_t1
             -> FreeBvarsT' ((Tup x TermNameT)::bound) accum_t1 t2 out
             -> FreeBvarsT' bound accum (T_Lam x t1 t2) out

   | FBT_Afn : bound:bnames -> accum:bnames -> t1:typ
             -> out:bnames
             -> FreeBvarsT' bound accum t1 out
             -> FreeBvarsT' bound accum (T_Afn t1) out


   | FBT_Asc : bound:bnames -> accum:bnames -> t1:typ -> k:kind
             -> accum_t1:bnames
             -> out:bnames
             -> FreeBvarsT' bound accum t1 accum_t1
             -> FreeBvarsK' bound accum_t1 k out
             -> FreeBvarsT' bound accum (T_Ascribe t1 k) out

and FreeBvarsV' :: bnames => bnames => value => bnames => P =
   | FBV_Var1 : bound:bnames -> accum:bnames -> a:bvar
             -> NotMem (Tup a TermNameT) bound
             -> FreeBvarsV' bound accum (V_Var (GV_Bound a)) ((Tup a TermNameT)::accum)

   | FBV_Var2 : bound:bnames -> accum:bnames -> a:bvar
             -> Mem (Tup a TermNameT) bound
             -> FreeBvarsV' bound accum (V_Var (GV_Bound a)) accum

   | FBV_FVar : bound:bnames -> accum:bnames -> a:vlname
             -> FreeBvarsV' bound accum (V_Var (GV_Free a)) accum

   | FBV_VUnit : bound:bnames -> accum:bnames
             -> FreeBvarsV' bound accum V_Unit accum

   | FBV_Fun : bound:bnames -> accum:bnames -> x:bvar -> t:typ -> e:expr
             -> accum_t:bnames
             -> out:bnames
             -> FreeBvarsT' bound accum t accum_t
             -> FreeBvarsE' ((Tup x TermNameT)::bound) accum_t e out
             -> FreeBvarsV' bound accum (V_Fun x t e) out

   | FBV_FunT : bound:bnames -> accum:bnames -> x:bvar -> k:kind -> e:expr
             -> accum_k:bnames
             -> out:bnames
             -> FreeBvarsK' bound accum k accum_k
             -> FreeBvarsE' ((Tup x TypeNameT)::bound) accum_k e out
             -> FreeBvarsV' bound accum (V_FunT x k e) out

   | FBV_Const : bound:bnames -> accum:bnames -> c:name -> tl:seq typ -> vl:seq value
             -> e1:expr -> e:expr -> v:vlname -> out:bnames
             -> CurryT (E_Value (V_Var (GV_Free v))) tl e1
             -> CurryV e1 vl e
             -> FreeBvarsE' bound accum e out
             -> FreeBvarsV' bound accum (V_Const c tl vl) out

   | FBV_Ascribe : bound:bnames -> accum:bnames -> v:value -> t:typ
             -> accum_v:bnames
             -> out:bnames
             -> FreeBvarsV' bound accum v accum_v
             -> FreeBvarsT' bound accum_v t out
             -> FreeBvarsV' bound accum (V_Ascribe v t) out

and FreeBvarsE' :: bnames => bnames => expr => bnames => P =
   | FBE_Val :  bound:bnames -> accum:bnames -> v:value
              -> accum':bnames
              -> FreeBvarsV' bound accum v accum'
              -> FreeBvarsE' bound accum (E_Value v) accum'

   | FBE_App :  bound:bnames -> accum:bnames -> e1:expr -> v2:value
             -> accum1:bnames
             -> out:bnames
             -> FreeBvarsE' bound accum e1 accum1
             -> FreeBvarsV' bound accum1 v2 out
             -> FreeBvarsE' bound accum (E_App e1 v2) out

   | FBE_TApp :  bound:bnames -> accum:bnames -> e1:expr -> t2:typ
             -> accum1:bnames
             -> out:bnames
             -> FreeBvarsE' bound accum e1 accum1
             -> FreeBvarsT' bound accum1 t2 out
             -> FreeBvarsE' bound accum (E_TApp e1 t2) out

   | FBE_LetIn :  bound:bnames -> accum:bnames -> x:bvar -> e1:expr -> e2:expr
             -> accum1:bnames
             -> out:bnames
             -> FreeBvarsE' bound accum e1 accum1
             -> FreeBvarsE' ((Tup x TermNameT)::bound) accum1 e2 out
             -> FreeBvarsE' bound accum (E_LetIn x e1 e2) out

   | FBE_Match :  bound:bnames -> accum:bnames
             -> v:value -> c:cname -> alphas:seq bvar -> xs:seq bvar -> ethen:expr -> eelse:expr
             -> accumv:bnames
             -> accumthen:bnames
             -> out:bnames
             -> bound1:bnames -> boundthen:bnames
             -> alphas':bnames -> xs':bnames
             -> AsTypeNames alphas alphas'
             -> AsTermNames xs xs'
             -> Append xs' bound bound1
             -> Append alphas' bound1 boundthen
             -> FreeBvarsV' bound accum v accumv
             -> FreeBvarsE' boundthen accumv ethen accumthen
             -> FreeBvarsE' bound accumthen eelse out
             -> FreeBvarsE' bound accum (E_Match v (MkPattern c alphas xs) ethen eelse) out

   | FBE_Assume :  bound:bnames -> accum:bnames -> t:typ
             -> out:bnames
             -> FreeBvarsT' bound accum t out
             -> FreeBvarsE' bound accum (E_Assume t) out

   | FBE_Ascribe :  bound:bnames -> accum:bnames -> e:expr -> t:typ
             -> accum_e:bnames
             -> out:bnames
             -> FreeBvarsE' bound accum e accum_e
             -> FreeBvarsT' bound accum_e t out
             -> FreeBvarsE' bound accum (E_Ascribe e t) out

type FreeBvarsK :: _ = FreeBvarsK' [] []
type FreeBvarsT :: _ = FreeBvarsT' [] []
type FreeBvarsV :: _ = FreeBvarsV' [] []
type FreeBvarsE :: _ = FreeBvarsE' [] []

type fvk :: _ = fun (k:kind)  => (bound:bnames -> a:bnames -> (fvs:bnames * FreeBvarsK' bound a k fvs))
type fvt :: _ = fun (k:typ)   => (bound:bnames -> a:bnames -> (fvs:bnames * FreeBvarsT' bound a k fvs))
type fvv :: _ = fun (k:value) => (bound:bnames -> a:bnames -> (fvs:bnames * FreeBvarsV' bound a k fvs))
type fve :: _ = fun (k:expr)  => (bound:bnames -> a:bnames -> (fvs:bnames * FreeBvarsE' bound a k fvs))

val free_bvars_kind'  : fix fvk fvt fvv fve -> k:kind  -> fvk k
let free_bvars_kind' ff k bound accum =
  match ff with
    | MkFix fbk fbt fbv fbe ->
        match k with
          | K_Base b -> (accum, FBK_Base bound accum b)
              
          | K_ProdK a k1 k2 ->
              let accum1, pf1 = fbk ff k1 bound accum in
              let out, pf2 = fbk ff k2 ((Tup a TypeNameT)::bound) accum1 in
                (out, FBK_ProdK bound accum a k1 k2 accum1 out pf1 pf2)
                  
          | K_ProdT a t1 k2 ->
              let accum1, pf1 = fbt ff t1 bound accum in
              let out, pf2 = fbk ff k2 ((Tup a TermNameT)::bound) accum1 in
                (out, FBK_ProdT bound accum a t1 k2 accum1 out pf1 pf2)

val free_bvars_typ' : fix fvk fvt fvv fve -> k:typ   -> fvt k
let free_bvars_typ' ff t bound accum =
  match ff with
    | MkFix fbk fbt fbv fbe ->
        match t with
          | T_Var (GV_Bound a) ->
              (match decideMem (Tup a TypeNameT) bound with
                 | InrStar pf_notmem -> (((Tup a TypeNameT)::accum), FBT_Var1 bound accum a pf_notmem)
                 | InlStar pf_mem -> (accum, FBT_Var2 bound accum a pf_mem))

          | T_Var (GV_Free a) ->
              (accum, FBT_FVar bound accum a)

          | T_Unit ->
              (accum, FBT_Unit bound accum)

          | T_Ind i ->
              (accum, FBT_Ind bound accum i)
                
          | T_VApp t v ->
              let accum_t, pf_t = fbt ff t bound accum in
              let out, pf_v = fbv ff v bound accum_t in
                (out, FBT_VApp bound accum t v accum_t out pf_t pf_v)

          | T_App t1 t2 ->
              let accum_t1, pf_t1 = fbt ff t1 bound accum in
              let out, pf_t2 = fbt ff t2 bound accum_t1 in
                (out, FBT_App bound accum t1 t2 accum_t1 out pf_t1 pf_t2)
                  
          | T_Prod x t1 t2 ->
              let accum_t1, pf_t1 = fbt ff t1 bound accum in
              let out, pf_t2 = fbt ff t2 ((Tup x TermNameT)::bound) accum_t1 in
                (out, FBT_Prod bound accum x t1 t2 accum_t1 out pf_t1 pf_t2)

          | T_ProdK x k1 t2 ->
              let accum_k1, pf_k1 = fbk ff k1 bound accum in
              let out, pf_t2 = fbt ff t2 ((Tup x TypeNameT)::bound) accum_k1 in
                (out, FBT_ProdK bound accum x k1 t2 accum_k1 out pf_k1 pf_t2)

          | T_Ref x t1 t2 ->
              let accum_t1, pf_t1 = fbt ff t1 bound accum in
              let out, pf_t2 = fbt ff t2 ((Tup x TermNameT)::bound) accum_t1 in
                (out, FBT_Ref bound accum x t1 t2 accum_t1 out pf_t1 pf_t2)

          | T_Lam x t1 t2 ->
              let accum_t1, pf_t1 = fbt ff t1 bound accum in
              let out, pf_t2 = fbt ff t2 ((Tup x TermNameT)::bound) accum_t1 in
                (out, FBT_Lam bound accum x t1 t2 accum_t1 out pf_t1 pf_t2)

          | T_Afn t1 ->
              let out, pf = fbt ff t1 bound accum in
                (out, FBT_Afn bound accum t1 out pf)
                  
          | T_Ascribe t1 k ->
              let accum_t1, pf_t1 = fbt ff t1 bound accum in
              let out, pf_k = fbk ff k bound accum_t1 in
                (out, FBT_Asc bound accum t1 k accum_t1 out pf_t1 pf_k)

val free_bvars_value' : fix fvk fvt fvv fve -> k:value -> fvv k
let free_bvars_value' ff v bound accum =
  match ff with
    | MkFix fbk fbt fbv fbe ->
        match v with
          | V_Var (GV_Bound x) ->
              (match decideMem (Tup x TermNameT) bound with
                 | InrStar pf_notmem -> (((Tup x TermNameT)::accum), FBV_Var1 bound accum x pf_notmem)
                 | InlStar pf_mem -> (accum, FBV_Var2 bound accum x pf_mem))

          | V_Var (GV_Free x) -> (accum, FBV_FVar bound accum x)

          | V_Fun x t e ->
              let accum_t1, pf_t1 = fbt ff t bound accum in
              let out, pf = fbe ff e ((Tup x TermNameT)::bound) accum_t1 in
                (out, FBV_Fun bound accum x t e accum_t1 out pf_t1 pf)

          | V_Fun a k e ->
              let accum_k, pf_k = fbk ff k bound accum in
              let out, pf = fbe ff e ((Tup x TypeNameT)::bound) accum_k in
                (out, FBV_FunT bound accum a k e accum_k out pf_k pf)

          | V_Unit -> (accum, FBV_VUnit bound accum)

          | V_Const c tl vl ->
              let v = freshname false in
              let e1, pf1 = curryt (E_Value (V_Var (GV_Free v))) tl in
              let e, pf2 = curryv e1 vl in
              let out, pf = fbe ff e bound accum in
                (out, FBV_Const bound accum c tl vl e1 e v out pf1 pf2 pf)

          | V_Ascribe v t ->
              let accum_v, pf_v = fbv ff v bound accum in
              let out, pf_t = fbt ff t bound accum_v in
                (out, FBV_Ascribe bound accum v t accum_v out pf_v pf_t)

val free_bvars_expr' : fix fvk fvt fvv fve -> k:expr  -> fve k
let free_bvars_expr' ff e bound accum =
  match ff with
    | MkFix fbk fbt fbv fbe ->
        match e with
          | E_Value v ->
              let out, pf = fbv ff v bound accum in
                (out, FBE_Val bound accum v out pf)

          | E_App e1 v2 ->
              let accum_1, pf_1 = fbe ff e1 bound accum in
              let out, pf = fbv ff v2 bound accum_1 in
                (out, FBE_App bound accum e1 v2 accum_1 out pf_1 pf)

          | E_TApp e1 t2 ->
              let accum_1, pf_1 = fbe ff e1 bound accum in
              let out, pf = fbt ff t2 bound accum_1 in
                (out, FBE_TApp bound accum e1 t2 accum_1 out pf_1 pf)

          | E_LetIn x e1 e2 ->
              let accum_1, pf_1 = fbe ff e1 bound accum in
              let out, pf = fbe ff e2 ((Tup x TermNameT)::bound) accum_1 in
                (out, FBE_LetIn bound accum x e1 e2 accum_1 out pf_1 pf)

          | E_Match v (MkPattern c alphas xs) ethen eelse ->
              let alphas', pf_alphas' = map_p<bvar, bname, AsTypeName> asTypeName alphas in
              let xs', pf_xs' = map_p<bvar, bname, AsTermName> asTermName xs in
              let b1, pf_b1 = append_pf xs' bound in
              let bthen, pf_bthen = append_pf alphas' b1 in
              let a1, pf1 = fbv ff v bound accum in
              let a2, pf2 = fbe ff ethen bthen a1 in
              let out, pf = fbe ff eelse bound a2 in
                (out, FBE_Match bound accum v c alphas xs ethen eelse a1 a2 out b1 bthen alphas' xs' pf_alphas' pf_xs' pf_b1 pf_bthen pf1 pf2 pf)

          | E_Assume t ->
              let out, pf = fbt ff t bound accum in
                (out, FBE_Assume bound accum t out pf)
                  
          | E_Ascribe e t ->
              let accum_1, pf_1 = fbe ff e bound accum in
              let out, pf = fbt ff t bound accum_1 in
                (out, FBE_Ascribe bound accum e t accum_1 out pf_1 pf)


val free_bvars_kind : k:kind -> (out:bnames * FreeBvarsK k out)
let free_bvars_kind k =
  free_bvars_kind'
    (MkFix
       free_bvars_kind'
       free_bvars_typ'
       free_bvars_value'
       free_bvars_expr') k [] []

val free_bvars_kind_nopf : kind -> seq name
let free_bvars_kind_nopf k =
  let x, _ = free_bvars_kind k in
    Prims.map (function (Tup n _) -> n) x

val free_bvars_typ : t:typ -> (out:bnames * FreeBvarsT t out)
let free_bvars_typ t =
  free_bvars_typ'
    (MkFix
       free_bvars_kind'
       free_bvars_typ'
       free_bvars_value'
       free_bvars_expr') t [] []

val free_bvars_typ_nopf : typ -> seq name
let free_bvars_typ_nopf t =
  let x, _ = free_bvars_typ t in
    Prims.map (function (Tup n _) -> n) x

val free_bvars_value : t:value -> (out:bnames * FreeBvarsV t out)
let free_bvars_value t =
  free_bvars_value'
    (MkFix
       free_bvars_kind'
       free_bvars_typ'
       free_bvars_value'
       free_bvars_expr') t [] []

end
(* ********************************************************************************  *)

module Binders
open Util
open FiniteSet
open Terms
open FreeNames

type BindersK' :: bnames => kind => bnames => P =
   | BNDK_Base  : bs:bnames -> b:basekind
              -> BindersK' bs (K_Base b) bs

   | BNDK_ProdK : bs:bnames -> a:bvar -> k1:kind -> k2:kind
                -> bs':bnames -> out:bnames
                -> BindersK' bs k1 bs'
                -> BindersK' ((Tup a TypeNameT)::bs') k2 out
                -> BindersK' bs (K_ProdK a k1 k2) out

   | BNDK_ProdT : bs:bnames -> a:bvar -> t1:typ -> k2:kind
                -> bs':bnames -> out:bnames
                -> BindersT' bs t1 bs'
                -> BindersK' ((Tup a TermNameT)::bs') k2 out
                -> BindersK' bs (K_ProdT a t1 k2) out

and BindersT' :: bnames => typ => bnames => P =
   | BNDT_Var : bs:bnames -> a:gvar tyname
             -> BindersT' bs (T_Var a) bs

   | BNDT_Unit : bs:bnames
             -> BindersT' bs T_Unit bs

   | BNDT_Ind : bs:bnames -> i:iname
             -> BindersT' bs (T_Ind i) bs

   | BNDT_VApp : bs:bnames -> t:typ -> v:value
             -> bs':bnames -> out:bnames
             -> BindersT' bs t bs'
             -> BindersV' bs' v out
             -> BindersT' bs (T_VApp t v) out

   | BNDT_App : bs:bnames -> t:typ -> t':typ
             -> bs':bnames -> out:bnames
             -> BindersT' bs t bs'
             -> BindersT' bs' t' out
             -> BindersT' bs (T_App t t') out

   | BNDT_Prod : bs:bnames -> x:bvar -> t1:typ -> t2:typ
             -> bs':bnames -> out:bnames
             -> BindersT' bs t1 bs'
             -> BindersT' ((Tup x TermNameT)::bs') t2 out
             -> BindersT' bs (T_Prod x t1 t2) out

   | BNDT_ProdK : bs:bnames -> x:bvar -> k1:kind -> t2:typ
             -> bs':bnames -> out:bnames
             -> BindersK' bs k1 bs'
             -> BindersT' ((Tup x TypeNameT)::bs') t2 out
             -> BindersT' bs (T_ProdK x k1 t2) out

   | BNDT_Ref :  bs:bnames -> x:bvar -> t1:typ -> t2:typ
             -> bs':bnames -> out:bnames
             -> BindersT' bs t1 bs'
             -> BindersT' ((Tup x TermNameT)::bs') t2 out
             -> BindersT' bs (T_Ref x t1 t2) out

   | BNDT_Lam :  bs:bnames -> x:bvar -> t1:typ -> t2:typ
             -> bs':bnames -> out:bnames
             -> BindersT' bs t1 bs'
             -> BindersT' ((Tup x TermNameT)::bs') t2 out
             -> BindersT' bs (T_Lam x t1 t2) out

   | BNDT_Afn : bs:bnames -> t:typ -> out:bnames
             -> BindersT' bs t out
             -> BindersT' bs (T_Afn t) out

   | BNDT_Asc : bs:bnames -> t:typ -> k:kind
             -> bs':bnames -> out:bnames
             -> BindersT' bs t bs'
             -> BindersK' bs' k out
             -> BindersT' bs (T_Ascribe t k) out

and BindersV' :: bnames => value => bnames => P =
   | BNDV_Var : bs:bnames -> a:gvar vlname
             -> BindersV' bs (V_Var a) bs

   | BNDV_Unit : bs:bnames -> BindersV' bs V_Unit bs

   | BNDV_Fun : bs:bnames -> x:bvar -> t:typ -> e:expr
             -> bs':bnames -> out:bnames
             -> BindersT' bs t bs'
             -> BindersE' ((Tup x TermNameT)::bs') e out
             -> BindersV' bs (V_Fun x t e) out

   | BNDV_FunT : bs:bnames -> x:bvar -> k:kind -> e:expr
             -> bs':bnames -> out:bnames
             -> BindersK' bs k bs'
             -> BindersE' ((Tup x TypeNameT)::bs') e out
             -> BindersV' bs (V_FunT x k e) out

   | BNDV_Const : bs:bnames -> c:name -> tl:seq typ -> vl:seq value
             -> e1:expr -> e:expr -> v:vlname -> out:bnames
             -> CurryT (E_Value (V_Var (GV_Free v))) tl e1
             -> CurryV e1 vl e
             -> BindersE' bs e out
             -> BindersV' bs (V_Const c tl vl) out

   | BNDV_Ascribe : bs:bnames -> v:value -> t:typ
             -> bs':bnames -> out:bnames
             -> BindersV' bs v bs'
             -> BindersT' bs' t out
             -> BindersV' bs (V_Ascribe v t) out

and BindersE' :: bnames => expr => bnames => P =
   | BNDE_Val :  bs:bnames -> v:value -> out:bnames
              -> BindersV' bs v out
              -> BindersE' bs (E_Value v) out

   | BNDE_App :  bs:bnames -> e:expr -> v:value
             -> bs':bnames -> out:bnames
             -> BindersE' bs e bs'
             -> BindersV' bs' v out
             -> BindersE' bs (E_App e v) out

   | BNDE_TApp :  bs:bnames -> e:expr -> t:typ
             -> bs':bnames -> out:bnames
             -> BindersE' bs e bs'
             -> BindersT' bs' t out
             -> BindersE' bs (E_TApp e t) out

   | BNDE_LetIn :  bs:bnames -> x:bvar -> e1:expr -> e2:expr
             -> bs':bnames -> out:bnames
             -> BindersE' bs e1 bs'
             -> BindersE' ((Tup x TermNameT)::bs') e2 out
             -> BindersE' bs (E_LetIn x e1 e2) out

   | BNDE_Match :  bs:bnames -> v:value -> c:cname -> alphas:seq bvar -> xs:seq bvar
             -> ethen:expr -> eelse:expr
             -> bs1:bnames -> bs2:bnames -> out:bnames
             -> bs1':bnames -> bs1'':bnames
             -> alphas':bnames -> xs':bnames
             -> AsTypeNames alphas alphas'
             -> AsTermNames xs xs'
             -> Append alphas' bs1 bs1'
             -> Append xs' bs1' bs1''
             -> BindersV' bs v bs1
             -> BindersE' bs1'' ethen bs2
             -> BindersE' bs2 eelse out
             -> BindersE' bs (E_Match v (MkPattern c alphas xs) ethen eelse) out

   | BNDE_Assume :  bs:bnames -> t:typ -> out:bnames
             -> BindersT' bs t out
             -> BindersE' bs (E_Assume t) out

   | BNDE_Ascribe : bs:bnames -> e:expr -> t:typ
             -> bs':bnames -> out:bnames
             -> BindersE' bs e bs'
             -> BindersT' bs' t out
             -> BindersE' bs (E_Ascribe e t) out

type BindersK :: _ = BindersK' []
type BindersT :: _ = BindersT' []
type BindersV :: _ = BindersV' []
type BindersE :: _ = BindersE' []

type bndk :: _ = fun (k:kind)  => (bs:bnames -> (out:bnames * BindersK' bs k out))
type bndt :: _ = fun (k:typ)   => (bs:bnames -> (out:bnames * BindersT' bs k out))
type bndv :: _ = fun (k:value) => (bs:bnames -> (out:bnames * BindersV' bs k out))
type bnde :: _ = fun (k:expr)  => (bs:bnames -> (out:bnames * BindersE' bs k out))


val binders_kind'  : fix bndk bndt bndv bnde -> k:kind  -> bndk k
let binders_kind' ff k bs =
  match ff with
    | MkFix binders_kind' binders_typ' binders_value' binders_expr' ->
        match k with
          | K_Base b -> (bs, BNDK_Base bs b)
              
          | K_ProdK a k1 k2 ->
              let bs', pf1 = binders_kind' ff k1 bs in
              let out, pf2 = binders_kind' ff k2 ((Tup a TypeNameT)::bs') in
                (out, BNDK_ProdK bs a k1 k2 bs' out pf1 pf2)
                  
          | K_ProdT a t1 k2 ->
              let bs', pf1 = binders_typ' ff t1 bs in
              let out, pf2 = binders_kind' ff k2 ((Tup a TermNameT)::bs') in
                (out, BNDK_ProdT bs a t1 k2 bs' out pf1 pf2)

val binders_typ' : fix bndk bndt bndv bnde -> t:typ  -> bndt t
let binders_typ' ff t bs =
  match ff with
    | MkFix binders_kind' binders_typ' binders_value' binders_expr' ->
        match t with
          | T_Var a -> (bs, BNDT_Var bs a)

          | T_Unit  -> (bs, BNDT_Unit bs)

          | T_Ind i -> (bs, BNDT_Ind bs i)
                
          | T_VApp t v ->
              let bs', pf1 = binders_typ' ff t bs in
              let out, pf2 = binders_value' ff v bs' in
                (out, BNDT_VApp bs t v bs' out pf1 pf2)

          | T_App t1 t2 ->
              let bs', pf1 = binders_typ' ff t1 bs in
              let out, pf2 = binders_typ' ff t2 bs' in
                (out, BNDT_App bs t1 t2 bs' out pf1 pf2)
                  
          | T_Prod x t1 t2 ->
              let bs', pf1 = binders_typ' ff t1 bs in
              let out, pf2 = binders_typ' ff t2 ((Tup x TermNameT)::bs') in
                (out, BNDT_Prod bs x t1 t2 bs' out pf1 pf2)

          | T_ProdK x k1 t2 ->
              let bs', pf1 = binders_kind' ff k1 bs in
              let out, pf2 = binders_typ' ff t2 ((Tup x TypeNameT)::bs') in
                (out, BNDT_ProdK bs x k1 t2 bs' out pf1 pf2)

          | T_Ref x t1 t2 ->
              let bs', pf1 = binders_typ' ff t1 bs in
              let out, pf2 = binders_typ' ff t2 ((Tup x TermNameT)::bs') in
                (out, BNDT_Ref bs x t1 t2 bs' out pf1 pf2)

          | T_Lam x t1 t2 ->
              let bs', pf1 = binders_typ' ff t1 bs in
              let out, pf2 = binders_typ' ff t2 ((Tup x TermNameT)::bs') in
                (out, BNDT_Lam bs x t1 t2 bs' out pf1 pf2)

          | T_Afn t1 ->
              let out, pf1 = binders_typ' ff t1 bs in
                (out, BNDT_Afn bs t1 out pf1)
                  
          | T_Ascribe t1 k ->
              let bs', pf1 = binders_typ' ff t1 bs in
              let out, pf2 = binders_kind' ff k bs' in
                (out, BNDT_Asc bs t1 k bs' out pf1 pf2)

val binders_value' : fix bndk bndt bndv bnde -> v:value  -> bndv v
let binders_value' ff v bs =
  match ff with
    | MkFix binders_kind' binders_typ' binders_value' binders_expr' ->
        match v with
          | V_Var a -> (bs, BNDV_Var bs a)

          | V_Fun x t e ->
              let bs', pf1 = binders_typ' ff t bs in
              let out, pf2 = binders_expr' ff e ((Tup x TermNameT)::bs') in
                (out, BNDV_Fun bs x t e bs' out pf1 pf2)

          | V_FunT x k e ->
              let bs', pf1 = binders_kind' ff k bs in
              let out, pf2 = binders_expr' ff e ((Tup x TypeNameT)::bs') in
                (out, BNDV_FunT bs x k e bs' out pf1 pf2)

          | V_Unit -> (bs, BNDV_Unit bs)

          | V_Const c tl vl ->
              let v = freshname false in
              let e1, pf1 = curryt (E_Value (V_Var (GV_Free v))) tl in
              let e, pf2 = curryv e1 vl in
              let out, pf = binders_expr' ff e bs in
                (out, BNDV_Const bs c tl vl e1 e v out pf1 pf2 pf)

          | V_Ascribe v t ->
              let bs', pf1 = binders_value' ff v bs in
              let out, pf2 = binders_typ' ff t bs' in
                (out, BNDV_Ascribe bs v t bs' out pf1 pf2)

val binders_expr' : fix bndk bndt bndv bnde -> e:expr  -> bnde e
let binders_expr' ff e bs =
  match ff with
    | MkFix binders_kind' binders_typ' binders_value' binders_expr' ->
        match e with
          | E_Value v ->
              let out, pf = binders_value' ff v bs in
                (out, BNDE_Val bs v out pf)

          | E_App e1 v2 ->
              let bs', pf1 = binders_expr' ff e1 bs in
              let out, pf2 = binders_value' ff v2 bs' in
                (out, BNDE_App bs e1 v2 bs' out pf1 pf2)

          | E_TApp e1 t2 ->
              let bs', pf1 = binders_expr' ff e1 bs in
              let out, pf2 = binders_typ' ff t2 bs' in
                (out, BNDE_TApp bs e1 t2 bs' out pf1 pf2)

          | E_LetIn x e1 e2 ->
              let bs', pf1 = binders_expr' ff e1 bs in
              let out, pf2 = binders_expr' ff e2 ((Tup x TermNameT)::bs') in
                (out, BNDE_LetIn bs x e1 e2 bs' out pf1 pf2)

          | E_Match v (MkPattern c alphas xs) ethen eelse ->
              let bs1, pf1 = binders_value' ff v bs in
              let alphas', pf_alphas' = map_p<bvar, bname, AsTypeName> asTypeName alphas in
              let xs', pf_xs' = map_p<bvar, bname, AsTermName> asTermName xs in
              let bs1', pf_append_1 = append_pf alphas' bs1 in
              let bs1'', pf_append_2 = append_pf xs' bs1' in
              let bs2, pf2 = binders_expr' ff ethen bs1'' in
              let out, pf3 = binders_expr' ff eelse bs2 in
                (out, (BNDE_Match
                         bs v c alphas xs ethen eelse bs1 bs2 out bs1' bs1'' alphas' xs'
                         pf_alphas' pf_xs' pf_append_1 pf_append_2 pf1 pf2 pf3))

          | E_Assume t ->
              let out, pf = binders_typ' ff t bs in
                (out, BNDE_Assume bs t out pf)
                  
          | E_Ascribe e1 t2 ->
              let bs', pf1 = binders_expr' ff e1 bs in
              let out, pf2 = binders_typ' ff t2 bs' in
                (out, BNDE_Ascribe bs e1 t2 bs' out pf1 pf2)

val binders_typ : k:typ -> (out:bnames * BindersT k out)
let binders_typ k =
  binders_typ'
    (MkFix
       binders_kind'
       binders_typ'
       binders_value'
       binders_expr') k []


val binders_value : k:value -> (out:bnames * BindersV k out)
let binders_value k =
  binders_value'
    (MkFix
       binders_kind'
       binders_typ'
       binders_value'
       binders_expr') k []

end

(* ********************************************************************************  *)

module Subst
open Util
open Terms
open FiniteSet
open FreeNames
open Binders

type vt :: _ = Either value typ

type SubstK :: bnames => kind => bvar => vt => kind => P =
   | SubstK_Base : xs:bnames -> x:bvar -> r:vt -> b:basekind
              -> SubstK xs (K_Base b) x r (K_Base b)

   | SubstK_ProdK  : xs:bnames -> x:bvar -> r:vt -> y:bvar
               -> k1:kind -> k1':kind
               -> k2:kind -> k2':kind
               -> SubstK xs k1 x r k1'
               -> SubstK ((Tup y TypeNameT)::xs) k2 x r k2'
               -> SubstK xs (K_ProdK y k1 k2) x r (K_ProdK y k1' k2')

   | SubstK_ProdT : xs:bnames -> x:bvar -> r:vt -> y:bvar
               -> t1:typ -> t1':typ
               -> k2:kind -> k2':kind
               -> SubstT xs t1 x r t1'
               -> SubstK ((Tup y TermNameT)::xs) k2 x r k2'
               -> SubstK xs (K_ProdT y t1 k2) x r (K_ProdT y t1' k2')

and SubstT :: bnames => typ => bvar => vt => typ => P =
   | SubstT_BVar : xs:bnames -> x:bvar -> t:typ -> esc:bnames -> binders:bnames
              -> NotMem (Tup x TypeNameT) xs
              -> FreeBvarsT t esc
              -> BindersT t binders
              -> Disjoint xs esc
              -> Disjoint xs binders
              -> SubstT xs (T_Var (GV_Bound x)) x (InrS t) t

   | SubstT_NBVarEq : xs:bnames -> x:bvar -> t:typ
                  -> Mem (Tup x TypeNameT) xs
                  -> SubstT xs (T_Var (GV_Bound x)) x (InrS t) (T_Var (GV_Bound x))

   | SubstT_NBVar : xs:bnames -> x:bvar -> r:typ -> y:bvar
              -> dummy:(Eq true true){y<>x}
              -> SubstT xs (T_Var (GV_Bound y)) x (InrS r) (T_Var (GV_Bound y))

   | SubstT_NBVarV : xs:bnames -> x:bvar -> r:value -> y:bvar
              -> SubstT xs (T_Var (GV_Bound y)) x (InlS r) (T_Var (GV_Bound y))

   | SubstT_FVar : xs:bnames -> x:bvar -> r:vt -> y:tyname
              -> SubstT xs (T_Var (GV_Free y)) x r (T_Var (GV_Free y))

   | SubstT_Unit : xs:bnames -> x:bvar -> r:vt
              -> SubstT xs T_Unit x r T_Unit

   | SubstT_Ind : xs:bnames -> x:bvar -> r:vt -> i:iname
              -> SubstT xs (T_Ind i) x r (T_Ind i)

   | SubstT_VApp  : xs:bnames -> x:bvar -> r:vt
               -> t1:typ -> t1':typ
               -> v1:value -> v1':value
               -> SubstT xs t1 x r t1'
               -> SubstV xs v1 x r v1'
               -> SubstT xs (T_VApp t1 v1) x r (T_VApp t1' v1')

   | SubstT_App   : xs:bnames -> x:bvar -> r:vt
               -> t1:typ -> t1':typ
               -> t2:typ -> t2':typ
               -> SubstT xs t1 x r t1'
               -> SubstT xs t2 x r t2'
               -> SubstT xs (T_App t1 t2) x r (T_App t1' t2')

   | SubstT_Prod  : xs:bnames -> x:bvar -> r:vt -> y:bvar
               -> t1:typ -> t1':typ
               -> t2:typ -> t2':typ
               -> SubstT xs t1 x r t1'
               -> SubstT ((Tup y TermNameT)::xs) t2 x r t2'
               -> SubstT xs (T_Prod y t1 t2) x r (T_Prod y t1' t2')

   | SubstT_ProdK : xs:bnames -> x:bvar -> r:vt -> y:bvar
               -> k1:kind -> k1':kind
               -> t2:typ -> t2':typ
               -> SubstK xs k1 x r k1'
               -> SubstT ((Tup y TypeNameT)::xs) t2 x r t2'
               -> SubstT xs (T_ProdK y k1 t2) x r (T_ProdK y k1' t2')

   | SubstT_Ref : xs:bnames -> x:bvar -> r:vt -> y:bvar
               -> t1:typ -> t1':typ
               -> t2:typ -> t2':typ
               -> SubstT xs t1 x r t1'
               -> SubstT ((Tup y TermNameT)::xs) t2 x r t2'
               -> SubstT xs (T_Ref y t1 t2) x r (T_Ref y t1' t2')

   | SubstT_Lam : xs:bnames -> x:bvar -> r:vt -> y:bvar
               -> t1:typ -> t1':typ
               -> t2:typ -> t2':typ
               -> SubstT xs t1 x r t1'
               -> SubstT ((Tup y TermNameT)::xs) t2 x r t2'
               -> SubstT xs (T_Lam y t1 t2) x r (T_Lam y t1' t2')

   | SubstT_Afn : xs:bnames -> x:bvar -> r:vt
               -> t1:typ -> t1':typ
               -> SubstT xs t1 x r t1'
               -> SubstT xs (T_Afn t1) x r (T_Afn t1')

   | SubstT_Asc : xs:bnames -> x:bvar -> r:vt
               -> t:typ -> t':typ
               -> k:kind -> k':kind
               -> SubstT xs t x r t'
               -> SubstK xs k x r k'
               -> SubstT xs (T_Ascribe t k) x r (T_Ascribe t' k')

and SubstV :: bnames => value => bvar => vt => value => P =
   | SubstV_BVar : xs:bnames -> x:bvar -> v:value -> esc:bnames -> binders:bnames
               -> NotMem (Tup x TermNameT) xs
               -> FreeBvarsV v esc
               -> BindersV v binders
               -> Disjoint xs esc
               -> Disjoint xs binders
               -> SubstV xs (V_Var (GV_Bound x)) x (InlS v) v

   | SubstV_NBVarEq : xs:bnames -> x:bvar -> v:value
                  -> Mem (Tup x TermNameT) xs
                  -> SubstV xs (V_Var (GV_Bound x)) x (InlS v) (V_Var (GV_Bound x))

   | SubstV_NBVar : xs:bnames -> x:bvar -> r:value -> y:bvar
              -> dummy:(Eq true true){y<>x}
              -> SubstV xs (V_Var (GV_Bound y)) x (InlS r) (V_Var (GV_Bound y))

   | SubstV_NBVarT : xs:bnames -> x:bvar -> r:typ -> y:bvar
              -> SubstV xs (V_Var (GV_Bound y)) x (InrS r) (V_Var (GV_Bound y))

   | SubstV_FVar : xs:bnames -> x:bvar -> r:vt -> y:vlname
              -> SubstV xs (V_Var (GV_Free y)) x r (V_Var (GV_Free y))

   | SubstV_Fun: xs:bnames -> x:bvar -> r:vt -> y:bvar
            -> t:typ -> t':typ
            -> e:expr -> e':expr
            -> SubstT xs t x r t'
            -> SubstE ((Tup y TermNameT)::xs) e x r e'
            -> SubstV xs (V_Fun y t e) x r (V_Fun y t' e')

   | SubstV_FunT: xs:bnames -> x:bvar -> r:vt -> y:bvar
            -> k:kind -> k':kind
            -> e:expr -> e':expr
            -> SubstK xs k x r k'
            -> SubstE ((Tup y TypeNameT)::xs) e x r e'
            -> SubstV xs (V_FunT y k e) x r (V_FunT y k' e')

   | SubstV_Boxed: xs:bnames -> x:bvar -> r:vt -> b:boxname
            -> v1:value -> v1':value
            -> SubstV xs v1 x r v1'
            -> SubstV xs (V_Boxed b v1) x r (V_Boxed b v1')

   | SubstV_Unit :  xs:bnames -> x:bvar -> r:vt
                -> SubstV xs V_Unit x r V_Unit

   | SubstV_Const: xs:bnames -> x:bvar -> r:vt -> d:cname
              -> tl:seq typ -> tl':seq typ
              -> vl:seq value  -> vl':seq value
              -> Zip typ typ (fun (t1:typ) (t2:typ) => SubstT xs t1 x r t2) tl tl'
              -> Zip value value (fun (v1:value) (v2:value) => SubstV xs v1 x r v2) vl vl'
              -> SubstV xs (V_Const d tl vl) x r (V_Const d tl' vl')

   | SubstV_Asc : xs:bnames -> x:bvar -> r:vt
              -> v1:value -> v1':value
              -> t:typ -> t':typ
              -> SubstV xs v1 x r v1'
              -> SubstT xs t x r t'
              -> SubstV xs (V_Ascribe v1 t) x r (V_Ascribe v1' t')

and SubstE :: bnames => expr => bvar => vt => expr => P =
  | SubstE_Value : xs:bnames -> x:bvar -> r:vt
            -> v1:value -> v1':value
            -> SubstV xs v1 x r v1'
            -> SubstE xs (E_Value v1) x r (E_Value v1')

  | SubstE_App : xs:bnames -> x:bvar -> r:vt
            -> e:expr -> e':expr
            -> v1:value -> v1':value
            -> SubstE xs e x r e'
            -> SubstV xs v1 x r v1'
            -> SubstE xs (E_App e v1) x r (E_App e' v1')

  | SubstE_TApp : xs:bnames -> x:bvar -> r:vt
            -> e:expr -> e':expr
            -> t:typ -> t':typ
            -> SubstE xs e x r e'
            -> SubstT xs t x r t'
            -> SubstE xs (E_TApp e t) x r (E_TApp e' t')

  | SubstE_LetIn : xs:bnames -> x:bvar -> r:vt -> y:bvar
           -> e1:expr -> e1':expr
           -> e2:expr -> e2':expr
           -> SubstE xs e1 x r e1'
           -> SubstE ((Tup y TermNameT)::xs) e2 x r e2'
           -> SubstE xs (E_LetIn y e1 e2) x r (E_LetIn y e1' e2')

  | SubstE_Match : xs:bnames -> x:bvar -> r:vt
           -> v1:value -> v1':value
           -> c:cname -> alphas:seq bvar -> ys:seq bvar
           -> alphas':bnames -> ys':bnames
           -> e1:expr -> e1':expr
           -> e2:expr -> e2':expr
           -> xs1tmp:bnames -> xs1:bnames
           -> AsTypeNames alphas alphas'
           -> AsTermNames ys ys'
           -> Append ys' xs xs1tmp
           -> Append alphas' xs1tmp xs1
           -> SubstV xs v1 x r v1'
           -> SubstE xs1 e1 x r e1'
           -> SubstE xs e2 x r e2'
           -> SubstE xs (E_Match v1 (MkPattern c alphas ys) e1 e2) x r
                        (E_Match v1' (MkPattern c alphas ys) e1' e2')

  | SubstE_Assume : xs:bnames -> x:bvar -> r:vt
           -> t:typ -> t':typ
           -> SubstT xs t x r t'
           -> SubstE xs (E_Assume t) x r (E_Assume t')

  | SubstE_Asc : xs:bnames -> x:bvar -> r:vt
              -> e1:expr -> e1':expr
              -> t:typ -> t':typ
              -> SubstE xs e1 x r e1'
              -> SubstT xs t x r t'
              -> SubstE xs (E_Ascribe e1 t) x r (E_Ascribe e1' t')

type sk :: _ = fun (k:kind)   => (xs:bnames -> x:bvar -> r:vt -> (k':kind   * SubstK xs k x r k'))
type st :: _ = fun (t:typ)    => (xs:bnames -> x:bvar -> r:vt -> (t':typ    * SubstT xs t x r t'))
type sv :: _ = fun (u:value)  => (xs:bnames -> x:bvar -> r:vt -> (u':value  * SubstV xs u x r u'))
type se :: _ = fun (e:expr)   => (xs:bnames -> x:bvar -> r:vt -> (e':expr   * SubstE xs e x r e'))

private val subst_k': fix sk st sv se -> k:kind -> sk k
let subst_k' f k xs x r =
  match f with MkFix f_k f_t f_v f_e ->
    match k with
      | K_Base b -> k, SubstK_Base xs x r b

      | K_ProdK a k1 k2 ->
          if x=a
          then raise (strcat "subst_k1: non-unique names: " (tostr k))
          else
            let k1', pf1 = f_k f k1 xs x r in
            let k2', pf2 = f_k f k2 ((Tup a TypeNameT)::xs) x r in
              K_ProdK a k1' k2', SubstK_ProdK xs x r a k1 k1' k2 k2' pf1 pf2
               
      | K_ProdT y t1 k2 ->
          if x=y
          then raise (strcat "subst_k2: non-unique names: " (tostr k))
          else
            let t1', pf1 = f_t f t1 xs x r in
            let k2', pf2 = f_k f k2 ((Tup y TermNameT)::xs) x r in
              K_ProdT y t1' k2', SubstK_ProdT xs x r y t1 t1' k2 k2' pf1 pf2

private val subst_t': fix sk st sv se -> t:typ -> st t
let subst_t' f t xs x r =
  match f with MkFix f_k f_t f_v f_e ->
    match t with
      | T_Var (GV_Bound y) ->
          (match r with
             | InlS v ->
                 t, SubstT_NBVarV xs x v y
             | InrS t' ->
                 if x=y then
                   match decideMem (Tup x TypeNameT) xs with
                     | InlStar pf_mem -> t, SubstT_NBVarEq xs x t' pf_mem
                     | InrStar pf_notmem ->
                         let esc, pf_free = free_bvars_typ t' in
                         let binders, pf_binders = binders_typ t' in
                           match checkDisjoint xs esc with
                             | NoneP -> raise "Failed captures check"
                             | SomeP pf_disj ->
                                 match checkDisjoint xs binders with
                                   | NoneP -> raise "Failed distinct binders check"
                                   | SomeP pf_disj_binders ->
                                       (t', (SubstT_BVar
                                               xs x t' esc binders pf_notmem pf_free pf_binders
                                               pf_disj pf_disj_binders))
                 else t, SubstT_NBVar xs x t' y (Refl_eq true))
            
      | T_Var (GV_Free y) -> t, SubstT_FVar xs x r y
          
      | T_Unit -> t, SubstT_Unit xs x r

      | T_Ind i -> t, SubstT_Ind xs x r i

      | T_VApp t1 v1 ->
          let t1', pf1 = f_t f t1 xs x r in
          let v1', pf2 = f_v f v1 xs x r in
            T_VApp t1' v1', SubstT_VApp xs x r t1 t1' v1 v1' pf1 pf2

      | T_App t1 t2 ->
          let t1', pf1 = f_t f t1 xs x r in
          let t2', pf2 = f_t f t2 xs x r in
            T_App t1' t2', SubstT_App xs x r t1 t1' t2 t2' pf1 pf2
          
      | T_Prod y t1 t2 ->
          if x=y
          then raise (strcat "subst_t1: non-unique names: " (tostr t))
          else
            let t1', pf1 = f_t f t1 xs x r in
            let t2', pf2 = f_t f t2 ((Tup y TermNameT)::xs) x r in
              T_Prod y t1' t2', SubstT_Prod xs x r y t1 t1' t2 t2' pf1 pf2

      | T_ProdK y k1 t2 ->
          if x=y
          then raise (strcat "subst_t2: non-unique names: " (tostr t))
          else
            let k1', pf1 = f_k f k1 xs x r in
            let t2', pf2 = f_t f t2 ((Tup y TypeNameT)::xs) x r in
              T_ProdK y k1' t2', SubstT_ProdK xs x r y k1 k1' t2 t2' pf1 pf2

      | T_Ref y t1 t2 ->
          if x=y
          then raise (strcat "subst_t3: non-unique names: " (tostr t))
          else
            let t1', pf1 = f_t f t1 xs x r in
            let t2', pf2 = f_t f t2 ((Tup y TermNameT)::xs) x r in
              T_Ref y t1' t2', SubstT_Ref xs x r y t1 t1' t2 t2' pf1 pf2

      | T_Lam y t1 t2 ->
          if x=y
          then raise (strcat "subst_t4: non-unique names: " (tostr t))
          else
            let t1', pf1 = f_t f t1 xs x r in
            let t2', pf2 = f_t f t2 ((Tup y TermNameT)::xs) x r in
              T_Lam y t1' t2', SubstT_Lam xs x r y t1 t1' t2 t2' pf1 pf2

      | T_Afn t1 ->
          let t1', pf1 = f_t f t1 xs x r in
            T_Afn t1', SubstT_Afn xs x r t1 t1' pf1

      | T_Ascribe t1 k ->
          let t1', pf1 = f_t f t1 xs x r in
          let k', pf2 = f_k f k xs x r in
            T_Ascribe t1' k', SubstT_Asc xs x r t1 t1' k k' pf1 pf2

private val subst_v': fix sk st sv se -> v:value -> sv v
let subst_v' f v1 xs x r =
  match f with MkFix f_k f_t f_v f_e ->
    match v1 with
      | V_Var (GV_Bound y) ->
          (match r with
             | InrS t ->
                 v1, SubstV_NBVarT xs x t y
             | InlS v ->
                 if x=y then
                   match decideMem (Tup x TermNameT) xs with
                     | InlStar pf_mem -> v1, SubstV_NBVarEq xs x v pf_mem
                     | InrStar pf_notmem ->
                         let esc, pf_free = free_bvars_value v in
                         let binders, pf_binders = binders_value v in
                           match checkDisjoint xs esc with
                             | NoneP -> raise "Failed captures check"
                             | SomeP pf_disj ->
                                 match checkDisjoint xs binders with
                                   | NoneP -> raise "Failed distinct binders check"
                                   | SomeP pf_disj_binders ->
                                       (v, (SubstV_BVar
                                              xs x v esc binders pf_notmem pf_free
                                              pf_binders pf_disj pf_disj_binders))
                 else v1, SubstV_NBVar xs x v y (Refl_eq true))
      
      | V_Var (GV_Free y) -> v1, SubstV_FVar xs x r y

      | V_Fun y t e ->
          if x=y
          then raise (strcat "subst_v1: non-unique names: " (tostr v1))
          else
            let t', pf1 = f_t f t xs x r in
            let e', pf2 = f_e f e ((Tup y TermNameT)::xs) x r in
              V_Fun y t' e', SubstV_Fun xs x r y t t' e e' pf1 pf2

      | V_FunT y k e ->
          if x=y
          then raise (strcat "subst_v2: non-unique names: " (tostr v1))
          else
            let k', pf1 = f_k f k xs x r in
            let e', pf2 = f_e f e ((Tup y TypeNameT)::xs) x r in
              V_FunT y k' e', SubstV_FunT xs x r y k k' e e' pf1 pf2

      | V_Boxed b v1 ->
          let v1', pf1 = f_v f v1 xs x r in
            V_Boxed b v1', SubstV_Boxed xs x r b v1 v1' pf1
            
      | V_Unit -> V_Unit, SubstV_Unit xs x r

      | V_Const d tl vl ->
          let tl', pf1 =
            map_p<typ, typ, (fun (t:typ) (t':typ) => SubstT xs t x r t')> (fun t -> f_t f t xs x r) tl in
          let vl', pf2 =
            map_p<value, value, (fun (v1:value) (v1':value) => SubstV xs v1 x r v1')> (fun v1 -> f_v f v1 xs x r) vl in
            V_Const d tl' vl', SubstV_Const xs x r d tl tl' vl vl' pf1 pf2

      | V_Ascribe v1 t ->
          let v1', pf1 = f_v f v1 xs x r in
          let t', pf2 = f_t f t xs x r in
            V_Ascribe v1' t', SubstV_Asc xs x r v1 v1' t t' pf1 pf2

private val subst_e': fix sk st sv se -> e:expr -> se e
let subst_e' f e xs x r =
  match f with MkFix f_k f_t f_v f_e ->
    match e with
      | E_Value v1 ->
          let v1', pf = f_v f v1 xs x r in
            E_Value v1', SubstE_Value xs x r v1 v1' pf

      | E_App e1 v1 ->
          let e1', pf1 = f_e f e1 xs x r in
          let v1', pf2 = f_v f v1 xs x r in
            E_App e1' v1', SubstE_App xs x r e1 e1' v1 v1' pf1 pf2

      | E_TApp e1 t ->
          let e1', pf1 = f_e f e1 xs x r in
          let t', pf2 = f_t f t xs x r in
            E_TApp e1' t', SubstE_TApp xs x r e1 e1' t t' pf1 pf2
            
      | E_LetIn y e1 e2 ->
          if x=y
          then raise (strcat "subst_e1: non-unique names: " (tostr e))
          else
            let e1', pf1 = f_e f e1 xs x r in
            let e2', pf2 = f_e f e2 ((Tup y TermNameT)::xs) x r in
              E_LetIn y e1' e2', SubstE_LetIn xs x r y e1 e1' e2 e2' pf1 pf2
                
      | E_Match v1 p e1 e2 ->
          (match p with
             | MkPattern c alphas ys ->
                 let alphas', pf_alphas' = map_p<bvar, bname, AsTypeName> asTypeName alphas in
                 let ys', pf_ys' = map_p<bvar, bname, AsTermName> asTermName ys in
                 let xs1tmp, pf_xs1tmp = append_pf ys' xs in
                 let xs1, pf_xs1 = append_pf alphas' xs1tmp in
                 let v1', pf0 = f_v f v1 xs x r in
                 let e1', pf1 = f_e f e1 xs1 x r in
                 let e2', pf2 = f_e f e2 xs x r in
                   (E_Match v1' p e1' e2',
                    (SubstE_Match
                       xs x r v1 v1' c alphas ys alphas' ys' e1 e1' e2 e2'
                       xs1tmp xs1 pf_alphas' pf_ys' pf_xs1tmp pf_xs1 pf0 pf1 pf2)))
            
      | E_Ascribe e1 t ->
          let e1', pf1 = f_e f e1 xs x r in
          let t', pf2 = f_t f t xs x r in
            E_Ascribe e1' t', SubstE_Asc xs x r e1 e1' t t' pf1 pf2

type SubstKV :: _ = (fun (k:kind) (x:bvar) (v:value) (k':kind)   => SubstK [] k  x (InlS v) k')
type SubstTV :: _ = (fun (t:typ)  (x:bvar) (v:value) (t':typ)    => SubstT [] t  x (InlS v) t')
type SubstVV :: _ = (fun (v:value) (x:bvar) (v1:value) (v':value) => SubstV [] v x (InlS v1) v')
type SubstEV :: _ = (fun (e:expr) (x:bvar) (v1:value) (e':expr) => SubstE [] e x (InlS v1) e')

type SubstKT :: _ = (fun (k:kind) (x:bvar) (t:typ)   (k':kind)   => SubstK [] k  x (InrS t) k')
type SubstTT :: _ = (fun (t:typ)  (x:bvar) (t1:typ)  (t':typ)    => SubstT [] t  x (InrS t1) t')
type SubstVT :: _ = (fun (v:value) (x:bvar) (t1:typ) (v':value) => SubstV [] v x (InrS t1) v')
type SubstET :: _ = (fun (e:expr) (x:bvar) (t1:typ) (e':expr) => SubstE [] e x (InrS t1) e')

val subst_kv : k:kind -> x:bvar -> v:value -> (k':kind * SubstKV k x v k')
let subst_kv k x v =
  subst_k' (MkFix subst_k' subst_t' subst_v' subst_e') k [] x (InlS v)

val subst_tv : t:typ -> x:bvar -> v:value -> (t':typ * SubstTV t x v t')
let subst_tv t x v =
  subst_t' (MkFix subst_k' subst_t' subst_v' subst_e') t [] x (InlS v)

val subst_kt : k:kind -> x:bvar -> t:typ -> (k':kind * SubstKT k x t k')
let subst_kt k x t =
  subst_k' (MkFix subst_k' subst_t' subst_v' subst_e') k [] x (InrS t)

val subst_tt : t:typ -> x:bvar -> t1:typ -> (t':typ * SubstTT t x t1 t')
let subst_tt t x t1 =
  subst_t' (MkFix subst_k' subst_t' subst_v' subst_e') t [] x (InrS t1)

val subst_vv : v:value -> x:bvar -> v1:value -> (v':value * SubstVV v x v1 v')
let subst_vv v x v1 =
  subst_v' (MkFix subst_k' subst_t' subst_v' subst_e') v [] x (InlS v1)

val subst_vt : v:value -> x:bvar -> t:typ -> (v':value * SubstVT v x t v')
let subst_vt v x t1 =
  subst_v' (MkFix subst_k' subst_t' subst_v' subst_e') v [] x (InrS t1)

end


(* ******************************************************************************** *)

module Unify
open Util
open FiniteSet
open Terms
open Subst
open Env
open FreeNames

val subst_t : bindings -> typ -> typ
let subst_t bs t =
  fold_left (fun tin' b -> match tin', b with
               | tin, (LB_VlEq (V_Var (GV_Bound x)) v) ->
                   let x, _ = subst_tv tin x v in x
               | tin, (LB_TyEq (T_Var (GV_Bound a)) t) ->
                   let x, _ = subst_tt tin a t in x
               | _ -> tin') t bs

val subst_v: bindings -> v:value -> value
let subst_v bs v =
  fold_left (fun vin' b -> match vin', b with
               | vin, (LB_VlEq (V_Var (GV_Bound x)) v) ->
                   let x, _ = subst_vv vin x v in x
               | vin, (LB_TyEq (T_Var (GV_Bound a)) t) ->
                   let x, _ = subst_vt vin a t in x
               | _ -> vin') v bs


type ufix :: _ = (fix2 (seq bvar) (fun (alphas:seq bvar) => xs:seq bvar -> tpat:typ -> tv:typ -> option bindings)
                     (seq bvar) (fun (alphas:seq bvar) => xs:seq bvar -> vpat:value -> v:value -> option bindings))
                  
val unify_typ': ufix -> alphas:seq bvar -> xs:seq bvar -> tpat:typ -> tv:typ -> option bindings
let unify_typ' uf alphas xs tpat tv =
  match uf with
    | MkFix2 unify_typ' unify_val' ->
        if tpat=tv then Some []
        else
          match tpat, tv with
            | (T_Var (GV_Bound a)), _  when mem a alphas -> Some [(LB_TyEq tpat tv)]
            | T_Unit, T_Unit          -> Some []
            | (T_Ind i), (T_Ind j)     when i=j -> Some []
            | (T_VApp t1 v1), (T_VApp t2 v2) ->
                (match unify_typ' uf alphas xs t1 t2 with
                   | None -> None
                   | Some eqs ->
                       let v1' = subst_v eqs v1 in
                         match unify_val' uf alphas xs v1' v2 with
                           | None -> None
                           | Some eqs' -> Some (concat eqs eqs'))
            | (T_App t1 t1'), (T_App t2 t2') ->
                (match unify_typ' uf alphas xs t1 t2 with
                   | None -> None
                   | Some eqs ->
                       let t1'' = subst_t eqs t1' in 
                         match unify_typ' uf alphas xs t1'' t2' with
                           | None -> None
                           | Some eqs' -> Some (concat eqs eqs'))
            | (T_Afn t1), (T_Afn t2) -> unify_typ' uf alphas xs t1 t2
            | (T_Ascribe t1 k1), (T_Ascribe t2 k2) ->
                if k1=k2 then unify_typ' uf alphas xs t1 t2
                else raise (strcat "Unification for ascribed types, with unequal kinds " (strcat3 (tostr k1) " <> " (tostr k2)))
            | (T_Prod x t1 t1'), (T_Prod y t2 t2') -> nyi "Unification for prods"
            | (T_ProdK a k1 t1), (T_ProdK a k2 t2) -> nyi "Unification for prods"
            | (T_Ref x t1 phi1), (T_Ref y t2 phi2) -> nyi "Unification for ref"
            | (T_Lam x t1 phi1), (T_Lam y t2 phi2) -> nyi "Unification for lam"
            | _ -> None

val unify_val': ufix -> alphas:seq bvar -> xs:seq bvar -> vpat:value -> v:value -> option bindings
let unify_val' uf alphas xs vpat v =
  match uf with
    | MkFix2 unify_typ' unify_val' ->
        if v=vpat then Some []
        else
          match vpat, v with
            | (V_Var(GV_Bound x)), _ when mem x xs -> Some [(LB_VlEq vpat v)]
            | (V_Const cpat tspat vspat), (V_Const c ts vs) when cpat=c ->
                let eqsOpt =
                  fold_left2_opt (fun eqs tpat tval ->
                                    let tpat' = subst_t eqs tpat in
                                      match unify_typ' uf alphas xs tpat' tval with
                                        | None -> None
                                        | Some eqs' -> Some (concat eqs eqs'))
                    (Some []) tspat ts in
                  fold_left2_opt (fun eqs vpat v ->
                                    let vpat' = subst_v eqs vpat in 
                                      match unify_val' uf alphas xs vpat v with
                                        | None -> None
                                        | Some eqs' -> Some (concat eqs eqs'))
                    eqsOpt vspat vs
            | (V_Ascribe vpat tpat), (V_Ascribe v t) ->
                (match unify_val' uf alphas xs vpat v with
                   | None -> None
                   | Some eqs ->
                       let tpat' = subst_t eqs tpat in 
                         match unify_typ' uf alphas xs tpat' t with
                           | None -> None
                           | Some eqs' -> Some (concat eqs eqs'))
            | (V_Fun x1 t1 e1), (V_Fun x2 t2 e2) -> nyi "Unification for function values"
            | (V_FunT a1 k1 e1), (V_FunT a2 k2 e2) -> nyi "Unification for function values"
            | (V_Boxed b1 v1), (V_Boxed b2 v2) -> nyi "Unification for boxes"
            | _ -> None

val unify_typ: alphas:seq bvar -> xs:seq bvar -> tpat:typ -> tv:typ -> option bindings
let unify_typ alphas xs tpat tv =
  unify_typ'(MkFix2 unify_typ' unify_val') alphas xs tpat tv

val unify_val: alphas:seq bvar -> xs:seq bvar -> vpat:value -> v:value -> option bindings
let unify_val alphas xs vpat v =
  unify_val'(MkFix2 unify_typ' unify_val') alphas xs vpat v

end

(* ****************************************************************************** *)

module Z3Interface
open Util
open Terms
open Subst
open Env

private type LogicEntails :: icompartment => environment => bindings => typ => P =
    | LE_Admit : I:icompartment -> G:environment -> B:bindings -> phi:typ
           -> LogicEntails I G B phi

private type LogicEntails_EQ :: icompartment => environment => bindings => value => value => P =
    | LEQ_Admit : I:icompartment -> G:environment -> B:bindings -> v1:value -> v2:value
                -> LogicEntails_EQ I G B v1 v2

val query : I:icompartment -> F:environment -> G:bindings -> phi:typ -> optionP (LogicEntails I F G phi)
let query i f g phi = SomeP (LE_Admit i f g phi)

val query_equiv : I:icompartment -> F:environment -> G:bindings
               -> v1:value -> v2:value -> optionP (LogicEntails_EQ I F G v1 v2)
let query_equiv i f g v1 v2 = SomeP (LEQ_Admit i f g v1 v2)

end

(* ******************************************************************************** *)

module Typing
open Util
open FiniteSet
open Terms
open Subst
open Env
open Z3Interface
open Unify
open FreeNames

type acontext = seq bvar
type AContextSplit :: _ = (fun (a:acontext) (a1:acontext) (a2:acontext) => Partition a a1 a2)

type mode =
  | Term_level : mode
  | Type_level : mode

type ConcreteKind :: basekind => P =
  | CK_Star : ConcreteKind BK_Comp
  | CK_Afn  : ConcreteKind BK_Afn
  | CK_Prop : ConcreteKind BK_Prop

type KindCompat :: basekind => basekind => P =
  | KC_AffErs: KindCompat BK_Afn BK_Erase
  | KC_AffAff: KindCompat BK_Afn BK_Afn
  | KC_ErsAll: b:basekind -> KindCompat BK_Erase b
  | KC_StarAll: b:basekind -> KindCompat BK_Comp b
  | KC_PropAll: b:basekind -> KindCompat BK_Prop b

type AffineCheck :: basekind => basekind => P =
  | AC_AA: AffineCheck BK_Afn BK_Afn
  | AC_Star: b:basekind -> AffineCheck BK_Comp b
  | AC_Prop: b:basekind -> AffineCheck BK_Prop b
  | AC_Erase: b:basekind -> AffineCheck BK_Erase b

val decideAffineCheck : b1:basekind -> b2:basekind -> optionP (AffineCheck b1 b2)
let decideAffineCheck b1 b2 = match b1, b2 with
  | BK_Afn, BK_Afn -> SomeP AC_AA
  | BK_Comp, _ -> SomeP (AC_Star b2)
  | BK_Prop, _ -> SomeP (AC_Prop b2)
  | BK_Erase, _ -> SomeP (AC_Erase b2)

type BaseType :: iname => typ => P =
  | BT_Ind : i:iname -> BaseType i (T_Ind i)
  | BT_VApp : i:iname -> t:typ -> v:value
           -> BaseType i t
           -> BaseType i (T_VApp t v)
  | BT_TApp : i:iname -> t1:typ -> t2:typ
           -> BaseType i t1
           -> BaseType i (T_App t1 t2)

val decideBaseType: t:typ -> option(i:iname * BaseType i t)
let rec decideBaseType t = match t with
  | T_VApp t v ->
      (match decideBaseType t with
         | None -> None
         | Some((i, b)) -> Some (i, BT_VApp i t v b))
  | T_App t t' ->
      (match decideBaseType t with
         | None -> None
         | Some((i, b)) -> Some (i, BT_TApp i t t' b))
  | T_Ind i -> Some (i, BT_Ind i)
  | _ -> None
        
type exists_ds :: _ = (fun (i:inductive) (iks:seq ikind) =>
    (ex (seq constructor) (fun (ds:seq constructor) => Eq i (MkIndType iks ds))))
val mk_exds : i:inductive -> (iks:seq ikind * exists_ds i iks)
let mk_exds i = match i with
  | MkIndType iks ds -> (iks, MkEx3 i iks ds (Refl_eq i))

type exists_ik :: _ = (fun (i:inductive) (ds:seq constructor) =>
    (ex (seq ikind) (fun (iks:seq ikind) => Eq i (MkIndType iks ds))))
val mk_exik: i:inductive -> (ds:seq constructor * exists_ik i ds)
let mk_exik i = match i with
  | MkIndType iks ds -> (ds, MkEx4 i ds iks (Refl_eq i))

type exists_k :: _ = (fun (ik:ikind) (i:iname) =>
    (ex kind (fun (k:kind) => Eq ik (MkIKind i k))))
val mk_exk: ik:ikind -> (i:iname * exists_k ik i)
let mk_exk ik = match ik with
  | MkIKind i k -> (i, MkEx5 ik i k (Refl_eq ik))

type exists_ct :: _ = (fun (c:constructor) (cn:cname) =>
    (ex typ (fun (t:typ) => (Eq c (MkConstructor cn t)))))
val mk_exct: c:constructor -> (cn:cname * exists_ct c cn)
let mk_exct c = match c with
  | MkConstructor cn t -> (cn, MkEx6 c cn t (Refl_eq c))

type DistinctINames :: icompartment => P =
  | DI_Names : I:icompartment -> ikinds_seq:seq (seq ikind)
            -> ikinds: seq ikind -> inames:seq iname
            -> Zip inductive (seq ikind) exists_ds I ikinds_seq
            -> Flatten ikind ikinds_seq ikinds
            -> Zip ikind iname exists_k ikinds inames
            -> Distinct inames
            -> DistinctINames I

type DistinctConstrs :: icompartment => P =
  | DC_Names : I:icompartment -> constrs_seq:seq (seq constructor)
            -> constrs: seq constructor -> cnames:seq cname
            -> Zip inductive (seq constructor) exists_ik I constrs_seq
            -> Flatten constructor constrs_seq constrs
            -> Zip constructor cname exists_ct constrs cnames
            -> Distinct cnames
            -> DistinctConstrs I

val kind_compat: b1:basekind -> b2:basekind -> optionP (KindCompat b1 b2)
let kind_compat b1 b2 = match b1, b2 with
  | BK_Afn, BK_Erase -> SomeP (KC_AffErs)
  | BK_Afn, BK_Afn -> SomeP (KC_AffAff)
  | BK_Erase, _ -> SomeP (KC_ErsAll b2)
  | BK_Comp, _ -> SomeP (KC_StarAll b2)
  | BK_Prop, _ -> SomeP (KC_PropAll b2)
  | _ -> NoneP

type VIndexKindCompat :: basekind => basekind => P =
  | VKC_AffErs: VIndexKindCompat BK_Afn BK_Erase
  | VKC_ErsAll: b:basekind -> VIndexKindCompat BK_Erase b
  | VKC_StarAll: b:basekind -> VIndexKindCompat BK_Comp b
  | VKC_PropAll: b:basekind -> VIndexKindCompat BK_Prop b

val vindex_kind_compat: b1:basekind -> b2:basekind -> optionP (VIndexKindCompat b1 b2)
let vindex_kind_compat b1 b2 = match b1, b2 with
  | BK_Afn, BK_Erase -> SomeP VKC_AffErs
  | BK_Erase, _ -> SomeP (VKC_ErsAll b2)
  | BK_Comp, _ -> SomeP (VKC_StarAll b2)
  | BK_Prop, _ -> SomeP (VKC_PropAll b2)
  | _, _  -> impos (tostr b2)

type KindCompatElim :: basekind => basekind => P  =
  | KCE_Id : b:basekind -> KindCompatElim b b
  | KCE_AnyStar : b:basekind -> KindCompatElim BK_Comp b
  | KCE_AnyAfn : b:basekind -> KindCompatElim BK_Afn b

val kind_compat_elim : bresult:basekind -> belim:basekind -> optionP (KindCompatElim bresult belim)
let kind_compat_elim bresult belim =
  if bresult=belim then SomeP (KCE_Id bresult)
  else match bresult, belim with
    | BK_Comp, _ -> SomeP (KCE_AnyStar belim)
    | BK_Afn, _ -> SomeP (KCE_AnyAfn belim)
    | _ -> NoneP

(* -------------------------------------------------------------------- *)
type al2binding =  (* :: P = *)
  | AL2_Type : bvar -> bvar -> typ -> al2binding
  | AL2_Kind : bvar -> bvar -> kind -> al2binding

type al2bindings :: _ = seq al2binding

type AL2Merge_R :: bindings => al2bindings => bindings => P =
  | AL2M_Nil :
      B:bindings
    -> AL2Merge_R B [] B

  | AL2M_ConsType :
      B:bindings -> x:bvar -> y:bvar -> t:typ -> D:al2bindings -> BC:bindings
    -> AL2Merge_R B D BC
    -> AL2Merge_R B ((AL2_Type x y t) :: D) ((LB_BvarTy y t)::BC)

  | AL2M_ConsKind :
      B:bindings -> a:bvar -> b:bvar -> k:kind -> D:al2bindings -> BC:bindings
    -> AL2Merge_R B D BC
    -> AL2Merge_R B ((AL2_Kind a b k) :: D) ((LB_BvarKind b k)::BC)

val al2_merge : b:bindings -> d:al2bindings -> (b':bindings * AL2Merge_R b d b')
let rec al2_merge b d = match d with
  | [] -> (b, AL2M_Nil b)
  | (AL2_Type x y t)::d' ->
      let b0, pf0 = al2_merge b d' in
        (((LB_BvarTy y t)::b0), AL2M_ConsType b x y t d' b0 pf0)
  | (AL2_Kind aa bb k)::d' ->
      let b0, pf0 = al2_merge b d' in
        (((LB_BvarKind bb k)::b0), AL2M_ConsKind b aa bb k d' b0 pf0)

type type_equiv :: icompartment => environment => bindings => al2bindings => typ => typ => P =
  | TE_Refl:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> t:typ
    -> type_equiv I G B D t t

  | TE_Sym:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> t1:typ -> t2:typ
    -> type_equiv I G B D t2 t1
    -> type_equiv I G B D t1 t2

  | TE_Trans:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> t1:typ -> t2:typ -> t3:typ
    -> type_equiv I G B D t1 t2
    -> type_equiv I G B D t2 t3
    -> type_equiv I G B D t1 t3

  | TE_TApp:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> t1:typ -> t2:typ
    -> u1:typ -> u2:typ
    -> type_equiv I G B D t1 t2
    -> type_equiv I G B D u1 u2
    -> type_equiv I G B D (T_App t1 u1) (T_App t2 u2)

  | TE_Prod:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> x:bvar -> y:bvar
    -> t1:typ -> t2:typ
    -> u1:typ -> u2:typ
    -> type_equiv I G B D t1 t2
    -> type_equiv I G B ((AL2_Type x y t1)::D) u1 u2
    -> type_equiv I G B D (T_Prod x t1 u1) (T_Prod y t2 u2)

  | TE_ProdK:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> a:bvar -> b:bvar
    -> k1:kind -> k2:kind
    -> t1:typ -> t2:typ
    -> kind_equiv I G B D k1 k2
    -> type_equiv I G B ((AL2_Kind a b k1)::D) t1 t2
    -> type_equiv I G B D (T_ProdK a k1 t1) (T_ProdK b k2 t2)

  | TE_Ref:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> x:bvar -> y:bvar
    -> t1:typ -> t2:typ
    -> phi1:typ -> phi2:typ
    -> type_equiv I G B D t1 t2
    -> type_equiv I G B ((AL2_Type x y t1)::D) phi1 phi2
    -> type_equiv I G B D (T_Ref x t1 phi1) (T_Ref y t2 phi2)

  | TE_Lam:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> x:bvar -> y:bvar
    -> t1:typ -> t2:typ
    -> u1:typ -> u2:typ
    -> type_equiv I G B D t1 t2
    -> type_equiv I G B ((AL2_Type x y t1)::D) u1 u2
    -> type_equiv I G B D (T_Lam x t1 u1) (T_Lam y t2 u2)

  | TE_Afn:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> t1:typ -> t2:typ
    -> type_equiv I G B D t1 t2
    -> type_equiv I G B D (T_Afn t1) (T_Afn t2)

  | TE_TyBeta: (* Note: renamed formal parameters *)
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> x:bvar -> u:typ -> t:typ -> v:value -> tsub:typ
    -> SubstTV t x v tsub
    -> type_equiv I G B D (T_VApp (T_Lam x u t) v) tsub

(* TODO: Fix FS_Dec.v. No equivalences in G. *)
(*   | TE_ValRefine: *)
(*       I:icompartment -> G:environment -> B:bindings -> D:al2bindings  *)
(*     -> t1:typ -> t2:typ -> v1:value -> v2:value  *)
(*     -> Mem (LB_VlEq v1 v2) G *)
(*     -> type_equiv I G B D t1 t2 *)
(*     -> type_equiv I G B D (T_VApp t1 v1) (T_VApp t2 v2) *)

(*   | TE_TyRefine: *)
(*     forall I Γ B D t1 t2, *)
(*         Mem {` t1 ≡τ t2 } Γ *)
(*      -> [! I | Γ | B | D] ?⊢ t1 ≡τ t2 *)

  | TE_VApp:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> t1:typ -> t2:typ -> v:value
    -> type_equiv I G B D t1 t2
    -> type_equiv I G B D (T_VApp t1 v) (T_VApp t2 v)

  | TE_BValRefine:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> t1:typ -> t2:typ -> v1:value -> v2:value
    -> Mem (LB_VlEq v1 v2) B
    -> type_equiv I G B D t1 t2
    -> type_equiv I G B D (T_VApp t1 v1) (T_VApp t2 v2)


  | TE_BValRefine_Logic:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> t1:typ -> t2:typ -> v1:value -> v2:value
    -> type_equiv I G B D t1 t2
    -> LogicEntails_EQ I G B v1 v2
    -> type_equiv I G B D (T_VApp t1 v1) (T_VApp t2 v2)

  | TE_BTyRefine:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> t1:typ -> t2:typ
    -> Mem (LB_TyEq t1 t2) B
    -> type_equiv I G B D t1 t2

  | TE_TyAlpha:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> t1:typ -> t2:typ -> x:bvar -> y:bvar -> t:typ -> t2':typ
    -> Mem (AL2_Type x y t) D
    -> SubstTV t2 y (V_Var (GV_Bound x)) t2'
    -> type_equiv I G B D t1 t2'
    -> type_equiv I G B D t1 t2

  | TE_KindAlpha:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> t1:typ -> t2:typ -> a:bvar -> b:bvar -> k:kind -> t2':typ
    -> Mem (AL2_Kind a b k) D
    -> SubstTT t2 b (T_Var (GV_Bound a)) t2'
    -> type_equiv I G B D t1 t2'
    -> type_equiv I G B D t1 t2

  | TE_Unascribe:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> t1:typ -> t2:typ -> k1:kind
    -> type_equiv I G B D t1 t2
    -> type_equiv I G B D (T_Ascribe t1 k1) t2

and kind_equiv :: icompartment => environment => bindings => al2bindings => kind => kind => P =
  | KE_Refl :
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> k:kind
    -> kind_equiv I G B D k k

  | KE_Sym: (* Note: addition in here. *)
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> k1:kind -> k2:kind
    -> kind_equiv I G B D k2 k1
    -> kind_equiv I G B D k1 k2

  | KE_ProdK :
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> a:bvar -> b:bvar -> k1:kind -> k1':kind -> k2:kind -> k2':kind (* NOTE: Change in order of args *)
    -> kind_equiv I G B D k1 k1'
    -> kind_equiv I G B ((AL2_Kind a b k1)::D) k2 k2'
    -> kind_equiv I G B D (K_ProdK a k1 k2) (K_ProdK b k1' k2')

  | KE_ProdT :
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> x:bvar -> y:bvar -> t:typ -> t':typ -> k:kind -> k':kind
    -> type_equiv I G B D t t'
    -> kind_equiv I G B ((AL2_Type x y t)::D) k k'
    -> kind_equiv I G B D (K_ProdT x t k) (K_ProdT y t' k')

  | KE_TyAlpha:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> k1:kind -> k2:kind -> x:bvar -> y:bvar -> t:typ -> k2':kind
    -> Mem (AL2_Type x y t) D
    -> SubstKV k2 y (V_Var (GV_Bound x)) k2'
    -> kind_equiv I G B D k1 k2'
    -> kind_equiv I G B D k1 k2

  | KE_KindAlpha:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> k1:kind -> k2:kind -> a:bvar -> b:bvar -> k:kind -> k2':kind
    -> Mem (AL2_Kind a b k) D
    -> SubstKT k2 b (T_Var (GV_Bound a)) k2'
    -> kind_equiv I G B D k1 k2'
    -> kind_equiv I G B D k1 k2

and value_equiv :: icompartment => environment => bindings => al2bindings => value => value => P =
  | VE_Refl:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> v:value
    -> value_equiv I G B D v v

  | VE_Sym:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> v1:value -> v2:value
    -> value_equiv I G B D v1 v2
    -> value_equiv I G B D v2 v1

  | VE_Fun:
       I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> x1:bvar -> t1:typ -> e1:expr
    -> x2:bvar -> t2:typ -> e2:expr
    -> type_equiv I G B D t1 t2
    -> expr_equiv I G B ((AL2_Type x1 x2 t1)::D) e1 e2
    -> value_equiv I G B D (V_Fun x1 t1 e1) (V_Fun x2 t2 e2)

  | VE_FunT:
       I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> x1:bvar -> k1:kind -> e1:expr
    -> x2:bvar -> k2:kind -> e2:expr
    -> kind_equiv I G B D k1 k2
    -> expr_equiv I G B ((AL2_Kind x1 x2 k1)::D) e1 e2
    -> value_equiv I G B D (V_FunT x1 k1 e1) (V_FunT x2 k2 e2)

  | VE_TyAlpha:
       I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> x:bvar -> y:bvar -> t:typ -> v1:value -> v2:value -> v2':value
    -> Mem (AL2_Type x y t) D
    -> SubstVV v2 y (V_Var (GV_Bound x)) v2'
    -> value_equiv I G B D v1 v2'
    -> value_equiv I G B D v1 v2

  | VE_KindAlpha:
       I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> x:bvar -> y:bvar -> k:kind -> v1:value -> v2:value -> v2':value
    -> Mem (AL2_Kind x y k) D
    -> SubstVT v2 y (T_Var (GV_Bound x)) v2'
    -> value_equiv I G B D v1 v2'
    -> value_equiv I G B D v1 v2

and expr_equiv :: icompartment => environment => bindings => al2bindings => expr => expr => P =
  | EE_Refl:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> e:expr
    -> expr_equiv I G B D e e

  | EE_Value:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> v1:value -> v2:value
    -> value_equiv I G B D v1 v2
    -> expr_equiv I G B D (E_Value v1) (E_Value v2)

  | EE_LetIn:
       I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> x1:bvar -> e1:expr -> e1':expr
    -> x2:bvar -> e2:expr -> e2':expr -> t:typ (* this is for any type t. Ok? *)
    -> expr_equiv I G B D e1 e2
    -> expr_equiv I G B ((AL2_Type x1 x2 t)::D) e1' e2'
    -> expr_equiv I G B D (E_LetIn x1 e1 e1') (E_LetIn x2 e2 e2')

  | EE_Match:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> v1:value -> p1:pattern -> e1:expr -> e1':expr
    -> v2:value -> p2:pattern -> e2:expr -> e2':expr -> D':al2bindings
    -> value_equiv I G B D v1 v2
    -> pattern_equiv D p1 p2 D'
    -> expr_equiv I G B D' e1 e2
    -> expr_equiv I G B D e1' e2'
    -> expr_equiv I G B D (E_Match v1 p1 e1 e1') (E_Match v2 p2 e2 e2')

  | EE_TyAlpha:
       I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> x:bvar -> y:bvar -> t:typ -> e1:expr -> e2:expr -> e2':expr
    -> Mem (AL2_Type x y t) D
    -> SubstEV e2 y (V_Var (GV_Bound x)) e2'
    -> expr_equiv I G B D e1 e2'
    -> expr_equiv I G B D e1 e2

  | EE_KindAlpha:
       I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> x:bvar -> y:bvar -> k:kind -> e1:expr -> e2:expr -> e2':expr
    -> Mem (AL2_Kind x y k) D
    -> SubstET e2 y (T_Var (GV_Bound x)) e2'
    -> expr_equiv I G B D e1 e2'
    -> expr_equiv I G B D e1 e2

and pattern_equiv :: al2bindings => pattern => pattern => al2bindings => P =
   | PE_Nil : D:al2bindings -> c:cname
           -> pattern_equiv D (MkPattern c [] []) (MkPattern c [] []) D

   | PE_ConsX : D:al2bindings -> c1:cname -> a1:seq bvar -> x1:seq bvar
           -> c2:cname -> a2:seq bvar -> x2:seq bvar
           -> x:bvar -> y:bvar -> t:typ -> D':al2bindings (* for all types t? *)
           -> pattern_equiv D (MkPattern c1 a1 x1) (MkPattern c2 a2 x2) D'
           -> pattern_equiv D (MkPattern c1 a1 (x::x1)) (MkPattern c2 a2 (y::x2)) ((AL2_Type x y t)::D')

   | PE_ConsT : D:al2bindings -> c1:cname -> a1:seq bvar
           -> c2:cname -> a2:seq bvar
           -> x:bvar -> y:bvar -> k:kind -> D':al2bindings (* for all kinds k? *)
           -> pattern_equiv D (MkPattern c1 a1 []) (MkPattern c2 a2 []) D'
           -> pattern_equiv D (MkPattern c1 (x::a1) []) (MkPattern c2 (y::a2) []) ((AL2_Kind x y k)::D')

type Subkinding :: icompartment => environment => bindings => al2bindings => kind => kind => P =
  | SK_Refl :
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> k1:kind -> k2:kind
    -> kind_equiv I G B D k1 k2
    -> Subkinding I G B D k1 k2

  (* | SK_P_Star: *)
  (*     I:icompartment -> G:environment -> B:bindings -> D:al2bindings *)
  (*   -> Subkinding I G B D (K_Base BK_Prop) (K_Base BK_Comp) *)

  | SK_P_E:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> Subkinding I G B D (K_Base BK_Prop) (K_Base BK_Erase)

  | SK_Star_E:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> Subkinding I G B D (K_Base BK_Comp) (K_Base BK_Erase)

  | SK_ProdT: (* Note: changed name *)
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> x:bvar -> y:bvar -> t:typ -> t':typ -> k:kind -> k':kind
    -> Subtyping I G B D t' t
    -> Subkinding I G B ((AL2_Type x y t')::D) k k'
    -> Subkinding I G B D (K_ProdT x t k) (K_ProdT y t' k')

  | SK_ProdK:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> a:bvar -> b:bvar -> k1:kind -> k1':kind -> k2:kind -> k2':kind  (* Changed arg order *)
    -> Subkinding I G B D k1' k1
    -> Subkinding I G B ((AL2_Kind a b k1')::D) k2 k2'
    -> Subkinding I G B D (K_ProdK a k1 k2) (K_ProdK b k1' k2')

  | SK_Trans:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> k1:kind -> k2:kind -> k3:kind
    -> Subkinding I G B D k1 k2
    -> Subkinding I G B D k2 k3
    -> Subkinding I G B D k1 k3

and Subtyping :: icompartment => environment => bindings => al2bindings => typ => typ => P =
  | ST_Refl :
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> t1:typ -> t2:typ
    -> type_equiv I G B D t1 t2
    -> Subtyping I G B D t1 t2

  | ST_Prod :
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> x:bvar -> y:bvar -> t:typ -> t':typ -> u:typ -> u':typ
    -> Subtyping I G B D t' t
    -> Subtyping I G B ((AL2_Type x y t')::D) u u'
    -> Subtyping I G B D (T_Prod x t u) (T_Prod y t' u')

  | ST_ProdK :
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> a:bvar -> b:bvar -> k:kind -> k':kind -> t:typ -> t':typ
    -> Subkinding I G B D k' k
    -> Subtyping I G B ((AL2_Kind a b k')::D) t t'
    -> Subtyping I G B D (T_ProdK a k t) (T_ProdK b k' t')

  | ST_RefLeft :
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> x:bvar -> t:typ -> t':typ -> phi:typ
    -> Subtyping I G B D t t'
    -> Subtyping I G B D (T_Ref x t phi) t'

  | ST_RefRight :
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> BC:bindings -> x:bvar -> t:typ -> t':typ -> phi:typ
    -> AL2Merge_R B D BC
    -> Subtyping I G B D t t'
    -> LogicEntails I G ((LB_BvarTy x t)::BC) phi
    -> Subtyping I G B D t (T_Ref x t' phi)

  | ST_Afn:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> t1:typ -> t2:typ
    -> Subtyping I G B D t1 t2
    -> Subtyping I G B D (T_Afn t1) (T_Afn t2)

  | ST_Trans:
      I:icompartment -> G:environment -> B:bindings -> D:al2bindings
    -> t1:typ -> t2:typ -> t3:typ
    -> Subtyping I G B D t1 t2
    -> Subtyping I G B D t2 t3
    -> Subtyping I G B D t1 t3
              
type AQual :: acontext => typ => typ => P =
  | AQual_Nil : t:typ -> AQual [] t t
  | AQual_Q : a:acontext -> t:typ -> AQual a t (T_Afn t)

type StripQual :: typ => typ => P =
  | StripQual_A : t:typ -> StripQual (T_Afn t) t
  | StripQual_Id : t:typ -> StripQual t t

val strip_qual : q:typ -> (t:typ * StripQual q t)
let strip_qual q = match q with
  | T_Afn t -> (t, StripQual_A t)
  | _ -> (q, StripQual_Id q)

val aqual : a:acontext -> t:typ -> (q:typ * AQual a t q)
let aqual a t = match a with
  | [] -> t, AQual_Nil t
  | _ -> (T_Afn t), AQual_Q a t
  
type Bindings :: bindings => typ => seq bvar => seq bvar => bindings => P =
     | Bindings_nil : B:bindings -> t:typ -> Bindings B t [] [] B

     | Bindings_tcons : B:bindings -> formal:bvar -> k:kind -> t:typ -> t':typ
                        -> a:bvar -> al:seq bvar -> xs:seq bvar -> B':bindings
                        -> SubstTT t formal (T_Var (GV_Bound a)) t'
                        -> Bindings ((LB_BvarKind a k)::B) t' al xs B'
                        -> Bindings B (T_ProdK formal k t) (a::al) xs B'

     | Bindings_vcons : B:bindings -> formal:bvar -> t1:typ -> t2:typ -> t2':typ
                        -> x:bvar -> xs:seq bvar -> B':bindings
                        -> SubstTV t2 formal (V_Var (GV_Bound x)) t2'
                        -> Bindings ((LB_BvarTy x t1)::B) t2' [] xs B'
                        -> Bindings B (T_Prod formal t1 t2) [] (x::xs) B'


type PatternTypeMatch :: bindings => seq bvar => seq typ => seq bvar => seq value => typ => typ => P =
   | PTM_Base : t:typ -> PatternTypeMatch [] [] [] [] [] t t

   | PTM_ValueCons : eqs:bindings -> x:bvar -> xs:seq bvar -> v:value -> vs:seq value
                     -> t1:typ -> t1':typ -> t2:typ -> fvs1:bnames -> eqs':bindings
                     -> FreeBvarsT t1 fvs1
                     -> Mem (Tup x TermNameT) fvs1
                     -> PatternTypeMatch eqs [] [] xs vs t1' t2
                     -> SubstTV t1 x v t1'
                     -> Append eqs [(LB_VlEq (V_Var (GV_Bound x)) v)] eqs'
                     -> PatternTypeMatch eqs' [] [] (x::xs) (v::vs) t1 t2

   | PTM_ValueConsNotMem : eqs:bindings -> x:bvar -> xs:seq bvar -> vs:seq value
                        -> t1:typ -> t2:typ
                        -> PatternTypeMatch eqs [] [] xs vs t1 t2
                        -> PatternTypeMatch eqs [] [] (x::xs) vs t1 t2


   | PTM_TypeCons : eqs:bindings -> a:bvar -> alphas:seq bvar -> t:typ -> ts:seq typ
                     -> xs:seq bvar -> vs:seq value -> t1:typ -> t1':typ -> t2:typ -> fvs1:bnames -> eqs':bindings
                     -> FreeBvarsT t1 fvs1
                     -> Mem (Tup a TypeNameT) fvs1
                     -> PatternTypeMatch eqs alphas ts xs vs t1' t2
                     -> SubstTT t1 a t t1'
                     -> Append eqs [(LB_TyEq (T_Var (GV_Bound a)) t)] eqs'
                     -> PatternTypeMatch eqs' (a::alphas) (t::ts) xs vs t1 t2

   | PTM_TypeConsNotMem : eqs:bindings -> a:bvar -> alphas:seq bvar -> ts:seq typ
                       -> xs:seq bvar -> vs:seq value -> t1:typ -> t2:typ
                       -> PatternTypeMatch eqs alphas ts xs vs t1 t2
                       -> PatternTypeMatch eqs (a::alphas) ts xs vs t1 t2


type exists_t :: _ = (fun (a:bvar) (b:locbinding) => (ex typ (fun (ta:typ) => Eq b (LB_TyEq (T_Var (GV_Bound a)) ta))))
val tyEq: a:bvar -> b:locbinding -> optionP (exists_t a b)
let tyEq a b = match b with
  | LB_TyEq (T_Var (GV_Bound a')) ta when a=a' ->
      SomeP (MkEx7 b a ta (Refl_eq b))
  | _ -> NoneP

type exists_v :: _ = (fun (a:bvar) (b:locbinding) => (ex value (fun (va:value) => Eq b (LB_VlEq (V_Var (GV_Bound a)) va))))
val vlEq: a:bvar -> b:locbinding -> optionP (exists_v a b)
let vlEq a b = match b with
  | LB_VlEq (V_Var (GV_Bound a')) va when a=a' ->
      SomeP (MkEx8 b a va (Refl_eq b))
  | _ -> NoneP


val ptmAuxAux: b:bindings -> xs:seq bvar -> t1:typ -> t2:typ
           -> (eqs:bindings * vs:seq value * PatternTypeMatch eqs [] [] xs vs t1 t2)
let rec ptmAuxAux b xs t1 t2 =
  match xs with
    | [] ->
        if t1=t2
        then ([], [], PTM_Base t1)
        else raise "Impos: bad unification"
    | x::xl ->
        match find<locbinding, (exists_v x)> (vlEq x) b with
            (* | Some (((LB_VlEq (V_Var (GV_Bound x')) vx), (MkEx _vx (Refl_eq _)), pf_mem)) ->  *)
            (* TODO: Destruction of user-defined dependent ex not working  *)
          | Some (((LB_VlEq (V_Var (GV_Bound x')) vx), _, pf_mem)) when x=x' ->
              let fvs1, pf_fvs1 = free_bvars_typ t1 in
                (match decideMem (Tup x TermNameT) fvs1 with
                   | InrStar _ ->
                       (* raise (strcat "Impos---free variables invariant (TermNameT)" (tostr (x, t1, fvs1))) *)
                       raise "Impos---free variables invariant (TermNameT)"
                   | InlStar pf_mem ->
                       let t1', pfsubst = subst_tv t1 x vx in
                       let (eqs, vs, pf_ptm) = ptmAuxAux b xl t1' t2 in
                       let eqs', apf = append_pf eqs [(LB_VlEq (V_Var (GV_Bound x)) vx)] in
                       let pf' = PTM_ValueCons eqs x xl vx vs t1 t1' t2 fvs1 eqs' pf_fvs1 pf_mem pf_ptm pfsubst apf in
                         (eqs', (vx::vs), pf'))
          | None ->
              let (eqs, vs, pf_ptm) = ptmAuxAux b xl t1 t2 in
              let pf' = PTM_ValueConsNotMem eqs x xl vs t1 t2 pf_ptm in
                (eqs, vs, pf')



val ptmAux: b:bindings -> alphas:seq bvar -> xs:seq bvar -> t1:typ -> t2:typ
        -> (eqs:bindings * ts:seq typ * vs:seq value * PatternTypeMatch eqs alphas ts xs vs t1 t2)
let rec ptmAux b alphas xs t1 t2 =
  match alphas with
    | [] ->
        let (eqs, vs, pf) = ptmAuxAux b xs t1 t2 in
          (eqs, [], vs, pf)
    | a::al ->
        match find<locbinding, (exists_t a)> (tyEq a) b with
          (* | Some (((LB_TyEq (T_Var (GV_Bound a')) ta), (MkEx _ta (Refl_eq _)), pf_mem)) ->
             TODO: Destruction of user-defined dependent pair not working
          *)
          | Some (((LB_TyEq (T_Var (GV_Bound a')) ta), _, pf_mem)) when a=a' ->
              let fvs1, pf_fvs1 = free_bvars_typ t1 in
                (match decideMem (Tup a TypeNameT) fvs1 with
                   | InrStar _ -> raise (strcat "Impos---free variables invariant (TypNameT)" (tostr (a, t1, fvs1)))
                   | InlStar pf_mem ->
                       let t1', pfsubst = subst_tt t1 a ta in
                       let (eqs, ts, vs, pf_ptm) = ptmAux b al xs t1' t2 in
                       let eqs', apf = append_pf eqs [(LB_TyEq (T_Var (GV_Bound a)) ta)] in
                       let pf' = PTM_TypeCons eqs a al ta ts xs vs t1 t1' t2 fvs1 eqs' pf_fvs1 pf_mem pf_ptm pfsubst apf in
                         eqs', (ta::ts), vs, pf')
          | None ->
              let (eqs, ts, vs, pf_ptm) = ptmAux b al xs t1 t2 in
              let pf' = PTM_TypeConsNotMem eqs a al ts xs vs t1 t2 pf_ptm in
                (eqs, ts, vs, pf')

val mkPatternEqs :  alphas:seq bvar -> xs:seq bvar -> t1:typ -> t2:typ
                 -> (eqs:bindings * ts:seq typ * vs:seq value * PatternTypeMatch eqs alphas ts xs vs t1 t2)
let mkPatternEqs alphas xs t1 t2 =
  let _ = debug_println "About to call unify" in
  match unify_typ alphas xs t1 t2 with
    | None ->
        let _ = println "Type of pattern does not match type of scrutinee" in
        let _ = println (strcat "Available type variables : " (tostr alphas)) in
        let _ = println (strcat "xAvailable value variables : " (tostr xs)) in
        let _ = println (strcat "Pattern type : " (tostr t1)) in
        let _ = println (strcat "Scrutinee type : " (tostr t2)) in
          raise "Type of pattern does not match type of scrutinee"
    | Some b ->
        let _ = debug_println "returned from unify" in
          ptmAux b alphas xs t1 t2
       
(* ******************************************************************************** *)
type wfK :: icompartment => environment => bindings => kind => basekind => P =
   | WFK_Base  : I:icompartment -> G:environment -> B:bindings
                 -> b:basekind
                 -> wfEnv I G B
                 -> wfK I G B (K_Base b) b

   | WFK_ProdK : I:icompartment -> G:environment -> B:bindings
                 -> a:bvar -> k1:kind -> b1:basekind -> k2:kind -> b2:basekind
                 -> KindCompat b1 b2
                 -> wfK I G B k1 b1
                 -> wfK I G ((LB_BvarKind a k1)::B) k2 b2
                 -> wfK I G B (K_ProdK a k1 k2) b2

   | WFK_ProdT : I:icompartment -> G:environment -> B:bindings
                 -> x:bvar -> t:typ -> tb:basekind -> k:kind -> b:basekind
                 -> VIndexKindCompat tb b
                 -> wfT I G B t (K_Base tb)
                 -> wfK I G ((LB_BvarTy x t)::B) k b
                 -> wfK I G B (K_ProdT x t k) b

and wfT :: icompartment => environment => bindings => typ => kind => P =

   | WFT_Var : I:icompartment -> G:environment -> B:bindings
                -> a:bvar -> k:kind
                -> wfEnv I G B
                -> Mem (LB_BvarKind a k) B
                -> wfT I G B (T_Var (GV_Bound a)) k

   | WFT_FVar : I:icompartment -> G:environment -> B:bindings
                -> a:tyname -> k:kind
                -> wfEnv I G B
                -> Mem (FV_TyName a k) G
                -> wfT I G B (T_Var (GV_Free a)) k

   | WFT_Unit : I:icompartment -> G:environment -> B:bindings
                -> wfEnv I G B
                -> wfT I G B T_Unit (K_Base BK_Comp)

   | WFT_Ind : I:icompartment -> G:environment -> B:bindings
                -> i:name -> k:kind
                -> wfEnv I G B
                -> ICompBinds_I I i k
                -> wfT I G B (T_Ind i) k

   | WFT_VApp : I:icompartment -> G:environment -> B:bindings
                -> u:typ -> v:value -> x:bvar -> t:typ -> k:kind -> kres:kind
                -> wfT I G B u (K_ProdT x t k)
                -> value_ty I G B [] Type_level v t
                -> SubstKV k x v kres
                -> wfT I G B (T_VApp u v) kres

   | WFT_App : I:icompartment -> G:environment -> B:bindings
                -> t:typ -> u:typ -> a:bvar -> k:kind -> k':kind -> kres:kind
                -> wfT I G B t (K_ProdK a k k')
                -> wfT I G B u k
                -> SubstKT k' a u kres
                -> wfT I G B (T_App t u) kres

   | WFT_Prod : I:icompartment -> G:environment -> B:bindings
                -> x:bvar -> t:typ -> bt:basekind
                -> u:typ -> bu:basekind
                -> ConcreteKind bt
                -> ConcreteKind bu
                -> wfT I G B t (K_Base bt)
                -> wfT I G ((LB_BvarTy x t)::B) u (K_Base bu)
                -> wfT I G B (T_Prod x t u) (K_Base bu)

   | WFT_ProdK : I:icompartment -> G:environment -> B:bindings
                -> a:bvar -> k:kind -> b:basekind
                -> u:typ -> bu:basekind
                -> ConcreteKind bu
                -> wfK I G B k b
                -> wfT I G ((LB_BvarKind a k)::B) u (K_Base bu)
                -> wfT I G B (T_ProdK a k u) (K_Base bu)

   | WFT_Ref : I:icompartment -> G:environment -> B:bindings
                -> x:bvar -> t:typ -> phi:typ -> bt:basekind
                -> ConcreteKind bt
                -> wfT I G B t (K_Base bt)
                -> wfT I G ((LB_BvarTy x t)::B) phi (K_Base BK_Erase)
                -> wfT I G B (T_Ref x t phi) (K_Base bt)

   | WFT_Lam : I:icompartment -> G:environment -> B:bindings
                -> x:bvar -> t:typ -> bt:basekind -> u:typ -> ku:kind
                -> ConcreteKind bt
                -> wfT I G B t (K_Base bt)
                -> wfT I G ((LB_BvarTy x t)::B) u ku
                -> wfT I G B (T_Lam x t u) (K_ProdT x t ku)

   | WFT_Afn : I:icompartment -> G:environment -> B:bindings
                -> t:typ
                -> wfT I G B t (K_Base BK_Comp)
                -> wfT I G B (T_Afn t) (K_Base BK_Afn)

   | WFT_Ascribe : I:icompartment -> G:environment -> B:bindings
                     -> t:typ -> k:kind
                     -> wfT I G B t k
                     -> wfT I G B (T_Ascribe t k) k

   | WFT_Sub : I:icompartment -> G:environment -> B:bindings
                 -> t:typ -> k:kind -> k':kind -> b:basekind
                 -> wfT I G B t k
                 -> Subkinding I G B [] k k'
                 -> wfK I G B k' b
                 -> wfT I G B t k'

and value_ty :: icompartment => environment => bindings => acontext => mode => value => typ => P =
   | WFV_Var :  I:icompartment -> G:environment -> B:bindings -> m:mode
                  -> x:bvar -> t:typ
                  -> wfEnv I G B
                  -> Mem (LB_BvarTy x t) B
                  -> wfT I G B t (K_Base BK_Comp)
                  -> value_ty I G B [] m (V_Var (GV_Bound x)) t

   | WFV_VarP :  I:icompartment -> G:environment -> B:bindings -> m:mode
                  -> x:bvar -> t:typ
                  -> wfEnv I G B
                  -> Mem (LB_BvarTy x t) B
                  -> wfT I G B t (K_Base BK_Prop)
                  -> value_ty I G B [] m (V_Var (GV_Bound x)) t

   | WFV_VarT :  I:icompartment -> G:environment -> B:bindings
                  -> x:bvar -> t:typ
                  -> wfEnv I G B
                  -> Mem (LB_BvarTy x t) B
                  -> value_ty I G B [] Type_level (V_Var (GV_Bound x)) t

   | WFV_VarA :  I:icompartment -> G:environment -> B:bindings -> m:mode
                  -> x:bvar -> t:typ
                  -> wfEnv I G B
                  -> Mem (LB_BvarTy x t) B
                  -> value_ty I G B [x] m (V_Var (GV_Bound x)) t

   | WFV_FVar :  I:icompartment -> G:environment -> B:bindings -> m:mode
                  -> x:vlname -> t:typ
                  -> wfEnv I G B
                  -> Mem (FV_VlName x t) G
                  -> value_ty I G B [] m (V_Var (GV_Free x)) t


   | WFV_Unit :  I:icompartment -> G:environment -> B:bindings -> m:mode
                 -> value_ty I G B [] m V_Unit T_Unit

   | WFV_Const :  I:icompartment -> G:environment -> B:bindings -> X:acontext -> m:mode
                   -> c:cname -> ts:seq typ -> vs:seq value
                   -> tc:typ -> u:typ -> k:kind -> x:bvar -> cmon:expr -> e:expr
                   -> CurryT (E_Value (V_Var (GV_Bound x))) ts cmon
                   -> CurryV cmon vs e
                   -> ICompBinds_C I c tc
                   -> wfT I G B u k
                   -> expression_ty I G ((LB_BvarTy x tc)::B) X m e u
                   -> value_ty I G B X m (V_Const c ts vs) u

   | WFV_Fun : I:icompartment -> G:environment -> B:bindings -> X:acontext -> m:mode
                 -> t:typ -> bt:basekind -> u:typ -> x:bvar -> body:expr -> Q:typ
                 -> ConcreteKind bt
                 -> AQual X (T_Prod x t u) Q
                 -> wfT I G B t (K_Base bt)
                 -> expression_ty I G ((LB_BvarTy x t)::B) (x::X) m body u
                 -> value_ty I G B X m (V_Fun x t body) Q

   | WFV_FunT :  I:icompartment -> G:environment -> B:bindings -> X:acontext -> m:mode
                 -> k:kind -> bk:basekind -> u:typ -> a:bvar -> body:expr -> Q:typ
                 -> AQual X (T_ProdK a k u) Q
                 -> wfK I G B k bk
                 -> expression_ty I G ((LB_BvarKind a k)::B) X m body u
                 -> value_ty I G B X m (V_FunT a k body) Q

   | WFV_Ref :  I:icompartment -> G:environment -> B:bindings -> X:acontext -> m:mode
                 -> v:value -> x:bvar -> T:typ -> phi:typ
                 -> LogicEntails I G ((LB_VlEq v (V_Var (GV_Bound x)))::(LB_BvarTy x T)::B) phi
                 -> value_ty I G B X m v T
                 -> value_ty I G B X m v (T_Ref x T phi)

   | WFV_WeakenX : I:icompartment -> G:environment -> B:bindings -> X:acontext -> X1:acontext -> X2:acontext -> m:mode
                 -> v:value -> T:typ
                 -> AContextSplit X X1 X2
                 -> value_ty I G B X1 m v T
                 -> value_ty I G B X m v T

   | WFV_Ascribe : I:icompartment -> G:environment -> B:bindings -> X:acontext -> m:mode
                 -> v:value -> t:typ
                 -> value_ty I G B X m v t
                 -> value_ty I G B X m (V_Ascribe v t) t

   | WFV_Sub : I:icompartment -> G:environment -> B:bindings -> X:acontext -> m:mode
                 -> v:value -> t:typ -> u:typ -> k:kind
                 -> value_ty I G B X m v t
                 -> Subtyping I G B [] t u
                 -> wfT I G B u k
                 -> value_ty I G B X m v u

and expression_ty :: icompartment => environment => bindings => acontext => mode => expr => typ => P =
   | WFE_Val : I:icompartment -> G:environment -> B:bindings -> X:acontext -> m:mode
             -> v:value -> T:typ
             -> value_ty I G B X m v T
             -> expression_ty I G B X m (E_Value v) T

   | WFE_App : I:icompartment -> G:environment -> B:bindings -> X:acontext -> X1:acontext -> X2:acontext -> m:mode
             -> e:expr -> v:value -> x:bvar -> t:typ -> u:typ -> tv:typ -> tres:typ
             -> AContextSplit X X1 X2
             -> StripQual tv (T_Prod x t u)
             -> SubstTV u x v tres
             -> expression_ty I G B X1 m e tv
             -> value_ty I G B X2 m v t
             -> expression_ty I G B X m (E_App e v) tres

   | WFE_TApp : I:icompartment -> G:environment -> B:bindings -> X:acontext -> m:mode
                  -> a:bvar -> k:kind -> t:typ -> e:expr -> te:typ -> u:typ -> tres:typ
                  -> StripQual te (T_ProdK a k u)
                  -> SubstTT u a t tres
                  -> expression_ty I G B X m e te
                  -> wfT I G B t k
                  -> expression_ty I G B X m (E_TApp e t) tres

   | WFE_LetIn : I:icompartment -> G:environment -> B:bindings -> X:acontext -> X1:acontext -> X2:acontext -> m:mode
                -> x:bvar -> e:expr -> body:expr -> t:typ -> bt:basekind -> u:typ -> bu:basekind
                -> AContextSplit X X1 X2
                -> wfT I G B t (K_Base bt)
                -> wfT I G B u (K_Base bu)
                -> KindCompatElim bu bt
                -> expression_ty I G B X1 m e t
                -> expression_ty I G ((LB_BvarTy x t)::B) (x::X2) m body u
                -> expression_ty I G B X m (E_LetIn x e body) u

   | WFE_Match : I:icompartment -> G:environment -> B:bindings
               -> X:acontext -> X1:acontext -> X2:acontext -> m:mode
               -> Eqs:bindings -> B':bindings -> v:value
               -> pt:seq typ -> pv:seq value
               -> ethen:expr -> eelse:expr -> t:typ -> bt:basekind
               -> tv:typ -> btv:basekind -> tpat:typ
               -> c:cname -> alphas:seq bvar -> xs:seq bvar -> tc:typ
               -> ts:seq typ
               -> vs:seq value
               -> Bthen:bindings
               -> Xthen:acontext
               -> AsTyps alphas ts
               -> AsVals xs vs
               -> ICompBinds_C I c tc
               -> Bindings B tc alphas xs B'
               -> AContextSplit X X1 X2
               -> PatternTypeMatch Eqs alphas pt xs pv tpat tv
               -> Append ((LB_VlEq v (V_Const c ts vs))::Eqs) B' Bthen
               -> Append X2 xs Xthen
               -> wfT I G B tv (K_Base btv)
               -> wfT I G B t (K_Base bt)
               -> KindCompatElim bt btv
               -> value_ty I G B X1 m v tv
               -> value_ty I G B' xs m (V_Const c ts vs) tpat
               -> expression_ty I G Bthen Xthen m ethen t
               -> expression_ty I G B X2 m eelse t
               -> expression_ty I G B X m (E_Match v (MkPattern c alphas xs) ethen eelse) t

   | WFE_Assume : I:icompartment -> G:environment -> B:bindings -> X:acontext -> m:mode
                   -> x:bvar -> phi:typ
                   -> wfT I G B phi (K_Base BK_Erase)
                   -> expression_ty I G B X m (E_Assume phi) (T_Ref x T_Unit phi)

   | WFE_WeakenX : I:icompartment -> G:environment -> B:bindings -> X:acontext -> X1:acontext -> X2:acontext -> m:mode
                    -> e:expr -> t:typ
                    -> AContextSplit X X1 X2
                    -> expression_ty I G B X1 m e t
                    -> expression_ty I G B X m e t

   | WFE_Ascribe : I:icompartment -> G:environment -> B:bindings -> X:acontext -> m:mode
                     -> e:expr -> t:typ
                     -> expression_ty I G B X m e t
                     -> expression_ty I G B X m (E_Ascribe e t) t

   | WFE_Sub : I:icompartment -> G:environment -> B:bindings -> X:acontext -> m:mode
                 -> e:expr -> t:typ -> u:typ -> k:kind
                 -> expression_ty I G B X m e t
                 -> Subtyping I G B [] t u
                 -> wfT I G B u k
                 -> expression_ty I G B X m e u

and wfI :: icompartment => P =
   | WFI_Nil : wfI []

   | WFI_Cons : I:icompartment
               -> is:seq ikind -> ds:seq constructor -> b:basekind
               -> wfIKinds I is b
               -> wfConstrs ((MkIndType is [])::I) is ds b
               -> DistinctINames ((MkIndType is ds)::I)
               -> DistinctConstrs ((MkIndType is ds)::I)
               -> wfI I
               -> wfI ((MkIndType is ds)::I)

and wfIKinds :: icompartment => seq ikind => basekind => P =
   | WFIK_Nil : I:icompartment -> b:basekind -> wfIKinds I [] b

   | WFIK_Cons : I:icompartment -> name:iname -> k:kind -> is:seq ikind -> b:basekind
                -> wfK I [] [] k b
                -> wfIKinds I is b
                -> wfIKinds I ((MkIKind name k)::is) b

and wfConstrs :: icompartment => seq ikind => seq constructor => basekind => P =
  | WFC_Nil : I:icompartment -> is:seq ikind -> b:basekind -> wfConstrs I is [] b

  | WFC_Cons : I:icompartment -> is:seq ikind -> c:cname -> t:typ -> cs:seq constructor
              -> b:basekind
              -> ConcreteKind b
              -> wfT I [] [] t (K_Base b)
              -> constrAfn is I [] t b
              -> wfConstrs I is cs b
              -> wfConstrs I is ((MkConstructor c t)::cs) b

and constrAfn :: seq ikind => icompartment => bindings => typ => basekind => P =
  | CA_Base : is:seq ikind -> I:icompartment -> B:bindings -> t:typ -> b:basekind
             -> i:iname -> k:kind -> Mem (MkIKind i k) is
             -> BaseType i t
             -> wfT I [] B t (K_Base b)
             -> constrAfn is I B t b

  | CA_Prod : is:seq ikind -> I:icompartment -> B:bindings
            -> x:bvar -> t:typ -> bt:basekind
            -> u:typ -> b:basekind
            -> wfT I [] B t (K_Base bt)
            -> constrAfn is I ((LB_BvarTy x t)::B) u b
            -> AffineCheck bt b
            -> constrAfn is I B (T_Prod x t u) b
              
  | CA_ProdK :  is:seq ikind -> I:icompartment -> B:bindings
            -> a:bvar -> k:kind -> bk:basekind
            -> u:typ -> b:basekind
            -> wfK I [] B k bk
            -> constrAfn is I ((LB_BvarKind a k)::B) u b
            -> AffineCheck bk b (* Perhaps we do not need this here. It does not appear in the paper rules in the TR *)
            -> constrAfn is I B (T_ProdK a k u) b

and wfIG :: icompartment => environment => P =
   | WFIG_Nil : I:icompartment -> wfI I -> wfIG I []

   | WFIG_ConsV : I:icompartment -> v:vlname -> t:typ -> G:environment -> b:basekind
              -> vs:seq vlname
              -> VlNames G vs
              -> wfT I G [] t (K_Base b)
              -> ConcreteKind b
              -> NotMem v vs
              -> wfIG I G
              -> wfIG I ((FV_VlName v t)::G)

   | WFIG_ConsT : I:icompartment -> a:tyname -> k:kind -> G:environment -> b:basekind
              -> tnames:seq tyname
              -> TyNames G tnames
              -> wfK I G [] k b
              -> NotMem a tnames
              -> wfIG I G
              -> wfIG I ((FV_TyName a k)::G)

and wfEnv :: icompartment => environment => bindings => P =
(*    | WFENV_Admit : I:icompartment -> G:environment -> B:bindings -> wfEnv I G B *)

   | WF_Nil : I:icompartment -> G:environment
            -> wfIG I G
            -> wfEnv I G []

   | WF_WeakTerm : I:icompartment -> G:environment -> B:bindings
                 -> x:bvar -> t:typ -> b:basekind -> names:seq bvar
                 -> BindingBvars B names
                 -> NotMem x names
                 -> ConcreteKind b
                 -> wfT I G B t (K_Base b)
                 -> wfEnv I G B
                 -> wfEnv I G ((LB_BvarTy x t)::B )


   | WF_WeakType : I:icompartment -> G:environment -> B:bindings
                 -> a:bvar -> k:kind -> b:basekind -> names:seq bvar
                 -> BindingBvars B names
                 -> NotMem a names
                 -> wfK I G B k b
                 -> wfEnv I G B
                 -> wfEnv I G ((LB_BvarKind a k)::B)

   | WF_WeakVlEq :  I:icompartment -> G:environment -> B:bindings
                  -> v1:value -> v2:value -> t1:typ -> t2:typ
                  -> wfEnv I G B
                  -> value_ty I G B [] Type_level v1 t1
                  -> value_ty I G B [] Type_level v2 t2
                  -> type_equiv I G B [] t1 t2
                  -> wfEnv I G ((LB_VlEq v1 v2)::B)

   | WF_WeakTyEq :  I:icompartment -> G:environment -> B:bindings
                  -> t1:typ -> t2:typ -> k1:kind -> k2:kind
                  -> wfEnv I G B
                  -> wfT I G B t1 k1
                  -> wfT I G B t2 k2
                  -> kind_equiv I G B [] k1 k2
                  -> wfEnv I G ((LB_TyEq t1 t2)::B)

type wfEnvB :: _ = (fun (i:icompartment) (g:environment) (b:bindings) => option (xs:seq bvar * tmp:(BindingBvars b xs) * wfEnv i g b))
val getWFigb:  i:icompartment -> g:environment -> b:bindings -> wfEnvB i g b -> W (wfEnv i g b)
let getWFigb i g b wfenvb = match wfenvb with
  | Some ((xs, bindingspf, wfigb)) -> MkW wfigb

val check_concrete_kind : b:basekind -> optionP (ConcreteKind b)
let check_concrete_kind b = match b with
  | BK_Comp -> SomeP CK_Star
  | BK_Afn -> SomeP CK_Afn
  | BK_Prop -> SomeP CK_Prop
  | BK_Erase -> NoneP

type fix5 :: (kind => *) => (typ => *) => (value => *) => (expr => *) => (icompartment => *) => * =
  | MkFix5 : 'a::(kind  => *)
         -> 'b::(typ   => *)
         -> 'c::(value => *)
         -> 'd::(expr  => *)
         -> 'e::(icompartment => *)
         -> (fix5 'a 'b 'c 'd 'e -> k:kind     -> 'a k)
         -> (fix5 'a 'b 'c 'd 'e -> t:typ      -> 'b t)
         -> (fix5 'a 'b 'c 'd 'e -> v:value    -> 'c v)
         -> (fix5 'a 'b 'c 'd 'e -> e:expr     -> 'd e)
         -> (fix5 'a 'b 'c 'd 'e -> i:icompartment -> 'e i)
         -> fix5 'a 'b 'c 'd 'e

type texpr :: _ = fun (e:expr)  => (I:icompartment -> G:environment -> B:bindings -> A:acontext
                                     -> m:mode -> wfEnvB I G B -> (t:typ * A1:acontext * A2:acontext * AContextSplit A A1 A2 *
                                                                    expression_ty I G B A1 m e t))
type tval :: _  = fun (v:value) => (I:icompartment -> G:environment -> B:bindings -> A:acontext
                                     -> m:mode -> wfEnvB I G B -> (t:typ * A1:acontext * A2:acontext * AContextSplit A A1 A2 *
                                                                    value_ty I G B A1 m v t))
type ktyp :: _  = fun (t:typ)   => (I:icompartment -> G:environment -> B:bindings -> wfEnvB I G B
                                     -> (k:kind * wfT I G B t k))
type okk  :: _  = fun (k:kind)  => (I:icompartment -> G:environment -> B:bindings -> wfEnvB I G B
                                     -> (b:basekind * wfK I G B k b))
type extenv :: _ = fun (I:icompartment) => (G:environment -> B:bindings -> b:locbinding -> wfEnvB I G B -> string -> (wfEnvB I G (b::B)))


val mkBindings : fix5 okk ktyp tval texpr extenv
               -> i:icompartment -> g:environment -> b:bindings
               -> t:typ -> alphas:seq bvar -> xs:seq bvar
               -> wfEnvB i g b
               -> (b':bindings * xx:Bindings b t alphas xs b' * wfEnvB i g b')
let rec mkBindings ff i g b t alphas xs wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    match t with
      | T_ProdK formal k t2 ->
          (match alphas with
             | a::al ->
(*                  let b1 = (LB_BvarKind a k)::b in *)
                 let wfenvb1 = extenv' ff i g b (LB_BvarKind a k) wfenvb "ext1" in
                 let t2', pf_subst = subst_tt t2 formal (T_Var (GV_Bound a)) in
                 let b', pf, wfenvb' = mkBindings ff i g ((LB_BvarKind a k)::b) t2' al xs wfenvb1 in
                   b', Bindings_tcons b formal k t2 t2' a al xs b' pf_subst pf, wfenvb'
             | _ -> raise "Not enough pattern type variables")

      | T_Prod formal t1 t2 ->
          (match alphas, xs with
             | [], (x::xtl) ->
(*                  let b1 = (LB_BvarTy x t1)::b in *)
                 let wfenvb1 = extenv' ff i g b (LB_BvarTy x t1) wfenvb "ext2" in
                 let t2', pf_subst = subst_tv t2 formal (V_Var (GV_Bound x)) in
                 let b', pf, wfenvb' = mkBindings ff i g ((LB_BvarTy x t1)::b) t2' [] xtl wfenvb1 in
                   b', Bindings_vcons b formal t1 t2 t2' x xtl b' pf_subst pf, wfenvb'
             | _ -> raise "Not enough pattern variables; or too many type variables")
            
      | _ ->
          (match alphas, xs with
             | [], [] -> b, Bindings_nil b t, wfenvb
             | _ -> raise "Too many pattern variables")


(* ******************************************************************************** *)
(* Type equivalence *)
(* ******************************************************************************** *)
val print_equalities : typ -> typ -> bindings -> unit
let rec print_equalities t u bindings = match bindings with
  | [] -> ()
  | (LB_TyEq t' u')::rest ->
      if (t=t') || (u=u') || (t=u') || (u=t')
      then (print_stderr "Env contains: ";
            print_stderr (tostr (LB_TyEq t' u'));
            print_equalities t u rest)
      else
        print_equalities t u rest
  | _::rest -> print_equalities t u rest
      
type tequiv_t :: _ = (fun (i:icompartment) => g:environment -> b:bindings -> d:al2bindings
                        -> t1:typ -> t2:typ
                        -> optionP (type_equiv i g b d t1 t2))
type kequiv_t :: _ = (fun (i:icompartment) => g:environment -> b:bindings -> d:al2bindings
                        -> k1:kind -> k2:kind
                        -> optionP (kind_equiv i g b d k1 k2))

type fixequiv :: _ = fix2 icompartment tequiv_t icompartment kequiv_t


let should_alpha x y f =
  if (x="__dummy") || (y="__dummy") || (x=y)
  then false
  else mem y (f())
  
val tequiv_prod: fixequiv -> i:icompartment -> g:environment -> b:bindings -> d:al2bindings
              -> x:bvar -> y:bvar -> t1:typ -> t2:typ -> u1:typ -> u2:typ
              -> option (type_equiv i g b d t1 t2 *
                         type_equiv i g b ((AL2_Type x y t1)::d) u1 u2)
let tequiv_prod ff i g b d x y t1 t2 u1 u2 =
  match ff with MkFix2 tequiv' kequiv' ->
    match tequiv' ff i g b d t1 t2 with
      | NoneP -> None
      | SomeP pf1 ->
          let alpha = should_alpha x y (fun () -> free_bvars_typ_nopf u2) in
          let d' = (AL2_Type x y t1)::d in
            if alpha then
              let u2', pf_subst = subst_tv u2 y (V_Var (GV_Bound x)) in
                match tequiv' ff i g b d' u1 u2' with
                  | NoneP -> None
                  | SomeP pf2' ->
                      let pf2 = TE_TyAlpha i g b d' u1 u2 x y t1 u2' (Mem_hd (AL2_Type x y t1) d) pf_subst pf2' in
                        Some (pf1, pf2)
            else
              match tequiv' ff i g b d' u1 u2 with
                | NoneP -> None
                | SomeP pf2 -> Some(pf1, pf2)

val tequiv_prodk: fixequiv -> i:icompartment -> g:environment -> b:bindings -> d:al2bindings
                -> aa:bvar -> bb:bvar -> k1:kind -> k2:kind -> t1:typ -> t2:typ
                -> option (kind_equiv i g b d k1 k2 *
                           type_equiv i g b ((AL2_Kind aa bb k1)::d) t1 t2)
let tequiv_prodk ff i g b d aa bb k1 k2 t1 t2 =
  match ff with MkFix2 tequiv' kequiv' ->
    match kequiv' ff i g b d k1 k2 with
      | NoneP -> None
      | SomeP pf1 ->
          let alpha = should_alpha aa bb (fun () -> free_bvars_typ_nopf t2) in
          let d' = (AL2_Kind aa bb k1)::d in
            if alpha then
              let t2', pf_subst = subst_tt t2 bb (T_Var (GV_Bound aa)) in
                match tequiv' ff i g b d' t1 t2' with
                  | NoneP -> None
                  | SomeP pf2' ->
                      let pf2 = TE_KindAlpha i g b d' t1 t2 aa bb k1 t2' (Mem_hd (AL2_Kind aa bb k1) d) pf_subst pf2' in
                        Some (pf1, pf2)
            else
              match tequiv' ff i g b d' t1 t2 with
                | NoneP -> None
                | SomeP pf2 -> Some(pf1, pf2)

val tequiv': fixequiv -> i:icompartment -> tequiv_t i
let tequiv' ff i g b d t u =
  match ff with MkFix2 tequiv' kequiv' ->
    if t=u
    then SomeP (TE_Refl i g b d t)
    else
      match t, u with
        | (T_App t1 u1), (T_App t2 u2) ->
            (match tequiv' ff i g b d t1 t2 with
               | NoneP -> NoneP
               | SomeP pf1 ->
                   match tequiv' ff i g b d u1 u2 with
                     | NoneP -> NoneP
                     | SomeP pf2 -> SomeP (TE_TApp i g b d t1 t2 u1 u2 pf1 pf2))

        | (T_Prod x t1 u1), (T_Prod y t2 u2) ->
            (match tequiv_prod ff i g b d x y t1 t2 u1 u2 with
               | None -> NoneP
               | Some((pf1, pf2)) ->  SomeP (TE_Prod i g b d x y t1 t2 u1 u2 pf1 pf2))
                   
        | (T_Ref x t1 phi1), (T_Ref y t2 phi2) ->
            (match tequiv_prod ff i g b d x y t1 t2 phi1 phi2 with
               | None -> NoneP
               | Some((pf1, pf2)) -> SomeP (TE_Ref i g b d x y t1 t2 phi1 phi2 pf1 pf2))

        | (T_Lam x t1 u1), (T_Lam y t2 u2) ->
            (match tequiv_prod ff i g b d x y t1 t2 u1 u2 with
               | None -> NoneP
               | Some((pf1, pf2)) -> SomeP (TE_Lam i g b d x y t1 t2 u1 u2 pf1 pf2))

        | (T_ProdK aa k1 t1), (T_ProdK bb k2 t2) ->
            (match tequiv_prodk ff i g b d aa bb k1 k2 t1 t2 with
               | None -> NoneP
               | Some((pf1, pf2)) -> SomeP (TE_ProdK i g b d aa bb k1 k2 t1 t2 pf1 pf2))
                             
        | (T_Afn t1), (T_Afn t2) ->
            (match tequiv' ff i g b d t1 t2 with
               | NoneP -> NoneP
               | SomeP pf -> SomeP (TE_Afn i g b d t1 t2 pf))

        | (T_VApp t1 v1), (T_VApp t2 v2) ->
            (match tequiv' ff i g b d t1 t2 with
               | NoneP -> NoneP
               | SomeP pf1 ->
                   match query_equiv i g b v1 v2 with
                     | NoneP -> NoneP
                     | SomeP pf2 ->
                         SomeP (TE_BValRefine_Logic i g b d t1 t2 v1 v2 pf1 pf2))

        | (T_Var (GV_Bound a)), _ ->
            (match mem_pf (LB_TyEq t u) b with
               | NoneP ->
                   (match mem_pf (LB_TyEq u t) b with
                      | NoneP ->
                          print_stderr "Failed to refine type variable: ";
                          print_stderr (tostr a);
                          print_equalities t u b;
                          NoneP
                      | SomeP pf -> SomeP (TE_Sym i g b d t u (TE_BTyRefine i g b d u t pf)))
               | SomeP pf -> SomeP (TE_BTyRefine i g b d t u pf))

        | _, (T_Var (GV_Bound _)) ->
            (match tequiv' ff i g b d u t with
               | SomeP pf -> SomeP (TE_Sym i g b d t u pf)
               | _ -> NoneP)
              
        | _ -> NoneP (* TyBeta handled by whnf, transitivity too.
                       valued refinement is always via logic, not BValRefine *)

val kequiv': fixequiv -> i:icompartment -> kequiv_t i                    
let kequiv' ff i g b d k l =
  match ff with MkFix2 tequiv' kequiv' ->
    if k=l
    then SomeP (KE_Refl i g b d k)
    else
      match k, l with
        | (K_ProdK aa k1 k2), (K_ProdK bb k1' k2') ->
            (match kequiv' ff i g b d k1 k1' with
               | NoneP -> NoneP
               | SomeP pf1 ->
                   let d' = (AL2_Kind aa bb k1)::d in
                     if should_alpha aa bb (fun () -> free_bvars_kind_nopf k2')
                     then
                       let k2'', pf_subst = subst_kt k2' bb (T_Var (GV_Bound aa)) in
                         match kequiv' ff i g b d' k2 k2'' with
                           | NoneP -> NoneP
                           | SomeP pf2' ->
                               let pf2 = KE_KindAlpha i g b d' k2 k2' aa bb k1 k2'' (Mem_hd (AL2_Kind aa bb k1) d) pf_subst pf2' in
                                 SomeP (KE_ProdK i g b d aa bb k1 k1' k2 k2' pf1 pf2)
                     else
                       match kequiv' ff i g b d' k2 k2' with
                         | NoneP -> NoneP
                         | SomeP pf2 -> SomeP (KE_ProdK i g b d aa bb k1 k1' k2 k2' pf1 pf2))
              
        | (K_ProdT x t1 k1), (K_ProdT y t2 k2) ->
            (match tequiv' ff i g b d t1 t2 with
               | NoneP -> NoneP
               | SomeP pf1 ->
                   let d' = (AL2_Type x y t1)::d in
                     if should_alpha x y (fun () -> free_bvars_kind_nopf k2)
                     then
                       let k2', pf_subst = subst_kv k2 y (V_Var (GV_Bound x)) in
                         match kequiv' ff i g b d' k1 k2' with
                           | NoneP -> NoneP
                           | SomeP pf2' ->
                               let pf2 = KE_TyAlpha i g b d' k1 k2 x y t1 k2' (Mem_hd (AL2_Type x y t1) d) pf_subst pf2' in
                                 SomeP (KE_ProdT i g b d x y t1 t2 k1 k2 pf1 pf2)
                     else
                       match kequiv' ff i g b d' k1 k2 with
                         | NoneP -> NoneP
                         | SomeP pf2 -> SomeP(KE_ProdT i g b d x y t1 t2 k1 k2 pf1 pf2))

        | _ ->  NoneP

val tequiv : i:icompartment -> tequiv_t i
let tequiv i g b d t1 t2 = tequiv' (MkFix2 tequiv' kequiv') i g b d t1 t2
  
val kequiv : i:icompartment -> kequiv_t i
let kequiv i g b d k1 k2 = kequiv' (MkFix2 tequiv' kequiv') i g b d k1 k2

(* ******************************************************************************** *)
(* Type normalization *)
(* ******************************************************************************** *)
type whnf_t  :: _ = (fun (i:icompartment) => g:environment -> b:bindings -> d:al2bindings
                      -> t1:typ
                      -> (t2:typ * type_equiv i g b d t1 t2))
type kwhnf_t :: _ = (fun (i:icompartment) => g:environment -> b:bindings -> d:al2bindings
                       -> k1:kind
                       -> (k2:kind * kind_equiv i g b d k1 k2))
type fixwhnf :: _ = fix2 icompartment whnf_t icompartment kwhnf_t

val whnf' : fixwhnf -> i:icompartment -> whnf_t i
let whnf' ff i g b d t =
  match ff with MkFix2 whnf' kwhnf' ->
    match t with
      | T_Var _ ->
          let eqOpt =
            find<locbinding, (fun (l:locbinding) => (Eq t t))>
              (fun b ->
                 match b with
                   | LB_TyEq t' _ when t=t' -> SomeP (Refl_eq t)
                   | _ -> NoneP) b in
            (match eqOpt with
               | Some ((LB_TyEq t' u, _, pf_mem)) when t=t' ->
                   let res, pf_u = whnf' ff i g b d u in
                     (res, TE_Trans i g b d t u res (TE_BTyRefine i g b d t u pf_mem) pf_u)
               | None -> (t, TE_Refl i g b d t))

      | T_Unit -> (t, TE_Refl i g b d t)

      | T_Ind _ -> (t, TE_Refl i g b d t)

      | T_VApp t1 v2 ->
          let (t1', pf1) = whnf' ff i g b d t1 in
          let eq_cong = TE_VApp i g b d t1 t1' v2 pf1 in
            (match t1' with
               | T_Lam x t1_1 t1_2 ->
                   let beta, pf_subst = subst_tv t1_2 x v2 in
                   let res, eq_beta_res = whnf' ff i g b d beta in
                   let eq_beta = TE_TyBeta i g b d x t1_1 t1_2 v2 beta pf_subst in
                   let eq_res = TE_Trans i g b d (T_VApp t1' v2) beta res eq_beta eq_beta_res in
                   let eq = TE_Trans i g b d t (T_VApp t1' v2) res eq_cong eq_res in
                     res, eq
               | _ ->
                   let res = T_VApp t1' v2 in
                     (res, eq_cong))

      | T_App t1 t2 ->
          let (t1', pf1) = whnf' ff i g b d t1 in
          let (t2', pf2) = whnf' ff i g b d t2 in
          let res = T_App t1' t2' in
            (res, (TE_TApp i g b d t1 t1' t2 t2' pf1 pf2))

      | T_Prod x t1 t2 ->
          let (t1', pf1) = whnf' ff i g b d t1 in
          let (t2', pf2) = whnf' ff i g b ((AL2_Type x x t1)::d) t2 in
          let res = T_Prod x t1' t2' in
            (res, (TE_Prod i g b d x x t1 t1' t2 t2' pf1 pf2))

      | T_Ref x t1 phi2 ->
          let (t1', pf1) = whnf' ff i g b d t1 in
          let (phi2', pf2) = whnf' ff i g b ((AL2_Type x x t1)::d) phi2 in
          let res = T_Ref x t1' phi2' in
            (res, (TE_Ref i g b d x x t1 t1' phi2 phi2' pf1 pf2))

      | T_Lam x t1 t2 ->
          let (t1', pf1) = whnf' ff i g b d t1 in
          let (t2', pf2) = whnf' ff i g b ((AL2_Type x x t1)::d) t2 in
          let res = T_Lam x t1' t2' in
            (res, (TE_Lam i g b d x x t1 t1' t2 t2' pf1 pf2))

      | T_ProdK a k1 t2 ->
          let (k1', pf1) = kwhnf' ff i g b d k1 in
          let (t2', pf2) = whnf' ff i g b ((AL2_Kind a a k1)::d) t2 in
          let res = T_ProdK a k1' t2' in
            (res, (TE_ProdK i g b d a a k1 k1' t2 t2' pf1 pf2))

      | T_Afn t1 ->
          let t1', pf = whnf' ff i g b d t1 in
          let res = T_Afn t1' in
            (res, TE_Afn i g b d t1 t1' pf)

      | T_Ascribe t1 k1 ->
          let t1', pf = whnf' ff i g b d t1 in
            (t1', TE_Unascribe i g b d t1 t1' k1 pf)

val kwhnf' : fixwhnf -> i:icompartment -> kwhnf_t i
let kwhnf' ff i g b d k =
  match ff with MkFix2 whnf' kwhnf' ->
    match k with
      | K_Base _ -> (k, KE_Refl i g b d k)
      | K_ProdT x t1 k2 ->
          let t1', pf1 = whnf' ff i g b d t1 in
          let k2', pf2 = kwhnf' ff i g b ((AL2_Type x x t1)::d) k2 in
          let res = K_ProdT x t1' k2' in
            (res, KE_ProdT i g b d x x t1 t1' k2 k2' pf1 pf2)
      | K_ProdT a k1 k2 ->
          let k1', pf1 = kwhnf' ff i g b d k1 in
          let k2', pf2 = kwhnf' ff i g b ((AL2_Kind a a k1)::d) k2 in
          let res = K_ProdK a k1' k2' in
            (res, KE_ProdK i g b d a a k1 k1' k2 k2' pf1 pf2)

val whnf : i:icompartment -> whnf_t i
let whnf i g b d t = whnf' (MkFix2 whnf' kwhnf') i g b d t

val kwhnf : i:icompartment -> kwhnf_t i
let kwhnf i g b d k = kwhnf' (MkFix2 whnf' kwhnf') i g b d k

(* ******************************************************************************** *)
(* Type conversion (subtyping) *)
(* ******************************************************************************** *)
type tconv_t :: _ = (fun (i:icompartment) => g:environment -> b:bindings -> d:al2bindings
                        -> t1:typ -> t2:typ
                        -> optionP (Subtyping i g b d t1 t2))
type kconv_t :: _ = (fun (i:icompartment) => g:environment -> b:bindings -> d:al2bindings
                        -> k1:kind -> k2:kind
                        -> optionP (Subkinding i g b d k1 k2))

type fixconv :: _ = fix2 icompartment tconv_t icompartment kconv_t

val tconv': fixconv -> i:icompartment -> tconv_t i
let tconv' ff i g b d t t' =
  match ff with MkFix2 tconv' kconv' ->
    match tequiv i g b d t t' with
      | SomeP pf -> SomeP (ST_Refl i g b d t t' pf)
      | NoneP ->
          match t, t' with
            | T_Ref x u1 phi, u1' ->
                (match tconv' ff i g b d u1 u1' with
                   | NoneP -> NoneP
                   | SomeP pf -> SomeP (ST_RefLeft i g b d x u1 u1' phi pf))

            | u1, T_Ref x u1' phi ->
                (match tconv' ff i g b d u1 u1' with
                   | NoneP -> NoneP
                   | SomeP pf_sub ->
                       let b', pf_merge = al2_merge b d in
                         match query i g ((LB_BvarTy x u1)::b') phi with
                           | NoneP -> NoneP
                           | SomeP pf_entails ->
                               SomeP (ST_RefRight i g b d b' x u1 u1' phi pf_merge pf_sub pf_entails))
                  
            | (T_Prod x1 t1 t2), (T_Prod y1 u1 u2) ->
                (match tconv' ff i g b d u1 t1 with
                   | NoneP -> NoneP
                   | SomeP pf1 ->
                       let d' = ((AL2_Type x1 y1 u1)::d) in
                         if should_alpha x1 y1 (fun () -> free_bvars_typ_nopf u2)
                         then
                           let u2', pf_subst = subst_tv u2 y1 (V_Var (GV_Bound x1)) in
                             match tconv' ff i g b d' t2 u2' with
                               | NoneP -> NoneP
                               | SomeP pf2' ->
                                   let pf2 =
                                     ST_Trans i g b d' t2 u2' u2
                                       pf2' (ST_Refl i g b d' u2' u2
                                               (TE_TyAlpha i g b d' u2' u2 x1 y1 u1 u2'
                                                  (Mem_hd (AL2_Type x1 y1 u1) d) pf_subst (TE_Refl i g b d' u2'))) in
                                     SomeP (ST_Prod i g b d x1 y1 t1 u1 t2 u2 pf1 pf2)
                         else
                           match tconv' ff i g b d' t2 u2 with
                             | NoneP -> NoneP
                             | SomeP pf2 -> SomeP (ST_Prod i g b d x1 y1 t1 u1 t2 u2 pf1 pf2))
                  
            | (T_ProdK aa k1 t2), (T_ProdK bb l1 u2) ->
                (match kconv' ff i g b d l1 k1 with
                   | NoneP -> NoneP
                   | SomeP pf1 ->
                       let d' = ((AL2_Kind aa bb l1)::d) in
                         if should_alpha aa bb (fun () -> free_bvars_typ_nopf u2)
                         then
                           let u2', pf_subst = subst_tt u2 bb (T_Var (GV_Bound aa)) in
                             match tconv' ff i g b d' t2 u2' with
                               | NoneP -> NoneP
                               | SomeP pf2' ->
                                   let pf2 =
                                     ST_Trans i g b d' t2 u2' u2
                                       pf2' (ST_Refl i g b d' u2' u2
                                               (TE_KindAlpha i g b d' u2' u2 aa bb l1 u2'
                                                  (Mem_hd (AL2_Kind aa bb l1) d) pf_subst (TE_Refl i g b d' u2'))) in
                                     SomeP (ST_ProdK i g b d aa bb k1 l1 t2 u2 pf1 pf2)
                         else
                           match tconv' ff i g b d' t2 u2 with
                             | NoneP -> NoneP
                             | SomeP pf2 -> SomeP (ST_ProdK i g b d aa bb k1 l1 t2 u2 pf1 pf2))

            | (T_Afn t1), (T_Afn u1) ->
                (match tconv' ff i g b d t1 u1 with
                   | NoneP -> NoneP
                   | SomeP pf -> SomeP (ST_Afn i g b d t1 u1 pf))

            | _ ->
                (print_stderr "Error: subtyping failed between: ";
                 print_stderr (tostr t);
                 print_stderr (tostr t');
                 NoneP)

val kconv': fixconv -> i:icompartment -> kconv_t i
let kconv' ff i g b d k1 k2 =
  match ff with MkFix2 tconv' kconv' ->
    match kequiv i g b d k1 k2 with
      | SomeP pf -> SomeP (SK_Refl i g b d k1 k2 pf)
      | NoneP ->
          match k1, k2 with
            (* | (K_Base BK_Prop),  (K_Base BK_Comp) ->  Some (SK_P_Star i g b d) *)
            | (K_Base BK_Comp),  (K_Base BK_Erase) -> SomeP (SK_Star_E i g b d)
            | (K_Base BK_Prop),  (K_Base BK_Erase) ->  SomeP (SK_P_E i g b d)
                (* Some (SK_Trans i g b d *)
                (*         (K_Base BK_Prop) (K_Base BK_Comp) (K_Base BK_Erase) *)
                (*         (SK_P_Star i g b d) *)
                (*         (SK_Star_E i g b d)) *)

            | (K_ProdT x t1 l1), (K_ProdT y t2 l2) ->
                (match tconv' ff i g b d t2 t1 with
                   | NoneP -> NoneP
                   | SomeP pf1 ->
                       let d' = (AL2_Type x y t2)::d in
                         if should_alpha x y (fun () -> free_bvars_kind_nopf l2)
                         then
                           let l2', pf_subst = subst_kv l2 y (V_Var (GV_Bound x)) in
                             match kconv' ff i g b d' l1 l2' with
                               | NoneP -> NoneP
                               | SomeP pf2' ->
                                   let pf2 =
                                     SK_Trans i g b d' l1 l2' l2
                                       pf2' (SK_Refl i g b d' l2' l2
                                               (KE_TyAlpha i g b d' l2' l2 x y t2 l2'
                                                  (Mem_hd (AL2_Type x y t2) d) pf_subst (KE_Refl i g b d' l2'))) in
                                     SomeP (SK_ProdT i g b d x y t1 t2 l1 l2 pf1 pf2)
                         else
                           match kconv' ff i g b d' l1 l2 with
                             | NoneP -> NoneP
                             | SomeP pf2 -> SomeP (SK_ProdT i g b d x y t1 t2 l1 l2 pf1 pf2))

            | (K_ProdK aa m1 l1), (K_ProdK bb m2 l2) ->
                (match kconv' ff i g b d m2 m1 with
                   | NoneP -> NoneP
                   | SomeP pf1 ->
                       let d' = (AL2_Kind aa bb m2)::d in
                         if should_alpha aa bb (fun () -> free_bvars_kind_nopf l2)
                         then
                           let l2', pf_subst = subst_kt l2 bb (T_Var (GV_Bound aa)) in
                             match kconv' ff i g b d' l1 l2' with
                               | NoneP -> NoneP
                               | SomeP pf2' ->
                                   let pf2 =
                                     SK_Trans i g b d' l1 l2' l2
                                       pf2' (SK_Refl i g b d' l2' l2
                                               (KE_KindAlpha i g b d' l2' l2 aa bb m2 l2'
                                                  (Mem_hd (AL2_Kind aa bb m2) d) pf_subst (KE_Refl i g b d' l2'))) in
                                     SomeP (SK_ProdK i g b d aa bb m1 m2 l1 l2 pf1 pf2)
                         else
                           match kconv' ff i g b d' l1 l2 with
                             | NoneP -> NoneP
                             | SomeP pf2 -> SomeP (SK_ProdK i g b d aa bb m1 m2 l1 l2 pf1 pf2))

            | _ -> NoneP

val tconv : i:icompartment -> g:environment -> b:bindings
          -> t1:typ -> t2:typ
          -> optionP (Subtyping i g b [] t1 t2)
let tconv i g b t1 t2 =
  let t1', pf1 = whnf i g b [] t1 in
  let t2', pf2 = whnf i g b [] t2 in
    match tconv' (MkFix2 tconv' kconv') i g b [] t1' t2' with
      | NoneP -> NoneP
      | SomeP pf ->
          SomeP (ST_Trans i g b [] t1 t1' t2
                   (ST_Refl i g b [] t1 t1' pf1 )
                   (ST_Trans i g b [] t1' t2' t2 pf
                      (ST_Refl i g b [] t2' t2 (TE_Sym i g b [] t2' t2 pf2))))
            
val kconv : i:icompartment -> g:environment -> b:bindings
          -> k1:kind -> k2:kind
          -> optionP (Subkinding i g b [] k1 k2)
let kconv i g b k1 k2 =
  let k1', pf1 = kwhnf i g b [] k1 in
  let k2', pf2 = kwhnf i g b [] k2 in
    match kconv' (MkFix2 tconv' kconv') i g b [] k1' k2' with
      | NoneP -> NoneP
      | SomeP pf ->
          SomeP (SK_Trans i g b [] k1 k1' k2
                   (SK_Refl i g b [] k1 k1' pf1)
                   (SK_Trans i g b [] k1' k2' k2 pf
                      (SK_Refl i g b [] k2' k2 (KE_Sym i g b [] k2' k2 pf2))))
            
(* ******************************************************************************** *)
(* Main kinding/typing judgments *)
(* ******************************************************************************** *)
val subkinding: t:typ ->  i:icompartment -> g:environment -> b:bindings
              -> k:kind -> k':kind -> bk:basekind
              -> wfT i g b t k
              -> wfK i g b k' bk
              -> optionP (wfT i g b t k')
let subkinding t i g b k k' bk pft pfk =
  if k=k'
  then SomeP pft
  else
    match kconv i g b k k' with
      | NoneP -> NoneP
      | SomeP pf_sub -> SomeP (WFT_Sub i g b t k k' bk pft pf_sub pfk)
          
val subtypingV: e:value -> i:icompartment -> g:environment -> b:bindings -> a:acontext -> m:mode
              -> t:typ -> t':typ -> k:kind
              -> value_ty i g b a m e t
              -> wfT i g b t' k
              -> optionP (value_ty i g b a m e t')
let subtypingV e i g b a m t t' k pft pfk =
  if t=t'
  then SomeP pft
  else
    match tconv i g b t t' with
      | NoneP -> NoneP
      | SomeP pf_sub ->
          SomeP (WFV_Sub i g b a m e t t' k pft pf_sub pfk)
      
val subtypingE: e:expr -> i:icompartment -> g:environment -> b:bindings -> a:acontext -> m:mode
              -> t:typ -> t':typ -> k:kind
              -> expression_ty i g b a m e t
              -> wfT i g b t' k
              -> optionP (expression_ty i g b a m e t')
let subtypingE e i g b a m t t' k pft pfk =
  if t=t' then SomeP pft
  else
    match tconv i g b t t' with
      | NoneP -> NoneP
      | SomeP pf_sub ->
          SomeP (WFE_Sub i g b a m e t t' k pft pf_sub pfk)

val weaken_x_not_in_a1:  x:bvar -> a:acontext -> a1:acontext -> a2:acontext
                      -> AContextSplit (x::a) a1 a2
                      -> i:icompartment -> g:environment -> b:bindings -> m:mode -> e:expr -> t:typ
                      -> expression_ty i g b a1 m e t
                      -> (a1':acontext * a2':acontext * AContextSplit (x::a) (x::a1') a2' * expression_ty i g b (x::a1') m e t)
let weaken_x_not_in_a1 x a a1 a2 split_xa i g b m e t pf_e =
  match findPerm' x a2 with
    | None -> raise "Impossible 5"
    | Some ((a2', perm_a2)) -> (*  perm_a2 : Perm a2 (x::a2') *)
        let split_xa' = partPerm3 (x::a) a1 a2 (x::a2') perm_a2 split_xa in
        let part_a = partUnconsR x a a1 a2' split_xa' in
          (* split_xa : AContextSplit (x::a) a1 (x::a2') *)
          (* part_a : AContextSplit a a1 a2' *)
        let part_a1_nil = partAllL a1 in
        let part_xa1 = partConsR x a1 a1 [] part_a1_nil in
        let weakened = WFE_WeakenX i g b (x::a1) a1 [x] m e t part_xa1 pf_e in
        let part_xa = partConsL x a a1 a2' part_a in
          (a1, a2', part_xa, weakened)


val weaken_x : x:bvar -> a:acontext -> a1:acontext -> a2:acontext
             -> AContextSplit (x::a) a1 a2
             -> i:icompartment -> g:environment -> b:bindings -> m:mode -> e:expr -> t:typ
             -> expression_ty i g b a1 m e t
             -> (a1':acontext * a2':acontext * AContextSplit (x::a) (x::a1') a2' * expression_ty i g b (x::a1') m e t)
let rec weaken_x x a a1 a2 split_xa i g b m e t pf_e =
  match findPerm' x a1 with
    | Some ((a1', perm_a1)) -> (* perm_a1 : Perm a1 (x::a1') *)
        let x_a1' = (x::a1') in
        let partNil = partAllL x_a1' in (* Part (x::a1') (x::a1') [] *)
        let part = partPerm2 x_a1' x_a1' a1 [] (Perm_Sym a1 x_a1' perm_a1) partNil in
        let pf_e' = WFE_WeakenX i g b x_a1' a1 [] m e t part pf_e in
        let pf_part = partPerm2 (x::a) a1 x_a1' a2 perm_a1 split_xa  in
          (* pf_part: AContextSplit (x::a) (x::a1') a2 *)
          (a1', a2, pf_part, pf_e')

    | _ -> weaken_x_not_in_a1 x a a1 a2 split_xa i g b m e t pf_e

(* ------------------------------ ETyping ---------------------------------------- *)

val etyping_App_Subst :   fix5 okk ktyp tval texpr extenv
                          -> i:icompartment -> g:environment -> b:bindings -> a:acontext -> m:mode
                          -> e1:expr -> q:typ -> a1:acontext -> a2:acontext -> Partition a a1 a2
                          -> expression_ty i g b a1 m e1 q
                          -> x:bvar -> t1:typ -> t2:typ -> pf_strip:StripQual q (T_Prod x t1 t2)
                          -> v2:value -> t1':typ -> a2_1:acontext -> a2_2:acontext -> Partition a2 a2_1 a2_2
                          -> value_ty i g b a2_1 m v2 t1'
                          -> wfEnvB i g b
                          -> (tres:typ * used:acontext * unused:acontext * Partition a used unused *
                                expression_ty i g b used m (E_App e1 v2) tres)
let etyping_App_Subst ff i g b a m e1 q a1 a2 part_a pf_e1 x t1 t2 pf_strip v2 t1' a2_1 a2_2 part_a2 pf_v2' wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    let k, pf_t1 = kinding' ff t1 i g b wfenvb in
      (match subtypingV v2 i g b a2_1 m t1' t1 k pf_v2' pf_t1 with
         | NoneP ->
             (* let _ = println (strcat "Expected argument type: " (tostr t1)) in *)
             (* let _ = println (strcat "Got argument type: " (tostr t1')) in *)
             raise "Function application: argument type does not match type of formal"
         | SomeP pf_v2 ->
             let tres, pf_subst = subst_tv t2 x v2 in
             let a1_a2_1, part_a', part_a1_a2_1 = mergePartition a a1 a2 part_a a2_1 a2_2 part_a2 in
               (tres, a1_a2_1, a2_2, part_a',
                (WFE_App
                   i g b a1_a2_1 a1 a2_1 m
                   e1 v2 x t1 t2 q tres
                   part_a1_a2_1
                   pf_strip
                   pf_subst
                   pf_e1
                   pf_v2)))

 
val etyping_App : fix5 okk ktyp tval texpr extenv
              -> e1:expr -> v2:value
              -> texpr (E_App e1 v2)
let etyping_App ff e1 v2 i g b a m wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    let (q, a1, a2, part_a, pf_e1) = etyping' ff e1 i g b a m wfenvb in
      (match strip_qual q with
         | ((T_Prod x t1 t2), pf_strip) ->
             let (t1', a2_1, a2_2, part_a2, pf_v2') = vtyping' ff v2 i g b a2 m wfenvb in
               etyping_App_Subst ff i g b a m e1 q a1 a2 part_a pf_e1 x t1 t2 pf_strip v2 t1' a2_1 a2_2 part_a2 pf_v2' wfenvb
         | _ -> raise (strcat "Function application expected a (qualified) function type; got " (tostr q)))

    
val etyping_TApp : fix5 okk ktyp tval texpr extenv
                -> e1:expr -> t:typ
                -> texpr (E_TApp e1 t)
let etyping_TApp ff e1 t i g b a m wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    let (q, a1, a2, part_a, pf_e1) = etyping' ff e1 i g b a m wfenvb in
      (match strip_qual q with
         | ((T_ProdK x k t2), pf_strip) ->
             let (k', pf_kinding') = kinding' ff t i g b wfenvb in
             let bk, pf_bk = okkind' ff k i g b wfenvb in
               (match subkinding t i g b k' k bk pf_kinding' pf_bk with
                  | NoneP ->
                      let _ = println (strcat "Expected argument kind: " (tostr k)) in
                      let _ = println (strcat "Got argument kind: " (tostr k')) in
                        raise "Function type-application argument kind does not match kind of formal"
                  | SomeP pf_kinding ->
                      let tres, pf_subst = subst_tt t2 x t in
                        (tres, a1, a2, part_a,
                         (WFE_TApp i g b a1 m x k t e1 q t2 tres
                            pf_strip pf_subst pf_e1 pf_kinding)))
         | _ -> raise (strcat "Type-application expected a (qualified) type-function; got " (tostr q)))


val etyping_LetIn : fix5 okk ktyp tval texpr extenv
                 -> x:bvar -> e1:expr -> e2:expr
                 -> texpr (E_LetIn x e1 e2)
let etyping_LetIn ff x e1 e2 i g b a m wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    let (t1, used1, unused1, part_a, pf_e1) = etyping' ff e1 i g b a m wfenvb in
    let k1, pf_kinding1 = kinding' ff t1 i g b wfenvb in
    let wfenvb' = extenv' ff i g b (LB_BvarTy x t1) wfenvb "ext 3" in
    let (t2, x_used2, x_unused, part_x_unused1, pf_e2) = etyping' ff e2 i g ((LB_BvarTy x t1)::b) (x::unused1) m wfenvb' in
    let used2, unused, part_x_unused1, w_pf_e2 = weaken_x x unused1 x_used2 x_unused part_x_unused1 i g ((LB_BvarTy x t1)::b) m e2 t2 pf_e2 in
    let part_unused1 = partUnconsL x unused1 used2 unused part_x_unused1 in
    let (k2, pf_kinding2) = kinding' ff t2 i g b wfenvb in
      (match k1, k2 with
         | K_Base bt1, K_Base bt2 ->
             match kind_compat_elim bt2 bt1 with
               | NoneP -> raise (strcat "Incompatible cross-universe elimination (let): " (strcat (strcat (tostr bt2) " ^^ ") (tostr bt1)))
               | SomeP kce_pf ->
                   let used, part_a_used_unused, part_used_1_2 = mergePartition a used1 unused1 part_a used2 unused part_unused1 in
                     (t2, used, unused, part_a_used_unused,
                      (WFE_LetIn
                         i g b used used1 used2 m
                         x e1 e2 t1 bt1 t2 bt2
                         part_used_1_2
                         pf_kinding1
                         pf_kinding2
                         kce_pf
                         pf_e1
                         w_pf_e2))
               | _ -> raise "Impos: expected base kinds")


val etyping_Assume : fix5 okk ktyp tval texpr extenv
                  -> phi:typ -> texpr (E_Assume phi)
let etyping_Assume ff phi i g b a m wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    let k, pf_kinding = kinding' ff phi i g b wfenvb in
      (match k with
         | K_Base BK_Erase ->
             let part_a_nil = partAllR a in
             let x = freshname false in
             let tres = (T_Ref x T_Unit phi) in
               (tres, [], a, part_a_nil, WFE_Assume i g b [] m x phi pf_kinding)
         | _ -> raise (strcat "Expected E-kinded formula in dynamic assumption; got " (tostr k)))


val etyping_Match_branches_fin : fix5 okk ktyp tval texpr extenv
                           -> i:icompartment -> g:environment -> b:bindings -> a:acontext -> m:mode
                           -> v:value -> c:cname -> alphas:seq bvar -> xs:seq bvar -> ethen:expr -> eelse:expr
                           -> ts:seq typ -> AsTyps alphas ts
                           -> vs:seq value -> AsVals xs vs
                           -> tc:typ -> ICompBinds_C i c tc
                           -> b':bindings -> Bindings b tc alphas xs b'
                           -> tv:typ -> x1:acontext -> x2sup:acontext -> Partition a x1 x2sup
                           -> value_ty i g b x1 m v tv
                           -> btv:basekind -> wfT i g b tv (K_Base btv)
                           -> tpat:typ -> value_ty i g b' xs m (V_Const c ts vs) tpat
                           -> eqs:bindings -> pt:seq typ -> pv:seq value
                           -> pf_ptm:PatternTypeMatch eqs alphas pt xs pv tpat tv
                           -> bthen:bindings -> Append ((LB_VlEq v (V_Const c ts vs))::eqs) b' bthen
                           -> xthensup:acontext -> xthen':acontext -> xthen_rest:acontext
                           -> Partition xthensup xthen' xthen_rest
                           -> tbranch:typ -> expression_ty i g bthen xthen' m ethen tbranch
                           -> xelse':acontext -> xelse_rest:acontext -> Partition x2sup xelse' xelse_rest
                           -> expression_ty i g b xelse' m eelse tbranch
                           -> wfEnvB i g b
                           -> (t':typ * used:acontext * unused:acontext * Partition a used unused *
                                 expression_ty i g b used m (E_Match v (MkPattern c alphas xs) ethen eelse) t')
let etyping_Match_branches_fin ff i g b a m v c alphas xs ethen eelse ts pf_astyps vs pf_asvals tc pf_icompc
                               b' pf_bindingsb' tv x1 x2sup pf_split_x1_x2sup pf_tv btv pf_tv_kinding
                               tpat pf_tpat eqs pt pv pf_ptm bthen pf_append_bthen xthensup xthen' xthen_rest
                               split_then tbranch pf_typing_then'
                               xelse' xelse_rest split_else pf_typing_else wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    let k_tthen, pf_tthen_kinding = kinding' ff tbranch i g b wfenvb in
      match k_tthen with
        | K_Base bt ->
            (match xthen' with
               | [] ->
                   (match xelse' with
                      | [] ->
                          (match kind_compat_elim bt btv with
                             | NoneP ->
                                 (* raise (strcat "Incompatible cross-universe elimination (match): "  *)
                                 (*          (strcat (strcat (tostr bt) " ^^ ") (tostr btv))) *)
                                 raise "Incompatible cross-universe elimination (match): "
                             | SomeP kce_pf ->
                                 let x1nil, pf_split_a_x1nil_x2sup, pf_split_x1nil_x1_nil =
                                   mergePartition a x1 x2sup pf_split_x1_x2sup [] x2sup (partAllR x2sup) in
                                 let pf_typing_then =
                                   WFE_WeakenX i g bthen xs [] xs m ethen tbranch (partAllR xs) pf_typing_then' in
                                   (tbranch, x1nil, x2sup, pf_split_a_x1nil_x2sup,
                                    (WFE_Match
                                       i g b x1nil x1 [] m eqs b' v pt pv ethen eelse tbranch bt tv btv tpat
                                       c alphas xs tc ts vs bthen xs
                                       pf_astyps pf_asvals pf_icompc pf_bindingsb' pf_split_x1nil_x1_nil
                                       pf_ptm pf_append_bthen (Append_Nil xs)
                                       pf_tv_kinding pf_tthen_kinding kce_pf
                                       pf_tv pf_tpat pf_typing_then pf_typing_else)))
                      | _ -> raise "NYI: non-empty affine contexts")
               | _ -> raise "NYI: non-empty affine contexts")
        | _ -> raise "Impos: non-basekinded branch"

val extendWithEqs: fix5 okk ktyp tval texpr extenv
                 -> i:icompartment -> g:environment -> b:bindings
                 -> eqs:bindings -> wfEnvB i g b
                 -> (b':bindings * Append eqs b b' * wfEnvB i g b')
let rec extendWithEqs ff i g b eqs wfenvb = match eqs with
  | [] -> (b, Append_Nil b, wfenvb)
  | eq::tl ->
      match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv'  ->
        let b', apf, wfenvb' = extendWithEqs ff i g b tl wfenvb in
        let wfenvbout = extenv' ff i g b' eq wfenvb' "ext 4" in
          ((eq::b'), (Append_Cons eq tl b b' apf), wfenvbout)

val etyping_Match_branches : fix5 okk ktyp tval texpr extenv
                           -> i:icompartment -> g:environment -> b:bindings -> a:acontext -> m:mode
                           -> v:value -> c:cname -> alphas:seq bvar -> xs:seq bvar -> ethen:expr -> eelse:expr
                           -> ts:seq typ -> AsTyps alphas ts
                           -> vs:seq value -> AsVals xs vs
                           -> tc:typ -> ICompBinds_C i c tc
                           -> b':bindings -> Bindings b tc alphas xs b'
                           -> tv:typ -> x1:acontext -> x2sup:acontext -> Partition a x1 x2sup
                           -> value_ty i g b x1 m v tv
                           -> btv:basekind -> wfT i g b tv (K_Base btv)
                           -> wfEnvB i g b -> wfEnvB i g b'
                           -> (t':typ * used:acontext * unused:acontext * Partition a used unused *
                                 expression_ty i g b used m (E_Match v (MkPattern c alphas xs) ethen eelse) t')
let etyping_Match_branches ff i g b a m v c alphas xs ethen eelse ts pf_astyps vs pf_asvals tc pf_icompc
                           b' pf_bindingsb' tv x1 x2sup pf_split_x1_x2sup pf_tv btv pf_tv_kinding wfenvb wfenvb' =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv'  ->
    let vpat = (V_Const c ts vs) in
    let (tpat, xs', rest_xs', pf_split_xs_rest_xs', pf_typing_pat') = vtyping' ff vpat i g b' xs m wfenvb' in
    let pf_tpat = WFV_WeakenX i g b' xs xs' rest_xs' m vpat tpat pf_split_xs_rest_xs' pf_typing_pat' in
    let eqs, pt, pv, pf_ptm = mkPatternEqs alphas xs tpat tv in
    let eqs' = (LB_VlEq v vpat)::eqs in
(*     let _ = print_stderr (strcat "Extending environment with equations: " (tostr eqs')) in  *)
    let bthen, pf_append_bthen, wfenvbthen = extendWithEqs ff i g b' eqs' wfenvb' in
    let xthensup, _pf_append_xthensup = append_pf xs x2sup in
    let (tthen, xthen', xthen_rest, split_then, pf_typing_then') = etyping' ff ethen i g bthen xthensup m wfenvbthen in
    let (telse, xelse', xelse_rest, split_else, pf_typing_else) = etyping' ff eelse i g b x2sup m wfenvb in
      if tthen=telse
      then
        etyping_Match_branches_fin
          ff i g b a m v c alphas xs ethen eelse ts pf_astyps vs pf_asvals tc pf_icompc
          b' pf_bindingsb' tv x1 x2sup pf_split_x1_x2sup pf_tv btv pf_tv_kinding
          tpat pf_tpat eqs pt pv pf_ptm bthen pf_append_bthen xthensup xthen' xthen_rest
          split_then tthen pf_typing_then' xelse' xelse_rest split_else pf_typing_else wfenvb
      else (* raise (strcat "Unequal branch typs: " (strcat3 (tostr tthen) " <> " (tostr telse))) *)
        raise "Unequal branch typs: "
          

val etyping_Match : fix5 okk ktyp tval texpr extenv
                  -> v:value -> c:cname -> alphas:seq bvar -> xs:seq bvar -> ethen:expr -> eelse:expr
                  -> texpr (E_Match v (MkPattern c alphas xs) ethen eelse)
let etyping_Match ff v c alphas xs ethen eelse i g b a m wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    let ts, pf_astyps = asTyps alphas in
    let vs, pf_asvals = asVals xs in
      (match lookup_dcon i c with
         | None -> (* raise (strcat "Pattern constructor not found: " (tostr c)) *)
             raise "Pattern constructor not found: "
         | Some ((tc, pf_icompc)) ->
             let b', pf_bindingsb', wfenvb' = mkBindings ff i g b tc alphas xs wfenvb in
             let (tv, x1, x2sup, pf_split_x1_x2sup, pf_tv) = vtyping' ff v i g b a m wfenvb in
             let kv, pf_tv_kinding = kinding' ff tv i g b wfenvb in
               match kv with
                 | K_Base btv ->
                     etyping_Match_branches
                       ff i g b a m v c alphas xs ethen eelse ts pf_astyps vs pf_asvals tc pf_icompc
                       b' pf_bindingsb' tv x1 x2sup pf_split_x1_x2sup pf_tv btv pf_tv_kinding wfenvb wfenvb'
                 | _ -> raise "Impos--E_Match kv<>K_Base")
        

val etyping_Ascribe : fix5 okk ktyp tval texpr extenv
                   -> e':expr -> t:typ
                   -> texpr (E_Ascribe e' t)
let etyping_Ascribe ff e' t i g b a m wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    let (t', used, unused, split, pft) = etyping' ff e' i g b a m wfenvb in
    let k, pfk = kinding' ff t i g b wfenvb in
      (match subtypingE e' i g b used m t' t k pft pfk with
         | SomeP pf' -> (t, used, unused, split, WFE_Ascribe i g b used m e' t pf')
         | _ -> raise "Could not prove subtyping" )

private val etyping' : fix5 okk ktyp tval texpr extenv -> e:expr -> texpr e
let etyping' ff e i g b a m wfenvb =
  (* let _ = debug_println (strcat "etyping' for expression: " (string_of_any e)) in *)
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    match e with
      | E_Value v ->
          let (t, used, unused, pf_part, pf) = vtyping' ff v i g b a m wfenvb in
            (t, used, unused, pf_part, WFE_Val i g b used m v t pf)
            
      | E_App e1 v2 -> etyping_App ff e1 v2 i g b a m wfenvb
              
      | E_TApp e1 t -> etyping_TApp ff e1 t i g b a m wfenvb
          
      | E_LetIn x e1 e2 -> etyping_LetIn ff x e1 e2 i g b a m wfenvb

      | E_Assume phi -> etyping_Assume ff phi i g b a m wfenvb

      | E_Match v (MkPattern c alphas xs) ethen eelse ->
          etyping_Match ff v c alphas xs ethen eelse i g b a m wfenvb
              
      | E_Ascribe e' t -> etyping_Ascribe ff e' t i g b a m wfenvb

      | _ -> raise "Impos 6"

(* ------------------------------ VTyping ---------------------------------------- *)

val vtyping_Var_Term_level_BK_Prop : i:icompartment -> g:environment -> b:bindings -> a:acontext -> m:mode
                                  -> x:bvar -> t:typ -> Mem (LB_BvarTy x t) b
                                  -> wfT i g b t (K_Base BK_Prop)
                                  -> wfEnvB i g b
                                  -> (t':typ * used:acontext * unused:acontext * Partition a used unused *
                                       value_ty i g b used m (V_Var (GV_Bound x)) t')
let vtyping_Var_Term_level_BK_Prop i g b a m x t mem pf_kinding wfenvb =
  match getWFigb i g b wfenvb with
    | MkW wfigb ->
        let part_a_nil = partAllR a in
          (t, [], a, part_a_nil, WFV_VarP i g b m x t wfigb mem pf_kinding)

val vtyping_Var_Term_level_K_Any : i:icompartment -> g:environment -> b:bindings -> a:acontext -> m:mode
                                  -> x:bvar -> t:typ -> Mem (LB_BvarTy x t) b
                                  -> k:kind -> wfT i g b t k
                                  -> wfEnvB i g b
                                  -> (t':typ * used:acontext * unused:acontext * Partition a used unused *
                                        value_ty i g b used m (V_Var (GV_Bound x)) t')
let vtyping_Var_Term_level_K_Any i g b a m x t mem k pf_kinding wfenvb =
  match findPerm x a with
    | None -> raise "Capability for the use of affine assumption is absent: "
    | Some ((a_tl, pf_part)) ->
        match getWFigb i g b wfenvb with
          | MkW wfigb -> (t, [x], a_tl, pf_part, WFV_VarA i g b m x t wfigb mem)
          

val vtyping_Var_Term_level :   fix5 okk ktyp tval texpr extenv
                            -> i:icompartment -> g:environment -> b:bindings -> a:acontext -> m:mode
                            -> x:bvar -> t:typ -> Mem (LB_BvarTy x t) b
                            -> wfEnvB i g b
                            -> (t':typ * used:acontext * unused:acontext * Partition a used unused *
                                  value_ty i g b used m (V_Var (GV_Bound x)) t')
let vtyping_Var_Term_level ff i g b a m x t mem wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    let (k, pf_kinding) = kinding' ff t i g b wfenvb in
      match k with
        | K_Base BK_Comp ->
            (match getWFigb i g b wfenvb with
               | MkW wfigb -> (t, [], a, (partAllR a), WFV_Var i g b m x t wfigb mem pf_kinding))
        | K_Base BK_Prop ->
            vtyping_Var_Term_level_BK_Prop i g b a m x t mem pf_kinding wfenvb
        | _ ->
            vtyping_Var_Term_level_K_Any i g b a m x t mem k pf_kinding wfenvb

val vtyping_Var : fix5 okk ktyp tval texpr extenv
                 -> x:bvar
                 -> tval (V_Var (GV_Bound x))
let vtyping_Var ff x i g b a m wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    match lookup_ty b x with
      | None -> (* raise (strcat "Variable not found: " (tostr x)) *)
          raise "Variable not found: "
      | Some ((t, mem)) ->
          if m=Type_level
          then let part_a_nil = partAllR a in
            match getWFigb i g b wfenvb with
              | MkW wfigb -> (t, [], a, part_a_nil, WFV_VarT i g b x t wfigb mem)
          else vtyping_Var_Term_level ff i g b a m x t mem wfenvb
            
val vtyping_FVar : fix5 okk ktyp tval texpr extenv
                 -> x:bvar
                 -> tval (V_Var (GV_Free x))
let vtyping_FVar ff x i g b a m wfenvb  =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    match lookup_vlname g x with
      | None -> raise (strcat "Variable not found in context: " (tostr x))
          (* (strcat3 "Environment is " (tostr g) *)
          (*    (strcat "Icomp is " (tostr i)))) *)
      | Some ((t, mem)) ->
          let part_a_nil = partAllR a in
            match getWFigb i g b wfenvb with
              | MkW wfigb -> (t, [], a, part_a_nil, WFV_FVar i g b m x t wfigb mem)

val vtyping_Unit : fix5 okk ktyp tval texpr extenv
                  -> tval V_Unit
let vtyping_Unit ff i g b a m wfenvb =
  (T_Unit, [], a, partAllR a, WFV_Unit i g b m)

val vtyping_Const : fix5 okk ktyp tval texpr extenv
                 -> d:cname -> ts:seq typ -> vs:seq value
                 -> tval (V_Const d ts vs)
let vtyping_Const ff d ts vs i g b a m wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    (match lookup_dcon i d with
       | None -> raise (strcat "Data constructor not found: " (tostr d))
       | Some ((td, ibinds)) ->
           let x = freshname false in
           let emon, curry_t = curryt (E_Value (V_Var (GV_Bound x))) ts in
           let e, curry_v = curryv emon vs in
           let wfenvb' = extenv' ff i g b (LB_BvarTy x td) wfenvb "ext 5" in
           let (tres, used, unused, part_a, pf_e) = etyping' ff e i g ((LB_BvarTy x td)::b) a m wfenvb' in
           let k, pf_k = kinding' ff tres i g b wfenvb in
             (tres, used, unused, part_a,
              (WFV_Const i g b used m d ts vs td tres k x emon e curry_t curry_v ibinds pf_k pf_e)))


val vtyping_Fun : fix5 okk ktyp tval texpr extenv
                 -> x:bvar -> t:typ -> e1:expr
                 -> tval (V_Fun x t e1)
let vtyping_Fun ff x t e1 i g b a m wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    let (k, pf_kinding) = kinding' ff t i g b wfenvb in
      (match k with
         | K_Base bk ->
             (match check_concrete_kind bk with
                | NoneP -> raise (strcat "Expect formal parameter to have a concrete kind; got " (tostr bk))
                | SomeP ck_pf ->
                    let wfenvb' = extenv' ff i g b (LB_BvarTy x t) wfenvb "ext 6" in
                    let (t', used_x, unused_x, part_xa, pf_e1) = etyping' ff e1 i g ((LB_BvarTy x t)::b) (x::a) m wfenvb' in
                    let used, unused, part_xa, pf_e1' = weaken_x x a used_x unused_x part_xa i g ((LB_BvarTy x t)::b) m e1 t' pf_e1 in
                    let q, aq = aqual used (T_Prod x t t') in
                    let part_a = partUnconsL x a used unused part_xa in
                      (q, used, unused, part_a, WFV_Fun i g b used m t bk t' x e1 q ck_pf aq pf_kinding pf_e1'))
         | _ -> raise (strcat "Expect formal parameter to have a concrete kind; got " (tostr k)))


val vtyping_FunT : fix5 okk ktyp tval texpr extenv
                 -> x:bvar -> k:kind -> e1:expr
                 -> tval (V_FunT x k e1)
let vtyping_FunT ff x k e1 i g b a m wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    let bk, ok_k = okkind' ff k i g b wfenvb in
    let wfenvb' = extenv' ff i g b (LB_BvarKind x k) wfenvb "ext 7" in
    let t, used, unused, part_a, pf_e1 = etyping' ff e1 i g ((LB_BvarKind x k)::b) a m wfenvb' in
    let q, aq = aqual used (T_ProdK x k t) in
      (q, used, unused, part_a, WFV_FunT i g b used m k bk t x e1 q aq ok_k pf_e1)


val vtyping_Ascribe : fix5 okk ktyp tval texpr extenv
                 -> v':value -> t:typ
                 -> tval (V_Ascribe v' t)
let vtyping_Ascribe ff v' t i g b a m wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    let (t', used, unused, split, pft) = vtyping' ff v' i g b a m wfenvb in
    let k, pfk = kinding' ff t i g b wfenvb in
      (match subtypingV v' i g b used m t' t k pft pfk with
         | SomeP pf' -> (t, used, unused, split, (WFV_Ascribe i g b used m v' t pf'))
         | _ -> raise "Could not prove subtyping" )

private val vtyping' : fix5 okk ktyp tval texpr extenv -> v:value -> tval v
let vtyping' ff v i g b a m wfenvb =
  (* let _ = debug_println (strcat "vtyping' for value: " (string_of_any v)) in *)
  match v with
    | V_Var (GV_Bound x) -> vtyping_Var ff x i g b a m wfenvb
    | V_Var (GV_Free x) -> vtyping_FVar ff x i g b a m wfenvb
    | V_Unit -> vtyping_Unit ff i g b a m wfenvb
    | V_Const d ts vs -> vtyping_Const ff d ts vs i g b a m wfenvb
    | V_Fun x t e1 -> vtyping_Fun ff x t e1 i g b a m wfenvb
    | V_FunT x k e1 -> vtyping_FunT ff x k e1 i g b a m wfenvb
    | V_Ascribe v' t -> vtyping_Ascribe ff v' t i g b a m wfenvb
    | _ -> raise "Value subtyping NYI"

(* ------------------------------ Kinding ---------------------------------------- *)

val kinding_Var : fix5 okk ktyp tval texpr extenv
                -> a:bvar -> ktyp (T_Var (GV_Bound a))
let kinding_Var ff a i g b wfenvb =
  match lookup_kind b a with
    | None -> raise (strcat "Type variable not found: " (tostr a))
    | Some ((k, mem)) ->
        match getWFigb i g b wfenvb with
          | MkW wfigb -> (k, WFT_Var i g b a k wfigb mem)

val kinding_FVar : fix5 okk ktyp tval texpr extenv
                -> a:bvar -> ktyp (T_Var (GV_Free a))
let kinding_FVar ff a i g b wfenvb =
  match lookup_tyname g a with
    | None -> raise (strcat "Free type variable not found: " (tostr a))
    | Some ((k, mem)) ->
        match getWFigb i g b wfenvb with
          | MkW wfigb -> (k, WFT_FVar i g b a k wfigb mem)

val kinding_Unit : fix5 okk ktyp tval texpr extenv
                -> ktyp T_Unit
let kinding_Unit ff i g b wfenvb =
  match getWFigb i g b wfenvb with
    | MkW wfigb -> ((K_Base BK_Comp), WFT_Unit i g b wfigb)

val kinding_Ind : fix5 okk ktyp tval texpr extenv
                -> j:iname -> ktyp (T_Ind j)
let kinding_Ind ff iname i g b wfenvb =
  match lookup_iname i iname with
    | None -> raise (strcat "Type name not found: " (tostr iname))
      | Some ((k, binds)) ->
          match getWFigb i g b wfenvb with
            | MkW wfigb -> (k, WFT_Ind i g b iname k wfigb binds)

val kinding_VApp : fix5 okk ktyp tval texpr extenv
                -> t:typ -> v:value -> ktyp (T_VApp t v)
let kinding_VApp ff t v i g b wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    let tk, pf_t = kinding' ff t i g b wfenvb in
      (match tk with
         | K_ProdT x tv k ->
             let (tv', used, unused, part_nil, pf_v') = vtyping' ff v i g b [] Type_level wfenvb in
               (* generalized GADT-style refinement doesn't work *)
               (* match partitionUnNil used unused part_nil with *)
               (*    | (Refl_eq _, Refl_eq _) -> *)
               (match used, unused with
                  | [], [] ->
                      let tv_bk, pf_tv_bk = kinding' ff tv i g b wfenvb in
                        (match subtypingV v i g b used Type_level tv' tv tv_bk pf_v' pf_tv_bk with
                           | NoneP ->
                               let _ = println (strcat "Expected argument type: " (tostr tv)) in
                               let _ = println (strcat "Got argument type: " (tostr tv')) in
                                 raise "Type-level value application: type of argument does not match the type of formal"
                           | SomeP pf_v ->
                               let kres, pf_subst = subst_kv k x v in
                                 (kres, WFT_VApp i g b t v x tv k kres pf_t pf_v pf_subst)))
         | _ -> raise (strcat "Type value-application: expected a function-kinded type; got " (tostr tk)))


val kinding_TApp : fix5 okk ktyp tval texpr extenv
                -> t1:typ -> t2:typ -> ktyp (T_App t1 t2)
let kinding_TApp ff t1 t2 i g b wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    let t1k, pf_t1 = kinding' ff t1 i g b wfenvb in
      (match t1k with
         | K_ProdK x k1 k2 ->
             let k1', pf_t2' = kinding' ff t2 i g b wfenvb in
             let bk1, pf_bk1 = okkind' ff k1 i g b wfenvb in
               (match subkinding t2 i g b k1' k1 bk1 pf_t2' pf_bk1 with
                  | NoneP ->
                      let _ = println (strcat "Expected argument kind: " (tostr k1)) in
                      let _ = println (strcat "Got argument kind: " (tostr k1')) in
                        raise "Type application: kind of argument does not match the kind of formal"
                  | SomeP pf_t2 ->
                      let kres, pf_subst = subst_kt k2 x t2 in
                        (kres, WFT_App i g b t1 t2 x k1 k2 kres pf_t1 pf_t2 pf_subst))
         | _ -> raise (strcat "Type application: expected a function-kinded type; got " (tostr t1k)))

val kinding_Prod : fix5 okk ktyp tval texpr extenv
                -> x:bvar -> t1:typ -> t2:typ
                -> ktyp (T_Prod x t1 t2)
let kinding_Prod ff x t1 t2 i g b wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    (match kinding' ff t1 i g b wfenvb with
       | (K_Base b1, pf1) ->
           match check_concrete_kind b1 with
             | NoneP -> raise (strcat "Function arrows require concrete-kinded domains; got " (tostr b1))
             | SomeP ck1 ->
                 let wfenvb' = extenv' ff i g b (LB_BvarTy x t1) wfenvb "ext 8" in
                   (match kinding' ff t2 i g ((LB_BvarTy x t1)::b) wfenvb' with
                      | (K_Base b2, pf2) ->
                          match check_concrete_kind b2 with
                            | NoneP -> raise (strcat "Function arrows require concrete-kinded ranges; got " (tostr b2))
                            | SomeP ck2 -> (K_Base b2, WFT_Prod i g b x t1 b1 t2 b2 ck1 ck2 pf1 pf2)))

val kinding_ProdK : fix5 okk ktyp tval texpr extenv
                -> a:bvar -> k1:kind -> t2:typ
                -> ktyp (T_ProdK a k1 t2)
let kinding_ProdK ff a k1 t2 i g b wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    let b1, ok = okkind' ff k1 i g b wfenvb in
    let wfenvb' = extenv' ff i g b (LB_BvarKind a k1) wfenvb "ext 9" in
      (match kinding' ff t2 i g ((LB_BvarKind a k1)::b) wfenvb' with
         | (K_Base b2, pf_2) ->
             (match check_concrete_kind b2 with
                | NoneP -> raise (strcat "Type-function arrows require concrete-kinded ranges; got " (tostr b2))
                | SomeP ck2 ->
                    (K_Base b2, WFT_ProdK i g b a k1 b1 t2 b2 ck2 ok pf_2))
         | _ -> raise (strcat "Type-function arrows require concrete-kinded ranges; got " (tostr b1)))

val kinding_Ref : fix5 okk ktyp tval texpr extenv
                -> x:bvar -> t1:typ -> phi:typ
                -> ktyp (T_Ref x t1 phi)
let kinding_Ref ff x t1 phi i g b wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    let bk1, pf1 = kinding' ff t1 i g b wfenvb in
      (match bk1 with
         | K_Base b1 ->
             (match check_concrete_kind b1 with
                | NoneP -> raise (strcat "Refinement apply only concrete-kinded types; got " (tostr b1))
                | SomeP ck1 ->
                    let wfenvb' = extenv' ff i g b (LB_BvarTy x t1) wfenvb "ext 10" in
                    let bk, pf2' = kinding' ff phi i g ((LB_BvarTy x t1)::b) wfenvb' in
                    let bk_e, pf_bke = okkind' ff (K_Base BK_Erase) i g ((LB_BvarTy x t1)::b) wfenvb' in
                      (match subkinding phi i g ((LB_BvarTy x t1)::b) bk (K_Base BK_Erase) bk_e pf2' pf_bke with
                         | NoneP -> raise (strcat "Refinement formulas must be E-kinded; got " (tostr bk))
                         | SomeP pf2 ->
                             (K_Base b1, WFT_Ref i g b x t1 phi b1 ck1 pf1 pf2)))
         | _ -> raise (strcat "Refinements apply only concrete-kinded types; got " (tostr bk1)))
        
val kinding_Lam : fix5 okk ktyp tval texpr extenv
                -> x:bvar -> t1:typ -> t2:typ
                -> ktyp (T_Lam x t1 t2)
let kinding_Lam ff x t1 t2 i g b wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    let bk1, pf1 = kinding' ff t1 i g b wfenvb in
      (match bk1 with
         | K_Base b1 ->
             (match check_concrete_kind b1 with
                | NoneP -> raise (strcat "Type-lambdas expect only concrete-kinded domains; got " (tostr b1))
                | SomeP ck1 ->
                    let wfenvb' = extenv' ff i g b (LB_BvarTy x t1) wfenvb "ext 11" in
                    let k2, pf2 = kinding' ff t2 i g ((LB_BvarTy x t1)::b) wfenvb' in
                      (K_ProdT x t1 k2, WFT_Lam i g b x t1 b1 t2 k2 ck1 pf1 pf2))
         | _ -> raise (strcat "Type-lambdas expect only concrete-kinded domains; got " (tostr bk1)))

val kinding_Afn : fix5 okk ktyp tval texpr extenv
                -> t1:typ
                -> ktyp (T_Afn t1)
let kinding_Afn ff t1 i g b wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    (match kinding' ff t1 i g b wfenvb with
       | (K_Base BK_Comp, pf1) -> (K_Base BK_Afn, WFT_Afn i g b t1 pf1)
       | (k, _) -> raise (strcat "Affine qualifier only applies to *-kinded types; got " (tostr k)))


val kinding_Ascribe : fix5 okk ktyp tval texpr extenv
                   -> t':typ -> k:kind
                   -> ktyp (T_Ascribe t' k)
let kinding_Ascribe ff t' k i g b wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    let (k', pf) = kinding' ff t' i g b wfenvb in
    let bk, pf_ok = okkind' ff k i g b wfenvb in
      (match subkinding t' i g b k' k bk pf pf_ok with
         | SomeP pf' -> (k, (WFT_Ascribe i g b t' k pf'))
         | _ -> raise "Could not prove subkinding")

private val kinding' : fix5 okk ktyp tval texpr extenv -> t:typ -> ktyp t
let kinding' ff t i g b wfenvb =
  (* let _ = debug_println (strcat "kinding' for type: " (string_of_any t)) in *)
  match t with
    | T_Var (GV_Bound a) -> kinding_Var ff a i g b wfenvb
    | T_Var (GV_Free a) -> kinding_FVar ff a i g b wfenvb
    | T_Unit -> kinding_Unit ff i g b wfenvb
    | T_Ind iname -> kinding_Ind ff iname i g b wfenvb
    | T_VApp t v -> kinding_VApp ff t v i g b wfenvb
    | T_App t1 t2 -> kinding_TApp ff t1 t2 i g b wfenvb
    | T_Prod x t1 t2 -> kinding_Prod ff x t1 t2 i g b wfenvb
    | T_ProdK a k1 t2 -> kinding_ProdK ff a k1 t2 i g b wfenvb
    | T_Ref x t1 phi -> kinding_Ref ff x t1 phi i g b wfenvb
    | T_Lam x t1 t2 -> kinding_Lam ff x t1 t2 i g b wfenvb
    | T_Afn t1 -> kinding_Afn ff t1 i g b wfenvb
    | T_Ascribe t' k -> kinding_Ascribe ff t' k i g b wfenvb
    | _ -> raise "Impos 8"


(* ------------------------------ Okkind ---------------------------------------- *)

val okkind_Base : fix5 okk ktyp tval texpr extenv
                -> kb:basekind -> okk (K_Base kb)
let okkind_Base ff kb i g b wfenvb =
  match getWFigb i g b wfenvb with
    | MkW wfigb -> (kb, WFK_Base i g b kb wfigb)

val okkind_ProdK : fix5 okk ktyp tval texpr extenv
                -> a:bvar -> k1:kind -> k2:kind
                -> okk (K_ProdK a k1 k2)
let okkind_ProdK ff a k1 k2 i g b wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    let b1, ok1 = okkind' ff k1 i g b wfenvb in
    let wfenvb' = extenv' ff i g b (LB_BvarKind a k1) wfenvb "ext 12" in
    let b2, ok2 = okkind' ff k2 i g ((LB_BvarKind a k1)::b) wfenvb' in
      (match kind_compat b1 b2 with
         | SomeP kc -> (b2, WFK_ProdK i g b a k1 b1 k2 b2 kc ok1 ok2)
         | NoneP -> raise (strcat "Incompatible domain/range kinds: " (strcat3 (tostr b1) " ^^ " (tostr b2))))

val okkind_ProdT : fix5 okk ktyp tval texpr extenv
                -> x:bvar -> t:typ -> k2:kind
                -> okk (K_ProdT x t k2)
let okkind_ProdT ff x t k2 i g b wfenvb =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extenv' ->
    (match kinding' ff t i g b wfenvb with
       | (K_Base tb, pf1) ->
           let wfenvb' = extenv' ff i g b (LB_BvarTy x t) wfenvb "ext 13" in
           let b2, ok2 = okkind' ff k2 i g ((LB_BvarTy x t)::b) wfenvb' in
             (match vindex_kind_compat tb b2 with
                | SomeP vkc ->(b2, WFK_ProdT i g b x t tb k2 b2 vkc pf1 ok2)
                | NoneP -> raise (strcat "Incompatible domain/range kinds: " (strcat3 (tostr tb) " ^^ " (tostr b2))))
       | (k, _) -> raise (strcat "Non-base-kinded type domain in kind-level arrow: " (tostr k)))
      
private val okkind' : fix5 okk ktyp tval texpr extenv -> k:kind -> okk k
let okkind' ff k i g b wfenvb =
  match k with
    | K_Base kb -> okkind_Base ff kb i g b wfenvb
    | K_ProdK a k1 k2 -> okkind_ProdK ff a k1 k2 i g b wfenvb
    | K_ProdT x t k2 -> okkind_ProdT ff x t k2 i g b wfenvb

(**********************************************************************************)
(* Well-formedness checks for the local bindings *)
(**********************************************************************************)
val bindingBvars: b:bindings -> (xs:seq bvar * BindingBvars b xs)
let rec bindingBvars bindings = match bindings with
  | [] -> [], BB_Nil
  | (LB_BvarTy x t)::tl ->
      let xs, pfxs = bindingBvars tl in
        (x::xs), BB_BVT tl x t xs pfxs
  | (LB_BvarKind a k)::tl ->
      let xs, pfxs = bindingBvars tl in
        (a::xs), BB_BTK tl a k xs pfxs
  | (LB_VlEq v1 v2)::tl ->
      let xs, pfxs = bindingBvars tl in
        xs, BB_VlEq tl v1 v2 xs pfxs
  | (LB_TyEq t1 t2)::tl ->
      let xs, pfxs = bindingBvars tl in
        xs, BB_TyEq tl t1 t2 xs pfxs

val raiseExtendEnv : i:icompartment -> g:environment -> b:bindings -> lb:locbinding -> string -> wfEnvB i g (lb::b)
let raiseExtendEnv i g b lb msg = raise (strcat "ExtendEnv failed: " msg)

val trykconv: fix5 okk ktyp tval texpr extenv
             -> i:icompartment -> g:environment -> b:bindings
             -> wfEnvB i g b
             -> t1:typ -> k1:kind -> wfT i g b t1 k1
             -> t2:typ -> k2:kind -> wfT i g b t2 k2
             -> option (k1':kind * wfT i g b t1 k1' *
                          k2':kind * wfT i g b t2 k2' *
                          kind_equiv i g b [] k1' k2')
let trykconv ff i g b wfenvb t1 k1 pf1 t2 k2 pf2 =
  match ff with MkFix5 okkind' kinding' vtyping' etyping' extendEnv' ->
    match kequiv i g b [] k1 k2 with
      | SomeP pf -> Some (k1, pf1, k2, pf2, pf)
      | NoneP ->
          match kconv i g b k1 k2 with
            | NoneP -> None
            | SomeP pfsub ->
                let (bk, pfok) = okkind' ff k2 i g b wfenvb in
                  Some (k2, (WFT_Sub i g b t1 k1 k2 bk pf1 pfsub pfok), k2, pf2, KE_Refl i g b [] k2)
  
val extendEnvWeakTerm : fix5 okk ktyp tval texpr extenv
                            -> i:icompartment -> g:environment -> b:bindings
                            -> x:bvar -> t:typ -> wfEnvB i g b -> string
                            -> wfEnvB i g ((LB_BvarTy x t)::b)
let extendEnvWeakTerm ff i g b x t wfenvb msg =
  match wfenvb with
    | Some ((xs, pfxs, wfigb)) ->
        match ff with MkFix5 okkind' kinding' vtyping' etyping' extendEnv' ->
          (match kinding' ff t i g b wfenvb, decideMem x xs with
             | ((K_Base bk), wft), (InrStar nm) ->
                 (match check_concrete_kind bk with
                    | SomeP ck ->
                        let wfigb' = WF_WeakTerm i g b x t bk xs pfxs nm ck wft wfigb in
                        let pfxs' = BB_BVT b x t xs pfxs in
                          Some((x::xs), pfxs', wfigb')
                    | NoneP -> raiseExtendEnv i g b (LB_BvarTy x t)  (strcat3 msg "extenv failed1: Non-concrete term var: " (strcat3 (tostr t) " :: " (tostr bk))))
             | _ -> raiseExtendEnv i g b (LB_BvarTy x t) (strcat3 msg "extenv failed2: Ill-kinded type or duplicate name: " (strcat3 (tostr t) " or " (tostr (x::xs)))))
      
        
val extendEnvWeakTy : fix5 okk ktyp tval texpr extenv
                            -> i:icompartment -> g:environment -> b:bindings
                            -> a:bvar -> k:kind -> wfEnvB i g b -> string
                            -> wfEnvB i g ((LB_BvarKind a k)::b)
let extendEnvWeakTy ff i g b a k wfenvb msg =
  match wfenvb with
    | Some ((xs, pfxs, wfigb)) ->
        match ff with MkFix5 okkind' kinding' vtyping' etyping' extendEnv' ->
          (match okkind' ff k i g b wfenvb, decideMem a xs with
             | (bk, wfk), InrStar nm ->
                 let wfigb' = WF_WeakType i g b a k bk xs pfxs nm wfk wfigb in
                 let pfxs' = BB_BTK b a k xs pfxs in
                   Some((a::xs), pfxs', wfigb')
             | _ -> raiseExtendEnv i g b (LB_BvarKind a k) (strcat3 msg "extenv failed3: Ill-formed kind or duplicate name: " (strcat3 (tostr k) " or " (tostr (a::xs)))))

val extendEnvVlEq : fix5 okk ktyp tval texpr extenv
                            -> i:icompartment -> g:environment -> b:bindings
                            -> v1:value -> v2:value -> wfEnvB i g b -> string
                            -> wfEnvB i g ((LB_VlEq v1 v2)::b)
let extendEnvVlEq ff i g b v1 v2 wfenvb msg =
  match wfenvb with
    | Some((xs, pfxs, wfigb)) ->
        match ff with MkFix5 okkind' kinding' vtyping' etyping' extendEnv' ->
          (match (vtyping' ff v1 i g b [] Type_level wfenvb,
                  vtyping' ff v2 i g b [] Type_level wfenvb) with
             | (t1, [], _, _, pf1), (t2, [], _, _, pf2) ->
                 (match tequiv i g b [] t1 t2 with
                    | NoneP ->
                        raiseExtendEnv i g b (LB_VlEq v1 v2) (strcat msg
                                                                (strcat3
                                                                   "extenv failed4--value typing, unequal types : "
                                                                   (strcat3 (tostr t1) " <> " (tostr t2))
                                                                   (strcat "   In context: " (tostr b))))
                    | SomeP teq ->
                        let wfigb' = WF_WeakVlEq i g b v1 v2 t1 t2 wfigb pf1 pf2 teq in
                        let pfxs' = BB_VlEq b v1 v2 xs pfxs in
                          Some(xs, pfxs', wfigb'))
             | _ -> raiseExtendEnv i g b (LB_VlEq v1 v2) (strcat3 msg
                                                            "extenv failed5--untypeable value equalities "
                                                            (strcat3 (tostr v1) " or " (tostr v2))))
            

val extendEnvTyEq : fix5 okk ktyp tval texpr extenv
                   -> i:icompartment -> g:environment -> b:bindings
                   -> t1:typ -> t2:typ -> wfEnvB i g b -> string
                   -> wfEnvB i g ((LB_TyEq t1 t2)::b)
let extendEnvTyEq ff i g b t1 t2 wfenvb msg =
  match wfenvb with
    | Some((xs, pfxs, wfigb)) ->
        match ff with MkFix5 okkind' kinding' vtyping' etyping' extendEnv' ->
          (match (kinding' ff t1 i g b wfenvb,
                  kinding' ff t2 i g b wfenvb) with
             | (k1, pf1), (k2, pf2) ->
                 (match trykconv ff i g b wfenvb t2 k2 pf2 t1 k1 pf1 with
                    | None ->
                        (match trykconv ff i g b wfenvb t1 k1 pf1 t2 k2 pf2 with
                           | None ->
                               raiseExtendEnv i g b (LB_TyEq t1 t2) (strcat msg
                                                                       (strcat3
                                                                          "extenv failed6--unequal kinds : "
                                                                          (strcat3 (strcat3 (tostr t1) "::" (tostr k1)) " <> "
                                                                             (strcat3 (tostr t2) "::" (tostr k2)))
                                                                          (strcat "   In context: " (tostr b))))
                           | Some ((k1, pf1, k2, pf2, keq)) ->
                               let wfigb' = WF_WeakTyEq i g b t1 t2 k1 k2 wfigb pf1 pf2 keq in
                               let pfxs = BB_TyEq b t1 t2 xs pfxs in
                                 Some(xs, pfxs, wfigb'))
                    | Some ((k2, pf2, k1, pf1, keq)) ->
                        let wfigb' = WF_WeakTyEq i g b t1 t2 k1 k2 wfigb pf1 pf2 (KE_Sym i g b [] k1 k2 keq) in
                        let pfxs = BB_TyEq b t1 t2 xs pfxs in
                          Some(xs, pfxs, wfigb'))
             | _ -> raiseExtendEnv i g b (LB_TyEq t1 t2) (strcat3 msg
                                                            "extenv failed7--unkinded type equalities "
                                                            (strcat3 (tostr t1) " or " (tostr t2))))
        

private val extendEnv' : fix5 okk ktyp tval texpr extenv -> i:icompartment -> extenv i
let extendEnv' ff i g b binding wfenvb msg =
  match binding with
    | LB_BvarTy x t -> extendEnvWeakTerm ff i g b x t wfenvb msg
    | LB_BvarKind a k -> extendEnvWeakTy ff i g b a k wfenvb msg
    | LB_VlEq v1 v2 -> extendEnvVlEq ff i g b v1 v2 wfenvb msg
    | LB_TyEq t1 t2 -> extendEnvTyEq ff i g b t1 t2 wfenvb msg
    | _ -> raise "unmatched"
              
val extendEnv: i:icompartment -> extenv i
let extendEnv i g b lb wfenvb msg =
  extendEnv' (MkFix5 okkind' kinding' vtyping' etyping' extendEnv') i g b lb wfenvb msg

val etyping : e:expr -> texpr e
let etyping e i g b a m wfenvb =
  etyping' (MkFix5 okkind' kinding' vtyping' etyping' extendEnv') e i g b a m wfenvb

val okkind : k:kind -> okk k
let okkind k i g b wfenvb =
  okkind' (MkFix5 okkind' kinding' vtyping' etyping' extendEnv') k i g b wfenvb

val kinding: t:typ -> ktyp t
let kinding k i g b wfenvb =
  kinding' (MkFix5 okkind' kinding' vtyping' etyping' extendEnv') k i g b wfenvb

(**********************************************************************************)
(* Well-formedness checks on the static environment *)
(**********************************************************************************)

val check_wfIKinds : I:icompartment -> wfIG I []  -> iks:seq ikind -> option basekind -> (b:basekind * wfIKinds I iks b)
let rec check_wfIKinds i wfig iks bopt = match iks, bopt with
  | [], Some b -> (b, WFIK_Nil i b)

  | ((MkIKind iname k)::iks'), _ ->
      match okkind k i [] [] (Some ([], BB_Nil, WF_Nil i [] wfig)) with
        | (b, wfk) ->
            let (b', pftl) = check_wfIKinds i wfig iks' (Some b) in
              if b=b'
              then (b, WFIK_Cons i iname k iks' b wfk pftl)
              else raise (strcat "Failed consistent kinds check: " (strcat3 (strcat3 (tostr b) " :: " (tostr b')) " in " (tostr iks)))
                      
val check_constrAfn : i:icompartment
                    -> iks:seq ikind
                    -> b:bindings
                    -> t:typ
                    -> bk:basekind
                    -> wfEnvB i [] b
                    -> W (constrAfn iks i b t bk)
let rec check_constrAfn i iks b t bk wfenvb = match t with
  | T_Prod x t1 u ->
      (match kinding t1 i [] b wfenvb with
         | (K_Base bt1), wft1 ->
             let wfenvb' = extendEnv i [] b (LB_BvarTy x t1) wfenvb "ext 14" in
               (match check_constrAfn i iks ((LB_BvarTy x t1)::b) u bk wfenvb' with
                  | MkW ca_u ->
                      match decideAffineCheck bt1 bk with
                        | SomeP achk -> MkW (CA_Prod iks i b x t1 bt1 u bk wft1 ca_u achk)
                        | _ -> raise (strcat "Failed affine check: " (tostr t)))
         | _ -> raise (strcat "Failed constr kinding: " (tostr t)))
        
  | T_ProdK a k1 u ->
      (match okkind k1 i [] b wfenvb with
         | bk1, wfk ->
             let wfenvb' = extendEnv i [] b (LB_BvarKind a k1) wfenvb "ext 15" in
               (match check_constrAfn i iks ((LB_BvarKind a k1)::b) u bk wfenvb' with
                  | MkW ca_u ->
                      match decideAffineCheck bk1 bk with
                        | SomeP achk -> MkW (CA_ProdK iks i b a k1 bk1 u bk wfk ca_u achk)
                        | _ -> raise (strcat "Failed affine check: " (tostr t)))
         | _ -> raise (strcat "Failed constr kinding: " (tostr t)))

  | _ ->
      (match decideBaseType t with
         | None -> raise (strcat "Constructor builds non-base type: " (tostr t))
         | Some((iname, basetype)) ->
             match find<ikind, (fun (i:ikind) => TT)> (function (MkIKind iname' _) when iname=iname' -> SomeP True | _ -> NoneP) iks with
               | Some (((MkIKind iname' k), _, mem)) when iname=iname' ->
                   (match kinding t i [] b wfenvb with
                      | (K_Base bk'), wft when bk=bk' -> MkW (CA_Base iks i b t bk iname k mem basetype wft )
                      | _ -> raise (strcat "Constructor builds type of unexpected kind  " (strcat3 (tostr t) " !:: " (tostr bk))))
               | _ -> raise (strcat "Constructor builds unexpected inductive:  " (strcat3 (tostr t) " <> " (tostr iname))))
        

val check_wfConstrs : i:icompartment
                     -> wfIG i []
                     -> iks:seq ikind
                     -> ds:seq constructor -> b:basekind
                     -> W (wfConstrs i iks ds b)
let rec check_wfConstrs i wfig iks ds b = match ds with
  | [] -> MkW (WFC_Nil i iks b)
  | hd::tl -> match hd with
      | MkConstructor c t ->
(*           print_stderr (strcat3 "Checking wfconstrs for constructor "  (tostr c) (strcat " at type " (tostr t))); *)
          (match kinding t i [] [] (Some ([], BB_Nil, WF_Nil i [] wfig)) with
             | (K_Base b', wft) when b=b' ->
(*                  print_stderr (strcat (tostr c) " is well-kinded");  *)
                 (match check_constrAfn i iks [] t b (Some ([], BB_Nil, WF_Nil i [] wfig)),  check_concrete_kind b with
                    | MkW cafn, SomeP ck ->
                        (match check_wfConstrs i wfig iks tl b with
                           | MkW wftl -> MkW (WFC_Cons i iks c t tl b ck wft cafn wftl))
                    | _ -> raise (strcat "Failed concrete kind check: " (strcat3 (tostr hd) " :: " (tostr b)))))
            
val extendDistinctInames: itl:icompartment
                       -> ditl:DistinctINames itl
                       -> i:inductive
                       -> W (DistinctINames (i::itl))
let extendDistinctInames itl ditl i = match ditl, i with
  | (DI_Names _ iks_tl iks_flat_tl inames_tl zip1_tl flat_tl zip2_tl di_tl), (MkIndType iks ds) ->
      let iks_l = iks::iks_tl in
      let iks_flat, apf = append_pf iks iks_flat_tl in
      let zip1 = (Zip_Cons<inductive, (seq ikind), exists_ds> itl iks_tl i iks zip1_tl
                    (MkEx9 i iks ds (Refl_eq i))) in
      let flat = Flatten_Cons iks iks_tl iks_flat_tl iks_flat flat_tl apf in
        match extendZip iks_flat_tl inames_tl zip2_tl iks_flat mk_exk with
          | None -> raise (strcat "extendZip failed for inames: " (tostr i) )
          | Some((_, inames, _, zip2)) ->
              match checkDistinctCache inames_tl di_tl inames with
                | NoneP -> raise (strcat "extendDistinctCache failed for inames: " (tostr i))
                | SomeP di -> MkW (DI_Names (i::itl) iks_l iks_flat inames zip1 flat zip2 di)
  

val extendDistinctConstrs: itl:icompartment
                        -> dctl:DistinctConstrs itl
                        -> i:inductive
                        -> W (DistinctConstrs (i::itl))
let extendDistinctConstrs itl dctl i = match dctl, i with
  | (DC_Names _ c_tl cflat_tl cnames_tl zip1_tl flat_tl zip2_tl dc_tl), (MkIndType iks ds) ->
      let c_l = ds::c_tl in
      let cflat, apf = append_pf ds cflat_tl in
      let zip1 = Zip_Cons<inductive, (seq constructor), exists_ik> itl c_tl i ds zip1_tl
        (MkEx10 i ds iks (Refl_eq i)) in
      let flat = Flatten_Cons ds c_tl cflat_tl cflat flat_tl apf in
        match extendZip cflat_tl cnames_tl zip2_tl cflat mk_exct with
          | None ->  raise (strcat "extendZip failed for constrs: " (tostr i))
          | Some((_, cnames, _, zip2)) ->
              match checkDistinctCache cnames_tl dc_tl cnames with
                | NoneP -> raise (strcat "extendDistinctCache failed for constrs: " (tostr i))
                | SomeP dc -> MkW (DC_Names (i::itl) c_l cflat cnames zip1 flat zip2 dc)
                      
val checkWFI : I:icompartment -> (x1:wfI I * x2:DistinctINames I * DistinctConstrs I)
let rec checkWFI i = match i with
  | [] -> (WFI_Nil,
           (DI_Names [] [] [] [] (Zip_Nil<inductive, (seq ikind), exists_ds>) Flatten_Nil (Zip_Nil<ikind, iname, exists_k>) Distinct_nil),
           (DC_Names [] [] [] [] (Zip_Nil<inductive, (seq constructor), exists_ik>) Flatten_Nil (Zip_Nil<constructor, cname, exists_ct>) Distinct_nil))
  | hd::tl ->
      match hd with
        | MkIndType iks ds ->
            let (wf_tl, ditl, dctl) = checkWFI tl in
            let diopt = extendDistinctInames tl ditl hd in
            let dcopt = extendDistinctConstrs tl dctl hd in
            let b, wf_iks = check_wfIKinds tl (WFIG_Nil tl wf_tl) iks None in
              match diopt, dcopt with
                | (MkW di), (MkW dc) ->
                    let stub = (MkIndType iks []) in
                    let stub_tl = stub::tl in
                      match extendDistinctInames tl ditl stub, extendDistinctConstrs tl dctl stub with
                        | (MkW di'), (MkW dc') ->
                            let wf_stub_tl = WFI_Cons tl iks [] b wf_iks (WFC_Nil stub_tl iks b) di' dc' wf_tl in
                              (match check_wfConstrs stub_tl (WFIG_Nil stub_tl wf_stub_tl) iks ds b with
                                 | MkW wf_constrs ->
                                     let pf = WFI_Cons tl iks ds b wf_iks wf_constrs di dc wf_tl in
                                       (pf, di, dc))

val extendWFIG : I:icompartment
            -> G:environment
            -> b:fvbinding
            -> vls:seq vlname
            -> tys:seq tyname
            -> VlNames G vls
            -> TyNames G tys
            -> wfIG I G
            -> (wfig:wfIG I (b::G) *
                vls':seq vlname *
                tys':seq tyname *
                VlNames (b::G) vls' *
                TyNames (b::G) tys')
let extendWFIG i g b vls tys vlnames tynames wfig =
  match b with
    | (FV_VlName v t) ->
        (match kinding t i g [] (Some ([], BB_Nil, WF_Nil i g wfig)) with
           | ((K_Base bk), wft) ->
               (match check_concrete_kind bk, decideMem v vls with
                  | SomeP ck, InrStar nm ->
                      let wfigb = WFIG_ConsV i v t g bk vls vlnames wft ck nm wfig in
                      let vls', vlnames = (v::vls), VLN_ConsV g v t vls vlnames in
                      let tynames = TYN_ConsV g v t tys tynames in
                        (wfigb, vls', tys, vlnames, tynames)
                  | _ -> raise "wfg: fail1")
           | _ -> raise "wfg: fail2")
  | (FV_TyName a k) ->
      match okkind k i g [] (Some ([], BB_Nil, WF_Nil i g wfig)) with
        | (bk, wfk) ->
            (match decideMem a tys with
               | InrStar nm ->
                   let wfigb = WFIG_ConsT i a k g bk tys tynames wfk nm wfig in
                   let vlnames = VLN_ConsT g a k vls vlnames in
                   let tys', tynames = (a::tys), TYN_ConsT g a k tys tynames in
                     (wfigb, vls, tys', vlnames, tynames)
               | _ -> raise "wfg: fail 3")
        | _ -> raise "wfg: fail 4"

(* val extendEnvironment: I:icompartment -> G:environment -> wfIG I G -> G':environment -> (GG':environment * wfIG I GG') *)
(* let extendEnvironment i g wfig g' =  *)
(*   let gg', _ = append_pf g' g in  *)
(*     match checkWFIG i gg' with  *)
(*       | MkW pf -> (gg', pf) *)

val extendEnvironment: I:icompartment
            -> G:environment
            -> G':environment
            -> vls:seq vlname
            -> tys:seq tyname
            -> VlNames G vls
            -> TyNames G tys
            -> wfIG I G
            -> (GG':environment *
                  wfIG I GG')
let rec extendEnvironment i g g' vls tys vlnames tynames wfig = match g' with
  | [] -> (g, wfig)
  | hd::tl ->
      let wfig', vls', tys', vlnames', tynames' = extendWFIG i g hd vls tys vlnames tynames wfig in
        extendEnvironment i (hd::g) tl vls' tys' vlnames' tynames' wfig'

val checkWFG : I:icompartment -> wfI I -> G:environment -> (x1:wfIG I G * vls:seq vlname * tys:seq tyname * VlNames G vls * TyNames G tys)
let rec checkWFG i wfi g = match g with
  | [] -> (WFIG_Nil i wfi, [], [], VLN_Nil, TYN_Nil)
  | hd::tl ->
      let (wfitl, vls, tys, vlnames, tynames) = checkWFG i wfi tl in
        extendWFIG i tl hd vls tys vlnames tynames wfitl

(* val checkWFG : I:icompartment -> wfI I -> G:environment -> (x1:wfIG I G * vls:seq vlname * tys:seq tyname * VlNames G vls * TyNames G tys) *)
(* let rec checkWFG i wfi g = match g with *)
(*   | [] -> (WFIG_Nil i wfi, [], [], VLN_Nil, TYN_Nil) *)
(*   | (FV_VlName v t)::tl -> *)
(*       let wftl, vls, tys, vlnames, tynames = checkWFG i wfi tl in *)
(*         (match kinding t i tl [] (Some ([], BB_Nil, WF_Nil i tl wftl)) with *)
(*            | ((K_Base bk), wft) ->  *)
(*                (match check_concrete_kind bk, decideMem v vls with  *)
(*                   | Some ck, InrStar nm ->  *)
(*                       let wf = WFIG_ConsV i v t tl bk vls vlnames wft ck nm wftl in  *)
(*                       let vls', vlnames = (v::vls), VLN_ConsV tl v t vls vlnames in *)
(*                       let tynames = TYN_ConsV tl v t tys tynames in *)
(*                         (wf, vls', tys, vlnames, tynames) *)
(*                   | _ -> raise "wfg: fail1") *)
(*            | _ -> raise "wfg: fail2") *)
(*   | (FV_TyName a k)::tl -> *)
(*       let (wftl, vls, tys, vlnames, tynames) = checkWFG i wfi tl in  *)
(*         match okkind k i tl [] (Some ([], BB_Nil, WF_Nil i tl wftl)) with  *)
(*           | (bk, wfk) ->  *)
(*               (match decideMem a tys with  *)
(*                  | InrStar nm ->  *)
(*                      let wf = WFIG_ConsT i a k tl bk tys tynames wfk nm wftl in  *)
(*                      let vlnames = VLN_ConsT tl a k vls vlnames in *)
(*                      let tys', tynames = (a::tys), TYN_ConsT tl a k tys tynames in *)
(*                        (wf, vls, tys', vlnames, tynames) *)
(*                  | _ -> raise "wfg: fail 3") *)
(*           | _ -> raise "wfg: fail 4" *)

val checkWFIG: I:icompartment -> G:environment -> (x:wfIG I G * vls:seq vlname * tys:seq tyname * VlNames G vls * TyNames G tys)
let checkWFIG i g =
  let (wfi, _, _) = checkWFI i in
    checkWFG i wfi g
        
val checkWFEnv : I:icompartment -> G:environment -> wfIG I G -> b:bindings -> wfEnvB I G b
let rec checkWFEnv i g wfig b = match b with
  | [] -> Some ([], BB_Nil, WF_Nil i g wfig)
  | hd::tl ->
      let wfenvtl = checkWFEnv i g wfig tl in
        extendEnv i g tl hd wfenvtl "ext 16"

val check_expr : i:icompartment -> g:environment -> wfIG i g -> b:bindings -> A:acontext -> m:mode -> e:expr
              -> (t:typ * A1:acontext * A2:acontext * AContextSplit A A1 A2 * expression_ty i g b A1 m e t)
let check_expr i g wfig b a m e =
  let wfenvb = checkWFEnv i g wfig b in
    etyping e i g b a m wfenvb

end
