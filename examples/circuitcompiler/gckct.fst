(*--build-config
options:--admit_fsi FStar.Set;
other-files:FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.List.fst fixnat.fst mylist.fst
--*)
module Bool_circuit
open MyList
open Fixnat

(* BINARY REPRESENTATION *)

(* Binary representations of natural numbers, as lists of booleans *)

(* TODO: None of this is tail recursive; might want to fix that *)

val b2i: bool -> Tot nat
let b2i b = if b then 1 else 0

val i2b: n:nat{n<=1} -> Tot bool
let i2b n = if n = 0 then false else true

(* assumes MSB is first *)
val bintonat: n:nat -> nlist bool n -> Tot (fixnat n)
let rec bintonat (nb:nat) bl =
  match bl with
  | [] -> 0
  | hd::tl ->
     let x = b2i hd in
     x*(exp2 (nb-1)) + (bintonat (nb-1) tl)

val nattobin_helper: #nb:nat{nb > 0} -> n:(fixnat nb) -> Tot (nlist bool (log2 #nb n))
let rec nattobin_helper #nb n =
 if n <= 1 then [i2b n]
 else
   let res = nattobin_helper #(nb-1) (n / 2) in
   let digit = i2b (n % 2) in
   digit::res

val bton_snoc: nl:nat -> l:(nlist bool nl) -> b:bool ->
     Lemma (requires True)
           (ensures (bintonat (nl+1) (snoc #_ #nl l b)) ==
                     ((bintonat nl l)*2 + (b2i b))) (decreases l)
let rec bton_snoc nl l b =
 match l with
 | [] -> ()
 | hd::tl ->
   let _ = assert ((snoc #_ #nl (hd::tl) b) == hd::(snoc #_ #(nl-1) tl b)) in
   let _ = assert ((bintonat (nl+1) (hd::(snoc #_ #(nl-1) tl b))) ==
                     ((b2i hd)*(exp2 nl) + (bintonat #nl (snoc #_ #(nl-1) tl b)))) in
   let _ = bton_snoc (nl-1) tl b in
   let _ = assert (((b2i hd)*(exp2 nl) + (bintonat (nl-1) tl)*2 + (b2i b)) ==
                   ((b2i hd)*(exp2 (nl-1))*2 + (bintonat (nl-1) tl)*2 + (b2i b))) in
                   (* TODO: Doesn't verify the following, but should *)
                   (*
   let _ = assert (((b2i hd)*(exp2 (nl-1))*2 + (bintonat (nl-1) tl)*2 + (b2i b)) ==
                   (((b2i hd)*(exp2 (nl-1)) + (bintonat (nl-1) tl))*2 + (b2i b))) in
                   *)
                   admit()
(*
   let _ = assert ((((b2i hd)*(exp2 (nl-1)) + (bintonat (nl-1) tl))*2 + (b2i b)) ==
                   (bintonat nl l)*2 + (b2i b)) (* QED *)
*)

(* Lemma: bton and ntob are inverses *)
val correct_ntob_helper: nb:nat{nb > 0} -> n:(fixnat nb) ->
     Lemma (requires True)
           (ensures (bintonat (log2 #nb n) (MyList.revT #_ #(log2 #nb n) (nattobin_helper #nb n))) == n) (decreases n)
let rec correct_ntob_helper nb n =
 if n <= 1 then ()
 else
   let _ = correct_ntob_helper (nb-1) (n/2) in
   let nl = log2 #nb n in
   let _ = rev_snoc (nl-1) (nattobin_helper #(nb-1) (n/2)) (i2b (n%2)) in
   bton_snoc (nl-1) (MyList.revT #_ #(nl-1) (nattobin_helper #(nb-1) (n/2))) (i2b (n%2))

val pad: #nl:nat -> nb:nat -> (l:(nlist bool nl){nl <= nb}) -> Tot (nlist bool nb) (decreases (nb - nl))
let rec pad #nl nb l =
 if nl = nb then l
 else
   let l' = false::l in
   pad #(nl+1) nb l'

(* lemma: padding does not change the final value *)
val padding_preserves_semantics: nb:nat -> nb':nat -> (l:(nlist bool nb){nb <= nb'}) ->
     Lemma (requires True)
           (ensures ((bintonat nb l) == (bintonat nb' (pad #nb nb' l)))) (decreases (nb' - nb))
let rec padding_preserves_semantics nb nb' l =
 if nb = nb' then ()
 else padding_preserves_semantics (nb+1) nb' (false::l)

val nattobin: #nb:nat{nb > 0} -> n:(fixnat nb) -> Tot (nlist bool nb)
let nattobin #nb n =
 let bl = log2 #nb n in
 let bs = nattobin_helper #nb n in
 let bs' = MyList.revT #_ #bl bs in
 pad #bl nb bs'

(* Lemma: conversion routines, with padding, are correct *)
val correct_nattobin: nb:nat{nb > 0} -> n:(fixnat nb) ->
     Lemma (requires True)
           (ensures (bintonat nb (nattobin #nb n)) == n)
let correct_nattobin nb n =
 let nl = log2 #nb n in
 let bs = nattobin_helper #nb n in
 let bs' = MyList.revT #_ #nl bs in
 correct_ntob_helper nb n;
 padding_preserves_semantics nl nb bs'

(* CIRCUITS *)

type booleanop =
| AND
| XOR

type booleanckt =
| BConst of bool
| Gate of booleanop * booleanckt * booleanckt

(* Interpreted with MSB first *)
type booleanckt_bundle (n:nat) = l:(nlist booleanckt n)

(* implementation of copy operation, i <- j *)
(*)
val copy: booleanckt -> booleanckt
let copy j = Gate (XOR, j, Wirezero)
*)

(* Semantics *)

val evalboolckt: booleanckt -> Tot bool
let rec evalboolckt bckt =
  match bckt with
  | BConst b -> b
  | Gate (op, bckt1, bckt2) ->
    let b1 = evalboolckt bckt1 in
    let b2 = evalboolckt bckt1 in
    (match op with
    | AND -> b1 && b2
    | XOR -> if b1 && b2 then false else b1 || b2)

val evalboolckt_bundle: #n:nat -> (booleanckt_bundle n) -> Tot (nlist bool n)
let evalboolckt_bundle #n b =
  MyList.mapT #_ #_ #n evalboolckt b

(* Constant circuit *)

val genbooleanckt_const: #nb:nat{nb > 0} -> n:(fixnat nb) -> Tot (booleanckt_bundle nb)
let genbooleanckt_const #nb n =
  let bl = nattobin #nb n in
  MyList.mapT #bool #booleanckt #nb BConst bl

val map_inverse: #n:nat -> #a:Type -> #b:Type -> l:(nlist a n) -> f:(a -> Tot b) -> g:(b -> Tot a) ->
      Lemma (requires (forall x. g (f x) == x))
            (ensures ((MyList.mapT #_ #_ #n g (MyList.mapT #_ #_ #n f l)) == l)) (decreases l)
let rec map_inverse #n l f g =
  match l with
  | [] -> ()
  | hd::tl -> map_inverse #(n-1) #_ #_ tl f g

val const_correct: #nb:nat{nb > 0} -> n:(fixnat nb) ->
    Lemma (requires (True))
          (ensures ((bintonat #nb (evalboolckt_bundle #nb (genbooleanckt_const #nb n))) == n))
let rec const_correct #nb n =
  let bl = nattobin #nb n in
  map_inverse #nb #_ #_ bl BConst evalboolckt;
  correct_nattobin nb n

(* HERE *)

(* Adder circuit *)

val add_helper: nb:nat -> (booleanckt_bundle nb)*booleanckt -> booleanckt -> booleanckt -> Tot ((booleanckt_bundle (nb+1)) * booleanckt)
let add_helper nb acc b1 b2 =
  let (out,c) = acc in
  let gate1 = Gate (XOR, b1, c) in
  let gate2 = Gate (XOR, b2, c) in
  let gate3 = Gate (AND, gate1, gate2) in
  let c' = Gate (XOR, gate3, c) in
  let gate5 = Gate (XOR, b1, b2) in
  let res = Gate (XOR, gate5, c) in
  res::out, c'

val genbooleanckt_add: #nb:nat -> r1:(booleanckt_bundle nb) -> r2:(booleanckt_bundle nb) -> Tot (booleanckt_bundle nb)
let genbooleanckt_add #nb r1 r2 =
  let (rout, _) = MyList.fold_left2T #_ #_ #(fun (nb:nat) -> (booleanckt_bundle nb)*booleanckt) #nb
                    add_helper 0 (empty_nl, Wirezero) r1 r2 in
(* TODO: Figure out whether I need to add this.
  List.rev_append rout []
*)
  rout

let test() =
  let nsize = 4 in
  let n1 = ntofn 12 nsize in
  let n2 = ntofn 8 nsize in
  let x1 = genbooleanckt_const #nsize n1 in
  let x2 = genbooleanckt_const #nsize n2 in
  let x3 = genbooleanckt_add #nsize x1 x2 in
  let res = evalboolckt_bundle #nsize x3 in
  let resN = bintonat #nsize res in
(*)  let _ = IO.print_string (IO.string_of_int resN) in *)
  ()


test()

(*


let f (g, ckt, l, index) b l2 =
(* allocate nat width number of wires *)
let g',r' = alloc_wrange g natsize in
let l' = rangetolist r' in
(*
* iterate over l2
* if i < index, pass on, copy 0 to corresponding bit in l'
* if i >= index, add an AND gate with inp as b and l2[curr]
* copy it to corresponding bit in l'
*)
let rec iter (_l2: list nat) (_l': list nat) (i: nat) (_ckt: booleanckt) =
if i = natsize then
_ckt
else if i < index then
iter _l2 (List.tl _l') (i + 1) (_ckt @ [(copy (List.hd _l') 0)])
else
iter (List.tl _l2) (List.tl _l') (i + 1) (_ckt @ [(AND(List.hd _l', b, List.hd _l2))])
in
(g, ckt @ (iter l2 l' 0 []), l @ [r'], index + 1, l2)

let genbooleanckt_mult g r1 r2 rout =
let l1 = rangetolist r1 in
let l2 = rangetolist r2 in
let l3 = rangetolist rout in
(*
* ckt is the circuit to which we append to
* l is the list of wire ranges that we need to add later on
* index is the current bit index in l2 (starts from 0)
* b is the actual bit
*)

let (g, rowckts, rlist, _) = List.fold_left f (g, [], [], 0) l1 in

(* now we need to have add circuits for ranges in rlist *)
let g,rinit = alloc_wrange g natsize in
let rinitckts = List.map (fun i -> copy i 0) (rangetolist rinit) in

let f (g, ckt, accum) r =
let g,rout = alloc_wrange g natsize in
let g,_ckt = genbooleanckt_add g accum r rout in
(g, ckt @ _ckt, rout)
in

let (g, addckts, accum) = List.fold_left f (g, [], rinit) rlist in
let f ckt b1 b2 = ckt @ [(copy b1 b2)] in
let outckts = List.fold_left2 f [] l3 (rangetolist accum) in
g, rowckts @ rinitckts @ addckts @ outckts

let genbooleanckt g elt =
match elt with
| Gate(Natop_plus,r1,r2,r3) -> genbooleanckt_add g r1 r2 r3
| Const(r,n) ->
assert((rsize r) = natsize);
let l1 = rangetolist r in
let l2 = nattobin n in
(*List.fold_left2 (fun c i1 i2 -> c @ [copy i1 i2]) [] l1 l2*)
g, List.rev_append (List.fold_left2 (fun (c:booleanckt) (i1:nat) (i2:nat) -> (copy i1 i2)::c) [] l1 l2) []
| _ -> failwith "unimplemented"*)
