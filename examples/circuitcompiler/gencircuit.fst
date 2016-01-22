(*--build-config
options:--admit_fsi FStar.Set;
other-files:FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.List.fst fixnat.fst wires.fst
--*)
module Bool_circuit
open Wires

type booleanop =
| AND
| XOR

type booleanckt_elt = booleanop * nat * nat * nat (* 1st = 2nd op 3rd *)

type booleanckt =
| Wirezero
| Wireone
| Gate of booleanckt_elt * booleanckt * booleanckt

type booleanckt_bundle = list booleanckt

(* implementation of copy operation, i <- j *)
let copy i j = (XOR, i, j, wirezero)

val evalboolckt: bckt:booleanckt -> Tot bool
let rec evalboolckt bckt =
  match bckt with
  | Wirezero -> false
  | Wireone -> true
  | Gate ((op,_,_,_), bckt1, bckt2) ->
    let b1 = evalboolckt bckt1 in
    let b2 = evalboolckt bckt1 in
    (match op with
    | AND -> b1 && b2
    | XOR -> if b1 && b2 then false else b1 || b2)

val evalboolckt_bundle: booleanckt_bundle -> Tot (list bool)
let evalboolckt_bundle b =
  List.mapT evalboolckt b

(* Creating circuits *)

(* XXX made it here *)

type env = nat

val genbooleanckt_add: g:env -> r1:wrange -> r2:wrange -> rout:wrange -> env*(list booleanckt)
let genbooleanckt_add g r1 r2 rout =
  let l1 = rangetolist r1 in
  let l2 = rangetolist r2 in
  let lout = rangetolist rout in
  let add_helper (acc:env*(list booleanckt)*booleanckt) (b1:nat) (b2:nat) : (env * (list booleanckt) * booleanckt) =
    let (g,out,c) = acc in
    let g1,(t1, _) = alloc_wrange g 1 in
    let g2,(t2, _) = alloc_wrange g1 1 in
    let g3,(t3, _) = alloc_wrange g2 1 in
    let g4,(c1, _) = alloc_wrange g3 1 in
    let g5,(t4, _) = alloc_wrange g4 1 in
    let g6,(s, _) = alloc_wrange g5 1 in
    let gate1 = (XOR, t1, b1, c) in
    let gate2 = (XOR, t2, b2, c) in
    let gate3 = (AND, t3, t1, t2) in
    let gate4 = (XOR, c1, t3, c) in
    let gate5 = (XOR, t4, b1, b2) in
    let gate6 = (XOR, s, t4, c) in
    (*(ckt @ [g1; g2; g3; g4; g5; g6], out @ [s], c1)*)
    g6, gate6::gate5::gate4::gate3::gate2::gate1::ckt, s::out, c1 in
  (* val fold_left2: ('s -> 'a -> 'b -> 's) -> 's -> list 'a -> list 'b -> 's *)
  let (g1, rbckt, rout, _) = List.fold_left2 add_helper (g, [], [], wirezero) l1 l2 in
  let (bckt, out) = List.rev_append rbckt [], List.rev_append rout [] in
  (*let f ckt b1 b2 = ckt @ [copy b1 b2] in*)
  let f ckt b1 b2 = (copy b1 b2)::ckt in
  let l = List.rev_append (List.fold_left2 f bckt lout out) [] in
  g1,l



(*
(* TODO: Make this a total function. Maybe do it by carrying around the size
required for the nat with the nat itself *)
val nattobin: n:nat -> list nat
let nattobin n =
let rec helper (n:nat) : list nat =
if n <= 1 then [n]
else (n % 2)::(helper (n / 2)) in
let rec pad (l:list nat) : list nat =
if List.length l > natsize then
failwith "natsize not sufficient"
else if List.length l = natsize then
l
else
pad (l @ [0])
in
pad (helper n)


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
