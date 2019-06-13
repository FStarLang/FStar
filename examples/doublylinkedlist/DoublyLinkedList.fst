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

module DoublyLinkedList

open FStar
open FStar.HyperStack.ST
open FStar.Ghost
open LowStar.ModifiesPat
open FStar.List.Tot
open FStar.List.Pure
open LowStar.BufferOps
module Mod = LowStar.Modifies
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer

/// Convenience renaming

unfold let heap = HS.mem
unfold let contains #a #rrel #rel h b = B.live #a #rrel #rel h b

/// Convenience patterns

let lemma_non_null (#t:Type) (a:pointer_or_null t) :
  Lemma
    (requires (a =!= null))
    (ensures (len a = 1ul))
    [SMTPat (len a)] =
  null_unique a

/// Convenience operators

unfold let (.[]) (s:list 'a) (n:nat{n < length s}) = index s n
unfold let (~.) (#t:Type) (a:t) : Tot (erased (list t)) = hide ([a])
unfold let (^+) (#t:Type) (a:t) (b:erased (list t)) : Tot (erased (list t)) = elift2 Cons (hide a) b
unfold let (+^) (#t:Type) (a:erased (list t)) (b:t) : Tot (erased (list t)) = elift2 append a (hide [b])
unfold let (^@^) (#t:Type) (a:erased (list t)) (b:erased (list t)) : Tot (erased (list t)) = elift2 append a b
unfold let (@) (a:pointer 't) (h0:heap) = B.get h0 a 0
unfold let (^@) (a:pointer_or_null 't{a =!= null}) (h0:heap) = B.get h0 a 0

/// All the data structures

#set-options "--__no_positivity"

unopteq
(** Node of a doubly linked list *)
type node (t:Type0) = {
  (* forward link *)
  flink: pointer_or_null (node t);
  (* backward link *)
  blink: pointer_or_null (node t);
  (* payload *)
  p: t;
}

#reset-options

private
type nodelist t = list (pointer (node t))

unopteq
(** Doubly linked list head *)
type dll (t:Type0) ={
  lhead: pointer_or_null (node t);
  ltail: pointer_or_null (node t);
  nodes: erased (nodelist t);
}

type nonempty_dll t = (h:dll t{h.lhead =!= null /\ h.ltail =!= null})

unopteq private
(** An "almost valid" dll *)
type piece t = {
  phead: pointer (node t);
  ptail: pointer (node t);
  pnodes: erased (nodelist t);
}

unopteq private
(** An intermediate for when linked lists are being formed or destroyed *)
type fragment t =
  | Frag0 : fragment t
  | Frag1 : piece t -> fragment t
  | Frag2 : piece t -> piece t -> fragment t
  | Frag3 : piece t -> piece t -> piece t -> fragment t

/// Some useful empty initializers

(** Initialize an element of a doubly linked list *)
val empty_node: #t:Type -> payload:t -> node t
let empty_node #t payload =
  { flink = null ; blink = null ; p = payload }

(** Initialize a doubly linked list head *)
val empty_list: #t:Type -> dll t
let empty_list #t =
  { lhead = null ; ltail = null ; nodes = hide [] }

/// Convenience wrappers for writing properties on fragments

let fragment_for_each0 (#t:Type) (pr:piece t -> GTot Type0) (f:fragment t) : GTot Type0 =
  match f with
  | Frag0 -> True
  | Frag1 p1 -> pr p1
  | Frag2 p1 p2 -> pr p1 /\ pr p2
  | Frag3 p1 p2 p3 -> pr p1 /\ pr p2 /\ pr p3

let fragment_for_each1 (#t:Type) (#u:Type) (pr:u -> piece t -> GTot Type0) (v:u) (f:fragment t) : GTot Type0 =
  match f with
  | Frag0 -> True
  | Frag1 p1 -> pr v p1
  | Frag2 p1 p2 -> pr v p1 /\ pr v p2
  | Frag3 p1 p2 p3 -> pr v p1 /\ pr v p2 /\ pr v p3

let fragment_length (#t:Type) (f:fragment t) : GTot int =
  match f with
  | Frag0 -> 0
  | Frag1 _ -> 1
  | Frag2 _ _ -> 2
  | Frag3 _ _ _ -> 3

/// Ghostly connections

let dll_ghostly_connections (#t:Type) (d:dll t) : GTot Type0 =
  let nodes = reveal d.nodes in
  match length nodes with
  | 0 -> d.lhead == null /\ d.ltail == null
  | _ -> d.lhead =!= null /\ d.ltail =!= null /\
         d.lhead == hd nodes /\
         d.ltail == last nodes

let piece_ghostly_connections (#t:Type) (p:piece t) : GTot Type0 =
  let nodes = reveal p.pnodes in
  match length nodes with
  | 0 -> False
  | _ -> p.phead == hd nodes /\
        p.ptail == last nodes

let rec fragment_ghostly_connections (#t:Type) (f:fragment t) : GTot Type0 =
  fragment_for_each0 piece_ghostly_connections f

/// Containment properties
///
/// WARNING: [@] and [^@] require containment to reasonably talk about
/// what they do.

let rec nodelist_contained0 (#t:Type) (h0:heap) (nl:nodelist t) : GTot Type0 =
  match nl with
  | [] -> True
  | n :: ns -> h0 `contains` n /\ nodelist_contained0 h0 ns
let rec nodelist_contained (#t:Type) (h0:heap) (nl:nodelist t) : GTot Type0 =
  nodelist_contained0 h0 nl

let dll_contained (#t:Type) (h0:heap) (d:dll t) : GTot Type0 =
  h0 `contains` d.lhead /\
  h0 `contains` d.ltail /\
  nodelist_contained h0 (reveal d.nodes)

let piece_contained (#t:Type) (h0:heap) (p:piece t) : GTot Type0 =
  h0 `contains` p.phead /\
  h0 `contains` p.ptail /\
  nodelist_contained h0 (reveal p.pnodes)

let rec fragment_contained (#t:Type) (h0:heap) (f:fragment t) : GTot Type0 =
  fragment_for_each1 piece_contained h0 f

/// Footprints

let node_fp_f (#t:Type) (n:node t) : GTot Mod.loc =
  Mod.loc_buffer n.flink
let node_fp_b (#t:Type) (n:node t) : GTot Mod.loc =
  Mod.loc_buffer n.blink

let rec nodelist_fp0 (#t:Type) (n:nodelist t) : GTot Mod.loc =
  match n with
  | [] -> Mod.loc_none
  | n :: ns -> Mod.loc_union (Mod.loc_buffer n) (nodelist_fp0 ns)
let rec nodelist_fp_f (#t:Type) (h0:heap) (n:nodelist t) : GTot Mod.loc =
  match n with
  | [] -> Mod.loc_none
  | n :: ns -> Mod.loc_union (Mod.loc_buffer (n@h0).flink) (nodelist_fp_f h0 ns)
let rec nodelist_fp_b (#t:Type) (h0:heap) (n:nodelist t) : GTot Mod.loc =
  match n with
  | [] -> Mod.loc_none
  | n :: ns -> Mod.loc_union (Mod.loc_buffer (n@h0).blink) (nodelist_fp_b h0 ns)

let dll_fp0 (#t:Type) (d:dll t) : GTot Mod.loc =
  Mod.loc_union // ghostly connections should give us this union for
                // free, but still useful to have
    (Mod.loc_union (Mod.loc_buffer d.lhead) (Mod.loc_buffer d.ltail))
    (nodelist_fp0 (reveal d.nodes))
let dll_fp_f (#t:Type) (h0:heap) (d:dll t) : GTot Mod.loc =
  let a = if g_is_null d.lhead then Mod.loc_none else Mod.loc_buffer (d.lhead^@h0).flink in
  let b = if g_is_null d.ltail then Mod.loc_none else Mod.loc_buffer (d.ltail^@h0).flink in
  Mod.loc_union // ghostly connections should give us this union for
                // free, but still useful to have
    (Mod.loc_union a b)
    (nodelist_fp_f h0 (reveal d.nodes))
let dll_fp_b (#t:Type) (h0:heap) (d:dll t) : GTot Mod.loc =
  let a = if g_is_null d.lhead then Mod.loc_none else Mod.loc_buffer (d.lhead^@h0).blink in
  let b = if g_is_null d.ltail then Mod.loc_none else Mod.loc_buffer (d.ltail^@h0).blink in
  Mod.loc_union // ghostly connections should give us this union for
                // free, but still useful to have
    (Mod.loc_union a b)
    (nodelist_fp_b h0 (reveal d.nodes))

let piece_fp0 (#t:Type) (p:piece t) : GTot Mod.loc =
  Mod.loc_union // ghostly connections should give us this union for
                // free, but still useful to have
    (Mod.loc_union (Mod.loc_buffer p.phead) (Mod.loc_buffer p.ptail))
    (nodelist_fp0 (reveal p.pnodes))
let piece_fp_f (#t:Type) (h0:heap) (p:piece t) : GTot Mod.loc =
  Mod.loc_union // ghostly connections should give us this union for
                // free, but still useful to have
    (Mod.loc_union (Mod.loc_buffer (p.phead@h0).flink) (Mod.loc_buffer (p.ptail@h0).flink))
    (nodelist_fp_f h0 (reveal p.pnodes))
let piece_fp_b (#t:Type) (h0:heap) (p:piece t) : GTot Mod.loc =
  Mod.loc_union // ghostly connections should give us this union for
                // free, but still useful to have
    (Mod.loc_union (Mod.loc_buffer (p.phead@h0).blink) (Mod.loc_buffer (p.ptail@h0).blink))
    (nodelist_fp_b h0 (reveal p.pnodes))

let rec fragment_fp0 (#t:Type) (f:fragment t) : GTot Mod.loc =
  match f with
  | Frag0 -> Mod.loc_none
  | Frag1 p1 -> piece_fp0 p1
  | Frag2 p1 p2 -> Mod.loc_union (piece_fp0 p1) (piece_fp0 p2)
  | Frag3 p1 p2 p3 -> Mod.loc_union (piece_fp0 p1) (Mod.loc_union (piece_fp0 p2) (piece_fp0 p3))

/// Helper patterns for footprints

let loc_includes_union_l_nodelist_fp0 (#t: Type) (s1 s2:loc) (nl:nodelist t) :
  Lemma
    (requires (loc_includes s1 (nodelist_fp0 nl) \/ loc_includes s2 (nodelist_fp0 nl)))
    (ensures (loc_includes (loc_union s1 s2) (nodelist_fp0 nl)))
    [SMTPat (loc_includes (loc_union s1 s2) (nodelist_fp0 nl))] =
  loc_includes_union_l s1 s2 (nodelist_fp0 nl)

let loc_includes_union_l_dll_fp0 (#t: Type) (s1 s2:loc) (d:dll t) :
  Lemma
    (requires (loc_includes s1 (dll_fp0 d) \/ loc_includes s2 (dll_fp0 d)))
    (ensures (loc_includes (loc_union s1 s2) (dll_fp0 d)))
    [SMTPat (loc_includes (loc_union s1 s2) (dll_fp0 d))] =
  loc_includes_union_l s1 s2 (dll_fp0 d)

let loc_includes_union_l_piece_fp0 (#t: Type) (s1 s2:loc) (p:piece t) :
  Lemma
    (requires (loc_includes s1 (piece_fp0 p) \/ loc_includes s2 (piece_fp0 p)))
    (ensures (loc_includes (loc_union s1 s2) (piece_fp0 p)))
    [SMTPat (loc_includes (loc_union s1 s2) (piece_fp0 p))] =
  loc_includes_union_l s1 s2 (piece_fp0 p)

let loc_includes_union_l_fragment_fp0 (#t: Type) (s1 s2:loc) (f:fragment t) :
  Lemma
    (requires (loc_includes s1 (fragment_fp0 f) \/ loc_includes s2 (fragment_fp0 f)))
    (ensures (loc_includes (loc_union s1 s2) (fragment_fp0 f)))
    [SMTPat (loc_includes (loc_union s1 s2) (fragment_fp0 f))] =
  loc_includes_union_l s1 s2 (fragment_fp0 f)

/// Equivalence for locations

let loc_equiv (a b:Mod.loc) = Mod.loc_includes a b /\ Mod.loc_includes b a

let loc_equiv_trans (a b c:Mod.loc) :
  Lemma
    (requires (loc_equiv a b /\ loc_equiv b c))
    (ensures (loc_equiv a c))
    [SMTPat (loc_equiv a b);
     SMTPat (loc_equiv b c);
     SMTPat (loc_equiv a c)] =
  Mod.loc_includes_trans a b c;
  Mod.loc_includes_trans c b a

let loc_equiv_union_union_loc (a b c:Mod.loc) :
  Lemma
    (requires (loc_equiv b c))
    (ensures (loc_equiv
                (Mod.loc_union a b)
                (Mod.loc_union a c)))
    [SMTPat (loc_equiv
                (Mod.loc_union a b)
                (Mod.loc_union a c))] =
  let incl = Mod.loc_includes in
  let u = Mod.loc_union in
  // assert (b `incl` c);
  Mod.loc_includes_union_l a b c;
  // assert ((a `u` b) `incl` c);
  Mod.loc_includes_union_l a b a;
  // assert ((a `u` b) `incl` a);
  // assert ((a `u` b) `incl` (a `u` c));
  Mod.loc_includes_union_l a c b;
  Mod.loc_includes_union_l a c a

/// Anti aliasing properties

let node_aa (#t:Type) (n:node t) : GTot Type0 =
  Mod.loc_disjoint (node_fp_f n) (node_fp_b n)

let rec nodelist_aa_r (#t:Type) (nl:nodelist t) : GTot Type0 =
  match nl with
  | [] -> True
  | n :: ns ->
    Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 ns) /\
    nodelist_aa_r ns
let rec nodelist_aa_l (#t:Type) (nl:nodelist t) : GTot Type0 (decreases (length nl)) =
  match nl with
  | [] -> True
  | _ ->
    let ns, n = unsnoc nl in lemma_unsnoc_length nl;
    Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 ns) /\
    nodelist_aa_l ns
let nodelist_aa (#t:Type) (nl:nodelist t) : GTot Type0 =
  nodelist_aa_l nl /\ nodelist_aa_r nl

let dll_aa (#t:Type) (d:dll t) : GTot Type0 =
  nodelist_aa (reveal d.nodes)

let piece_aa (#t:Type) (p:piece t) : GTot Type0 =
  nodelist_aa (reveal p.pnodes)

let rec fragment_aa0 (#t:Type) (f:fragment t) : GTot Type0 =
  fragment_for_each0 piece_aa f
let rec fragment_aa_lr (#t:Type) (f:fragment t) : GTot Type0 =
  match f with
  | Frag0 -> True
  | Frag1 p1 -> True
  | Frag2 p1 p2 -> Mod.loc_disjoint (piece_fp0 p1) (piece_fp0 p2)
  | Frag3 p1 p2 p3 -> ((Mod.loc_disjoint (piece_fp0 p1) (piece_fp0 p2)) /\
                       (Mod.loc_disjoint (piece_fp0 p2) (piece_fp0 p3)) /\
                       (Mod.loc_disjoint (piece_fp0 p3) (piece_fp0 p1)))
let fragment_aa (#t:Type) (f:fragment t) : GTot Type0 =
  fragment_aa0 f /\ fragment_aa_lr f

/// Connectivity properties

let ( |> ) (#t:Type) (a:node t) (b:pointer (node t)) : GTot Type0 =
  a.flink == b

let ( <| ) (#t:Type) (a:pointer (node t)) (b: node t) : GTot Type0 =
  b.blink == a

let rec nodelist_conn (#t:Type) (h0:heap) (nl:nodelist t) : GTot Type0 (decreases (length nl)) =
  match nl with
  | [] -> True
  | n1 :: rest -> match rest with
    | [] -> True
    | n2 :: ns ->
      n1@h0 |> n2 /\
      n1 <| n2@h0 /\
      nodelist_conn h0 rest

let dll_conn (#t:Type) (h0:heap) (d:dll t) : GTot Type0 =
  nodelist_conn h0 (reveal d.nodes) /\
  (d.lhead =!= null ==> (d.lhead@h0).blink == null) /\
  (d.ltail =!= null ==> (d.ltail@h0).flink == null)

let piece_conn (#t:Type) (h0:heap) (p:piece t) : GTot Type0 =
  nodelist_conn h0 (reveal p.pnodes)

let rec fragment_conn (#t:Type) (h0:heap) (f:fragment t) : GTot Type0 =
  fragment_for_each1 piece_conn h0 f

/// Validity properties
///
/// These are just a combination of
/// + Ghostly connections
/// + Containment properties
/// + Anti aliasing properties
/// + Connectivity properties

let nodelist_valid (#t:Type) (h0:heap) (nl:nodelist t) : GTot Type0 =
  nodelist_contained h0 nl /\
  nodelist_aa nl /\
  nodelist_conn h0 nl

let dll_valid (#t:Type) (h0:heap) (d:dll t) : GTot Type0 =
  dll_ghostly_connections d /\
  dll_contained h0 d /\
  dll_aa d /\
  dll_conn h0 d

let piece_valid (#t:Type) (h0:heap) (p:piece t) : GTot Type0 =
  piece_ghostly_connections p /\
  piece_contained h0 p /\
  piece_aa p /\
  piece_conn h0 p

let fragment_valid (#t:Type) (h0:heap) (f:fragment t) : GTot Type0 =
  fragment_ghostly_connections f /\
  fragment_contained h0 f /\
  fragment_aa f /\
  fragment_conn h0 f

/// Useful operations on nodes

let ( =|> ) (#t:Type) (a:pointer (node t)) (b:pointer (node t)) : StackInline unit
    (requires (fun h0 ->
         h0 `contains` a /\ h0 `contains` b /\
         Mod.loc_disjoint (Mod.loc_buffer a) (Mod.loc_buffer b)))
    (ensures (fun h0 _ h1 ->
         Mod.modifies (Mod.loc_buffer a) h0 h1 /\
         h1 `contains` a /\
         (a@h0).p == (a@h1).p /\
         (a@h0).blink == (a@h1).blink /\
         b@h0 == b@h1 /\
         (a@h1) |> b)) =
  a *= { !*a with flink = b }

let ( <|= ) (#t:Type) (a:pointer (node t)) (b:pointer (node t)) : StackInline unit
    (requires (fun h0 ->
         h0 `contains` a /\ h0 `contains` b /\
         Mod.loc_disjoint (Mod.loc_buffer a) (Mod.loc_buffer b)))
    (ensures (fun h0 _ h1 ->
         Mod.modifies (Mod.loc_buffer b) h0 h1 /\
         h1 `contains` b /\
         a@h0 == a@h1 /\
         (b@h0).p == (b@h1).p /\
         (b@h0).flink == (b@h1).flink /\
         a <| (b@h1))) =
  b *= { !*b with blink = a }

let ( !=|> ) (#t:Type) (a:pointer (node t)) : StackInline unit
    (requires (fun h0 -> h0 `contains` a))
    (ensures (fun h0 _ h1 ->
         Mod.modifies (Mod.loc_buffer a) h0 h1 /\
         h1 `contains` a /\
         (a@h0).p == (a@h1).p /\
         (a@h0).blink == (a@h1).blink /\
         (a@h1).flink == null)) =
  a *= { !*a with flink = null }

let ( !<|= ) (#t:Type) (a:pointer (node t)) : StackInline unit
    (requires (fun h0 -> h0 `contains` a))
    (ensures (fun h0 _ h1 ->
         Mod.modifies (Mod.loc_buffer a) h0 h1 /\
         h1 `contains` a /\
         (a@h0).p == (a@h1).p /\
         (a@h0).flink == (a@h1).flink /\
         (a@h1).blink == null)) =
  a *= { !*a with blink = null }

/// Extraction lemmas: these allow one to use one of the properties
/// above, which are defined inductively, to get the property at one
/// of the latter elements of the list.

let rec extract_nodelist_contained (#t:Type) (h0:heap) (nl:nodelist t) (i:nat{i < length nl}) :
  Lemma
    (requires (nodelist_contained h0 nl))
    (ensures (h0 `contains` nl.[i])) =
  match i with
  | 0 -> ()
  | _ -> extract_nodelist_contained h0 (tl nl) (i - 1)

let rec extract_nodelist_fp0 (#t:Type) (nl:nodelist t) (i:nat{i < length nl}) :
  Lemma
    (ensures (Mod.loc_includes
                (nodelist_fp0 nl)
                (Mod.loc_buffer nl.[i]))) =
  match i with
  | 0 -> ()
  | _ -> extract_nodelist_fp0 (tl nl) (i - 1)

let rec extract_nodelist_aa_r (#t:Type) (nl:nodelist t) (i:nat{i < length nl}) :
  Lemma
    (requires (nodelist_aa_r nl))
    (ensures (
        let left, n, right = split3 nl i in
        Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 right))) =
  match i with
  | 0 -> ()
  | _ -> extract_nodelist_aa_r (tl nl) (i - 1)

let rec extract_nodelist_aa_l (#t:Type) (nl:nodelist t) (i:nat{i < length nl}) :
  Lemma
    (requires (nodelist_aa_l nl))
    (ensures (
        let left, n, right = split3 nl i in
        Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 left)))
    (decreases (length nl)) =
  if i = length nl - 1 then () else (
    let a, b = unsnoc nl in lemma_unsnoc_length nl;
    let left, n, right = split3 nl i in
    lemma_unsnoc_split3 nl i;
    // assert (append (left) (n :: (fst (unsnoc right))) == a);
    extract_nodelist_aa_l a i;
    lemma_split3_unsnoc nl i
  )

let rec extract_nodelist_conn (#t:Type) (h0:heap) (nl:nodelist t) (i:nat{i < length nl - 1}) :
  Lemma
    (requires (nodelist_conn h0 nl))
    (ensures (
        (nl.[i]@h0 |> nl.[i+1]) /\
        (nl.[i] <| nl.[i+1]@h0)))
    (decreases (length nl)) =
  match i with
  | 0 -> ()
  | _ -> extract_nodelist_conn h0 (tl nl) (i - 1)

/// Validity is maintained upon breaking the lists, via (hd :: tl)

let rec nodelist_remains_aa_l (#t:Type) (nl:nodelist t) :
  Lemma
    (requires (nodelist_aa_l nl /\ length nl > 0))
    (ensures (nodelist_aa_l (tl nl)))
    (decreases (length nl))
    [SMTPat (nodelist_aa_l (tl nl))] =
  match nl with
  | [n] -> ()
  | _ ->
    let ns, n = unsnoc nl in lemma_unsnoc_length nl;
    let ns', n' = unsnoc (tl nl) in
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 ns));
    // assert (n' == n);
    // assert (ns' == tl ns);
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 ns'));
    nodelist_remains_aa_l ns

(* Rest of the validity predicates are held trivially due to their
   direction of definition *)

/// Properties maintained upon breaking the list, via unsnoc

let rec fst_unsnoc_nodelist_fp0 (#t:Type) (nl:nodelist t) :
  Lemma
    (requires (length nl > 0))
    (ensures (Mod.loc_includes (nodelist_fp0 nl) (nodelist_fp0 (fst (unsnoc nl)))))
    [SMTPat (Mod.loc_includes (nodelist_fp0 nl) (nodelist_fp0 (fst (unsnoc nl))))] =
  match nl with
  | [_] -> ()
  | n :: ns -> fst_unsnoc_nodelist_fp0 ns

let rec snd_unsnoc_nodelist_fp0 (#t:Type) (nl:nodelist t) :
  Lemma
    (requires (length nl > 0))
    (ensures (Mod.loc_includes (nodelist_fp0 nl) (Mod.loc_buffer (snd (unsnoc nl)))))
    [SMTPat (Mod.loc_includes (nodelist_fp0 nl) (Mod.loc_buffer (snd (unsnoc nl))))] =
  match nl with
  | [_] -> ()
  | n :: ns -> snd_unsnoc_nodelist_fp0 ns

let rec fst_unsnoc_nodelist_contained (#t:Type) (h0:heap) (nl:nodelist t) :
  Lemma
    (requires (nodelist_contained h0 nl /\ length nl > 0))
    (ensures (nodelist_contained h0 (fst (unsnoc nl)))) =
  match nl with
  | [_] -> ()
  | _ -> fst_unsnoc_nodelist_contained h0 (tl nl)

let rec fst_unsnoc_nodelist_aa (#t:Type) (nl:nodelist t) :
  Lemma
    (requires (nodelist_aa nl /\ length nl > 0))
    (ensures (nodelist_aa (fst (unsnoc nl)))) =
  match nl with
  | [_] -> ()
  | _ ->
    fst_unsnoc_nodelist_aa (tl nl);
    // assert (nodelist_aa_l (fst (unsnoc nl)));
    let n :: ns = fst (unsnoc nl) in
    Mod.loc_disjoint_includes
      (Mod.loc_buffer n) (nodelist_fp0 (tl nl))
      (Mod.loc_buffer n) (nodelist_fp0 ns);
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 ns));
    // assert (nodelist_aa_r (fst (unsnoc nl)));
    ()

let rec fst_unsnoc_nodelist_conn (#t:Type) (h0:heap) (nl:nodelist t) :
  Lemma
    (requires (nodelist_conn h0 nl /\ length nl > 0))
    (ensures (nodelist_conn h0 (fst (unsnoc nl)))) =
  match nl with
  | [_] -> ()
  | _ -> fst_unsnoc_nodelist_conn h0 (tl nl)

let fst_unsnoc_nodelist_valid (#t:Type) (h0:heap) (nl:nodelist t) :
  Lemma
    (requires (nodelist_valid h0 nl /\ length nl > 0))
    (ensures (nodelist_valid h0 (fst (unsnoc nl)))) =
  fst_unsnoc_nodelist_contained h0 nl;
  fst_unsnoc_nodelist_aa nl;
  fst_unsnoc_nodelist_conn h0 nl

/// Footprints are included, even upon breaking nodelist even further

let rec nodelist_includes_r_fp0 (#t:Type) (nl:nodelist t) (i j:nat) :
  Lemma
    (requires (i <= j /\ j < length nl))
    (ensures (
        let _, a = splitAt i nl in
        let _, b = splitAt j nl in
        Mod.loc_includes (nodelist_fp0 a) (nodelist_fp0 b)))
    (decreases (j - i)) =
  if i = j then () else (
    let temp, a = splitAt i nl in lemma_splitAt nl temp a i;
    let temp, b = splitAt j nl in lemma_splitAt nl temp b j;
    if i = j - 1 then (
      List.Pure.Properties.splitAt_assoc i 1 nl;
      // assert (tl a == b);
      ()
    ) else (
      nodelist_includes_r_fp0 nl i (j - 1);
      nodelist_includes_r_fp0 nl (j - 1) j;
      let temp, c = splitAt (j - 1) nl in lemma_splitAt nl temp c (j - 1);
      Mod.loc_includes_trans (nodelist_fp0 a) (nodelist_fp0 c) (nodelist_fp0 b)
    )
  )

let rec nodelist_includes_l_fp0 (#t:Type) (nl:nodelist t) (i j:nat) :
  Lemma
    (requires (i <= j /\ j < length nl))
    (ensures (
       let a, _ = splitAt i nl in
       let b, _ = splitAt j nl in
       Mod.loc_includes (nodelist_fp0 b) (nodelist_fp0 a)))
    (decreases (j - i)) =
  if i = j then () else (
    let a, a' = splitAt i nl in lemma_splitAt nl a a' i;
    let b, b' = splitAt j nl in lemma_splitAt nl b b' j;
    if i = j - 1 then (
      List.Pure.Properties.splitAt_assoc i 1 nl;
      // assert (b == append a [hd a']);
      lemma_unsnoc_append a [hd a'];
      // assert (snd (unsnoc b) == hd a');
      // assert (fst (unsnoc b) == a);
      fst_unsnoc_nodelist_fp0 b
    ) else (
      nodelist_includes_l_fp0 nl i (j - 1);
      nodelist_includes_l_fp0 nl (j - 1) j;
      let c, c' = splitAt (j - 1) nl in lemma_splitAt nl c c' (j - 1);
      Mod.loc_includes_trans (nodelist_fp0 b) (nodelist_fp0 c) (nodelist_fp0 a)
    )
  )

/// Total conversions between fragments, pieces, and dlls

let tot_dll_to_piece (#t:Type) (h0:heap) (d:nonempty_dll t{dll_valid h0 d}) :
  Tot (p:piece t{piece_valid h0 p}) =
  { phead = d.lhead ; ptail = d.ltail ; pnodes = d.nodes }

let tot_dll_to_fragment (#t:Type) (h0:heap) (d:dll t{dll_valid h0 d /\ d.lhead =!= null}) :
  Tot (f:fragment t{fragment_valid h0 f}) =
  Frag1 (tot_dll_to_piece h0 d)

let tot_piece_to_dll (#t:Type) (h0:heap) (p:piece t{
    piece_valid h0 p /\
    (p.phead@h0).blink == null /\
    (p.ptail@h0).flink == null}) :
  Tot (d:dll t{dll_valid h0 d}) =
  { lhead = p.phead ; ltail = p.ptail ; nodes = p.pnodes }

(* The conversions piece<->fragment are trivial *)

/// Properties maintained when appending nodelists

let rec nodelist_append_contained (#t:Type) (h0:heap) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_contained h0 nl1 /\ nodelist_contained h0 nl2))
    (ensures (nodelist_contained h0 (append nl1 nl2))) =
  match nl1 with
  | [] -> ()
  | _ :: nl1' -> nodelist_append_contained h0 nl1' nl2

let rec nodelist_append_fp0 (#t:Type) (nl1 nl2:nodelist t) :
  Lemma
    (ensures (
        loc_equiv
          (nodelist_fp0 (append nl1 nl2))
          (Mod.loc_union (nodelist_fp0 nl1) (nodelist_fp0 nl2)))) =
  match nl1 with
  | [] -> ()
  | n :: nl1' ->
    nodelist_append_fp0 nl1' nl2;
    // assert (loc_equiv
    //           (nodelist_fp0 (append nl1' nl2))
    //           (Mod.loc_union (nodelist_fp0 nl1') (nodelist_fp0 nl2)));
    // assert (loc_equiv
    //          (nodelist_fp0 nl1)
    //          (Mod.loc_union (Mod.loc_buffer n) (nodelist_fp0 nl1')));
    // assert (loc_equiv
    //           (Mod.loc_union (Mod.loc_union (Mod.loc_buffer n) (nodelist_fp0 nl1')) (nodelist_fp0 nl2))
    //           (Mod.loc_union (Mod.loc_buffer n) (Mod.loc_union (nodelist_fp0 nl1') (nodelist_fp0 nl2))));
    // assert (loc_equiv
    //           (Mod.loc_union (nodelist_fp0 nl1) (nodelist_fp0 nl2))
    //           (Mod.loc_union (Mod.loc_buffer n) (Mod.loc_union (nodelist_fp0 nl1') (nodelist_fp0 nl2))));
    // assert (loc_equiv
    //           (Mod.loc_union (Mod.loc_buffer n) (Mod.loc_union (nodelist_fp0 nl1') (nodelist_fp0 nl2)))
    //           (Mod.loc_union (Mod.loc_buffer n) (nodelist_fp0 (append nl1' nl2))));
    loc_equiv_trans
      (Mod.loc_union (nodelist_fp0 nl1) (nodelist_fp0 nl2))
      (Mod.loc_union (Mod.loc_buffer n) (Mod.loc_union (nodelist_fp0 nl1') (nodelist_fp0 nl2)))
      (Mod.loc_union (Mod.loc_buffer n) (nodelist_fp0 (append nl1' nl2)));
    // assert (loc_equiv
    //           (Mod.loc_union (nodelist_fp0 nl1) (nodelist_fp0 nl2))
    //           (Mod.loc_union (Mod.loc_buffer n) (nodelist_fp0 (append nl1' nl2))));
    ()

#set-options "--z3rlimit 20"

let rec nodelist_append_aa_l (#t:Type) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_aa_l nl1 /\ nodelist_aa_l nl2 /\
               Mod.loc_disjoint (nodelist_fp0 nl1) (nodelist_fp0 nl2)))
    (ensures (nodelist_aa_l (append nl1 nl2)))
    (decreases (length nl2)) =
  match nl2 with
  | [] -> append_l_nil nl1
  | _ ->
    let nl2', n = unsnoc nl2 in lemma_unsnoc_length nl2;
    nodelist_append_fp0 nl1 nl2';
    // assert (nodelist_aa_l nl2');
    assert (Mod.loc_includes (nodelist_fp0 nl2) (nodelist_fp0 nl2')); // OBSERVE
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 nl2'));
    lemma_unsnoc_is_last nl2;
    assert (Mod.loc_includes (nodelist_fp0 nl2) (Mod.loc_buffer n)); // OBSERVE
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 nl1));
    // assert (loc_equiv (nodelist_fp0 (append nl1 nl2')) (Mod.loc_union (nodelist_fp0 nl1) (nodelist_fp0 nl2')));
    nodelist_append_aa_l nl1 nl2';
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 (append nl1 nl2')));
    lemma_unsnoc_append nl1 nl2;
    // assert (append nl1 nl2' == fst (unsnoc (append nl1 nl2)));
    // assert (n == snd (unsnoc (append nl1 nl2)));
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 (fst (unsnoc (append nl1 nl2)))));
    ()

#reset-options

let rec nodelist_append_aa_r (#t:Type) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_aa_r nl1 /\ nodelist_aa_r nl2 /\
               Mod.loc_disjoint (nodelist_fp0 nl1) (nodelist_fp0 nl2)))
    (ensures (nodelist_aa_r (append nl1 nl2))) =
  match nl1 with
  | [] -> ()
  | _ ->
    nodelist_append_fp0 (tl nl1) nl2;
    nodelist_append_aa_r (tl nl1) nl2

let nodelist_append_aa (#t:Type) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_aa nl1 /\ nodelist_aa nl2 /\
               Mod.loc_disjoint (nodelist_fp0 nl1) (nodelist_fp0 nl2)))
    (ensures (nodelist_aa (append nl1 nl2))) =
  nodelist_append_aa_l nl1 nl2; nodelist_append_aa_r nl1 nl2

let rec nodelist_append_conn (#t:Type) (h0:heap) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_conn h0 nl1 /\ nodelist_conn h0 nl2 /\
               Mod.loc_disjoint (nodelist_fp0 nl1) (nodelist_fp0 nl2) /\
               length nl1 > 0 /\ length nl2 > 0 /\ // For "= 0", it is trivially held
               (last nl1)@h0 |> (hd nl2) /\
               (last nl1) <| (hd nl2)@h0))
    (ensures (nodelist_conn h0 (append nl1 nl2))) =
  match nl1 with
  | [_] -> ()
  | _ -> nodelist_append_conn h0 (tl nl1) nl2

let nodelist_append_valid (#t:Type) (h0:heap) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_valid h0 nl1 /\ nodelist_valid h0 nl2 /\
               Mod.loc_disjoint (nodelist_fp0 nl1) (nodelist_fp0 nl2) /\
               length nl1 > 0 /\ length nl2 > 0 /\ // For "= 0", it is trivially held
               (last nl1)@h0 |> (hd nl2) /\
               (last nl1) <| (hd nl2)@h0))
    (ensures (nodelist_valid h0 (append nl1 nl2))) =
  nodelist_append_contained h0 nl1 nl2;
  nodelist_append_aa nl1 nl2;
  nodelist_append_conn h0 nl1 nl2

/// Useful property for for piece merging

let loc_includes_union_r_inv (a b c:Mod.loc) :
  Lemma
    (requires (Mod.loc_includes a (Mod.loc_union b c)))
    (ensures (Mod.loc_includes a b /\ Mod.loc_includes a c)) =
  Mod.loc_includes_union_l b c b;
  Mod.loc_includes_trans a (Mod.loc_union b c) b;
  Mod.loc_includes_union_l b c c;
  Mod.loc_includes_trans a (Mod.loc_union b c) c

/// Piece merging

#set-options "--z3rlimit 10"

let piece_merge (#t:Type) (h0:heap)
    (p1:piece t{piece_valid h0 p1})
    (p2:piece t{piece_valid h0 p2}) :
  Pure (piece t)
    (requires (let a, b = last (reveal p1.pnodes), hd (reveal p2.pnodes) in
               (a@h0 |> b) /\
               (a <| b@h0) /\
               Mod.loc_disjoint (piece_fp0 p1) (piece_fp0 p2)))
    (ensures (fun p -> piece_valid h0 p)) =
  let p = { phead = p1.phead ; ptail = p2.ptail ; pnodes = p1.pnodes ^@^ p2.pnodes } in
  lemma_append_last (reveal p1.pnodes) (reveal p2.pnodes);
  nodelist_append_valid h0 (reveal p1.pnodes) (reveal p2.pnodes);
  p

#reset-options

let piece_merge_fp0 (#t:Type) (h0:heap)
    (p1:piece t{piece_valid h0 p1})
    (p2:piece t{piece_valid h0 p2}) :
  Lemma
    (requires (let a, b = last (reveal p1.pnodes), hd (reveal p2.pnodes) in
               (a@h0 |> b) /\
               (a <| b@h0) /\
               Mod.loc_disjoint (piece_fp0 p1) (piece_fp0 p2)))
    (ensures (loc_equiv
                (piece_fp0 (piece_merge h0 p1 p2))
                (Mod.loc_union (piece_fp0 p1) (piece_fp0 p2)))) =
  let p = piece_merge h0 p1 p2 in
  let n1, n2, n = reveal p1.pnodes, reveal p2.pnodes, reveal p.pnodes in
  nodelist_append_fp0 n1 n2;
  // assert (loc_equiv (nodelist_fp0 n) (Mod.loc_union (nodelist_fp0 n1) (nodelist_fp0 n2)));
  // assert (hd n1 == p1.phead);
  // assert (Mod.loc_includes (nodelist_fp0 n1) (Mod.loc_buffer p1.phead));
  // assert (Mod.loc_includes (nodelist_fp0 n) (Mod.loc_buffer p.phead));
  // assert (last n2 == p2.ptail);
  extract_nodelist_fp0 n2 (length n2 - 1);
  lemma_unsnoc_is_last n2;
  // assert (Mod.loc_includes (nodelist_fp0 n2) (Mod.loc_buffer p2.ptail));
  extract_nodelist_fp0 n (length n - 1);
  lemma_unsnoc_is_last n;
  // assert (Mod.loc_includes (nodelist_fp0 n) (Mod.loc_buffer p.ptail));
  loc_includes_union_r_inv (nodelist_fp0 n) (nodelist_fp0 n1) (nodelist_fp0 n2);
  // assert (Mod.loc_includes (nodelist_fp0 n) (nodelist_fp0 n1));
  // assert (Mod.loc_includes (nodelist_fp0 n) (nodelist_fp0 n2));
  //
  // assert (loc_equiv (nodelist_fp0 n) (piece_fp0 p));
  extract_nodelist_fp0 n1 (length n1 - 1);
  lemma_unsnoc_is_last n1;
  // assert (loc_equiv (nodelist_fp0 n1) (piece_fp0 p1));
  // assert (loc_equiv (nodelist_fp0 n2) (piece_fp0 p2));
  //
  // assert (Mod.loc_includes (nodelist_fp0 n) (Mod.loc_union (nodelist_fp0 n1) (nodelist_fp0 n2)));
  Mod.loc_includes_trans (nodelist_fp0 n) (piece_fp0 p)
    (Mod.loc_union (nodelist_fp0 n1) (nodelist_fp0 n2));
  Mod.loc_includes_trans (nodelist_fp0 n)
    (Mod.loc_union (nodelist_fp0 n1) (nodelist_fp0 n2))
    (Mod.loc_union (piece_fp0 p1) (piece_fp0 p2));
  // assert (Mod.loc_includes (piece_fp0 p) (Mod.loc_union (piece_fp0 p1) (piece_fp0 p2)));
  //
  // assert (Mod.loc_includes (Mod.loc_union (nodelist_fp0 n1) (nodelist_fp0 n2)) (nodelist_fp0 n));
  loc_equiv_trans (nodelist_fp0 n) (piece_fp0 p)
    (Mod.loc_union (nodelist_fp0 n1) (nodelist_fp0 n2));
  loc_equiv_trans (nodelist_fp0 n)
    (Mod.loc_union (nodelist_fp0 n1) (nodelist_fp0 n2))
    (Mod.loc_union (piece_fp0 p1) (piece_fp0 p2));
  loc_equiv_trans (piece_fp0 p) (nodelist_fp0 n)
    (Mod.loc_union (piece_fp0 p1) (piece_fp0 p2))

/// Fragment merging to a dll

let rec fragment_defragmentable (#t:Type) (h0:heap) (f:fragment t{fragment_valid h0 f}) :
  GTot Type0 =
  let aux (p1 p2:(p:piece t{piece_valid h0 p})) =
    let a, b = last (reveal p1.pnodes), hd (reveal p2.pnodes) in
    (a@h0 |> b) /\(a <| b@h0) in
  match f with
  | Frag0 -> True
  | Frag1 p1 -> True
  | Frag2 p1 p2 -> aux p1 p2
  | Frag3 p1 p2 p3 -> aux p1 p2 /\ aux p2 p3

let single_piece_fragment_valid (#t:Type) (h0:heap) (p:piece t) :
  Lemma
    (requires (piece_valid h0 p))
    (ensures (fragment_valid h0 (Frag1 p))) = ()

#set-options "--z3rlimit 5 --initial_ifuel 2"

let tot_defragmentable_fragment_to_dll (#t:Type) (h0:heap) (f:fragment t{
    fragment_valid h0 f /\
    fragment_defragmentable h0 f /\
    (fragment_length f > 0 ==>
     (let a, b = match f with
       | Frag1 p1 -> p1, p1
       | Frag2 p1 p2 -> p1, p2
       | Frag3 p1 _ p3 -> p1, p3 in
      ((a.phead@h0).blink == null) /\
      ((b.ptail@h0).flink == null)))
  }) :
  Tot (d:dll t{dll_valid h0 d}) =
  match f with
  | Frag0 -> empty_list
  | Frag1 p1 -> tot_piece_to_dll h0 p1
  | Frag2 p1 p2 -> tot_piece_to_dll h0 (piece_merge h0 p1 p2)
  | Frag3 p1 p2 p3 ->
    let p' = piece_merge h0 p1 p2 in
    piece_merge_fp0 h0 p1 p2;
    tot_piece_to_dll h0 (piece_merge h0 p' p3)

#reset-options

/// Properties of nodelists maintained upon splitting nodelists

let rec nodelist_split_contained (#t:Type) (h0:heap) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_contained h0 (append nl1 nl2)))
    (ensures (nodelist_contained h0 nl1 /\ nodelist_contained h0 nl2)) =
  match nl1 with
  | [] -> ()
  | _ :: nl1' -> nodelist_split_contained h0 nl1' nl2

let rec nodelist_split_fp0 (#t:Type) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_aa_r (append nl1 nl2)))
    (ensures (Mod.loc_disjoint (nodelist_fp0 nl1) (nodelist_fp0 nl2))) =
  match nl1 with
  | [] | [_] -> ()
  | _ ->
    match nl2 with
    | [] -> ()
    | _ ->
      // assert (length nl1 > 1);
      // assert (length nl2 > 0);
      nodelist_split_fp0 (tl nl1) nl2;
      append_length nl1 nl2;
      nodelist_includes_r_fp0 (tl (append nl1 nl2)) 0 (length nl1 - 1);
      // assert (snd (splitAt 0 (tl (append nl1 nl2))) == tl (append nl1 nl2));
      // assert (snd (splitAt (length nl1 - 1) (tl (append nl1 nl2))) == snd (splitAt (length nl1) (append nl1 nl2)));
      lemma_append_splitAt nl1 nl2;
      // assert (snd (splitAt (length nl1) (append nl1 nl2)) == nl2);
      // assert (Mod.loc_includes (nodelist_fp0 (tl (append nl1 nl2))) (nodelist_fp0 nl2));
      // assert (Mod.loc_disjoint (Mod.loc_buffer (hd nl1)) (nodelist_fp0 (tl (append nl1 nl2))));
      // assert (Mod.loc_disjoint (Mod.loc_buffer (hd nl1)) (nodelist_fp0 nl2));
      // assert (Mod.loc_disjoint (nodelist_fp0 (tl nl1)) (nodelist_fp0 nl2));
      Mod.loc_disjoint_union_r (nodelist_fp0 nl2) (Mod.loc_buffer (hd nl1)) (nodelist_fp0 (tl nl1));
      // assert (Mod.loc_disjoint (Mod.loc_union (Mod.loc_buffer (hd nl1)) (nodelist_fp0 (tl nl1))) (nodelist_fp0 nl2));
      ()

#set-options "--z3rlimit 30"

let rec nodelist_split_fp0_equiv (#t:Type) (nl1 nl2:nodelist t) :
  Lemma
    (ensures
       ((loc_equiv
           (nodelist_fp0 (append nl1 nl2))
           (Mod.loc_union
              (nodelist_fp0 nl1)
              (nodelist_fp0 nl2))))) =
  match nl1 with
  | [] -> ()
  | n :: ns ->
    nodelist_split_fp0_equiv ns nl2;
    assert (loc_equiv (nodelist_fp0 (append nl1 nl2))
              (Mod.loc_union
                 (Mod.loc_buffer n)
                 (Mod.loc_union
                    (nodelist_fp0 ns)
                    (nodelist_fp0 nl2)))); // OBSERVE
    assert (loc_equiv
              (Mod.loc_union
                 (Mod.loc_buffer n)
                 (Mod.loc_union
                    (nodelist_fp0 ns)
                    (nodelist_fp0 nl2)))
              (Mod.loc_union
                 (Mod.loc_union
                    (Mod.loc_buffer n)
                    (nodelist_fp0 ns))
                 (nodelist_fp0 nl2))) // OBSERVE

let rec nodelist_split_aa_l (#t:Type) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_aa_l (append nl1 nl2)))
    (ensures (nodelist_aa_l nl1 /\ nodelist_aa_l nl2))
    (decreases (length nl2)) =
  match nl2 with
  | [] -> append_l_nil nl1
  | _ ->
    let nl2', n = unsnoc nl2 in lemma_unsnoc_length nl2;
    lemma_unsnoc_append nl1 nl2;
    // assert (nodelist_aa_l (append nl1 nl2));
    // assert (nodelist_aa_l (append nl1 nl2'));
    nodelist_split_aa_l nl1 nl2';
    // assert (nodelist_aa_l nl2');
    // assert (n == snd (unsnoc (append nl1 nl2)));
    // assert (n == snd (unsnoc nl2));
    nodelist_append_fp0 nl1 nl2';
    // assert (Mod.loc_includes (nodelist_fp0 (append nl1 nl2')) (nodelist_fp0 nl2'));
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 nl2'));
    // assert (nodelist_aa_l nl2);
    ()

#reset-options

let rec nodelist_split_aa_r (#t:Type) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_aa_r (append nl1 nl2)))
    (ensures (nodelist_aa_r nl1 /\ nodelist_aa_r nl2)) =
  match nl1 with
  | [] -> ()
  | _ ->
    nodelist_split_aa_r (tl nl1) nl2;
    nodelist_append_fp0 (tl nl1) nl2

let nodelist_split_aa (#t:Type) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_aa (append nl1 nl2)))
    (ensures (nodelist_aa nl1 /\ nodelist_aa nl2 /\
               Mod.loc_disjoint (nodelist_fp0 nl1) (nodelist_fp0 nl2))) =
  nodelist_split_fp0 nl1 nl2;
  nodelist_split_aa_l nl1 nl2;
  nodelist_split_aa_r nl1 nl2

let rec nodelist_split_conn (#t:Type) (h0:heap) (nl1 nl2:nodelist t) :
  Lemma
    (requires (
        (nodelist_conn h0 (append nl1 nl2)) /\
        length nl1 > 0 /\ length nl2 > 0)) // For "= 0", it is trivially held
    (ensures (nodelist_conn h0 nl1 /\ nodelist_conn h0 nl2 /\
               (last nl1)@h0 |> (hd nl2) /\
               (last nl1) <| (hd nl2)@h0)) =
  match nl1 with
  | [_] -> ()
  | _ -> nodelist_split_conn h0 (tl nl1) nl2

let nodelist_split_valid (#t:Type) (h0:heap) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_valid h0 (append nl1 nl2) /\
               length nl1 > 0 /\ length nl2 > 0)) // For "= 0", it is trivially held
    (ensures (nodelist_valid h0 nl1 /\ nodelist_valid h0 nl2 /\
              Mod.loc_disjoint (nodelist_fp0 nl1) (nodelist_fp0 nl2) /\
               (last nl1)@h0 |> (hd nl2) /\
               (last nl1) <| (hd nl2)@h0)) =
  nodelist_split_contained h0 nl1 nl2;
  nodelist_split_aa nl1 nl2;
  nodelist_split_conn h0 nl1 nl2

/// Useful lemma to convert from dll_fp0 or piece_fp0 to nodelist_fp0
/// and vice-versa

let dll_fp0_is_nodelist_fp0 (#t:Type) (d:dll t) : Lemma
  (requires (dll_ghostly_connections d))
  (ensures
     (loc_equiv (dll_fp0 d) (nodelist_fp0 (reveal d.nodes)))) =
  if length (reveal d.nodes) > 0 then
    lemma_unsnoc_is_last (reveal d.nodes)
  else
    ()

let piece_fp0_is_nodelist_fp0 (#t:Type) (p:piece t) : Lemma
  (requires (piece_ghostly_connections p))
  (ensures
     (loc_equiv (piece_fp0 p) (nodelist_fp0 (reveal p.pnodes)))) =
  lemma_unsnoc_is_last (reveal p.pnodes)

/// Tot dll to fragment, with splitting

#set-options "--z3rlimit 60 --initial_fuel 8 --initial_ifuel 1"

let tot_dll_to_fragment_split (#t:Type) (h0:heap) (d:dll t{dll_valid h0 d})
    (n1 n2:pointer (node t)) :
  Pure (fragment t)
    (requires (
        n1 `memP` reveal d.nodes /\
        n2 `memP` reveal d.nodes /\
        n1@h0 |> n2 /\ n1 <| n2@h0))
    (ensures (fun f ->
         fragment_valid h0 f /\
         fragment_length f = 2 /\
         loc_equiv (dll_fp0 d) (fragment_fp0 f))) =
  let split_nodes = elift2_p split_using d.nodes (hide n2) in
  lemma_split_using (reveal d.nodes) n2;
  let l1, l2 = (elift1 fst split_nodes), (elift1 snd split_nodes) in
  let p1 = { phead = d.lhead ; ptail = n1 ; pnodes = l1 } in
  let p2 = { phead = n2 ; ptail = d.ltail ; pnodes = l2 } in
  let f = Frag2 p1 p2 in
  dll_fp0_is_nodelist_fp0 d;
  // assert (loc_equiv (dll_fp0 d) (nodelist_fp0 (reveal d.nodes)));
  nodelist_split_fp0_equiv (reveal l1) (reveal l2);
  nodelist_split_valid h0 (reveal l1) (reveal l2);
  lemma_unsnoc_is_last (reveal l1);
  lemma_unsnoc_is_last (reveal l2);
  lemma_unsnoc_is_last (reveal d.nodes);
  // assert (piece_ghostly_connections p1);
  // assert ( n2 == hd (reveal l2) );
  lemma_append_last (reveal l1) (reveal l2);
  // assert ( last (reveal l2) == last (append (reveal l1) (reveal l2)) );
  // assert ( d.ltail == last (reveal l2) );
  // assert (piece_ghostly_connections p2);
  // assert (fragment_ghostly_connections f);
  // assert (nodelist_contained h0 (reveal p1.pnodes));
  // assert (nodelist_contained h0 (reveal p2.pnodes));
  extract_nodelist_contained h0 (reveal l1) (length (reveal l1) - 1);
  // assert (h0 `contains` p1.ptail);
  // assert (fragment_contained h0 f);
  // assert (nodelist_aa (reveal p1.pnodes));
  // assert (nodelist_aa (reveal p2.pnodes));
  piece_fp0_is_nodelist_fp0 p1;
  piece_fp0_is_nodelist_fp0 p2;
  // assert (loc_equiv (dll_fp0 d)
  //           (Mod.loc_union (nodelist_fp0 (reveal l1)) (nodelist_fp0 (reveal l2))));
  // assert (loc_equiv (nodelist_fp0 (reveal l1)) (piece_fp0 p1));
  // assert (loc_equiv (nodelist_fp0 (reveal l2)) (piece_fp0 p2));
  // assert (loc_equiv
  //           (Mod.loc_union (nodelist_fp0 (reveal l1)) (nodelist_fp0 (reveal l2)))
  //           (Mod.loc_union (piece_fp0 p1) (piece_fp0 p2)));
  loc_equiv_trans
    (dll_fp0 d)
    (Mod.loc_union (nodelist_fp0 (reveal l1)) (nodelist_fp0 (reveal l2)))
    (Mod.loc_union (piece_fp0 p1) (piece_fp0 p2));
  // assert (loc_equiv (dll_fp0 d)
  //           (Mod.loc_union (piece_fp0 p1) (piece_fp0 p2)));
  // assert (Mod.loc_disjoint (piece_fp0 p1) (piece_fp0 p2));
  // assert (fragment_aa f);
  // assert (nodelist_conn h0 (reveal p1.pnodes));
  // assert (nodelist_conn h0 (reveal p2.pnodes));
  // assert (fragment_conn h0 f);
  f

#reset-options

/// Creating a dll from a single node. Pure and ST forms of this.

let tot_node_to_dll (#t:Type) (h0:heap) (n:pointer (node t)) :
  Pure (dll t)
    (requires (
        (h0 `contains` n) /\
        (((n@h0).flink == null)) /\
        ((n@h0).blink == null)))
    (ensures (fun d -> dll_valid h0 d)) =
  { lhead = n ; ltail = n ; nodes = ~. n }

let singleton_dll (#t:Type) (n:pointer (node t)) :
  StackInline (dll t)
    (requires (fun h0 ->
        (h0 `contains` n)))
    (ensures (fun h0 d h1 ->
         Mod.modifies (Mod.loc_buffer n) h0 h1 /\
         dll_valid h1 d)) =
  !=|> n;
  !<|= n;
  tot_node_to_dll (ST.get ()) n

/// Creating a piece from a single node.

let tot_node_to_piece (#t:Type) (h0:heap) (n:pointer (node t)) :
  Pure (piece t)
    (requires (
        (h0 `contains` n)))
    (ensures (fun p -> piece_valid h0 p)) =
  { phead = n ; ptail = n ; pnodes = ~. n }

/// Getting the "tail" of a piece

let tot_piece_tail (#t:Type) (h0:heap) (p:piece t) (n:pointer (node t)) :
  Pure (piece t)
    (requires (
        (piece_valid h0 p) /\
        (n == (((p.phead)@h0).flink)) /\
        (length (reveal p.pnodes) > 1)))
    (ensures (fun q ->
         (piece_valid h0 q) /\
         (reveal q.pnodes) == tl (reveal p.pnodes))) =
  { phead = n ; ptail = p.ptail ; pnodes = elift1_p (tot_to_gtot tl) p.pnodes }

/// If a dll is valid, then both the forward and backward links of
/// each of the nodes are contained in the heap, and disjoint from
/// each other

let lemma_dll_links_contained (#t:Type) (h0:heap) (d:dll t) (i:nat) :
  Lemma
    (requires (
        (dll_valid h0 d) /\
        (i < length (reveal d.nodes))))
    (ensures (
        let nodes = reveal d.nodes in
        (h0 `contains` (nodes.[i]@h0).flink) /\
        (h0 `contains` (nodes.[i]@h0).blink))) =
  let nl = reveal d.nodes in
  match nl with
  | [_] -> ()
  | _ ->
    (if i = 0 then () else extract_nodelist_conn h0 nl (i-1));
    (if i = length nl - 1 then () else extract_nodelist_conn h0 nl i);
    (if i = 0 then () else extract_nodelist_contained h0 nl (i - 1));
    (if i = length nl - 1 then () else extract_nodelist_contained h0 nl (i + 1));
    lemma_unsnoc_is_last nl

#reset-options "--initial_ifuel 2 --max_ifuel 2 --max_fuel 2 --initial_fuel 2 --z3rlimit 20"

let lemma_dll_links_disjoint (#t:Type) (h0:heap) (d:dll t) (i:nat) :
  Lemma
    (requires (
        (dll_valid h0 d) /\
        (i < length (reveal d.nodes))))
    (ensures (
        let nodes = reveal d.nodes in
        let left = (nodes.[i]@h0).blink in
        let right = (nodes.[i]@h0).flink in
        Mod.loc_disjoint
          (Mod.loc_buffer left)
          (Mod.loc_buffer right))) =
  let nl = reveal d.nodes in
  match nl with
  | [_] -> ()
  | _ ->
    lemma_unsnoc_length nl;
    let node_split = splitAt i nl in
    lemma_splitAt nl (fst node_split) (snd node_split) i;
    lemma_splitAt_index_hd i nl;
    let l1, x :: l2 = node_split in
    (if i = 0 then () else extract_nodelist_conn h0 nl (i-1));
    (if i = length nl - 1 then () else extract_nodelist_conn h0 nl i);
    (if i = 0 then () else (
        if i = length nl - 1 then (lemma_unsnoc_is_last nl) else (
          lemma_unsnoc_is_last l1;
          let left = last l1 in
          let right = hd l2 in
          lemma_splitAt_reindex_left i nl (length l1 - 1);
          // assert (left == (nl.[i]@h0).blink);
          lemma_splitAt_reindex_right i nl 1;
          // assert (right == (nl.[i]@h0).flink);
          nodelist_split_aa l1 (x :: l2);
          // assert (Mod.loc_disjoint (nodelist_fp0 l1) (nodelist_fp0 l2));
          assert (Mod.loc_includes (nodelist_fp0 l1) (Mod.loc_buffer left)); // OBSERVE
          assert (Mod.loc_includes (nodelist_fp0 l2) (Mod.loc_buffer right)); // OBSERVE
          ()
        )))

#reset-options

/// When something unrelated to a XYZ is changed, the XYZ itself shall
/// remain valid

let rec nodelist_remains_valid (#t:Type) (h0 h1:heap) (loc:Mod.loc) (nl:nodelist t) :
  Lemma
    (requires (
        (nodelist_valid h0 nl) /\
        (Mod.modifies loc h0 h1) /\
        (Mod.loc_disjoint loc (nodelist_fp0 nl))))
    (ensures (nodelist_valid h1 nl)) =
  match nl with
  | [] -> ()
  | _ -> nodelist_remains_valid h0 h1 loc (tl nl)

let piece_remains_valid (#t:Type) (h0 h1:heap) (loc:Mod.loc) (p:piece t) :
  Lemma
    (requires (
        (piece_valid h0 p) /\
        (Mod.modifies loc h0 h1) /\
        (Mod.loc_disjoint loc (piece_fp0 p))))
    (ensures (piece_valid h1 p)) =
  nodelist_remains_valid h0 h1 loc (reveal p.pnodes)

/// When outward facing pointers of ends of pieces are modified, they
/// still remain valid

#set-options "--z3rlimit 20"

let piece_remains_valid_b (#t:Type) (h0 h1:heap) (p:piece t) :
  Lemma
    (requires (
        (piece_valid h0 p) /\
        (Mod.modifies (Mod.loc_buffer p.phead) h0 h1) /\
        (h1 `contains` p.phead) /\
        (p.phead@h0).flink == (p.phead@h1).flink))
    (ensures (piece_valid h1 p) /\ (p.ptail@h0).flink == (p.ptail@h1).flink) =
  let nodes = reveal p.pnodes in
  if length nodes > 1 then (
    nodelist_includes_r_fp0 nodes 1 (length nodes - 1);
    lemma_unsnoc_is_last nodes;
    // assert (p.ptail == nodes.[length nodes - 1]);
    // assert (p.ptail@h0 == p.ptail@h1);
    // assert (h1 `contains` p.ptail);
    // assert (Mod.loc_disjoint (Mod.loc_buffer p.phead) (nodelist_fp0 (tl nodes)));
    nodelist_remains_valid h0 h1 (Mod.loc_buffer p.phead) (tl nodes)
  ) else ()

let piece_remains_valid_f (#t:Type) (h0 h1:heap) (p:piece t) :
  Lemma
    (requires (
        (piece_valid h0 p) /\
        (Mod.modifies (Mod.loc_buffer p.ptail) h0 h1) /\
        (h1 `contains` p.ptail) /\
        (p.ptail@h0).blink == (p.ptail@h1).blink))
    (ensures (piece_valid h1 p) /\ (p.phead@h0).blink == (p.phead@h1).blink) =
  let nodes = reveal p.pnodes in
  if length nodes > 1 then (
    fst_unsnoc_nodelist_valid h0 nodes;
    // assert (nodelist_valid h0 (fst (unsnoc nodes)));
    lemma_unsnoc_is_last nodes;
    // assert (Mod.loc_disjoint (Mod.loc_buffer p.ptail) (nodelist_fp0 (fst (unsnoc nodes))));
    nodelist_remains_valid h0 h1 (Mod.loc_buffer p.ptail) (fst (unsnoc nodes));
    // assert (nodelist_contained h1 (fst (unsnoc nodes)));
    // assert (h1 `contains` (snd (unsnoc nodes)));
    nodelist_append_contained h1 (fst (unsnoc nodes)) [snd (unsnoc nodes)];
    // assert (nodelist_contained h1 (reveal p.pnodes));
    // assert (piece_contained h1 p);
    extract_nodelist_conn h0 nodes (length nodes - 2);
    // let nl1 = fst (unsnoc nodes) in
    lemma_unsnoc_is_last (fst (unsnoc nodes));
    // assert (last nl1 == nl1.[length nl1 - 1]);
    // assert (last nl1 == nl1.[length nodes - 2]);
    lemma_unsnoc_index nodes (length nodes - 2);
    // assert (last nl1 == nodes.[length nodes - 2]);
    // assert ((last (fst (unsnoc nodes)))@h0 |> (hd [snd (unsnoc nodes)]));
    // assert (Mod.loc_disjoint (nodelist_fp0 (fst (unsnoc nodes))) (Mod.loc_buffer p.ptail));
    // assert (Mod.loc_disjoint (Mod.loc_buffer (last (fst (unsnoc nodes)))) (Mod.loc_buffer p.ptail));
    // assert (Mod.modifies (Mod.loc_buffer p.ptail) h0 h1);
    extract_nodelist_contained h0 nodes (length nodes - 2);
    // assert (h0 `contains` last (fst (unsnoc nodes)));
    // assert (Mod.loc_disjoint (nodelist_fp0 (fst (unsnoc nodes))) (Mod.loc_buffer p.ptail));
    assert (Mod.loc_includes (nodelist_fp0 (fst (unsnoc nodes))) (Mod.loc_buffer (last (fst (unsnoc nodes))))); // OBSERVE
    // assert (Mod.loc_disjoint (Mod.loc_buffer (last (fst (unsnoc nodes)))) (Mod.loc_buffer p.ptail));
    lemma_snoc_length (unsnoc nodes);
    // assert ((last (fst (unsnoc nodes)))@h0 == (last (fst (unsnoc nodes)))@h1);
    // assert ((last (fst (unsnoc nodes)))@h1 |> (hd [snd (unsnoc nodes)]));
    // assert ((last (fst (unsnoc nodes))) <| (hd [snd (unsnoc nodes)])@h1);
    nodelist_append_conn h1 (fst (unsnoc nodes)) [snd (unsnoc nodes)];
    // assert (nodelist_conn h1 (reveal p.pnodes));
    // assert (piece_conn h1 p);
    // assert ((p.phead@h0).blink == (p.phead@h1).blink);
    ()
  ) else ()

#reset-options

/// Testing is a node is within a dll or not

let node_not_in_dll (#t:Type) (h0:heap) (n:pointer (node t)) (d:dll t) =
  let m1 = Mod.loc_union (Mod.loc_buffer n)
      (Mod.loc_union (node_fp_b (n@h0)) (node_fp_f (n@h0))) in
  let m2 = Mod.loc_union (dll_fp0 d) (Mod.loc_union
                                        (dll_fp_f h0 d) (dll_fp_b h0 d)) in
  Mod.loc_disjoint m1 m2

/// Now for the actual ST operations that will be exposed :)

#set-options "--z3rlimit 500 --max_fuel 2 --max_ifuel 0"

let dll_insert_at_head (#t:Type) (d:dll t) (n:pointer (node t)) :
  StackInline (dll t)
    (requires (fun h0 ->
         (dll_valid h0 d) /\
         (h0 `contains` n) /\
         (node_not_in_dll h0 n d)))
    (ensures (fun h0 y h1 ->
         Mod.modifies (Mod.loc_union
                         (Mod.loc_buffer n)
                         (Mod.loc_buffer d.lhead)) h0 h1 /\
         dll_valid h1 y)) =
  if is_null d.lhead then (
    singleton_dll n
  ) else (
    let h = d.lhead in
    //
    let h0 = ST.get () in
    !<|= n;
    n =|> h;
    let h0' = ST.get () in
    n <|= h;
    let h1 = ST.get () in
    //
    let Frag1 p1 = tot_dll_to_fragment h0 d in
    let p = tot_node_to_piece h0 n in
    let f' = Frag2 p p1 in
    // assert (fragment_valid h1 [p]);
    // assert (fragment_ghostly_connections f);
    // assert (length f = 1);
    // assert (h1 `contains` (hd f).phead);
    piece_remains_valid h0 h0' (Mod.loc_buffer n) p1;
    // assert (piece_valid h0' (hd f));
    piece_remains_valid_b h0' h1 p1;
    // assert (h1 `contains` (hd f).ptail);
    // assert (nodelist_contained h1 (reveal (hd f).pnodes));
    // assert (piece_contained h1 (hd f));
    // assert (fragment_contained h1 f);
    // assert (fragment_aa f);
    // assert (nodelist_conn h1 (reveal (f.[0]).pnodes));
    // assert (fragment_conn h1 f);
    // assert (fragment_valid h1 f);
    // assert (fragment_valid h1 f');
    // assert (fragment_defragmentable h1 f');
    // assert (length f' > 0);
    // assert (is_null ((hd f').phead@h1).blink);
    // assert (is_null ((last f').ptail@h0).flink);
    // assert (is_null ((last f').ptail@h0').flink);
    // assert (is_null ((last f').ptail@h1).flink);
    let y = tot_defragmentable_fragment_to_dll h1 f' in
    // admit (); // Instead of StackInline, if we use ST everywhere in
    //           // this file, it is unable to prove things
    // assert (dll_valid h1 y);
    y
  )

#reset-options

#set-options "--z3rlimit 500 --max_fuel 2 --max_ifuel 0"

let dll_insert_at_tail (#t:Type) (d:dll t) (n:pointer (node t)) :
  StackInline (dll t)
    (requires (fun h0 ->
         (dll_valid h0 d) /\
         (h0 `contains` n) /\
         (node_not_in_dll h0 n d)))
    (ensures (fun h0 y h1 ->
         Mod.modifies (Mod.loc_union
                         (Mod.loc_buffer n)
                         (Mod.loc_buffer d.ltail)) h0 h1 /\
         dll_valid h1 y)) =
  if is_null d.lhead then (
    singleton_dll n
  ) else (
    let t = d.ltail in
    //
    let h0 = ST.get () in
    !=|> n;
    t <|= n;
    let h0' = ST.get () in
    lemma_dll_links_contained h0 d (length (reveal d.nodes) - 1);
    lemma_unsnoc_is_last (reveal d.nodes);
    // assert (Mod.loc_disjoint (Mod.loc_buffer (t@h0).blink) (Mod.loc_buffer n));
    t =|> n;
    let h1 = ST.get () in
    //
    let Frag1 p1 = tot_dll_to_fragment h0 d in
    let p = tot_node_to_piece h0 n in
    let f' = Frag2 p1 p in
    piece_remains_valid h0 h0' (Mod.loc_buffer n) p1;
    piece_remains_valid_f h0' h1 p1;
    let y = tot_defragmentable_fragment_to_dll h1 f' in
    y
  )

#reset-options

#set-options "--z3rlimit 1000 --initial_fuel 2 --initial_ifuel 2"

let dll_insert_after (#t:Type) (d:dll t) (e:pointer (node t)) (n:pointer (node t)) :
  StackInline (dll t)
    (requires (fun h0 ->
         (dll_valid h0 d) /\
         (e `memP` reveal d.nodes) /\
         (h0 `contains` n) /\
         (node_not_in_dll h0 n d)))
    (ensures (fun h0 y h1 ->
         Mod.modifies (Mod.loc_union
                         (Mod.loc_union
                            (Mod.loc_buffer n)
                            (Mod.loc_buffer d.ltail))
                         (Mod.loc_union
                            (Mod.loc_buffer e)
                            (Mod.loc_buffer (e@h0).flink))) h0 h1 /\
         dll_valid h1 y)) =
  let h0 = ST.get () in
  // assert (length (reveal d.nodes) > 0);
  lemma_dll_links_contained h0 d (reveal d.nodes `index_of` e);
  extract_nodelist_contained h0 (reveal d.nodes) (reveal d.nodes `index_of` e);
  let e1 = (!*e).blink in
  let e2 = (!*e).flink in
  if is_null e2 then (
    dll_insert_at_tail d n
  ) else (
    extract_nodelist_fp0 (reveal d.nodes) (reveal d.nodes `index_of` e);
    lemma_unsnoc_is_last (reveal d.nodes);
    extract_nodelist_conn h0 (reveal d.nodes) (reveal d.nodes `index_of` e);
    extract_nodelist_fp0 (reveal d.nodes) (reveal d.nodes `index_of` e + 1);
    if not (is_null e1) then (
      extract_nodelist_conn h0 (reveal d.nodes) (reveal d.nodes `index_of` e - 1);
      extract_nodelist_fp0 (reveal d.nodes) (reveal d.nodes `index_of` e - 1)
    ) else ();
    e <|= n;
    // let h' = ST.get () in assert (h' `contains` e2); assert (Mod.loc_disjoint (Mod.loc_buffer n) (Mod.loc_buffer e2));
    n =|> e2;
    let h0' = ST.get () in
    // assert (is_not_null e1 ==> e1 == (reveal d.nodes).[reveal d.nodes `index_of` e - 1]);
    // assert (is_not_null e1 ==> Mod.loc_includes (nodelist_fp0 (reveal d.nodes)) (Mod.loc_buffer e1));
    // assert (is_not_null e1 ==> Mod.loc_disjoint (Mod.loc_buffer n) (Mod.loc_buffer e1));
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (Mod.loc_buffer e1));
    Mod.modifies_buffer_elim e1 (Mod.loc_buffer n) h0 h0';
    e =|> n;
    let h0'' = ST.get () in
    // assert (h0 `contains` e2);
    // assert (h0' `contains` e2);
    // assert (e2 == (reveal d.nodes).[reveal d.nodes `index_of` e + 1]);
    extract_nodelist_aa_r (reveal d.nodes) (reveal d.nodes `index_of` e);
    lemma_split3_r_hd (reveal d.nodes) (reveal d.nodes `index_of` e);
    lemma_split3_append (reveal d.nodes) (reveal d.nodes `index_of` e);
    lemma_split3_index (reveal d.nodes) (reveal d.nodes `index_of` e);
    lemma_split3_length (reveal d.nodes) (reveal d.nodes `index_of` e);
    // assert (Mod.loc_includes (nodelist_fp0 (reveal d.nodes)) (nodelist_fp0 (let _,_,z = split3 (reveal d.nodes) (reveal d.nodes `index_of` e) in z)));
    // assert (Mod.loc_includes (nodelist_fp0 (let _,_,z = split3 (reveal d.nodes) (reveal d.nodes `index_of` e) in z)) (Mod.loc_buffer e2));
    // assert (Mod.loc_disjoint (Mod.loc_buffer e2) (Mod.loc_buffer e));
    // assert (Mod.modifies (Mod.loc_buffer e) h0' h0'');
    Mod.modifies_buffer_elim e2 (Mod.loc_buffer e) h0' h0'';
    // assert (h0'' `contains` e2);
    n <|= e2;
    let h1 = ST.get () in
    //
    // assert (e `memP` reveal d.nodes);
    // assert (e2 `memP` reveal d.nodes);
    // assert (e@h0 |> e2 /\ e <| e2@h0);
    let f = tot_dll_to_fragment_split h0 d e e2 in
    // assert (length f = 2);
    let Frag2 p1 p3 = f in
    // assert ([p1 ; p3] == f);
    let p2 = tot_node_to_piece h0 n in
    let f' = Frag3 p1 p2 p3 in
    // assert (Mod.modifies (Mod.loc_buffer n) h0 h0');
    // assert (piece_valid h0 p1);
    // assert (loc_equiv (dll_fp0 d) (fragment_fp0 f));
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (dll_fp0 d));
    // assert (Mod.loc_includes (dll_fp0 d) (fragment_fp0 f));
    // assert (Mod.loc_includes (fragment_fp0 f) (piece_fp0 p1));
    Mod.loc_includes_trans (dll_fp0 d) (fragment_fp0 f) (piece_fp0 p1);
    // assert (Mod.loc_includes (dll_fp0 d) (piece_fp0 p1));
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (piece_fp0 p1));
    piece_remains_valid h0 h0' (Mod.loc_buffer n) p1;
    // assert (piece_valid h0 p3);
    Mod.loc_includes_trans (dll_fp0 d) (fragment_fp0 f) (piece_fp0 p3);
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (piece_fp0 p3));
    piece_remains_valid h0 h0' (Mod.loc_buffer n) p3;
    piece_remains_valid_f h0' h0'' p1;
    // assert (Mod.loc_disjoint (piece_fp0 p1) (piece_fp0 p3));
    piece_remains_valid h0' h0'' (piece_fp0 p1) p3;
    piece_remains_valid h0'' h1 (piece_fp0 p3) p1;
    piece_remains_valid_b h0'' h1 p3;
    // assert ([p2 ; p3] == append [p2] [p3]);
    // assert (f' == append [p1] [p2 ; p3]);
    //
    // assert (fragment_valid h1 f');
    assert (fragment_defragmentable h1 (Frag2 p2 p3)); // OBSERVE
    // assert (fragment_defragmentable h1 f');
    // assert (length f' > 0);
    // assert (is_null ((hd f').phead@h1).blink);
    // lemma_unsnoc_is_last f';
    // assert (last f' == p3);
    // assert (is_null ((last f').ptail@h1).flink);
    let y = tot_defragmentable_fragment_to_dll h1 f' in
    y
  )

#reset-options

#set-options "--z3rlimit 50"

let dll_insert_before (#t:Type) (d:dll t) (e:pointer (node t)) (n:pointer (node t)) :
  StackInline (dll t)
    (requires (fun h0 ->
         (dll_valid h0 d) /\
         (e `memP` reveal d.nodes) /\
         (h0 `contains` n) /\
         (node_not_in_dll h0 n d)))
    (ensures (fun h0 y h1 ->
         Mod.modifies (Mod.loc_union
                         (Mod.loc_buffer d.lhead)
                         (Mod.loc_union
                            (Mod.loc_union
                               (Mod.loc_buffer n)
                               (Mod.loc_buffer d.ltail)) // this is needed due to using "after"
                                                         // TODO: Figure out a way to remove it
                            (Mod.loc_union
                               (Mod.loc_buffer (e@h0).blink)
                               (Mod.loc_buffer e)))) h0 h1 /\
         dll_valid h1 y)) =
  let h0 = ST.get () in
  extract_nodelist_contained h0 (reveal d.nodes) (reveal d.nodes `index_of` e);
  let e1 = (!*e).blink in
  lemma_dll_links_contained h0 d (reveal d.nodes `index_of` e);
  if is_null e1 then (
    dll_insert_at_head d n
  ) else (
    extract_nodelist_conn h0 (reveal d.nodes) (reveal d.nodes `index_of` e - 1);
    dll_insert_after d e1 n
  )

#reset-options

#set-options "--z3rlimit 20"

let dll_remove_head (#t:Type) (d:dll t) :
  StackInline (dll t)
    (requires (fun h0 ->
         (dll_valid h0 d) /\
         (length (reveal d.nodes) > 0)))
    (ensures (fun h0 y h1 ->
         Mod.modifies (Mod.loc_buffer (d.lhead@h0).flink) h0 h1 /\
         dll_valid h1 y)) =
  let h0 = ST.get () in
  let e = d.lhead in
  let e2 = (!*e).flink in
  if is_null e2 then (
    empty_list
  ) else (
    !<|= e2;
    let h1 = ST.get () in
    let f = tot_dll_to_fragment_split h0 d e e2 in
    let Frag2 p1 p2 = f in
    // assert (p1.phead == e);
    // assert (p1.ptail == e);
    let f' = Frag1 p2 in
    piece_remains_valid_b h0 h1 p2;
    let y = tot_defragmentable_fragment_to_dll h1 f' in
    y
  )

#reset-options

#set-options "--z3rlimit 50"

let dll_remove_tail (#t:Type) (d:dll t) :
  StackInline (dll t)
    (requires (fun h0 ->
         (dll_valid h0 d) /\
         (length (reveal d.nodes) > 0)))
    (ensures (fun h0 y h1 ->
         Mod.modifies (Mod.loc_buffer (d.ltail@h0).blink) h0 h1 /\
         dll_valid h1 y)) =
  let h0 = ST.get () in
  let e = d.ltail in
  let e1 = (!*e).blink in
  lemma_dll_links_contained h0 d (length (reveal d.nodes) - 1);
  lemma_unsnoc_is_last (reveal d.nodes);
  if is_null e1 then (
    empty_list
  ) else (
    extract_nodelist_contained h0 (reveal d.nodes) (length (reveal d.nodes) - 2);
    extract_nodelist_conn h0 (reveal d.nodes) (length (reveal d.nodes) - 2);
    // assert (e == (reveal d.nodes).[length (reveal d.nodes) - 1]);
    // assert (e1 == (reveal d.nodes).[length (reveal d.nodes) - 2]);
    !=|> e1;
    let h1 = ST.get () in
    let f = tot_dll_to_fragment_split h0 d e1 e in
    let Frag2 p1 p2 = f in
    // assert (p2.phead == e);
    // assert (p2.ptail == e);
    let f' = Frag1 p1 in
    piece_remains_valid_f h0 h1 p1;
    let y = tot_defragmentable_fragment_to_dll h1 f' in
    y
  )

#reset-options

#set-options "--z3rlimit 400"

let dll_remove_node (#t:Type) (d:dll t) (e:pointer (node t)) :
  StackInline (dll t)
    (requires (fun h0 ->
         (dll_valid h0 d) /\
         (e `memP` reveal d.nodes)))
    (ensures (fun h0 y h1 ->
         Mod.modifies (Mod.loc_union
                         (Mod.loc_union
                            (Mod.loc_buffer (d.lhead@h0).flink)
                            (Mod.loc_buffer (d.ltail@h0).blink))
                         (Mod.loc_union
                            (Mod.loc_buffer (e@h0).blink)
                            (Mod.loc_buffer (e@h0).flink))) h0 h1 /\
         dll_valid h1 y)) =
  let h0 = ST.get () in
  extract_nodelist_contained h0 (reveal d.nodes) (reveal d.nodes `index_of` e);
  let e1 = (!*e).blink in
  let e2 = (!*e).flink in
  lemma_dll_links_contained h0 d (reveal d.nodes `index_of` e);
  if is_null e1 then (
    dll_remove_head d
  ) else if is_null e2 then (
    dll_remove_tail d
  ) else (
    lemma_dll_links_contained h0 d (reveal d.nodes `index_of` e);
    extract_nodelist_conn h0 (reveal d.nodes) (reveal d.nodes `index_of` e - 1);
    extract_nodelist_aa_r (reveal d.nodes) (reveal d.nodes `index_of` e - 1);
    extract_nodelist_fp0 (reveal d.nodes) (reveal d.nodes `index_of` e);
    lemma_dll_links_disjoint h0 d (reveal d.nodes `index_of` e);
    e1 =|> e2;
    let h0' = ST.get () in
    e1 <|= e2;
    let h1 = ST.get () in
    // assert (e1 == (reveal d.nodes).[reveal d.nodes `index_of` e - 1]);
    // assert (e1 `memP` reveal d.nodes);
    // assert (e1@h0 |> e);
    let f = tot_dll_to_fragment_split h0 d e1 e in
    let Frag2 p1 p2 = f in
    let p2' = tot_piece_tail h0 p2 e2 in
    let f' = Frag2 p1 p2' in
    piece_remains_valid_f h0 h0' p1;
    piece_remains_valid h0' h1 (Mod.loc_buffer e2) p1;
    piece_remains_valid h0 h0' (Mod.loc_buffer e1) p2';
    piece_remains_valid_b h0' h1 p2';
    let y = tot_defragmentable_fragment_to_dll h1 f' in
    // assert (dll_valid h1 y);
    y
  )
