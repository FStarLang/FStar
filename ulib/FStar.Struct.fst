// with: --include ulib --include ulib/hyperstack

module FStar.Struct

module DM = FStar.DependentMap
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module HST = FStar.ST

private type struct (key: eqtype) (value: key -> Tot Type) =
  | MkStruct:
    (content: HS.reference (DM.t key value)) ->
    struct key value

noeq type struct_ptr : Type -> Tot Type =
| StructPtrNil:
  (#key: eqtype) ->
  (#value: (key -> Tot Type)) ->
  (s: struct key value) ->
  struct_ptr (DM.t key value)
| StructPtrCons:
  (#key: eqtype) ->
  (#value: (key -> Tot Type)) ->
  (p: struct_ptr (DM.t key value)) ->
  (field: key) ->
  struct_ptr (value field)

abstract let field
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (p: struct_ptr (DM.t key value))
  (fd: key)
: Tot (struct_ptr (value fd))
= StructPtrCons p fd

private let rec root
  (#value: Type)
  (p: struct_ptr value)
: Tot (key: eqtype & (value: (key -> Tot Type) & HS.reference (DM.t key value)))
= match p with
  | StructPtrNil #k #v s -> (| k, (| v, s.content |) |)
  | StructPtrCons p' _ -> root p'

abstract let contains
  (#value: Type)
  (h: HS.mem)
  (p: struct_ptr value)
: GTot Type0
= let (| k, (| v, s |) |) = root p in HS.contains h s

abstract let contains_field
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (h: HS.mem)
  (p: (struct_ptr (DM.t key value)))
  (fd: key)
: Lemma
  (requires True)
  (ensures (contains h (field p fd) <==> contains h p))
  [SMTPat (contains h (field p fd))]
= ()

abstract let rec sel
  (#value: Type)
  (h: HS.mem)
  (p: struct_ptr value {contains h p}) 
: GTot value
= match p with
  | StructPtrNil s ->
    HS.sel h s.content
  | StructPtrCons p' field ->
    DM.sel (sel h p') field

abstract let sel_field
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (h: HS.mem)
  (p: struct_ptr (DM.t key value) {contains h p})
  (fd: key)
: Lemma
  (requires True)
  (ensures (sel h (field p fd) == DM.sel (sel h p) fd))
  [SMTPat (sel h (field p fd))]
= ()

abstract let rec frameOf 
  (#value: Type)
  (p: struct_ptr value)
: GTot HH.rid
= let (| k, (| v, s |) |) = root p in HS.frameOf s

abstract let frameOf_field
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (p: struct_ptr (DM.t key value))
  (fd: key)
: Lemma
  (requires True)
  (ensures (frameOf (field p fd) == frameOf p))
  [SMTPat (frameOf (field p fd))]
= ()

abstract let live
  (#value: Type)
  (h: HS.mem)
  (p: struct_ptr value)
: GTot Type0
= contains h p

abstract let live_field
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (h: HS.mem)
  (p: struct_ptr (DM.t key value))
  (fd: key)
: Lemma
  (requires True)
  (ensures (live h (field p fd) <==> live h p))
  [SMTPat (live h (field p fd))]
= ()

abstract let rec memory_managed
  (#value: Type)
  (p: struct_ptr value)
: GTot bool
= let (| k, (| v, s |) |) = root p in s.HS.mm

abstract let memory_managed_field
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (p: struct_ptr (DM.t key value))
  (fd: key)
: Lemma
  (requires True)
  (ensures (memory_managed (field p fd) <==> memory_managed p))
  [SMTPat (memory_managed (field p fd))]
= ()

abstract let rec recall
  (#value: Type)
  (p: struct_ptr value {HS.is_eternal_region (frameOf p) && not (memory_managed p)})
: HST.Stack unit
  (requires (fun m -> True))
  (ensures (fun m0 _ m1 -> m0 == m1 /\ live m1 p))
=  let (| k, (| v, s |) |) = root p in HST.recall s

(* TODO: recall_field *)

let get
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (h: HS.mem)
  (p: struct_ptr (DM.t key value) {live h p})
  (field: key)
: GTot (value field)
= DM.sel (sel h p) field

noeq private type includes_t:
  (#value1: Type) ->
  (#value2: Type) ->
  (p1: struct_ptr value1) ->
  (p2: struct_ptr value2) ->
  Type
= | IncludesField:
    (#key: eqtype) ->
    (#value: (key -> Tot Type)) ->
    (p: struct_ptr (DM.t key value)) ->
    (fd: key) ->
    includes_t p (field p fd)
  | IncludesRefl:
    (#value: Type) ->
    (p: struct_ptr value) ->
    includes_t p p
  | IncludesTrans:
    (#value1: Type) ->
    (#value2: Type) ->
    (#value3: Type) ->
    (p1: struct_ptr value1) ->
    (p2: struct_ptr value2) ->
    (p3: struct_ptr value3) ->
    includes_t p1 p2 ->
    includes_t p2 p3 ->
    includes_t p1 p3

private let rec includes_t_rect
  (x: (#value1: Type) ->
      (#value2: Type) ->
      (p1: struct_ptr value1) ->
      (p2: struct_ptr value2) ->
      includes_t p1 p2 ->
      GTot Type)
  (h_field:
    (#key: eqtype) ->
    (#value: (key -> Tot Type)) ->
    (p: struct_ptr (DM.t key value)) ->
    (fd: key) ->
    (h: includes_t p (field p fd)) ->
    GTot (x p (field p fd) h))
  (h_refl:
    (#value: Type) ->
    (p: struct_ptr value) ->
    (h: includes_t p p) ->
    GTot (x p p h))
  (h_trans:
    (#value1: Type) ->
    (#value2: Type) ->
    (#value3: Type) ->
    (p1: struct_ptr value1) ->
    (p2: struct_ptr value2) ->
    (p3: struct_ptr value3) ->
    (h12: includes_t p1 p2) ->
    (h23: includes_t p2 p3) ->
    (h13: includes_t p1 p3) ->
    x p1 p2 h12 ->
    x p2 p3 h23 ->
    GTot (x p1 p3 h13))
  (#value1: Type)
  (#value2: Type)
  (p1: struct_ptr value1)
  (p2: struct_ptr value2)
  (h: includes_t p1 p2)
: Ghost (x p1 p2 h)
  (requires True)
  (ensures (fun _ -> True))
  (decreases h)
= match h with
  | IncludesField p fd -> h_field p fd h
  | IncludesRefl p -> h_refl p h
  | IncludesTrans p1 p2 p3 h12 h23 ->
    h_trans p1 p2 p3 h12 h23 h
      (includes_t_rect x h_field h_refl h_trans p1 p2 h12)
      (includes_t_rect x h_field h_refl h_trans p2 p3 h23)

abstract let includes
  (#value1: Type)
  (#value2: Type)
  ($p1: struct_ptr value1)
  ($p2: struct_ptr value2)
: GTot Type0
= squash (includes_t p1 p2)

abstract let rec includes_ind
  (x: (#value1: Type) ->
      (#value2: Type) ->
      (p1: struct_ptr value1) ->
      (p2: struct_ptr value2 {includes p1 p2} ) ->
      GTot Type0)
  (h_field:
    (#key: eqtype) ->
    (#value: (key -> Tot Type)) ->
    (p: struct_ptr (DM.t key value)) ->
    (fd: key {includes p (field p fd)}) ->
    Lemma (x p (field p fd)))
  (h_refl:
    (#value: Type) ->
    (p: struct_ptr value {includes p p}) ->
    Lemma (x p p))
  (h_trans:
    (#value1: Type) ->
    (#value2: Type) ->
    (#value3: Type) ->
    (p1: struct_ptr value1) ->
    (p2: struct_ptr value2) ->
    (p3: struct_ptr value3 {includes p1 p2 /\ includes p2 p3 /\ includes p1 p3 /\ x p1 p2 /\ x p2 p3}) ->
    Lemma (x p1 p3))
  (#value1: Type)
  (#value2: Type)
  (p1: struct_ptr value1)
  (p2: struct_ptr value2 {includes p1 p2})
: Lemma (x p1 p2)
=
  let h : squash (includes_t p1 p2) = FStar.Squash.join_squash () in
  FStar.Squash.bind_squash h (fun (h: includes_t p1 p2) ->
   includes_t_rect
     (fun #v1 #v2 p1 p2 h -> let _ = FStar.Squash.return_squash h in squash (x p1 p2))
     (fun #k #v p fd h -> let _ = FStar.Squash.return_squash h in h_field p fd)
     (fun #v p h -> let _ = FStar.Squash.return_squash h in h_refl p)
     (fun #v1 #v2 #v3 p1 p2 p3 h12 h23 h13 hx12 hx23 ->
       let _ = FStar.Squash.return_squash h12 in
       let _ = FStar.Squash.return_squash h23 in
       let _ = FStar.Squash.return_squash h13 in
       let _ = FStar.Squash.return_squash hx12 in
       let _ = FStar.Squash.return_squash hx23 in
       h_trans p1 p2 p3)
     p1 p2 h)

abstract let includes_field
  (#key: eqtype)
  (#value: (key -> Tot Type))
  ($p: struct_ptr (DM.t key value))
  (fd: key)
: Lemma
  (requires True)
  (ensures (includes p (field p fd)))
  [SMTPat (includes p (field p fd))]
= FStar.Squash.return_squash (IncludesField p fd)

abstract let includes_refl
  (#value: Type)
  ($p: struct_ptr value)
: Lemma
  (requires True)
  (ensures (includes p p))
  [SMTPat (includes p p)]
= FStar.Squash.return_squash (IncludesRefl p)

abstract let includes_trans
  (#value1 #value2 #value3: Type)
  ($p1: struct_ptr value1)
  ($p2: struct_ptr value2)
  ($p3: struct_ptr value3)
: Lemma
  (requires (includes p1 p2 /\ includes p2 p3))
  (ensures (includes p1 p3))
= let h12 : squash (includes_t p1 p2) = FStar.Squash.join_squash () in
  let h23 : squash (includes_t p2 p3) = FStar.Squash.join_squash () in
  FStar.Squash.bind_squash h12 (fun k12 ->
   FStar.Squash.bind_squash h23 (fun k23 ->
    FStar.Squash.return_squash (IncludesTrans p1 p2 p3 k12 k23)))

private let root_includes
  (#value1: Type)
  (#value2: Type)
  (p1: struct_ptr value1)
  (p2: struct_ptr value2 {includes p1 p2})
: Lemma (root p1 == root p2)
= includes_ind
  (fun #v1 #v2 p1 p2 -> root p1 == root p2)
  (fun #k #v p fd -> ())
  (fun #v p -> ())
  (fun #v1 #v2 #v3 p1 p2 p3 -> ())
  p1 p2

let contains_includes
  (#value1: Type)
  (#value2: Type)
  (h: HS.mem)
  (p1: struct_ptr value1)
  (p2: struct_ptr value2 {includes p1 p2})
: Lemma (contains h p1 <==> contains h p2)
= includes_ind
  (fun #v1 #v2 p1 p2 -> contains h p1 <==> contains h p2)
  (fun #k #v p fd -> contains_field h p fd)
  (fun #v p -> ())
  (fun #v1 #v2 #v3 p1 p2 p3 -> ())
  p1 p2

(* WIP

noeq private type disjoint_t:
  (#value1: Type) ->
  (#value2: Type) ->
  (p1: struct_ptr value1) ->
  (p2: struct_ptr value2) ->
  Type
= | DisjointRoot:
    (#value1: Type) ->
    (#value2: Type) ->
    ($p1: struct_ptr value1) ->
    ($p2: struct_ptr value2 { exists h . ~ (contains h p1 <==> contains h p2) } ) ->
    disjoint_t p1 p2
  | DisjointField:
    (#value1: Type) ->
    (#key2: eqtype) ->
    (#value2: (key2 -> Tot Type)) ->
    ($p1: struct_ptr value1) ->
    ($p2: struct_ptr (DM.t key2 value2)) ->
    disjoint_t p1 p2 ->
    (field2: key2) ->
    disjoint_t p1 (field p2 fd) 
  | DisjointFieldField:
    (#key: eqtype) ->
    (#value: (key -> Tot Type)) ->
    ($p: struct_ptr (DM.t key value)) ->
    (fd1: key) ->
    (fd2: key { fd1 <> fd2 } ) ->
    disjoint_t (field p fd1) (field p fd2)
  | DisjointIncludes:
    (#value1: Type) ->
    (#value2: Type) ->
    ($p1: struct_ptr value1) ->
    ($p2: struct_ptr value2 { exists h . ~ (contains h p1 <==> contains h p2) } ) ->
    disjoint_t p1 p2
*)  
