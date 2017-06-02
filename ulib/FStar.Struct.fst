// with: --include ulib --include ulib/hyperstack

module FStar.Struct
open FStar.HyperStack.ST
module DM = FStar.DependentMap
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

(** Paths within nested dependent maps *)

noeq private type path (from: Type) : (to: Type) -> Tot Type =
  | PathBase:
    path from from
  | PathField:
    (#key: eqtype) ->
    (#value: ((k: key) -> Tot Type)) ->
    (p: path from (DM.t key value)) ->
    (fd: key) ->
    path from (value fd)

private let rec path_sel
  (#from: Type)
  (#to: Type)
  (m: from)
  (p: path from to)
: Tot to
= match p with
  | PathBase -> m
  | PathField p' fd -> DM.sel (path_sel m p') fd

private let rec path_upd
  (#from: Type)
  (#to: Type)
  (m: from)
  (p: path from to)
  (v: to)
: Tot from
= match p with
  | PathBase -> v
  | PathField p' fd ->
    let s = path_sel m p' in
    let s' = DM.upd s fd v in
    path_upd m p' s'

private let rec path_sel_upd_same
  (#from: Type)
  (#to: Type)
  (m: from)
  (p: path from to)
  (v: to)
: Lemma
  (requires True)
  (ensures (path_sel (path_upd m p v) p == v))
  [SMTPat (path_sel (path_upd m p v) p)]
= match p with
  | PathBase -> ()
  | PathField p' fd ->
    let s = path_sel m p' in
    let s' = DM.upd s fd v in
    DM.sel_upd_same s fd v;
    path_sel_upd_same m p' s'

private let rec path_concat
  (#from: Type)
  (#through: Type)
  (#to: Type)
  (p: path from through)
  (q: path through to)
: Pure (path from to)
  (requires True)
  (ensures (fun _ -> True))
  (decreases q)
= match q with
  | PathBase -> p
  | PathField q' fd -> PathField (path_concat p q') fd

private let path_concat_base_r
  (#from: Type)
  (#to: Type)
  (p: path from to)
: Lemma
  (ensures (path_concat p PathBase == p))
= ()

private let rec path_concat_base_l
  (#from: Type)
  (#to: Type)
  (p: path from to)
: Lemma
  (requires True)
  (ensures (path_concat PathBase p == p))
  [SMTPat (path_concat PathBase p)]
= match p with
  | PathBase -> ()
  | PathField p' fd -> path_concat_base_l p'

private let rec path_concat_assoc
  (#t0 #t1 #t2 #t3: Type)
  (p01: path t0 t1)
  (p12: path t1 t2)
  (p23: path t2 t3)
: Lemma
  (requires True)
  (ensures (path_concat (path_concat p01 p12) p23 == path_concat p01 (path_concat p12 p23)))
  (decreases p23)
= match p23 with
  | PathBase -> ()
  | PathField p23' fd -> path_concat_assoc p01 p12 p23'

private let rec path_sel_concat
  (#from: Type)
  (#through: Type)
  (#to: Type)
  (m: from)
  (p: path from through)
  (q: path through to)
: Lemma
  (requires True)
  (ensures (path_sel m (path_concat p q) == path_sel (path_sel m p) q))
  (decreases q)
  [SMTPat (path_sel m (path_concat p q))]
= match q with
  | PathBase -> ()
  | PathField q' fd -> path_sel_concat m p q'

private let rec path_upd_concat
  (#from: Type)
  (#through: Type)
  (#to: Type)
  (m: from)
  (p: path from through)
  (q: path through to)
  (v: to)
: Lemma
  (requires True)
  (ensures (path_upd m (path_concat p q) v == path_upd m p (path_upd (path_sel m p) q v)))
  (decreases q)
  [SMTPat (path_upd m (path_concat p q) v)]
= match q with
  | PathBase -> ()
  | PathField q' fd ->
    let s = path_sel m (path_concat p q') in
    let s' = DM.upd s fd v in
    path_upd_concat m p q' s'

// TODO: rename as: prefix_of; use infix notation (p1 `prefix_of` p2)
private let rec path_includes
  (#from: Type)
  (#to1 #to2: Type)
  (p1: path from to1)
  (p2: path from to2)
: Ghost Type0
  (requires True)
  (ensures (fun _ -> True))
  (decreases p2)
= (to1 == to2 /\ p1 == p2) \/ (match p2 with
  | PathBase -> False
  | PathField p2' _ ->
    path_includes p1 p2'
  )

private let rec path_includes_base
  (#from: Type)
  (#to: Type)
  (p: path from to)
: Lemma
  (requires True)
  (ensures (path_includes (PathBase #from) p))
  [SMTPat (path_includes PathBase p)]
= match p with
  | PathBase -> ()
  | PathField p2' _ -> path_includes_base p2'

private let path_includes_refl
  (#from #to: Type)
  (p: path from to)
: Lemma
  (requires True)
  (ensures (path_includes p p))
  [SMTPat (path_includes p p)]
= ()

private let path_includes_field_r
  (#from: Type)
  (#key: eqtype)
  (#value: ((k: key) -> Tot Type))
  (p: path from (DM.t key value))
  (fd: key)
: Lemma
  (requires True)
  (ensures (path_includes p (PathField p fd)))
  [SMTPat (path_includes p (PathField p fd))]
= ()

private let rec path_includes_trans
  (#from #to1 #to2 #to3: Type)
  (p1: path from to1)
  (p2: path from to2)
  (p3: path from to3  {path_includes p1 p2 /\ path_includes p2 p3})
: Lemma
  (requires True)
  (ensures (path_includes p1 p3))
  (decreases p3)
= FStar.Classical.or_elim
    #(to2 == to3 /\ p2 == p3)
    #(match p3 with
      | PathBase -> False
      | PathField p3' _ ->
	path_includes p2 p3')
    #(fun _ -> path_includes p1 p3)
    (fun _ -> ())
    (fun _ -> match p3 with
      | PathBase -> assert False
      | PathField p3' _ ->
	path_includes_trans p1 p2 p3'
    )

private let rec path_includes_ind
  (#from: Type)
  (x: (#to1: Type) ->
      (#to2: Type) ->
      (p1: path from to1) ->
      (p2: path from to2 {path_includes p1 p2} ) ->
      GTot Type0)
  (h_field:
    (#key: eqtype) ->
    (#value: (key -> Tot Type)) ->
    (p: path from (DM.t key value)) ->
    (fd: key {path_includes p (PathField p fd)}) ->
    Lemma (x p (PathField p fd)))
  (h_refl:
    (#to: Type) ->
    (p: path from to {path_includes p p}) ->
    Lemma (x p p))
  (h_trans:
    (#to1: Type) ->
    (#to2: Type) ->
    (#to3: Type) ->
    (p1: path from to1) ->
    (p2: path from to2) ->
    (p3: path from to3 {path_includes p1 p2 /\ path_includes p2 p3 /\ path_includes p1 p3 /\ x p1 p2 /\ x p2 p3}) ->
    Lemma (x p1 p3))
  (#to1: Type)
  (#to2: Type)
  (p1: path from to1)
  (p2: path from to2 {path_includes p1 p2})
: Lemma
  (requires True)
  (ensures (x p1 p2))
  (decreases p2)
= FStar.Classical.or_elim
    #(to1 == to2 /\ p1 == p2)
    #(match p2 with
      | PathBase -> False
      | PathField p' fd -> path_includes p1 p')
    #(fun _ -> x p1 p2)
    (fun _ -> h_refl p1)
    (fun _ -> match p2 with
     | PathBase -> assert False
     | PathField p2' fd ->
       let _ = path_includes_ind x h_field h_refl h_trans p1 p2' in
       let _ = path_includes_field_r p2' fd in
       let _ = h_field p2' fd in
       h_trans p1 p2' p2
    )

private let rec path_length
  (#from #to: Type)
  (p: path from to)
: Tot nat
= match p with
  | PathBase -> 0
  | PathField p' _ -> 1 + path_length p'

private let path_includes_length
  (#from: Type)
  (#to1 #to2: Type)
  (p1: path from to1)
  (p2: path from to2 {path_includes p1 p2})
: Lemma
  (ensures (path_length p1 <= path_length p2))
= path_includes_ind
    (fun #to1_ #to2_ p1_ p2_ -> path_length p1_ <= path_length p2_)
    (fun #k #v p fd -> ())
    (fun #to p -> ())
    (fun #to1_ #to2_ #to3_ p1_ p2_ p3_ -> ())
    p1 p2

private let path_includes_field_l
  (#from: Type)
  (#key: eqtype)
  (#value: ((k: key) -> Tot Type))
  (p: path from (DM.t key value))
  (fd: key)
: Lemma
  (requires True)
  (ensures (~ (path_includes (PathField p fd) p)))
  [SMTPat (path_includes (PathField p fd) p)]
= assert (path_length (PathField p fd) > path_length p);
  FStar.Classical.forall_intro (path_includes_length #from #(value fd) #(DM.t key value) (PathField p fd))

private let rec path_includes_concat
  (#from: Type)
  (#through: Type)
  (#to: Type)
  (p: path from through)
  (q: path through to)
: Lemma
  (requires True)
  (ensures (path_includes p (path_concat p q)))
  (decreases q)
  [SMTPat (path_includes p (path_concat p q))]
= match q with
  | PathBase -> ()
  | PathField q' fd -> path_includes_concat p q'

private let path_includes_exists_concat
  (#from #through: Type)
  (p: path from through)
  (#to: Type)
  (q: path from to { path_includes p q } )
: Lemma
  (ensures (exists (r: path through to) . q == path_concat p r))
= path_includes_ind
    (fun #to1_ #to2_ p1_ p2_ -> exists r . p2_ == path_concat p1_ r)
    (fun #k #v p fd -> FStar.Classical.exists_intro (fun r -> PathField p fd == path_concat p r) (PathField PathBase fd))
    (fun #to p -> FStar.Classical.exists_intro (fun r -> p == path_concat p r) PathBase)
    (fun #to1_ #to2_ #to3_ p1_ p2_ p3_ ->
      FStar.Classical.exists_elim  (exists r . p3_ == path_concat p1_ r) #_ #(fun r12 -> p2_ == path_concat p1_ r12) () (fun r12 ->
	FStar.Classical.exists_elim (exists r . p3_ == path_concat p1_ r) #_ #(fun r23 -> p3_ == path_concat p2_ r23) () (fun r23 ->
	  path_concat_assoc p1_ r12 r23;
	  FStar.Classical.exists_intro (fun r -> p3_ == path_concat p1_ r) (path_concat r12 r23)
	)
      )
    )
    p q
  
noeq private type path_disjoint_t (#from: Type):
  (#to1: Type) ->
  (#to2: Type) ->
  (p1: path from to1) ->
  (p2: path from to2) ->
  Type
= | PathDisjointField:
    (#key: eqtype) ->
    (#value: (key -> Tot Type)) ->
    (p: path from (DM.t key value)) ->
    (fd1: key) ->
    (fd2: key { fd1 <> fd2 } ) ->
    path_disjoint_t (PathField p fd1) (PathField p fd2)
  | PathDisjointIncludes:
    (#to1: Type) ->
    (#to2: Type) ->
    (p1: path from to1) ->
    (p2: path from to2) ->
    (#to1': Type) ->
    (#to2': Type) ->
    (p1': path from to1' {path_includes p1 p1'}) ->
    (p2': path from to2' {path_includes p2 p2'}) ->
    path_disjoint_t p1 p2 ->
    path_disjoint_t p1' p2'

private let rec path_disjoint_t_rect
  (#from: Type)
  (x:
    (#value1: Type) ->
    (#value2: Type) ->
    (p1: path from value1) ->
    (p2: path from value2) ->
    (h: path_disjoint_t p1 p2) ->
    GTot Type)
  (h_field:
    (#key: eqtype) ->
    (#value: (key -> Tot Type)) ->
    (p: path from (DM.t key value)) ->
    (fd1: key) ->
    (fd2: key { fd1 <> fd2 } ) ->
    (h: path_disjoint_t (PathField p fd1) (PathField p fd2)) ->
    GTot (x (PathField p fd1) (PathField p fd2) h))
  (h_includes:
    (#value1: Type) ->
    (#value2: Type) ->
    (p1: path from value1) ->
    (p2: path from value2) ->
    (#value1': Type) ->
    (#value2': Type) ->
    (p1': path from value1' {path_includes p1 p1'}) ->
    (p2': path from value2' {path_includes p2 p2'}) ->
    (h: path_disjoint_t p1 p2) ->
    (h': path_disjoint_t p1' p2') ->
    (ihx: x p1 p2 h) ->
    GTot (x p1' p2' h'))
  (#value1: Type)
  (#value2: Type)
  (p1: path from value1)
  (p2: path from value2)
  (h: path_disjoint_t p1 p2)
: Ghost (x p1 p2 h)
  (requires True)
  (ensures (fun _ -> True))
  (decreases h)
= match h with
  | PathDisjointField p fd1 fd2 -> h_field p fd1 fd2 h
  | PathDisjointIncludes p1_ p2_ p1' p2' h_ -> h_includes p1_ p2_ p1' p2' h_ h (path_disjoint_t_rect x h_field h_includes p1_ p2_ h_)
  
private let path_disjoint
  (#from: Type)
  (#value1: Type)
  (#value2: Type)
  (p1: path from value1)
  (p2: path from value2)
: GTot Type0
= squash (path_disjoint_t p1 p2)

abstract let path_disjoint_ind
  (#from: Type)
  (x:
    (#value1: Type) ->
    (#value2: Type) ->
    (p1: path from value1) ->
    (p2: path from value2 {path_disjoint p1 p2} ) ->
    GTot Type0)
  (h_field:
    (#key: eqtype) ->
    (#value: (key -> Tot Type)) ->
    (p: path from (DM.t key value)) ->
    (fd1: key) ->
    (fd2: key { fd1 <> fd2 /\ path_disjoint (PathField p fd1) (PathField p fd2) } ) ->
    Lemma (x (PathField p fd1) (PathField p fd2)))
  (h_includes:
    (#value1: Type) ->
    (#value2: Type) ->
    (p1: path from value1) ->
    (p2: path from value2) ->
    (#value1': Type) ->
    (#value2': Type) ->
    (p1': path from value1' {path_includes p1 p1'}) ->
    (p2': path from value2' {path_includes p2 p2' /\ path_disjoint p1 p2 /\ path_disjoint p1' p2' /\ x p1 p2}) ->
    Lemma (x p1' p2'))
  (#value1: Type)
  (#value2: Type)
  (p1: path from value1)
  (p2: path from value2 { path_disjoint p1 p2 } )
: Lemma (x p1 p2)
= let h : squash (path_disjoint_t p1 p2) = FStar.Squash.join_squash () in
  FStar.Squash.bind_squash h (fun (h: path_disjoint_t p1 p2) ->
   path_disjoint_t_rect
     (fun #v1 #v2 p1 p2 h -> let _ = FStar.Squash.return_squash h in squash (x p1 p2))
     (fun #k #v p fd1 fd2 h -> let _ = FStar.Squash.return_squash h in h_field p fd1 fd2)
     (fun #v1 #v2 p1 p2 #v1' #v2' p1' p2' h h' hx ->
       let _ = FStar.Squash.return_squash h in
       let _ = FStar.Squash.return_squash h' in
       let _ = FStar.Squash.return_squash hx in
       h_includes p1 p2 p1' p2')
     p1 p2 h)

private let path_disjoint_field
  (#from: Type)
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (p: path from (DM.t key value))
  (fd1: key)
  (fd2: key {fd1 <> fd2})
: Lemma
  (requires True)
  (ensures (path_disjoint (PathField p fd1) (PathField p fd2)))
  [SMTPat (path_disjoint (PathField p fd1) (PathField p fd2))]
= FStar.Squash.return_squash (PathDisjointField p fd1 fd2)

private let path_disjoint_includes
  (#from: Type)
  (#to1: Type)
  (#to2: Type)
  (p1: path from to1)
  (p2: path from to2)
  (#to1': Type)
  (#to2': Type)
  (p1': path from to1')
  (p2': path from to2' {path_disjoint p1 p2 /\ path_includes p1 p1' /\ path_includes p2 p2'} )
: Lemma
  (ensures (path_disjoint p1' p2'))
= let h : squash (path_disjoint_t p1 p2) = FStar.Squash.join_squash () in
  FStar.Squash.bind_squash h (fun h -> FStar.Squash.return_squash (PathDisjointIncludes p1 p2 p1' p2' h))

let rec path_disjoint_sym
  (#from: Type)
  (#value1: Type)
  (#value2: Type)
  (p1: path from value1)
  (p2: path from value2)
: Lemma
  (requires (path_disjoint p1 p2))
  (ensures (path_disjoint p2 p1))
= path_disjoint_ind
  (fun #v1 #v2 p1 p2 -> path_disjoint p2 p1)
  (fun #k #v p fd1 fd2 -> path_disjoint_field p fd2 fd1)
  (fun #v1 #v2 p1 p2 #v1' #v2' p1' p2' -> path_disjoint_includes p2 p1 p2' p1')
  p1 p2

private let path_sel_upd_other
  (#from: Type)
  (#to1 #to2: Type)
  (p1: path from to1)
  (p2: path from to2 {path_disjoint p1 p2})
: Lemma
  (ensures (forall (m: from) (v: to1) . path_sel (path_upd m p1 v) p2 == path_sel m p2))
= path_disjoint_ind
  (fun #v1 #v2 p1_ p2_ -> forall (m: from) (v: v1) . path_sel (path_upd m p1_ v) p2_ == path_sel m p2_)
  (fun #ke #va p fd1 fd2 -> 
      FStar.Classical.forall_intro' #_ #(fun m -> forall  (v: va fd1) . path_sel (path_upd m (PathField p fd1) v) (PathField p fd2) == path_sel m (PathField p fd2)) (fun m ->
	  FStar.Classical.forall_intro' #_ #(fun v -> path_sel (path_upd m (PathField p fd1) v) (PathField p fd2) == path_sel m (PathField p fd2)) (fun v ->
	  path_sel_upd_same m p (DM.upd (path_sel m p) fd1 v);
	  DM.sel_upd_other (path_sel m p) fd1 v fd2)
      ))
  (fun #v1 #v2 p1 p2 #v1' #v2' p1' p2' ->
    let h1: squash (exists r1 . p1' == path_concat p1 r1) = path_includes_exists_concat p1 p1' in
    let h2: squash (exists r2 . p2' == path_concat p2 r2) = path_includes_exists_concat p2 p2' in
    FStar.Classical.forall_intro' #_ #(fun (m: from) -> forall v . path_sel (path_upd m p1' v) p2' == path_sel m p2') (fun (m: from) ->
      FStar.Classical.forall_intro' #_ #(fun (v: v1') -> path_sel (path_upd m p1' v) p2' == path_sel m p2') (fun (v: v1') ->
      FStar.Classical.exists_elim (path_sel (path_upd m p1' v) p2' == path_sel m p2') h1 (fun r1 ->
	FStar.Classical.exists_elim (path_sel (path_upd m p1' v) p2' == path_sel m p2') h2 (fun r2 ->
	  path_upd_concat m p1 r1 v;
	  path_sel_concat m p2 r2
	  )))))
  p1 p2

private let path_sel_upd_other'
  (#from: Type)
  (#to1 #to2: Type)
  (p1: path from to1)
  (p2: path from to2 {path_disjoint p1 p2})
  (m: from)
  (v: to1)
: Lemma
  (requires True)
  (ensures (path_sel (path_upd m p1 v) p2 == path_sel m p2))
  [SMTPat (path_sel (path_upd m p1 v) p2)]
= path_sel_upd_other p1 p2

(** Pointers into nested structures *)

noeq private type _struct_ptr : Type -> Tot Type =
  | StructPtr:
    (#from: Type) ->
    (content: Buffer.buffer from { Buffer.length content == 1 } ) ->
    (#to: Type) ->
    (p: path from to) ->
    _struct_ptr to
abstract let struct_ptr (t: Type): Tot Type =
  _struct_ptr t

let as_buffer_type (#t: Type) (s: struct_ptr t): GTot Type =
  StructPtr?.from s

let as_buffer (#t: Type) (s: struct_ptr t):
  Ghost (Buffer.buffer (as_buffer_type s))
  (requires True)
  (ensures (fun b -> Buffer.length b == 1))
= StructPtr?.content s

private let _field
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (p: struct_ptr (DM.t key value))
  (fd: key)
: Tot (struct_ptr (value fd))
= let (StructPtr #from content p') = p in
  let p' : path from (DM.t key value) = p' in
  let p'' : path from (value fd) = PathField p' fd in
  StructPtr content p''

let as_addr
  (#value: Type)
  (p: struct_ptr value)
: GTot nat
= Buffer.as_addr (as_buffer p)

let contains
  (#value: Type)
  (h: HS.mem)
  (p: struct_ptr value)
: GTot Type0
= Buffer.contains h (as_buffer p)

let unused_in
  (#value: Type)
  (p: struct_ptr value)
  (h: HS.mem)
: GTot Type0
= Buffer.unused_in (as_buffer p) h

let live
  (#value: Type)
  (h: HS.mem)
  (p: struct_ptr value)
: GTot Type0
= Buffer.live h (as_buffer p)

let unmapped_in
  (#value: Type)
  (p: struct_ptr value)
  (h: HS.mem)
: GTot Type0
= Buffer.unmapped_in (as_buffer p) h

abstract let live_contains
  (#value: Type)
  (h: HS.mem)
  (p: struct_ptr value)
: Lemma
  (requires (live h p))
  (ensures (contains h p))
  [SMTPatT (live h p)]
= () 

abstract let as_value
  (#value: Type)
  (h: HS.mem)
  (p: struct_ptr value {live h p (* required by Buffer.get, really? *) }) 
: GTot value
= let (StructPtr content p') = p in
  path_sel (Buffer.get h content 0) p'

let frameOf 
  (#value: Type)
  (p: struct_ptr value)
: GTot HH.rid
= Buffer.frameOf (as_buffer p)

let memory_managed
  (#value: Type)
  (p: struct_ptr value)
: GTot bool
= HS.is_mm (Buffer.content (as_buffer p))

abstract let recall
  (#value: Type)
  (p: struct_ptr value {HS.is_eternal_region (frameOf p) && not (memory_managed p)})
: HST.Stack unit
  (requires (fun m -> True))
  (ensures (fun m0 _ m1 -> m0 == m1 /\ live m1 p))
= assert (HS.is_mm (Buffer.content (as_buffer p)) = HS.is_mm (Buffer.content (StructPtr?.content p)));
  Buffer.recall (StructPtr?.content p)

let get
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (h: HS.mem)
  (p: struct_ptr (DM.t key value) {live h p})
  (field: key)
: GTot (value field)
= DM.sel (as_value h p) field

(* Equality predicate on struct contents, without quantifiers *)
let equal_values #a h (b:struct_ptr a) h' (b':struct_ptr a) : GTot Type0 =
  live h b /\ live h' b' /\ as_value h b == as_value h' b'

abstract let includes
  (#value1: Type)
  (#value2: Type)
  (p1: struct_ptr value1)
  (p2: struct_ptr value2)
: GTot Type0
= StructPtr?.from p1 == StructPtr?.from p2 /\ as_buffer p1 == as_buffer p2 /\ path_includes (StructPtr?.p p1) (StructPtr?.p p2)

abstract let as_buffer_includes
  (#value1: Type)
  (#value2: Type)
  (p1: struct_ptr value1)
  (p2: struct_ptr value2)
: Lemma
  (requires (includes p1 p2))
  (ensures (as_buffer_type p1 == as_buffer_type p2 /\ as_buffer p1 == as_buffer p2))
= ()

private let _from_buffer_index
  (#value: Type)
  (p: Buffer.buffer value)
  (i: nat{i < Buffer.length p})
: Tot (struct_ptr value)
= StructPtr (Buffer.sub p (UInt32.uint_to_t i) (UInt32.uint_to_t 1)) PathBase

abstract let gfrom_buffer_index
  (#value: Type)
  (p: Buffer.buffer value)
  (i: nat{i < Buffer.length p})
: GTot (struct_ptr value)
= _from_buffer_index p i

abstract let live_gfrom_buffer_index
  (#value: Type)
  (h: HS.mem)
  (p: Buffer.buffer value)
  (i: nat{i < Buffer.length p})
: Lemma
  (requires (Buffer.live h p))
  (ensures (live h (gfrom_buffer_index p i)))
  [SMTPat (live h (gfrom_buffer_index p i))]
= ()

abstract let contains_gfrom_buffer_index
  (#value: Type)
  (h: HS.mem)
  (p: Buffer.buffer value)
  (i: nat{i < Buffer.length p})
: Lemma
  (requires (Buffer.contains h p))
  (ensures (contains h (gfrom_buffer_index p i)))
  [SMTPat (contains h (gfrom_buffer_index p i))]
= ()

abstract let as_buffer_gfrom_buffer_index
  (#value: Type)
  (p: Buffer.buffer value)
  (i: nat{i < Buffer.length p})
: Lemma
  (as_buffer_type (gfrom_buffer_index p i) == value /\ as_buffer (gfrom_buffer_index p i) == Buffer.sub p (UInt32.uint_to_t i) (UInt32.uint_to_t 1))
= ()

#reset-options "--z3rlimit 16"

abstract let as_value_gfrom_buffer_index
  (#value: Type)
  (h: HS.mem)
  (p: Buffer.buffer value)
  (i: nat{i < Buffer.length p})
: Lemma
  (requires (Buffer.contains h p))
  (ensures (contains h (gfrom_buffer_index p i) /\ as_value h (gfrom_buffer_index p i) == Seq.index (Buffer.as_seq h p) i))
  [SMTPat (as_value h (gfrom_buffer_index p i)); SMTPatT (Buffer.contains h p)]
= ()

abstract let gfield
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (p: struct_ptr (DM.t key value))
  (fd: key)
: GTot (p' : struct_ptr (value fd) { includes p p' } )
= _field p fd

abstract let as_buffer_gfield
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (p: struct_ptr (DM.t key value))
  (fd: key)
: Lemma
  (requires True)
  (ensures (as_buffer_type (gfield p fd) == as_buffer_type p /\ as_buffer (gfield p fd) == as_buffer p))
= ()

abstract let contains_gfield
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (h: HS.mem)
  (p: (struct_ptr (DM.t key value)))
  (fd: key)
: Lemma
  (requires True)
  (ensures (contains h (gfield p fd) <==> contains h p))
  [SMTPat (contains h (gfield p fd))]
= ()

abstract let live_gfield
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (h: HS.mem)
  (p: struct_ptr (DM.t key value))
  (fd: key)
: Lemma
  (requires True)
  (ensures (live h (gfield p fd) <==> live h p))
  [SMTPat (live h (gfield p fd))]
= ()

abstract let as_value_gfield
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (h: HS.mem)
  (p: struct_ptr (DM.t key value))
  (fd: key)
: Lemma
  (requires (contains h p))
  (ensures (contains h p /\ as_value h (gfield p fd) == DM.sel (as_value h p) fd))
  [SMTPat (as_value h (gfield p fd)); SMTPatT (contains h p)]
= ()

abstract let as_value_gfield_live
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (h: HS.mem)
  (p: struct_ptr (DM.t key value))
  (fd: key)
: Lemma
  (requires (live h p))
  (ensures (live h p /\ as_value h (gfield p fd) == DM.sel (as_value h p) fd))
  [SMTPat (as_value h (gfield p fd)); SMTPatT (live h p)]
= ()

abstract let frameOf_gfield
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (p: struct_ptr (DM.t key value))
  (fd: key)
: Lemma
  (requires True)
  (ensures (frameOf (gfield p fd) == frameOf p))
  [SMTPat (frameOf (gfield p fd))]
= ()

(*
 * AR: need to investigate why is this needed
 *)
private let memory_managed_redundant_lemma (#a:Type) (s:struct_ptr a)
  :Lemma (memory_managed s = HS.is_mm (Buffer.content (as_buffer s)))
  = ()

abstract let memory_managed_gfield
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (p: struct_ptr (DM.t key value))
  (fd: key)
: Lemma
  (requires True)
  (ensures (memory_managed (gfield p fd) <==> memory_managed p))
  [SMTPat (memory_managed (gfield p fd))]
= let p' = gfield p fd in
  memory_managed_redundant_lemma p;
  memory_managed_redundant_lemma p';
  assert (memory_managed p = HS.is_mm (Buffer.content (as_buffer p))); //AR: something's wrong, i had to insert these asserts all over
  assert (memory_managed p' == HS.is_mm (Buffer.content (as_buffer p')))

abstract let includes_gfield
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (p: struct_ptr (DM.t key value))
  (fd: key)
: Lemma
  (requires True)
  (ensures (includes p (gfield p fd)))
  [SMTPat (includes p (gfield p fd))]
= ()

abstract let includes_refl
  (#value: Type)
  (p: struct_ptr value)
: Lemma
  (requires True)
  (ensures (includes p p))
  [SMTPat (includes p p)]
= ()

abstract let includes_trans
  (#value1 #value2 #value3: Type)
  (p1: struct_ptr value1)
  (p2: struct_ptr value2)
  (p3: struct_ptr value3)
: Lemma
  (requires (includes p1 p2 /\ includes p2 p3))
  (ensures (includes p1 p3))
  [SMTPatT (includes p1 p2); SMTPatT (includes p2 p3)]
= path_includes_trans (StructPtr?.p p1) (StructPtr?.p p2) (StructPtr?.p p3)

abstract let includes_ind
  (x: (#value1: Type) ->
      (#value2: Type) ->
      (p1: struct_ptr value1) ->
      (p2: struct_ptr value2 {includes p1 p2} ) ->
      GTot Type0)
  (h_field:
    (#key: eqtype) ->
    (#value: (key -> Tot Type)) ->
    (p: struct_ptr (DM.t key value)) ->
    (fd: key {includes p (gfield p fd)}) ->
    Lemma (x p (gfield p fd)))
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
= let from : Type = StructPtr?.from p1 in
  let content : Buffer.buffer from = StructPtr?.content p1 in
  path_includes_ind
    (fun #to1 #to2 p1_ p2_ -> x (StructPtr content p1_) (StructPtr content p2_))
    (fun #ke #va p fd -> h_field (StructPtr content p) fd)
    (fun #to p -> h_refl (StructPtr content p))
    (fun #to1 #to2 #to3 p1_ p2_ p3_ -> h_trans (StructPtr content p1_) (StructPtr content p2_) (StructPtr content p3_))
    (StructPtr?.p p1)
    (StructPtr?.p p2)

let contains_includes
  (#value1: Type)
  (#value2: Type)
  (h: HS.mem)
  (p1: struct_ptr value1)
  (p2: struct_ptr value2)
: Lemma
  (requires (includes p1 p2))
  (contains h p1 <==> contains h p2)
  [SMTPatT (contains h p2); SMTPatT (includes p1 p2)]
= includes_ind
  (fun #v1 #v2 p1 p2 -> contains h p1 <==> contains h p2)
  (fun #k #v p fd -> contains_gfield h p fd)
  (fun #v p -> ())
  (fun #v1 #v2 #v3 p1 p2 p3 -> ())
  p1 p2

let live_includes
  (#value1: Type)
  (#value2: Type)
  (h: HS.mem)
  (p1: struct_ptr value1)
  (p2: struct_ptr value2)
: Lemma
  (requires (includes p1 p2))
  (ensures (live h p1 <==> live h p2))
  [SMTPatT (live h p2); SMTPatT (includes p1 p2)]
= includes_ind
  (fun #v1 #v2 p1 p2 -> live h p1 <==> live h p2)
  (fun #k #v p fd -> live_gfield h p fd)
  (fun #v p -> ())
  (fun #v1 #v2 #v3 p1 p2 p3 -> ())
  p1 p2

abstract let disjoint
  (#value1: Type)
  (#value2: Type)
  (p1: struct_ptr value1)
  (p2: struct_ptr value2)
: GTot Type0
= Buffer.disjoint (as_buffer p1) (as_buffer p2) \/
  (StructPtr?.from p1 == StructPtr?.from p2 /\ as_buffer p1 == as_buffer p2 /\ path_disjoint (StructPtr?.p p1) (StructPtr?.p p2))

abstract let disjoint_root
  (#value1: Type)
  (#value2: Type)
  (p1: struct_ptr value1)
  (p2: struct_ptr value2)
: Lemma
  (requires (Buffer.disjoint (as_buffer p1) (as_buffer p2)))
  (ensures (disjoint p1 p2))
= ()

abstract let disjoint_gfrom_buffer_index_other
  (#value1: Type)
  (p1: Buffer.buffer value1)
  (#value2: Type)
  (p2: Buffer.buffer value2)
  (i1: nat{i1 < Buffer.length p1})
  (i2: nat{i2 < Buffer.length p2})
: Lemma
  (requires (Buffer.disjoint p1 p2))
  (ensures (disjoint (gfrom_buffer_index p1 i1) (gfrom_buffer_index p2 i2)))
  [SMTPat (disjoint (gfrom_buffer_index p1 i1) (gfrom_buffer_index p2 i2))]
= ()

abstract let disjoint_gfrom_buffer_index_same
  (#value: Type)
  (p: Buffer.buffer value)
  (i1: nat{i1 < Buffer.length p})
  (i2: nat{i2 < Buffer.length p})
: Lemma
  (requires (i1 <> i2))
  (ensures (disjoint (gfrom_buffer_index p i1) (gfrom_buffer_index p i2)))
  [SMTPat (disjoint (gfrom_buffer_index p i1) (gfrom_buffer_index p i2))]
= ()

abstract let disjoint_gfield
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (p: struct_ptr (DM.t key value))
  (fd1: key)
  (fd2: key)
: Lemma
  (requires (fd1 <> fd2))
  (ensures (disjoint (gfield p fd1) (gfield p fd2)))
  [SMTPat (disjoint (gfield p fd1) (gfield p fd2))]
= ()

abstract let disjoint_includes
  (#value1: Type)
  (#value2: Type)
  (p1: struct_ptr value1)
  (p2: struct_ptr value2)
  (#value1': Type)
  (#value2': Type)
  (p1': struct_ptr value1')
  (p2': struct_ptr value2')
: Lemma
  (requires (includes p1 p1' /\ includes p2 p2' /\ disjoint p1 p2))
  (ensures (disjoint p1' p2'))
= FStar.Classical.or_elim
    #(Buffer.disjoint (as_buffer p1) (as_buffer p2))
    #(StructPtr?.from p1 == StructPtr?.from p2 /\ as_buffer p1 == as_buffer p2 /\ path_disjoint (StructPtr?.p p1) (StructPtr?.p p2))
    #(fun _ -> disjoint p1' p2')
    (fun h -> ())
    (fun _ -> path_disjoint_includes (StructPtr?.p p1) (StructPtr?.p p2) (StructPtr?.p p1') (StructPtr?.p p2'))

abstract let disjoint_ind
  (x:
    (#value1: Type) ->
    (#value2: Type) ->
    (p1: struct_ptr value1) ->
    (p2: struct_ptr value2 {disjoint p1 p2} ) ->
    GTot Type0)
  (h_root:
    (#value1: Type) ->
    (#value2: Type) ->
    (p1: struct_ptr value1) ->
    (p2: struct_ptr value2 { Buffer.disjoint (as_buffer p1) (as_buffer p2) } ) ->
    Lemma (x p1 p2))
  (h_field:
    (#key: eqtype) ->
    (#value: (key -> Tot Type)) ->
    (p: struct_ptr (DM.t key value)) ->
    (fd1: key) ->
    (fd2: key { fd1 <> fd2 /\ disjoint (gfield p fd1) (gfield p fd2) } ) ->
    Lemma (x (gfield p fd1) (gfield p fd2)))
  (h_includes:
    (#value1: Type) ->
    (#value2: Type) ->
    (p1: struct_ptr value1) ->
    (p2: struct_ptr value2) ->
    (#value1': Type) ->
    (#value2': Type) ->
    (p1': struct_ptr value1' {includes p1 p1'}) ->
    (p2': struct_ptr value2' {includes p2 p2' /\ disjoint p1 p2 /\ disjoint p1' p2' /\ x p1 p2}) ->
    Lemma (x p1' p2'))
  (#value1: Type)
  (#value2: Type)
  (p1: struct_ptr value1)
  (p2: struct_ptr value2 { disjoint p1 p2 } )
: Lemma (x p1 p2)
= let diff_root : Type0 = Buffer.disjoint (as_buffer p1) (as_buffer p2) in
  FStar.Classical.or_elim
    #diff_root
    #(StructPtr?.from p1 == StructPtr?.from p2 /\ as_buffer p1 == as_buffer p2 /\ path_disjoint (StructPtr?.p p1) (StructPtr?.p p2))
    #(fun _ -> x p1 p2)
    (fun (k: squash diff_root) ->
      assume diff_root; // TODO: why not automatic???
      h_root p1 p2)
    (fun _ ->
      let from: Type = StructPtr?.from p1 in
      let (content1: Buffer.buffer from { Buffer.length content1 == 1 } ) = StructPtr?.content p1 in
      let (content2: Buffer.buffer from { Buffer.length content1 == 1 } ) = StructPtr?.content p2 in
      assert (content1 == content2);
      path_disjoint_ind
	(fun #v1 #v2 p1_ p2_ -> x (StructPtr content1 p1_) (StructPtr content1 p2_))
	(fun #ke #va p fd1 fd2 -> h_field (StructPtr content1 p) fd1 fd2)
	(fun #v1 #v2 p1_ p2_ #v1' #v2' p1' p2' -> h_includes (StructPtr content1 p1_) (StructPtr content1 p2_) (StructPtr content1 p1') (StructPtr content1 p2'))
	(StructPtr?.p p1)
	(StructPtr?.p p2);
       assert (x p1 p2)
     )

let disjoint_sym
  (#value1: Type)
  (#value2: Type)
  (p1: struct_ptr value1)
  (p2: struct_ptr value2)
: Lemma
  (requires (disjoint p1 p2))
  (ensures (disjoint p2 p1))
= disjoint_ind
  (fun #v1 #v2 p1 p2 -> disjoint p2 p1)
  (fun #v1 #v2 p1 p2 -> disjoint_root p2 p1)
  (fun #k #v p fd1 fd2 -> disjoint_gfield p fd2 fd1)
  (fun #v1 #v2 p1 p2 #v1' #v2' p1' p2' -> disjoint_includes p2 p1 p2' p1')
  p1 p2

let disjoint_sym'
  (#value1: Type)
  (#value2: Type)
  (p1: struct_ptr value1)
  (p2: struct_ptr value2)
: Lemma
  (requires True)
  (ensures (disjoint p1 p2 <==> disjoint p2 p1))
  [SMTPat (disjoint p1 p2)]
= FStar.Classical.move_requires (disjoint_sym #value1 #value2 p1) p2;
  FStar.Classical.move_requires (disjoint_sym #value2 #value1 p2) p1

let disjoint_includes_l #a #as #a' (x: struct_ptr a) (subx:struct_ptr as) (y:struct_ptr a') : Lemma
  (requires (includes x subx /\ disjoint x y))
  (ensures  (disjoint subx y))
  [SMTPatT (disjoint subx y); SMTPatT (includes x subx)]
  = disjoint_includes x y subx y

let disjoint_includes_l_swap #a #as #a' (x:struct_ptr a) (subx:struct_ptr as) (y:struct_ptr a') : Lemma
  (requires (includes x subx /\ disjoint x y))
  (ensures  (disjoint y subx))
  [SMTPatT (disjoint y subx); SMTPatT (includes x subx)]
  = ()

let live_disjoint
  (#value1: Type)
  (#value2: Type)
  (h: HS.mem)
  (p1: struct_ptr value1)
  (p2: struct_ptr value2)
: Lemma
  (requires (live h p1 /\ p2 `unused_in` h))
  (ensures (disjoint p1 p2))
  [SMTPatT (disjoint p1 p2); SMTPatT (live h p1)]
= live_contains h p1;
  disjoint_root p1 p2


(* Specialized clauses for small numbers of struct_ptrs *)
let modifies_ptr_0 rid h h' =
  Buffer.modifies_buf_0 rid h h'
  /\ (forall (#tt:Type) (bb:struct_ptr tt). (frameOf bb = rid /\ live h bb) ==> equal_values h bb h' bb)

let modifies_ptr_1 (#t:Type) rid (b:struct_ptr t) h h' = //would be good to drop the rid argument on these, since they can be computed from the struct_ptrs
  Buffer.modifies_buf_1 rid (as_buffer b) h h'
  /\ (forall (#tt:Type) (bb:struct_ptr tt). (frameOf bb = rid /\ live h bb /\ disjoint b bb) ==> equal_values h bb h' bb)


let modifies_ptr_0_0 rid h0 h1 h2 :
  Lemma (requires (modifies_ptr_0 rid h0 h1 /\ modifies_ptr_0 rid h1 h2))
	(ensures (modifies_ptr_0 rid h0 h2))
	[SMTPatT (modifies_ptr_0 rid h0 h1); SMTPatT (modifies_ptr_0 rid h1 h2)]
 = ()


(* Modifies clauses that do not change the shape of the HyperStack (h1.tip = h0.tip) *)
(* NB: those clauses are made abstract in order to make verification faster
   Lemmas follow to allow the programmer to make use of the real definition
   of those predicates in a general setting *)
abstract let modifies_0 h0 h1 =
  Buffer.modifies_0 h0 h1
  /\ modifies_ptr_0 h0.HS.tip h0 h1

(* This one is very generic: it says
 * - some references have changed in the frame of b, but
 * - among all struct_ptrs in this frame, b is the only one that changed. *)
abstract let modifies_1 (#a:Type) (b:struct_ptr a) h0 h1 =
  Buffer.modifies_1 (as_buffer b) h0 h1 /\
  modifies_ptr_1 (frameOf b) b h0 h1

(* Lemmas introducing the 'modifies' predicates *)
let modifies_0_intro h0 h1 : Lemma
  (requires (
     Buffer.modifies_0 h0 h1
  /\ modifies_ptr_0 h0.HS.tip h0 h1
  ))
  (ensures  (modifies_0 h0 h1))
  = ()

let modifies_1_intro (#a:Type) (b:struct_ptr a) h0 h1 : Lemma
  (requires (Buffer.modifies_1 (as_buffer b) h0 h1 /\ modifies_ptr_1 (frameOf b) b h0 h1))
  (ensures  (modifies_1 b h0 h1))
  = ()

(* Lemmas revealing the content of the specialized modifies clauses in order to
   be able to generalize them if needs be. *)
let  modifies_0_reveal h0 h1 : Lemma
  (requires (modifies_0 h0 h1))
  (ensures  (Buffer.modifies_0 h0 h1 /\ modifies_ptr_0 h0.HS.tip h0 h1))
  = ()

let modifies_1_reveal (#a:Type) (b:struct_ptr a) h0 h1 : Lemma
  (requires (modifies_1 b h0 h1))
  (ensures  (Buffer.modifies_1 (as_buffer b) h0 h1 /\ modifies_ptr_1 (frameOf b) b h0 h1))
  = ()

(* STStack effect specific lemmas *)
let lemma_ststack_1 (#a:Type) (b:struct_ptr a) h0 h1 h2 h3 : Lemma
  (requires (live h0 b /\ HS.fresh_frame h0 h1 /\ modifies_1 b h1 h2 /\ HS.popped h2 h3))
  (ensures  (modifies_1 b h0 h3))
  [SMTPatT (modifies_1 b h1 h2); SMTPatT (HS.fresh_frame h0 h1); SMTPatT (HS.popped h2 h3)]
  = Buffer.lemma_reveal_modifies_1 (as_buffer b) h1 h2;
    Buffer.lemma_intro_modifies_1 (as_buffer b) h0 h3

(** Transitivity lemmas *)
let modifies_0_trans h0 h1 h2 : Lemma
  (requires (modifies_0 h0 h1 /\ modifies_0 h1 h2))
  (ensures  (modifies_0 h0 h2))
  [SMTPatT (modifies_0 h0 h1); SMTPatT (modifies_0 h1 h2)]
  = ()

let modifies_1_trans (#a:Type) (b:struct_ptr a) h0 h1 h2 : Lemma
  (requires (modifies_1 b h0 h1 /\ modifies_1 b h1 h2))
  (ensures (modifies_1 b h0 h2))
  [SMTPatT (modifies_1 b h0 h1); SMTPatT (modifies_1 b h1 h2)]
  = ()

(* Specific modifies clause lemmas *)
val modifies_0_0: h0:HS.mem -> h1:HS.mem -> h2:HS.mem -> Lemma
  (requires (modifies_0 h0 h1 /\ modifies_0 h1 h2))
  (ensures  (modifies_0 h0 h2))
  [SMTPatT (modifies_0 h0 h1); SMTPatT (modifies_0 h1 h2)]
let modifies_0_0 h0 h1 h2 = ()

#reset-options "--z3rlimit 16"

let modifies_0_1 (#a:Type) (b:struct_ptr a) h0 h1 h2 : Lemma
  (requires (b `unused_in` h0 /\ modifies_0 h0 h1 /\ live h1 b /\ modifies_1 b h1 h2))
  (ensures  (modifies_0 h0 h2))
  [SMTPatT (modifies_0 h0 h1); SMTPatT (modifies_1 b h1 h2)]
  = Buffer.lemma_reveal_modifies_0 h0 h1;
    Buffer.lemma_reveal_modifies_1 (as_buffer b) h1 h2;
    Buffer.lemma_intro_modifies_0 h0 h2

(** Concrete allocators, getters and setters *)

// We create a struct_ptr for any type t (not necessarily a DM.t) and provide the initial value of type t

abstract let screate
  (#value:Type)
  (s: value)
: StackInline (struct_ptr value)
  (requires (fun h -> True))
  (ensures (fun (h0:HS.mem) b h1 ->
       b `unused_in` h0
     /\ live h1 b
     /\ frameOf b = h0.HS.tip
     /\ modifies_0 h0 h1
     /\ Map.domain h1.HS.h == Map.domain h0.HS.h
     /\ as_value h1 b == s))
= let h0 = HST.get () in
  let content: Buffer.buffer value =
     Buffer.create s (UInt32.uint_to_t 1)
  in
  let h1 = HST.get () in
  Buffer.lemma_reveal_modifies_0 h0 h1;
  StructPtr content PathBase

abstract let ecreate
  (#t:Type)
  (r:HH.rid)
  (s: t)
: ST (struct_ptr t)
  (requires (fun h -> HS.is_eternal_region r))
  (ensures (fun (h0:HS.mem) b h1 -> b `unused_in` h0
    /\ live h1 b
    /\ Map.domain h1.HS.h == Map.domain h0.HS.h
    /\ h1.HS.tip = h0.HS.tip
    /\ HS.modifies (Set.singleton r) h0 h1
    /\ HS.modifies_ref r Set.empty h0 h1
    /\ as_value h1 b == s
    /\ ~ (memory_managed b)))
= let h0 = HST.get() in
  let buf = Buffer.rcreate r s (UInt32.uint_to_t 1) in
  assert (~ (HS.is_mm (FStar.Buffer.content buf)));
  let b = StructPtr buf PathBase in
  memory_managed_redundant_lemma b;
  assert (as_buffer b == buf);
  assert (memory_managed b = HS.is_mm (FStar.Buffer.content (as_buffer b)));
  let h1 = HST.get() in
  b

abstract let from_buffer_index
  (#value: Type)
  (p: Buffer.buffer value)
  (i: UInt32.t {UInt32.v i < Buffer.length p})
: ST (struct_ptr value)
  (requires (fun h -> Buffer.live h p))
  (ensures (fun h0 p' h1 -> h0 == h1 /\ p' == gfrom_buffer_index p (UInt32.v i)))
= _from_buffer_index p (UInt32.v i)

abstract let field
 (#key: eqtype)
 (#value: (key -> Tot Type))
 (p: struct_ptr (DM.t key value))
 (fd: key)
: ST (struct_ptr (value fd))
  (requires (fun h -> live h p))
  (ensures (fun h0 p' h1 -> h0 == h1 /\ p' == gfield p fd))
= _field p fd

abstract let read
 (#value: Type)
 (p: struct_ptr value)
: ST value
  (requires (fun h -> live h p))
  (ensures (fun h0 v h1 -> live h0 p /\ h0 == h1 /\ v == as_value h0 p))
= let (StructPtr content p') = p in
  path_sel (Buffer.index (StructPtr?.content p) (UInt32.uint_to_t 0)) p'

abstract val write: #a:Type -> b:struct_ptr a -> z:a -> Stack unit
  (requires (fun h -> live h b))
  (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b
    /\ modifies_1 b h0 h1
    /\ as_value h1 b == z ))
let write #a b z =
  let v = Buffer.index (StructPtr?.content b) (UInt32.uint_to_t 0) in
  let v' = path_upd v (StructPtr?.p b) z in
  let h0 = HST.get () in
  Buffer.upd (StructPtr?.content b) (UInt32.uint_to_t 0) v';
  let h1 = HST.get () in
  Buffer.lemma_reveal_modifies_1 (as_buffer b) h0 h1  

(** Lemmas and patterns *)

val no_upd_lemma_0: #t:Type -> h0:HS.mem -> h1:HS.mem -> b:struct_ptr t -> Lemma
  (requires (live h0 b /\ modifies_0 h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal_values h0 b h1 b))
  [SMTPatT (modifies_0 h0 h1); SMTPatT (live h0 b)]
let no_upd_lemma_0 #t h0 h1 b = ()

val no_upd_lemma_1: #t:Type -> #t':Type -> h0:HS.mem -> h1:HS.mem -> a:struct_ptr t -> b:struct_ptr t' -> Lemma
  (requires (live h0 b /\ disjoint a b /\ modifies_1 a h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal_values h0 b h1 b))
  [SMTPatOr [ [ SMTPatT (modifies_1 a h0 h1); SMTPatT (as_value h1 b) ] ; [ SMTPatT (modifies_1 a h0 h1); SMTPatT (live h0 b) ] ] ]
let no_upd_lemma_1 #t #t' h0 h1 a b = ()

val no_upd_fresh: #t:Type -> h0:HS.mem -> h1:HS.mem -> a:struct_ptr t -> Lemma
  (requires (live h0 a /\ HS.fresh_frame h0 h1))
  (ensures  (live h0 a /\ live h1 a /\ equal_values h0 a h1 a))
  [SMTPatT (live h0 a); SMTPatT (HS.fresh_frame h0 h1)]
let no_upd_fresh #t h0 h1 a = ()

val no_upd_popped: #t:Type -> h0:HS.mem -> h1:HS.mem -> b:struct_ptr t -> Lemma
  (requires (live h0 b /\ frameOf b <> h0.HS.tip /\ HS.popped h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal_values h0 b h1 b))
  [SMTPatT (live h0 b); SMTPatT (HS.popped h0 h1)]
let no_upd_popped #t h0 h1 b = ()

let lemma_modifies_sub_1 #t h0 h1 (b:struct_ptr t) : Lemma
  (requires (h1 == h0))
  (ensures  (modifies_1 b h0 h1))
  [SMTPatT (live h0 b); SMTPatT (modifies_1 b h0 h1)]
  = Buffer.lemma_intro_modifies_1 (as_buffer b) h0 h1

let modifies_substruct_1 (#tsub #ta:Type) h0 h1 (sub:struct_ptr tsub) (a:struct_ptr ta) : Lemma
  (requires (live h0 a /\ modifies_1 sub h0 h1 /\ live h1 sub /\ includes a sub))
  (ensures  (modifies_1 a h0 h1 /\ live h1 a))
  [SMTPatT (modifies_1 sub h0 h1); SMTPatT (includes a sub)]
  = ()

let modifies_popped_1' (#t:Type) (a:struct_ptr t) h0 h1 h2 h3 : Lemma
  (requires (live h0 a /\ HS.fresh_frame h0 h1 /\ HS.popped h2 h3 /\ modifies_1 a h1 h2))
  (ensures  (modifies_1 a h0 h3))
  [SMTPatT (HS.fresh_frame h0 h1); SMTPatT (HS.popped h2 h3); SMTPatT (modifies_1 a h1 h2)]
  = ()

let live_popped (#t:Type) (b:struct_ptr t) h0 h1 : Lemma
  (requires (HS.popped h0 h1 /\ live h0 b /\ frameOf b <> h0.HS.tip))
  (ensures  (live h1 b))
  [SMTPatT (HS.popped h0 h1); SMTPatT (live h0 b)]
  = ()

let live_fresh (#t:Type) (b:struct_ptr t) h0 h1 : Lemma
  (requires (HS.fresh_frame h0 h1 /\ live h0 b))
  (ensures  (live h1 b))
  [SMTPatT (HS.fresh_frame h0 h1); SMTPatT (live h0 b)]
  = ()

let modifies_poppable_1 #t h0 h1 (b:struct_ptr t) : Lemma
  (requires (modifies_1 b h0 h1 /\ HS.poppable h0))
  (ensures  (HS.poppable h1))
  [SMTPatT (modifies_1 b h0 h1)]
  = ()


