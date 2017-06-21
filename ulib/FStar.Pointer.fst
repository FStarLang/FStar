module FStar.Pointer

module DM = FStar.DependentMap
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open HST // for := , !

(*** Definitions *)

(** Type codes *)

type base_typ =
| TUInt
| TUInt8
| TUInt16
| TUInt32
| TUInt64
| TInt
| TInt8
| TInt16
| TInt32
| TInt64
| TChar
| TBool
| TUnit

type typ =
| TBase:
  (b: base_typ) ->
  typ
| TStruct:
  (l: struct_typ) ->
  typ
| TArray:
  (length: UInt32.t) ->
  (t: typ) ->
  typ
| TPointer:
  (t: typ) ->
  typ
| TBuffer:
  (t: typ) ->
  typ
and struct_typ = (l: list (string * typ) { List.Tot.noRepeats (List.Tot.map fst l) })

let struct_field
  (l: struct_typ)
: Tot eqtype
= (s: string { List.Tot.mem s (List.Tot.map fst l) } )

let typ_of_struct_field
  (l: struct_typ)
  (f: struct_field l)
: Tot (t: typ {t << l})
= List.Tot.assoc_mem f l;
  let y = Some?.v (List.Tot.assoc f l) in
  List.Tot.assoc_precedes f l y;
  y

let rec typ_depth
  (t: typ)
: GTot nat
= match t with
  | TArray _ t -> 1 + typ_depth t
  | TStruct l -> 1 + struct_typ_depth l
  | _ -> 0
and struct_typ_depth
  (l: struct_typ)
: GTot nat
= match l with
  | [] -> 0
  | (_, t) :: l ->
    let n1 = typ_depth t in
    let n2 = struct_typ_depth l in
    if n1 > n2 then n1 else n2

let rec typ_depth_typ_of_struct_field
  (l: struct_typ)
  (f: struct_field l)
: Lemma
  (ensures (typ_depth (typ_of_struct_field l f) <= struct_typ_depth l))
  (decreases l)
= let ((f', _) :: l') = l in
  if f = f'
  then ()
  else begin
    let f: string = f in
    assert (List.Tot.mem f (List.Tot.map fst l'));
    List.Tot.assoc_mem f l';
    typ_depth_typ_of_struct_field l' f
  end

(** Pointers to data of type t *)

private type step: (from: typ) -> (to: typ) -> Tot Type0 =
  | StepField:
    (l: struct_typ) ->
    (fd: struct_field l) ->
    step (TStruct l) (typ_of_struct_field l fd)
  | StepCell:
    (length: UInt32.t) ->
    (value: typ) ->
    (index: UInt32.t { UInt32.v index < UInt32.v length } ) ->
    step (TArray length value) value

private type path (from: typ) : (to: typ) -> Tot Type0 =
  | PathBase:
    path from from
  | PathStep:
    (through: typ) ->
    (to: typ) ->
    (p: path from through) ->
    (s: step through to) ->
    path from to

private let step_typ_depth
  (#from #to: typ)
  (s: step from to)
: Lemma
  (typ_depth from > typ_depth to)
= match s with
  | StepField l fd ->
    typ_depth_typ_of_struct_field l fd
  | _ -> ()

private let rec path_typ_depth
  (#from #to: typ)
  (p: path from to)
: Lemma
  (ensures (
    typ_depth from >= typ_depth to /\ (
      (~ (PathBase? p)) ==> typ_depth from <> typ_depth to
  )))
  (decreases p)
= match p with
  | PathBase -> ()
  | PathStep _ _ p' s ->
    path_typ_depth p';
    step_typ_depth s

(*
private
let not_cell
  (#from #to: typ)
  (p: path from to)
: GTot bool
= match p with
  | PathStep _ _ _ (StepCell _ _ _) -> false
  | _ -> true

private type array_path (from: typ) (to_elem: typ) : (length: UInt32.t) -> Tot Type0 =
| PSingleton:
  (p: path from to_elem { not_cell p } ) ->
  array_path from to_elem 1ul
| PArray:
  length: UInt32.t ->
  path from (TArray length to_elem) ->
  array_path from to_elem length

private let path' (from: typ) (to: typ) : Tot Type0 =
  if TArray? to
  then
    let length = TArray?.length to in
    (array_path from (TArray?.t to) length * (offset: UInt32.t & (length': UInt32.t {UInt32.v offset + UInt32.v length' <= UInt32.v length})))
  else path from to
*)

noeq private type _pointer (to : typ): Type0 =
  | Pointer:
    (from: typ) ->
    (contents: HS.aref) ->
    (p: path from to) ->
    _pointer to

abstract let pointer (t: typ): Tot Type0 =
  _pointer t

(** Buffers *)

noeq private type buffer_root (t: typ) =
| BufferRootSingleton:
  (p: pointer t) ->
  buffer_root t
| BufferRootArray:
  (#max_length: UInt32.t) ->
  (p: pointer (TArray max_length t)) ->
  buffer_root t

private let buffer_root_length (#t: typ) (b: buffer_root t): Tot UInt32.t = match b with
| BufferRootSingleton _ -> 1ul
| BufferRootArray #t #len _ -> len

noeq private type _buffer (t: typ) =
| Buffer:
  (broot: buffer_root t) ->
  (bidx: UInt32.t) ->
  (blength: UInt32.t { UInt32.v bidx + UInt32.v blength <= UInt32.v (buffer_root_length broot) } ) ->
  _buffer t
abstract let buffer (t: typ): Tot Type0 = _buffer t

(** Interpretation of type codes *)

let type_of_base_typ
  (t: base_typ)
: Tot Type0
= match t with
  | TUInt -> nat
  | TUInt8 -> FStar.UInt8.t
  | TUInt16 -> FStar.UInt16.t
  | TUInt32 -> FStar.UInt32.t
  | TUInt64 -> FStar.UInt64.t
  | TInt -> int
  | TInt8 -> FStar.Int8.t
  | TInt16 -> FStar.Int16.t
  | TInt32 -> FStar.Int32.t
  | TInt64 -> FStar.Int64.t
  | TChar -> FStar.Char.char
  | TBool -> bool
  | TUnit -> unit

type array (length: UInt32.t) (t: Type) = (s: Seq.seq t {Seq.length s == UInt32.v length})

let type_of_struct_field'
  (l: struct_typ)
  (type_of_typ: (
    (t: typ { t << l } ) ->
    Tot Type0
  ))
  (f: struct_field l)
: Tot Type0 =
  List.Tot.assoc_mem f l;
  let y = typ_of_struct_field l f in
  List.Tot.assoc_precedes f l y;
  type_of_typ y

let rec type_of_typ
  (t: typ)
: Tot Type0
= match t with
  | TBase b -> type_of_base_typ b
  | TStruct l ->
    DM.t (struct_field l) (type_of_struct_field' l type_of_typ)
  | TArray length t ->
    array length (type_of_typ t)
  | TPointer t ->
    pointer t
  | TBuffer t ->
    buffer t

let type_of_struct_field
  (l: struct_typ)
: Tot (struct_field l -> Tot Type0)
= type_of_struct_field' l type_of_typ

let struct (l: struct_typ) = DM.t (struct_field l) (type_of_struct_field l)

let type_of_typ_struct
  (l: struct_typ)
: Lemma
  (type_of_typ (TStruct l) == struct l)
  [SMTPat (type_of_typ (TStruct l))]
= assert_norm (type_of_typ (TStruct l) == struct l)

let typ_of_type_type_of_struct_field
  (l: struct_typ)
  (f: struct_field l)
: Lemma
  (type_of_typ (typ_of_struct_field l f) == type_of_struct_field l f)
  [SMTPat (type_of_typ (typ_of_struct_field l f))]
= ()

let struct_sel (#l: struct_typ) (s: struct l) (f: struct_field l) : Tot (type_of_struct_field l f) =
  DM.sel s f

let struct_upd (#l: struct_typ) (s: struct l) (f: struct_field l) (v: type_of_struct_field l f) : Tot (struct l) =
  DM.upd s f v

let struct_create (l: struct_typ) (f: ((fd: struct_field l) -> Tot (type_of_struct_field l fd))) : Tot (struct l) =
  DM.create #(struct_field l) #(type_of_struct_field l) f

private
let rec dummy_val
  (t: typ)
: Tot (type_of_typ t)
= match t with
  | TBase b ->
    begin match b with
    | TUInt -> 0
    | TUInt8 -> UInt8.uint_to_t 0
    | TUInt16 -> UInt16.uint_to_t 0
    | TUInt32 -> UInt32.uint_to_t 0
    | TUInt64 -> UInt64.uint_to_t 0
    | TInt -> 0
    | TInt8 -> Int8.int_to_t 0
    | TInt16 -> Int16.int_to_t 0
    | TInt32 -> Int32.int_to_t 0
    | TInt64 -> Int64.int_to_t 0
    | TChar -> 'c'
    | TBool -> false
    | TUnit -> ()
    end
  | TStruct l ->
    struct_create l (fun f -> (
      dummy_val (typ_of_struct_field l f)
    ))
  | TArray length t -> Seq.create (UInt32.v length) (dummy_val t)
  | TPointer t -> Pointer t HS.dummy_aref PathBase
  | TBuffer t -> Buffer (BufferRootSingleton (Pointer t HS.dummy_aref PathBase)) 0ul 1ul

(*** Semantics of pointers *)

(** Pointer paths *)

private let rec path_sel
  (#from: typ)
  (#to: typ)
  (m: type_of_typ from)
  (p: path from to)
: Tot (type_of_typ to)
  (decreases p)
= match p with
  | PathBase -> m
  | PathStep through' to' p' s ->
    let (m': type_of_typ through') = path_sel m p' in
    begin match s with
    | StepField l fd ->
      let (m': struct l) = m' in
      struct_sel m' fd
    | StepCell length value i -> Seq.index m' (UInt32.v i)
    end

private let rec path_upd
  (#from: typ)
  (#to: typ)
  (m: type_of_typ from)
  (p: path from to)
  (v: type_of_typ to)
: Tot (type_of_typ from)
  (decreases p)
= match p with
  | PathBase -> v
  | PathStep through' to' p' st ->
    let (s: type_of_typ through') = path_sel m p' in
    let (s': type_of_typ through') = match st with
    | StepField l fd ->
      let (s: struct l) = s in
      struct_upd s fd v
    | StepCell length value i ->
      Seq.upd s (UInt32.v i) v
    in
    path_upd m p' s'

private let rec path_sel_upd_same
  (#from: typ)
  (#to: typ)
  (m: type_of_typ from)
  (p: path from to)
  (v: type_of_typ to)
: Lemma
  (requires True)
  (ensures (path_sel (path_upd m p v) p == v))
  (decreases p)
  [SMTPat (path_sel (path_upd m p v) p)]
= match p with
  | PathBase -> ()
  | PathStep through' to' p' st ->
    let (s: type_of_typ through') = path_sel m p' in
    let (s': type_of_typ through') = match st with
    | StepField l fd ->
      let (s: struct l) = s in
      let _ = DM.sel_upd_same s fd v in
      struct_upd s fd v
    | StepCell length value i ->
      let s' = Seq.upd s (UInt32.v i) v in
      Seq.lemma_index_upd1 s (UInt32.v i) v;
      s'
    in
    path_sel_upd_same m p' s'

private let rec path_concat
  (#from: typ)
  (#through: typ)
  (#to: typ)
  (p: path from through)
  (q: path through to)
: Pure (path from to)
  (requires True)
  (ensures (fun _ -> True))
  (decreases q)
= match q with
  | PathBase -> p
  | PathStep through' to' q' st -> PathStep through' to' (path_concat p q') st

private let path_concat_base_r
  (#from: typ)
  (#to: typ)
  (p: path from to)
: Lemma
  (ensures (path_concat p PathBase == p))
= ()

private let rec path_concat_base_l
  (#from: typ)
  (#to: typ)
  (p: path from to)
: Lemma
  (requires True)
  (ensures (path_concat PathBase p == p))
  (decreases p)
  [SMTPat (path_concat PathBase p)]
= match p with
  | PathBase -> ()
  | PathStep _ _ p' _ -> path_concat_base_l p'

private let rec path_concat_assoc
  (#t0 #t1 #t2 #t3: typ)
  (p01: path t0 t1)
  (p12: path t1 t2)
  (p23: path t2 t3)
: Lemma
  (requires True)
  (ensures (path_concat (path_concat p01 p12) p23 == path_concat p01 (path_concat p12 p23)))
  (decreases p23)
= match p23 with
  | PathBase -> ()
  | PathStep _ _ p23' _ -> path_concat_assoc p01 p12 p23'

private let rec path_sel_concat
  (#from: typ)
  (#through: typ)
  (#to: typ)
  (m: type_of_typ from)
  (p: path from through)
  (q: path through to)
: Lemma
  (requires True)
  (ensures (path_sel m (path_concat p q) == path_sel (path_sel m p) q))
  (decreases q)
  [SMTPat (path_sel m (path_concat p q))]
= match q with
  | PathBase -> ()
  | PathStep _ _ q' _ -> path_sel_concat m p q'

private let rec path_upd_concat
  (#from: typ)
  (#through: typ)
  (#to: typ)
  (m: type_of_typ from)
  (p: path from through)
  (q: path through to)
  (v: type_of_typ to)
: Lemma
  (requires True)
  (ensures (path_upd m (path_concat p q) v == path_upd m p (path_upd (path_sel m p) q v)))
  (decreases q)
  [SMTPat (path_upd m (path_concat p q) v)]
= match q with
  | PathBase -> ()
  | PathStep through' to' q' st ->
    let (s: type_of_typ through') = path_sel m (path_concat p q') in
    let (s': type_of_typ through') = match st with
    | StepField l fd ->
      let (s: struct l) = s in
      struct_upd s fd v
    | StepCell length value i ->
      Seq.upd s (UInt32.v i) v
    in
    path_upd_concat m p q' s'

// TODO: rename as: prefix_of; use infix notation (p1 `prefix_of` p2)
private let rec path_includes
  (#from: typ)
  (#to1 #to2: typ)
  (p1: path from to1)
  (p2: path from to2)
: Ghost bool
  (requires True)
  (ensures (fun _ -> True))
  (decreases p2)
= (to1 = to2 && p1 = p2) || (match p2 with
  | PathBase -> false
  | PathStep _ _ p2' _ ->
    path_includes p1 p2'
  )

private let rec path_includes_base
  (#from: typ)
  (#to: typ)
  (p: path from to)
: Lemma
  (requires True)
  (ensures (path_includes (PathBase #from) p))
  (decreases p)
  [SMTPat (path_includes PathBase p)]
= match p with
  | PathBase -> ()
  | PathStep _ _ p2' _ -> path_includes_base p2'

private let path_includes_refl
  (#from #to: typ)
  (p: path from to)
: Lemma
  (requires True)
  (ensures (path_includes p p))
  [SMTPat (path_includes p p)]
= ()

private let path_includes_step_r
  (#from #through #to: typ)
  (p: path from through)
  (s: step through to)
: Lemma
  (requires True)
  (ensures (path_includes p (PathStep through to p s)))
  [SMTPat (path_includes p (PathStep through to p s))]
= ()

private let rec path_includes_trans
  (#from #to1 #to2 #to3: typ)
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
      | PathStep _ _ p3' _ ->
	path_includes p2 p3')
    #(fun _ -> path_includes p1 p3)
    (fun _ -> ())
    (fun _ -> match p3 with
      | PathBase -> assert False
      | PathStep _ _ p3' _ ->
	path_includes_trans p1 p2 p3'
    )

private let rec path_includes_ind
  (#from: typ)
  (x: (#to1: typ) ->
      (#to2: typ) ->
      (p1: path from to1) ->
      (p2: path from to2 {path_includes p1 p2} ) ->
      GTot Type0)
  (h_step:
    (#through: typ) ->
    (#to: typ) ->
    (p: path from through) ->
    (s: step through to { path_includes p (PathStep through to p s) } ) ->
    Lemma (x p (PathStep through to p s)))
  (h_refl:
    (#to: typ) ->
    (p: path from to {path_includes p p}) ->
    Lemma (x p p))
  (h_trans:
    (#to1: typ) ->
    (#to2: typ) ->
    (#to3: typ) ->
    (p1: path from to1) ->
    (p2: path from to2) ->
    (p3: path from to3 {path_includes p1 p2 /\ path_includes p2 p3 /\ path_includes p1 p3 /\ x p1 p2 /\ x p2 p3}) ->
    Lemma (x p1 p3))
  (#to1: typ)
  (#to2: typ)
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
      | PathStep _ _  p' _ -> path_includes p1 p')
    #(fun _ -> x p1 p2)
    (fun _ -> h_refl p1)
    (fun _ -> match p2 with
     | PathBase -> assert False
     | PathStep _ _  p2' st ->
       let _ = path_includes_ind x h_step h_refl h_trans p1 p2' in
       let _ = path_includes_step_r p2' st in
       let _ = h_step p2' st in
       h_trans p1 p2' p2
    )

private let rec path_length
  (#from #to: typ)
  (p: path from to)
: Tot nat
  (decreases p)
= match p with
  | PathBase -> 0
  | PathStep _ _ p' _ -> 1 + path_length p'

private let path_includes_length
  (#from: typ)
  (#to1 #to2: typ)
  (p1: path from to1)
  (p2: path from to2 {path_includes p1 p2})
: Lemma
  (ensures (path_length p1 <= path_length p2))
= path_includes_ind
    (fun #to1_ #to2_ p1_ p2_ -> path_length p1_ <= path_length p2_)
    (fun #through #to p st -> ())
    (fun #to p -> ())
    (fun #to1_ #to2_ #to3_ p1_ p2_ p3_ -> ())
    p1 p2

private let path_includes_step_l
  (#from: typ)
  (#through: typ)
  (#to: typ)
  (p: path from through)
  (s: step through to)
: Lemma
  (requires True)
  (ensures (~ (path_includes (PathStep through to p s) p)))
  [SMTPat (path_includes (PathStep through to p s) p)]
= assert (path_length (PathStep through to p s) > path_length p);
  FStar.Classical.forall_intro (path_includes_length #from #to #through (PathStep through to p s))

private let rec path_includes_concat
  (#from: typ)
  (#through: typ)
  (#to: typ)
  (p: path from through)
  (q: path through to)
: Lemma
  (requires True)
  (ensures (path_includes p (path_concat p q)))
  (decreases q)
  [SMTPat (path_includes p (path_concat p q))]
= match q with
  | PathBase -> ()
  | PathStep _ _ q' _ -> path_includes_concat p q'

private let path_includes_exists_concat
  (#from #through: typ)
  (p: path from through)
  (#to: typ)
  (q: path from to { path_includes p q } )
: Lemma
  (ensures (exists (r: path through to) . q == path_concat p r))
= path_includes_ind
    (fun #to1_ #to2_ p1_ p2_ -> exists r . p2_ == path_concat p1_ r)
    (fun #through #to_ p s -> FStar.Classical.exists_intro (fun r -> PathStep through to_ p s == path_concat p r) (PathStep through to_ PathBase s))
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

private
let step_disjoint
  (#from: typ)
  (#to1 #to2: typ)
  (s1: step from to1)
  (s2: step from to2)
: GTot bool
= match s1 with
  | StepField _ fd1 ->
    let (StepField _ fd2) = s2 in
    fd1 <> fd2
  | StepCell _ _ i1 ->
    let (StepCell _ _ i2) = s2 in
    UInt32.v i1 <> UInt32.v i2

private
let step_eq
  (#from: typ)
  (#to1 #to2: typ)
  (s1: step from to1)
  (s2: step from to2)
: Tot (b: bool { b = true <==> to1 == to2 /\ s1 == s2 } )
= match s1 with
  | StepField l1 fd1 ->
    let (StepField _ fd2) = s2 in
    fd1 = fd2
  | StepCell _ _ i1 ->
    let (StepCell _ _ i2) = s2 in
    i1 = i2

private
let step_disjoint_not_eq
  (#from: typ)
  (#to1 #to2: typ)
  (s1: step from to1)
  (s2: step from to2)
: Lemma
  (ensures (step_disjoint s1 s2 = not (step_eq s1 s2)))
= ()

private
let step_disjoint_sym
  (#from: typ)
  (#to1 #to2: typ)
  (s1: step from to1)
  (s2: step from to2)
: Lemma
  (requires (step_disjoint s1 s2))
  (ensures (step_disjoint s2 s1))
= ()

noeq private type path_disjoint_t (#from: typ):
  (#to1: typ) ->
  (#to2: typ) ->
  (p1: path from to1) ->
  (p2: path from to2) ->
  Type0
= | PathDisjointStep:
    (#through: typ) ->
    (#to1: typ) ->
    (#to2: typ) ->
    (p: path from through) ->
    (s1: step through to1) ->
    (s2: step through to2 { step_disjoint s1 s2 } ) ->
    path_disjoint_t (PathStep through to1 p s1) (PathStep through to2 p s2)
  | PathDisjointIncludes:
    (#to1: typ) ->
    (#to2: typ) ->
    (p1: path from to1) ->
    (p2: path from to2) ->
    (#to1': typ) ->
    (#to2': typ) ->
    (p1': path from to1' {path_includes p1 p1'}) ->
    (p2': path from to2' {path_includes p2 p2'}) ->
    path_disjoint_t p1 p2 ->
    path_disjoint_t p1' p2'

private let rec path_disjoint_t_rect
  (#from: typ)
  (x:
    (#value1: typ) ->
    (#value2: typ) ->
    (p1: path from value1) ->
    (p2: path from value2) ->
    (h: path_disjoint_t p1 p2) ->
    GTot Type)
  (h_step:
    (#through: typ) ->
    (#to1: typ) ->
    (#to2: typ) ->
    (p: path from through) ->
    (s1: step through to1) ->
    (s2: step through to2 { step_disjoint s1 s2 } ) ->
    (h: path_disjoint_t (PathStep through to1 p s1) (PathStep through to2 p s2)) ->
    GTot (x (PathStep through to1 p s1) (PathStep through to2 p s2) h))
  (h_includes:
    (#value1: typ) ->
    (#value2: typ) ->
    (p1: path from value1) ->
    (p2: path from value2) ->
    (#value1': typ) ->
    (#value2': typ) ->
    (p1': path from value1' {path_includes p1 p1'}) ->
    (p2': path from value2' {path_includes p2 p2'}) ->
    (h: path_disjoint_t p1 p2) ->
    (h': path_disjoint_t p1' p2') ->
    (ihx: x p1 p2 h) ->
    GTot (x p1' p2' h'))
  (#value1: typ)
  (#value2: typ)
  (p1: path from value1)
  (p2: path from value2)
  (h: path_disjoint_t p1 p2)
: Ghost (x p1 p2 h)
  (requires True)
  (ensures (fun _ -> True))
  (decreases h)
= match h with
  | PathDisjointStep p s1 s2 -> h_step p s1 s2 h
  | PathDisjointIncludes p1_ p2_ p1' p2' h_ -> h_includes p1_ p2_ p1' p2' h_ h (path_disjoint_t_rect x h_step h_includes p1_ p2_ h_)

private let path_disjoint
  (#from: typ)
  (#value1: typ)
  (#value2: typ)
  (p1: path from value1)
  (p2: path from value2)
: GTot Type0
= squash (path_disjoint_t p1 p2)

private let path_disjoint_ind
  (#from: typ)
  (x:
    (#value1: typ) ->
    (#value2: typ) ->
    (p1: path from value1) ->
    (p2: path from value2 {path_disjoint p1 p2} ) ->
    GTot Type)
  (h_step:
    (#through: typ) ->
    (#to1: typ) ->
    (#to2: typ) ->
    (p: path from through) ->
    (s1: step through to1) ->
    (s2: step through to2 { step_disjoint s1 s2 /\ path_disjoint (PathStep through to1 p s1) (PathStep through to2 p s2) } ) ->
    Lemma (x (PathStep through to1 p s1) (PathStep through to2 p s2) ))
  (h_includes:
    (#value1: typ) ->
    (#value2: typ) ->
    (p1: path from value1) ->
    (p2: path from value2) ->
    (#value1': typ) ->
    (#value2': typ) ->
    (p1': path from value1' {path_includes p1 p1'}) ->
    (p2': path from value2' {path_includes p2 p2' /\ path_disjoint p1 p2 /\ path_disjoint p1' p2' /\ x p1 p2}) ->
    Lemma (x p1' p2'))
  (#value1: typ)
  (#value2: typ)
  (p1: path from value1)
  (p2: path from value2 { path_disjoint p1 p2 } )
: Lemma (x p1 p2)
= let h : squash (path_disjoint_t p1 p2) = FStar.Squash.join_squash () in
  FStar.Squash.bind_squash h (fun (h: path_disjoint_t p1 p2) ->
   path_disjoint_t_rect
     (fun #v1 #v2 p1 p2 h -> let _ = FStar.Squash.return_squash h in squash (x p1 p2))
     (fun #through #to1 #to2 p s1 s2 h -> let _ = FStar.Squash.return_squash h in h_step p s1 s2)
     (fun #v1 #v2 p1 p2 #v1' #v2' p1' p2' h h' hx ->
       let _ = FStar.Squash.return_squash h in
       let _ = FStar.Squash.return_squash h' in
       let _ = FStar.Squash.return_squash hx in
       h_includes p1 p2 p1' p2')
     p1 p2 h)

private let path_disjoint_step
  (#from: typ)
  (#through: typ)
  (#to1: typ)
  (#to2: typ)
  (p: path from through)
  (s1: step through to1)
  (s2: step through to2 { step_disjoint s1 s2 } )
: Lemma
  (requires True)
  (ensures (path_disjoint (PathStep through to1 p s1) (PathStep through to2 p s2)))
  [SMTPat (path_disjoint (PathStep through to1 p s1) (PathStep through to2 p s2))]
= FStar.Squash.return_squash (PathDisjointStep p s1 s2)

private let path_disjoint_includes
  (#from: typ)
  (#to1: typ)
  (#to2: typ)
  (p1: path from to1)
  (p2: path from to2)
  (#to1': typ)
  (#to2': typ)
  (p1': path from to1')
  (p2': path from to2' {path_disjoint p1 p2 /\ path_includes p1 p1' /\ path_includes p2 p2'} )
: Lemma
  (ensures (path_disjoint p1' p2'))
= let h : squash (path_disjoint_t p1 p2) = FStar.Squash.join_squash () in
  FStar.Squash.bind_squash h (fun h -> FStar.Squash.return_squash (PathDisjointIncludes p1 p2 p1' p2' h))

private
let rec path_disjoint_sym
  (#from: typ)
  (#value1: typ)
  (#value2: typ)
  (p1: path from value1)
  (p2: path from value2)
: Lemma
  (requires (path_disjoint p1 p2))
  (ensures (path_disjoint p2 p1))
= path_disjoint_ind
  (fun #v1 #v2 p1 p2 -> path_disjoint p2 p1)
  (fun #through #to1 #to2 p s1 s2 -> path_disjoint_step p s2 s1)
  (fun #v1 #v2 p1 p2 #v1' #v2' p1' p2' -> path_disjoint_includes p2 p1 p2' p1')
  p1 p2

private let rec path_equal
  (#from: typ)
  (#value1: typ)
  (#value2: typ)
  (p1: path from value1)
  (p2: path from value2)
: Tot (b: bool { b == true <==> (value1 == value2 /\ p1 == p2) } )
  (decreases p1)
= match p1 with
  | PathBase -> PathBase? p2
  | PathStep _ _ p1' s1 ->
    PathStep? p2 && (
      let (PathStep _ _ p2' s2) = p2 in (
        path_equal p1' p2' &&
        step_eq s1 s2
    ))

private
let rec path_length_concat
  (#t0 #t1 #t2: typ)
  (p01: path t0 t1)
  (p12: path t1 t2)
: Lemma
  (requires True)
  (ensures (path_length (path_concat p01 p12) == path_length p01 + path_length p12))
  (decreases p12)
= match p12 with
  | PathBase -> ()
  | PathStep _ _ p' s' -> path_length_concat p01 p'

private
let rec path_concat_inj_l
  (#from #through1: typ)
  (p1_: path from through1)
  (#v1: typ)
  (p1: path through1 v1)
  (#through2 #v2: typ)
  (p2_: path from through2)
  (p2: path through2 v2)
: Lemma
  (requires (path_equal (path_concat p1_ p1) (path_concat p2_ p2) == true /\ path_length p1_ == path_length p2_))
  (ensures (path_equal p1_ p2_ == true /\ path_equal p1 p2 == true))
  (decreases p1)
= path_length_concat p1_ p1;
  path_length_concat p2_ p2;
  match p1 with
  | PathBase -> ()
  | PathStep _ _ p1' s1 ->
    let (PathStep _ _ p2' s2) = p2 in
    path_concat_inj_l p1_ p1' p2_ p2'

private type path_disjoint_decomp_t
  (#from: typ)
  (#value1: typ)
  (#value2: typ)
  (p1: path from value1)
  (p2: path from value2)
: Type
= | PathDisjointDecomp:
    (d_through: typ) ->
    (d_p: path from d_through) ->
    (d_v1: typ) ->
    (d_s1: step d_through d_v1) ->
    (d_p1': path d_v1 value1) ->
    (d_v2: typ) ->
    (d_s2: step d_through d_v2) ->
    (d_p2': path d_v2 value2) ->
    squash (
      step_eq d_s1 d_s2 == false /\
      p1 == path_concat (PathStep _ _ d_p d_s1) d_p1' /\
      p2 == path_concat (PathStep _ _ d_p d_s2) d_p2'
    ) ->
    path_disjoint_decomp_t p1 p2

#reset-options "--z3rlimit 16"

private let path_disjoint_decomp_includes
  (#from: typ)
  (#value1: typ)
  (#value2: typ)
  (p1: path from value1)
  (p2: path from value2)
  (#value1': typ)
  (#value2': typ)
  (p1': path from value1')
  (p2': path from value2')
: Lemma
  (requires (
    path_includes p1 p1' /\
    path_includes p2 p2' /\ (
    exists (d : path_disjoint_decomp_t p1 p2) . True
  )))
  (ensures (exists (d: path_disjoint_decomp_t p1' p2') . True))
= let f
    (q1: path value1 value1' )
    (q2: path value2 value2' )
    (d: path_disjoint_decomp_t p1 p2)
  : Lemma
    (requires (
      p1' == path_concat p1 q1 /\
      p2' == path_concat p2 q2
    ))
    (ensures (exists (d: path_disjoint_decomp_t p1' p2') . True))
  = let (PathDisjointDecomp _ p _ s1 p1_ _ s2 p2_ _) = d in
    path_concat_assoc (PathStep _ _ p s1) p1_ q1;
    path_concat_assoc (PathStep _ _ p s2) p2_ q2;
    let d' : path_disjoint_decomp_t p1' p2' =
      PathDisjointDecomp _ p _ s1 (path_concat p1_ q1) _ s2 (path_concat p2_ q2) ()
    in
    Classical.exists_intro (fun _ -> True) d'
  in
  let g
    (q1: path value1 value1' )
    (q2: path value2 value2' )
    (d: path_disjoint_decomp_t p1 p2)
  : Lemma
    ((
      p1' == path_concat p1 q1 /\
      p2' == path_concat p2 q2
    ) ==> (
      exists (d: path_disjoint_decomp_t p1' p2') . True
    ))
  = Classical.move_requires (f q1 q2) d // FIXME: annoying to repeat those type annotations above. WHY WHY WHY can't I just use (fun q1 q2 d -> Classical.move_requires (f q1 q2) d) as an argument of Classical.forall_intro_3 below instead of this g???
  in  
  path_includes_exists_concat p1 p1' ;
  path_includes_exists_concat p2 p2' ;
  let _ : squash (exists (d: path_disjoint_decomp_t p1' p2') . True) =
    Classical.forall_intro_3 g
  in
  ()

private
let path_disjoint_decomp
  (#from: typ)
  (#value1: typ)
  (#value2: typ)
  (p1: path from value1)
  (p2: path from value2)
: Lemma
  (requires (path_disjoint p1 p2))
  (ensures (exists (d: path_disjoint_decomp_t p1 p2) . True))
= path_disjoint_ind
  (fun #v1 #v2 p1 p2 -> exists (d: path_disjoint_decomp_t p1 p2) . True)
  (fun #through #to1 #to2 p s1 s2 ->
    let d : path_disjoint_decomp_t (PathStep _ _ p s1) (PathStep _ _ p s2) =
      PathDisjointDecomp _ p _ s1 PathBase _ s2 PathBase ()
    in
    Classical.exists_intro (fun _ -> True) d
  )
  (fun #v1 #v2 p1 p2 #v1' #v2' p1' p2' -> path_disjoint_decomp_includes p1 p2 p1' p2')
  p1 p2

private
let path_disjoint_not_path_equal
  (#from: typ)
  (#value1: typ)
  (#value2: typ)
  (p1: path from value1)
  (p2: path from value2)
: Lemma
  (requires (path_disjoint p1 p2))
  (ensures (path_equal p1 p2 == false))
= let f
    (d: path_disjoint_decomp_t p1 p2)
  : Lemma (path_equal p1 p2 == false)
  = if path_equal p1 p2
    then
      let (PathDisjointDecomp _ p _ s1 p1_ _ s2 p2_ _) = d in
      path_concat_inj_l (PathStep _ _ p s1) p1_ (PathStep _ _ p s2) p2_
    else ()
  in
  path_disjoint_decomp p1 p2;
  Classical.forall_intro f

private
let rec path_destruct_l
  (#t0 #t2: typ)
  (p: path t0 t2)
: Tot (
    x: option (t1: typ & (s: step t0 t1 & (p' : path t1 t2 { p == path_concat (PathStep _ _ PathBase s) p' /\ path_length p' < path_length p } ) ) )
    { None? x <==> PathBase? p }
  )
  (decreases p)
= match p with
  | PathBase -> None
  | PathStep _ _ p' s ->
    begin match path_destruct_l p' with
    | None -> Some (| _, (| s,  PathBase |) |)
    | Some (| t_, (| s_, p_ |) |) ->
      Some (| t_, (| s_, PathStep _ _ p_ s |) |)
    end

private
let rec path_equal'
  (#from #to1 #to2: typ)
  (p1: path from to1)
  (p2: path from to2)
: Tot (b: bool { b == true <==> to1 == to2 /\ p1 == p2 } )
  (decreases (path_length p1))
= match path_destruct_l p1 with
  | None -> PathBase? p2
  | Some (| t1, (| s1, p1' |) |) ->
    begin match path_destruct_l p2 with
    | None -> false
    | (Some (| t2, (| s2, p2' |) |) ) ->
      step_eq s1 s2 &&
      path_equal' p1' p2'
    end

private
let path_includes_concat_l
  (#from #through #to1 #to2: typ)
  (p0: path from through)
  (p1: path through to1)
  (p2: path through to2)
: Lemma
  (requires (path_includes p1 p2))
  (ensures (path_includes (path_concat p0 p1) (path_concat p0 p2)))
= path_includes_ind
    (fun #to1_ #to2_ p1_ p2_ -> path_includes (path_concat p0 p1_) (path_concat p0 p2_))
    (fun #through #to p st -> ())
    (fun #to p -> path_includes_refl (path_concat p0 p))
    (fun #to1_ #to2_ #to3_ p1_ p2_ p3_ -> path_includes_trans (path_concat p0 p1_) (path_concat p0 p2_) (path_concat p0 p3_))
    p1 p2

private
let path_disjoint_concat
  (#from #through #to1 #to2: typ)
  (p0: path from through)
  (p1: path through to1)
  (p2: path through to2)
: Lemma
  (requires (path_disjoint p1 p2))
  (ensures (path_disjoint (path_concat p0 p1) (path_concat p0 p2)))
= path_disjoint_ind
    (fun #v1 #v2 p1 p2 -> path_disjoint (path_concat p0 p1) (path_concat p0 p2))
    (fun #through #to1 #to2 p s1 s2 -> path_disjoint_step (path_concat p0 p) s1 s2)
    (fun #v1 #v2 p1 p2 #v1' #v2' p1' p2' ->
      path_includes_concat_l p0 p1 p1';
      path_includes_concat_l p0 p2 p2';
      path_disjoint_includes (path_concat p0 p1) (path_concat p0 p2) (path_concat p0 p1') (path_concat p0 p2'))
  p1 p2

private
let rec not_path_equal_path_disjoint_same_type
  (#from: typ)
  (#value: typ)
  (p1: path from value)
  (p2: path from value)
: Lemma
  (requires (path_equal p1 p2 == false))
  (ensures (path_disjoint p1 p2))
  (decreases (path_length p1))
= assert (path_equal p1 p2 == path_equal' p1 p2);
  match path_destruct_l p1 with
  | None -> path_typ_depth p2
  | Some (| t1, (| s1, p1' |) |) ->
    begin match path_destruct_l p2 with
    | None -> path_typ_depth p1
    | Some (| t2, (| s2, p2' |) |) ->
      if step_eq s1 s2
      then begin
	not_path_equal_path_disjoint_same_type p1' p2' ;
	path_disjoint_concat (PathStep _ _ PathBase s1) p1' p2'
      end else begin
        path_disjoint_step PathBase s1 s2;
	path_includes_concat (PathStep _ _ PathBase s1) p1';
	path_includes_concat (PathStep _ _ PathBase s2) p2';
	path_disjoint_includes (PathStep _ _ PathBase s1) (PathStep _ _ PathBase s2) p1 p2
      end
    end

private let path_sel_upd_other
  (#from: typ)
  (#to1 #to2: typ)
  (p1: path from to1)
  (p2: path from to2 {path_disjoint p1 p2})
: Lemma
  (ensures (forall (m: type_of_typ from) (v: type_of_typ to1) . path_sel (path_upd m p1 v) p2 == path_sel m p2))
= path_disjoint_ind
  (fun #v1 #v2 p1_ p2_ -> forall (m: type_of_typ from) (v: type_of_typ v1) . path_sel (path_upd m p1_ v) p2_ == path_sel m p2_)
  (fun #through #to1_ #to2_ p s1 s2 ->
      FStar.Classical.forall_intro' #_ #(fun m -> forall  (v: type_of_typ to1_) . path_sel (path_upd m (PathStep through to1_ p s1) v) (PathStep through to2_ p s2) == path_sel m (PathStep through to2_ p s2)) (fun m ->
	  FStar.Classical.forall_intro' #_ #(fun v -> path_sel (path_upd m (PathStep through to1_ p s1) v) (PathStep through to2_ p s2) == path_sel m (PathStep through to2_ p s2)) (fun v ->
	  match s1 with
	  | StepField l1 fd1 ->
	    let (StepField _ fd2) = s2 in
	    let (s: struct l1) = path_sel m p in
	    path_sel_upd_same m p (struct_upd s fd1 v);
	    DM.sel_upd_other s fd1 v fd2
	  | StepCell length1 value1 i1 ->
	    let (StepCell _ _ i2) = s2 in
	    path_sel_upd_same m p (Seq.upd (path_sel m p) (UInt32.v i1) v);
	    Seq.lemma_index_upd2 (path_sel m p) (UInt32.v i1) v (UInt32.v i2)
      )))
  (fun #v1 #v2 p1 p2 #v1' #v2' p1' p2' ->
    let h1: squash (exists r1 . p1' == path_concat p1 r1) = path_includes_exists_concat p1 p1' in
    let h2: squash (exists r2 . p2' == path_concat p2 r2) = path_includes_exists_concat p2 p2' in
    FStar.Classical.forall_intro' #_ #(fun (m: type_of_typ from) -> forall v . path_sel (path_upd m p1' v) p2' == path_sel m p2') (fun (m: type_of_typ from) ->
      FStar.Classical.forall_intro' #_ #(fun (v: type_of_typ v1') -> path_sel (path_upd m p1' v) p2' == path_sel m p2') (fun (v: type_of_typ v1') ->
      FStar.Classical.exists_elim (path_sel (path_upd m p1' v) p2' == path_sel m p2') h1 (fun r1 ->
	FStar.Classical.exists_elim (path_sel (path_upd m p1' v) p2' == path_sel m p2') h2 (fun r2 ->
	  path_upd_concat m p1 r1 v;
	  path_sel_concat m p2 r2
	  )))))
  p1 p2

private let path_sel_upd_other'
  (#from: typ)
  (#to1 #to2: typ)
  (p1: path from to1)
  (p2: path from to2 {path_disjoint p1 p2})
  (m: type_of_typ from)
  (v: type_of_typ to1)
: Lemma
  (requires True)
  (ensures (path_sel (path_upd m p1 v) p2 == path_sel m p2))
  [SMTPat (path_sel (path_upd m p1 v) p2)]
= path_sel_upd_other p1 p2

(** Operations on pointers *)

abstract let equal
  (#t1 #t2: typ)
  (p1: pointer t1)
  (p2: pointer t2)
: Ghost bool
  (requires True)
  (ensures (fun b -> b == true <==> t1 == t2 /\ p1 == p2 ))
= Pointer?.from p1 = Pointer?.from p2 &&
  HS.aref_equal (Pointer?.contents p1) (Pointer?.contents p2) &&
  path_equal p1.p p2.p

abstract let as_addr (#t: typ) (p: pointer t): GTot nat =
  HS.aref_as_addr (Pointer?.contents p)

private let _field
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
: Tot (pointer (typ_of_struct_field l fd))
= let (Pointer from contents p') = p in
  let p' : path from (TStruct l) = p' in
  let p'' : path from (typ_of_struct_field l fd) = PathStep _ _ p' (StepField _ fd) in
  Pointer from contents p''

private let _cell
  (#length: UInt32.t)
  (#value: typ)
  (p: pointer (TArray length value))
  (i: UInt32.t {UInt32.v i < UInt32.v length})
: Tot (pointer value)
= let (Pointer from contents p') = p in
  let p' : path from (TArray length value) = p' in
  let p'' : path from value = PathStep _ _ p' (StepCell _ _ i) in
  Pointer from contents p''

abstract let unused_in
  (#value: typ)
  (p: pointer value)
  (h: HS.mem)
: GTot Type0
= let (Pointer from contents p') = p in
  HS.aref_unused_in contents h

private
let pointer_ref_contents : Type0 = (t: typ & type_of_typ t)

abstract let live
  (#value: typ)
  (h: HS.mem)
  (p: pointer value)
: GTot Type0
= let (Pointer from contents _) = p in (
    HS.aref_live_at h contents pointer_ref_contents /\ (
      let untyped_contents = HS.greference_of contents pointer_ref_contents in (
      dfst (HS.sel h untyped_contents) == from
  )))

private let greference_of
  (#value: typ)
  (p: pointer value)
: Ghost (HS.reference pointer_ref_contents)
  (requires (exists h . live h p))
  (ensures (fun x -> (exists h . live h p) /\ x == HS.greference_of (Pointer?.contents p) pointer_ref_contents /\ HS.aref_of x == Pointer?.contents p))
= HS.greference_of (Pointer?.contents p) pointer_ref_contents

private
let reference_of
  (h: HS.mem)
  (#value: typ)
  (p: pointer value)
: Pure (HS.reference pointer_ref_contents)
  (requires (live h p))
  (ensures (fun x -> live h p /\ x == greference_of p))
= HS.reference_of h (Pointer?.contents p) pointer_ref_contents

private
let unused_in_greference_of
  (#value: typ)
  (p: pointer value)
  (h: HS.mem)
: Lemma
  (requires (exists h . live h p))
  (ensures ((exists h . live h p) /\ (HS.unused_in (greference_of p) h <==> unused_in p h)))
  [SMTPatOr [
    [SMTPat (HS.unused_in (greference_of p) h)];
    [SMTPat (unused_in p h)];
  ]]
= ()

abstract let live_not_unused_in
  (#value: typ)
  (h: HS.mem)
  (p: pointer value)
: Lemma
  (ensures (live h p /\ p `unused_in` h ==> False))
  [SMTPatT (live h p); SMTPatT (p `unused_in` h)]
= let f () : Lemma
    (requires (live h p /\ p `unused_in` h))
    (ensures False)
  = let r = greference_of p in
    HS.contains_aref_unused_in h r (Pointer?.contents p)
  in
  Classical.move_requires f ()

abstract let gread
  (#value: typ)
  (h: HS.mem)
  (p: pointer value)
: GTot (type_of_typ value)
= if StrongExcludedMiddle.strong_excluded_middle (live h p)
  then
    let content = greference_of p in
    let (| _, c |) = HS.sel h content in
    path_sel c p.p
  else
    dummy_val value

abstract let frameOf
  (#value: typ)
  (p: pointer value)
: GTot HH.rid
= HS.frameOf_aref (Pointer?.contents p)

abstract let disjoint_roots_intro_pointer_vs_pointer
  (#value1 value2: typ)
  (h: HS.mem)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (requires (live h p1 /\ unused_in p2 h))
  (ensures (frameOf p1 <> frameOf p2 \/ as_addr p1 =!= as_addr p2))
= ()

abstract let disjoint_roots_intro_pointer_vs_reference
  (#value1: typ)
  (#value2: Type)
  (h: HS.mem)
  (p1: pointer value1)
  (p2: HS.reference value2)
: Lemma
  (requires (live h p1 /\ p2 `HS.unused_in` h))
  (ensures (frameOf p1 <> HS.frameOf p2 \/ as_addr p1 =!= HS.as_addr p2))
= ()

abstract let disjoint_roots_intro_reference_vs_pointer
  (#value1: Type)
  (#value2: typ)
  (h: HS.mem)
  (p1: HS.reference value1)
  (p2: pointer value2)
: Lemma
  (requires (HS.contains h p1 /\ p2 `unused_in` h))
  (ensures (HS.frameOf p1 <> frameOf p2 \/ HS.as_addr p1 =!= as_addr p2))
= ()

abstract let is_mm
  (#value: typ)
  (p: pointer value)
: GTot bool
= HS.aref_is_mm (Pointer?.contents p)

(* // TODO: recover with addresses?
abstract let recall
  (#value: Type)
  (p: pointer value {HS.is_eternal_region (frameOf p) && not (is_mm p)})
: HST.Stack unit
  (requires (fun m -> True))
  (ensures (fun m0 _ m1 -> m0 == m1 /\ live m1 p))
= HST.recall (Pointer?.content p)
*)

(* Equality predicate on struct contents, without quantifiers *)
let equal_values #a h (b:pointer a) h' (b':pointer a) : GTot Type0 =
  live h b /\ live h' b' /\ gread h b == gread h' b'

abstract let includes
  (#value1: typ)
  (#value2: typ)
  (p1: pointer value1)
  (p2: pointer value2)
: GTot bool
= Pointer?.from p1 = Pointer?.from p2 &&
  HS.aref_equal (Pointer?.contents p1) (Pointer?.contents p2) &&
  path_includes (Pointer?.p p1) (Pointer?.p p2)

#reset-options "--z3rlimit 16"

abstract let gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
: GTot (p' : pointer (typ_of_struct_field l fd) { includes p p' } )
= _field p fd

abstract let as_addr_gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires True)
  (ensures (as_addr (gfield p fd) == as_addr p))
  [SMTPat (as_addr (gfield p fd))]
= ()

abstract let unused_in_gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
  (h: HS.mem)
: Lemma
  (requires True)
  (ensures (unused_in (gfield p fd) h <==> unused_in p h))
  [SMTPat (unused_in (gfield p fd) h)]
= ()

abstract let live_gfield
  (h: HS.mem)
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires True)
  (ensures (live h (gfield p fd) <==> live h p))
  [SMTPat (live h (gfield p fd))]
= ()

abstract let gread_gfield
  (h: HS.mem)
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires True)
  (ensures (gread h (gfield p fd) == struct_sel (gread h p) fd))
  [SMTPatOr [[SMTPat (gread h (gfield p fd))]; [SMTPat (struct_sel (gread h p) fd)]]]
= ()

abstract let frameOf_gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires True)
  (ensures (frameOf (gfield p fd) == frameOf p))
  [SMTPat (frameOf (gfield p fd))]
= ()

abstract let is_mm_gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires True)
  (ensures (is_mm (gfield p fd) <==> is_mm p))
  [SMTPat (is_mm (gfield p fd))]
= ()

abstract let includes_gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires True)
  (ensures (includes p (gfield p fd)))
  [SMTPat (includes p (gfield p fd))]
= ()

abstract let gcell
  (#length: UInt32.t)
  (#value: typ)
  (p: pointer (TArray length value))
  (i: UInt32.t {UInt32.v i < UInt32.v length})
: GTot (pointer value)
= _cell p i

abstract let as_addr_gcell
  (#length: UInt32.t)
  (#value: typ)
  (p: pointer (TArray length value))
  (i: UInt32.t {UInt32.v i < UInt32.v length})
: Lemma
  (requires True)
  (ensures (as_addr (gcell p i) == as_addr p))
  [SMTPat (as_addr (gcell p i))]
= ()

abstract let unused_in_gcell
  (#length: UInt32.t)
  (#value: typ)
  (h: HS.mem)
  (p: pointer (TArray length value))
  (i: UInt32.t {UInt32.v i < UInt32.v length})
: Lemma
  (requires True)
  (ensures (unused_in (gcell p i) h <==> unused_in p h))
  [SMTPat (unused_in (gcell p i) h)]
= ()

abstract let live_gcell
  (#length: UInt32.t)
  (#value: typ)
  (h: HS.mem)
  (p: pointer (TArray length value))
  (i: UInt32.t {UInt32.v i < UInt32.v length})
: Lemma
  (requires True)
  (ensures (live h (gcell p i) <==> live h p))
  [SMTPat (live h (gcell p i))]
= ()

abstract let gread_gcell
  (#length: UInt32.t)
  (#value: typ)
  (h: HS.mem)
  (p: pointer (TArray length value))
  (i: UInt32.t {UInt32.v i < UInt32.v length})
: Lemma
  (requires True)
  (ensures (gread h (gcell p i) == Seq.index (gread h p) (UInt32.v i)))
  [SMTPat (gread h (gcell p i))]
= ()

abstract let frameOf_gcell
  (#length: UInt32.t)
  (#value: typ)
  (p: pointer (TArray length value))
  (i: UInt32.t {UInt32.v i < UInt32.v length})
: Lemma
  (requires True)
  (ensures (frameOf (gcell p i) == frameOf p))
  [SMTPat (frameOf (gcell p i))]
= ()

abstract let is_mm_gcell
  (#length: UInt32.t)
  (#value: typ)
  (p: pointer (TArray length value))
  (i: UInt32.t {UInt32.v i < UInt32.v length})
: Lemma
  (requires True)
  (ensures (is_mm (gcell p i) == is_mm p))
  [SMTPat (is_mm (gcell p i))]
= ()

abstract let includes_gcell
  (#length: UInt32.t)
  (#value: typ)
  (p: pointer (TArray length value))
  (i: UInt32.t {UInt32.v i < UInt32.v length})
: Lemma
  (requires True)
  (ensures (includes p (gcell p i)))
  [SMTPat (includes p (gcell p i))]
= ()

abstract let includes_refl
  (#value: typ)
  (p: pointer value)
: Lemma
  (requires True)
  (ensures (includes p p))
  [SMTPat (includes p p)]
= ()

abstract let includes_trans
  (#value1 #value2 #value3: typ)
  (p1: pointer value1)
  (p2: pointer value2)
  (p3: pointer value3)
: Lemma
  (requires (includes p1 p2 /\ includes p2 p3))
  (ensures (includes p1 p3))
  [SMTPatT (includes p1 p2); SMTPatT (includes p2 p3)]
= path_includes_trans (Pointer?.p p1) (Pointer?.p p2) (Pointer?.p p3)

abstract let includes_ind
  (x: (#value1: typ) ->
      (#value2: typ) ->
      (p1: pointer value1) ->
      (p2: pointer value2 {includes p1 p2} ) ->
      GTot Type0)
  (h_field:
    (l: struct_typ) ->
    (p: pointer (TStruct l)) ->
    (fd: struct_field l {includes p (gfield p fd)}) ->
    Lemma (x p (gfield p fd)))
  (h_cell:
    (#length: UInt32.t) ->
    (#value: typ) ->
    (p: pointer (TArray length value)) ->
    (i: UInt32.t {UInt32.v i < UInt32.v length /\ includes p (gcell p i)}) ->
    Lemma (x p (gcell p i)))
  (h_refl:
    (#value: typ) ->
    (p: pointer value {includes p p}) ->
    Lemma (x p p))
  (h_trans:
    (#value1: typ) ->
    (#value2: typ) ->
    (#value3: typ) ->
    (p1: pointer value1) ->
    (p2: pointer value2) ->
    (p3: pointer value3 {includes p1 p2 /\ includes p2 p3 /\ includes p1 p3 /\ x p1 p2 /\ x p2 p3}) ->
    Lemma (x p1 p3))
  (#value1: typ)
  (#value2: typ)
  (p1: pointer value1)
  (p2: pointer value2 {includes p1 p2})
: Lemma (x p1 p2)
= let (Pointer from contents _) = p1 in
  path_includes_ind
    (fun #to1 #to2 p1_ p2_ -> x (Pointer from contents p1_) (Pointer from contents p2_))
    (fun #through #to p s ->
      match s with
      | StepField l fd -> let (pt: pointer (TStruct l)) = (Pointer from contents p) in h_field l pt fd
      | StepCell length value i -> let (pt: pointer (TArray length value)) = (Pointer from contents p) in h_cell pt i
    )
    (fun #to p -> h_refl (Pointer from contents p))
    (fun #to1 #to2 #to3 p1_ p2_ p3_ -> h_trans (Pointer from contents p1_) (Pointer from contents p2_) (Pointer from contents p3_))
    (Pointer?.p p1)
    (Pointer?.p p2)

abstract
let unused_in_includes
  (#value1: typ)
  (#value2: typ)
  (h: HS.mem)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (requires (includes p1 p2))
  (unused_in p1 h <==> unused_in p2 h)
  [SMTPatT (unused_in p2 h); SMTPatT (includes p1 p2)]
= includes_ind
  (fun #v1 #v2 p1 p2 -> unused_in p1 h <==> unused_in p2 h)
  (fun l p fd -> unused_in_gfield p fd h)
  (fun #length #value p i -> unused_in_gcell h p i)
  (fun #v p -> ())
  (fun #v1 #v2 #v3 p1 p2 p3 -> ())
  p1 p2

abstract
let live_includes
  (#value1: typ)
  (#value2: typ)
  (h: HS.mem)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (requires (includes p1 p2))
  (ensures (live h p1 <==> live h p2))
  [SMTPatT (live h p2); SMTPatT (includes p1 p2)]
= includes_ind
  (fun #v1 #v2 p1 p2 -> live h p1 <==> live h p2)
  (fun l p fd -> live_gfield h p fd)
  (fun #length #value p i -> live_gcell h p i)
  (fun #v p -> ())
  (fun #v1 #v2 #v3 p1 p2 p3 -> ())
  p1 p2

abstract let disjoint
  (#value1: typ)
  (#value2: typ)
  (p1: pointer value1)
  (p2: pointer value2)
: GTot Type0
= if
    frameOf p1 = frameOf p2 &&
    as_addr p1 = as_addr p2
  then
    Pointer?.from p1 == Pointer?.from p2 /\
    Pointer?.contents p1 == Pointer?.contents p2 /\
    path_disjoint (Pointer?.p p1) (Pointer?.p p2)
  else
    True

abstract let disjoint_root
  (#value1: typ)
  (#value2: typ)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (requires (frameOf p1 <> frameOf p2 \/ as_addr p1 <> as_addr p2))
  (ensures (disjoint p1 p2))
= ()

abstract let disjoint_gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd1 fd2: struct_field l)
: Lemma
  (requires (fd1 <> fd2))
  (ensures (disjoint (gfield p fd1) (gfield p fd2)))
  [SMTPat (disjoint (gfield p fd1) (gfield p fd2))]
= ()

abstract let disjoint_gcell
  (#length: UInt32.t)
  (#value: typ)
  (p: pointer (TArray length value))
  (i1: UInt32.t {UInt32.v i1 < UInt32.v length})
  (i2: UInt32.t {UInt32.v i2 < UInt32.v length})
: Lemma
  (requires (UInt32.v i1 <> UInt32.v i2))
  (ensures (disjoint (gcell p i1) (gcell p i2)))
  [SMTPat (disjoint (gcell p i1) (gcell p i2))]
= ()

abstract let disjoint_includes
  (#value1: typ)
  (#value2: typ)
  (p1: pointer value1)
  (p2: pointer value2)
  (#value1': typ)
  (#value2': typ)
  (p1': pointer value1')
  (p2': pointer value2')
: Lemma
  (requires (includes p1 p1' /\ includes p2 p2' /\ disjoint p1 p2))
  (ensures (disjoint p1' p2'))
= if
    frameOf p1 = frameOf p2 &&
    as_addr p1 = as_addr p2
  then
    path_disjoint_includes (Pointer?.p p1) (Pointer?.p p2) (Pointer?.p p1') (Pointer?.p p2')
  else
    ()

abstract let disjoint_ind
  (x:
    (#value1: typ) ->
    (#value2: typ) ->
    (p1: pointer value1) ->
    (p2: pointer value2 {disjoint p1 p2} ) ->
    GTot Type0)
  (h_root:
    (#value1: typ) ->
    (#value2: typ) ->
    (p1: pointer value1) ->
    (p2: pointer value2 { frameOf p1 <> frameOf p2 \/ as_addr p1 <> as_addr p2 } ) ->
    Lemma (x p1 p2))
  (h_field:
    (#l: struct_typ) ->
    (p: pointer (TStruct l)) ->
    (fd1: struct_field l) ->
    (fd2: struct_field l { fd1 <> fd2 /\ disjoint (gfield p fd1) (gfield p fd2) } ) ->
    Lemma (x (gfield p fd1) (gfield p fd2)))
  (h_cell:
    (#length: UInt32.t) ->
    (#value: typ) ->
    (p: pointer (TArray length value)) ->
    (i1: UInt32.t {UInt32.v i1 < UInt32.v length}) ->
    (i2: UInt32.t {UInt32.v i2 < UInt32.v length /\ UInt32.v i1 <> UInt32.v i2 /\ disjoint (gcell p i1) (gcell p i2) }) ->
    Lemma (x (gcell p i1) (gcell p i2))
  )
  (h_includes:
    (#value1: typ) ->
    (#value2: typ) ->
    (p1: pointer value1) ->
    (p2: pointer value2) ->
    (#value1': typ) ->
    (#value2': typ) ->
    (p1': pointer value1' {includes p1 p1'}) ->
    (p2': pointer value2' {includes p2 p2' /\ disjoint p1 p2 /\ disjoint p1' p2' /\ x p1 p2}) ->
    Lemma (x p1' p2'))
  (#value1: typ)
  (#value2: typ)
  (p1: pointer value1)
  (p2: pointer value2 { disjoint p1 p2 } )
: Lemma (x p1 p2)
= if
    frameOf p1 = frameOf p2 &&
    as_addr p1 = as_addr p2
  then
    let (Pointer from contents _) = p1 in
    path_disjoint_ind
      (fun #v1 #v2 p1_ p2_ -> x (Pointer from contents p1_) (Pointer from contents p2_))
      (fun #through #to1 #to2 p s1 s2 ->
         match s1 with
         | StepField l fd1 ->
           let (StepField _ fd2) = s2 in
           h_field #l (Pointer from contents p) fd1 fd2
         | StepCell le va i1 ->
           let (StepCell _ _ i2) = s2 in
           h_cell #le #va (Pointer from contents p) i1 i2
      )
      (fun #v1 #v2 p1_ p2_ #v1' #v2' p1' p2' -> h_includes (Pointer from contents p1_) (Pointer from contents p2_) (Pointer from contents p1') (Pointer from contents p2'))
      (Pointer?.p p1)
      (Pointer?.p p2);
      assert (x p1 p2)
  else
    h_root p1 p2

abstract
let disjoint_sym
  (#value1: typ)
  (#value2: typ)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (requires (disjoint p1 p2))
  (ensures (disjoint p2 p1))
= disjoint_ind
  (fun #v1 #v2 p1 p2 -> disjoint p2 p1)
  (fun #v1 #v2 p1 p2 -> disjoint_root p2 p1)
  (fun #l p fd1 fd2 -> disjoint_gfield p fd2 fd1)
  (fun #le #va p i1 i2 -> disjoint_gcell p i2 i1)
  (fun #v1 #v2 p1 p2 #v1' #v2' p1' p2' -> disjoint_includes p2 p1 p2' p1')
  p1 p2

abstract
let disjoint_sym'
  (#value1: typ)
  (#value2: typ)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (requires True)
  (ensures (disjoint p1 p2 <==> disjoint p2 p1))
  [SMTPat (disjoint p1 p2)]
= FStar.Classical.move_requires (disjoint_sym #value1 #value2 p1) p2;
  FStar.Classical.move_requires (disjoint_sym #value2 #value1 p2) p1

abstract
let disjoint_includes_l #a #as #a' (x: pointer a) (subx:pointer as) (y:pointer a') : Lemma
  (requires (includes x subx /\ disjoint x y))
  (ensures  (disjoint subx y))
  [SMTPatT (disjoint subx y); SMTPatT (includes x subx)]
  = disjoint_includes x y subx y

abstract
let disjoint_includes_l_swap #a #as #a' (x:pointer a) (subx:pointer as) (y:pointer a') : Lemma
  (requires (includes x subx /\ disjoint x y))
  (ensures  (disjoint y subx))
  [SMTPatT (disjoint y subx); SMTPatT (includes x subx)]
  = ()

abstract
let live_not_equal_disjoint
  (#t: typ)
  (h: HS.mem)
  (p1 p2: pointer t)
: Lemma
  (requires (live h p1 /\ live h p2 /\ equal p1 p2 == false))
  (ensures (disjoint p1 p2))
= if
    frameOf p1 = frameOf p2 &&
    as_addr p1 = as_addr p2
  then begin
    let c1 = greference_of p1 in
    let c2 = greference_of p2 in
    HS.lemma_same_addrs_same_types_same_refs h c1 c2;
    not_path_equal_path_disjoint_same_type p1.p p2.p
  end else
    disjoint_root p1 p2

abstract
let live_unused_in_disjoint_strong
  (#value1: typ)
  (#value2: typ)
  (h: HS.mem)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (requires (live h p1 /\ unused_in p2 h))
  (ensures (frameOf p1 <> frameOf p2 \/ as_addr p1 <> as_addr p2))
= ()

abstract
let live_unused_in_disjoint
  (#value1: typ)
  (#value2: typ)
  (h: HS.mem)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (requires (live h p1 /\ unused_in p2 h))
  (ensures (disjoint p1 p2))
  [SMTPatT (disjoint p1 p2); SMTPatT (live h p1)]
= live_unused_in_disjoint_strong h p1 p2;
  disjoint_root p1 p2

(*** The modifies clause *)

// private // in fact, we have to expose this type, otherwise unification problems will appear everywhere
noeq type apointer =
| APointer:
  (a: typ) ->
  (p: pointer a) ->
  apointer

(** Sets of pointers. The set tracks not only the set of pointers, but
also the corresponding set of addresses (which cannot be constructed
by set comprehension, since it must be computational.)

In practice, we assume that all pointers in a set should be of the
same region, because that is how the modifies clause will be
defined. However, we do not need to enforce this constraint.

We could also completely remove this "assumption" and explicitly track
the regions and addresses within those regions. But this way would
actually defeat the practical purpose of regions.
*)
private
let set_addrs_t (pointers : TSet.set apointer) =
  addrs:Set.set nat {
    forall (n: nat) .
      Set.mem n addrs <==>
      (exists (x: apointer) . TSet.mem x pointers /\ as_addr (APointer?.p x) == n) }

abstract
noeq type set =
| Set:
  (pointers: TSet.set apointer) ->
  (addrs: Ghost.erased (set_addrs_t pointers) ) ->
  set

abstract
let set_amem
  (a: apointer)
  (s: set)
: GTot Type0
= TSet.mem a (Set?.pointers s)

let set_mem
  (#a: typ)
  (p: pointer a)
  (s: set)
: GTot Type0
= set_amem (APointer a p) s

abstract let set_empty: set =
  Set TSet.empty (Ghost.hide Set.empty)

abstract let set_amem_empty
  (x: apointer)
: Lemma
  (~ (set_amem x set_empty))
  [SMTPat (set_amem x set_empty)]
= ()

abstract let set_singleton
  (#a: typ)
  (x: pointer a)
: Tot set
=
  let pointers = TSet.singleton (APointer a x) in
  let f () : GTot (set_addrs_t pointers) = Set.singleton (as_addr x) in
  Set pointers (Ghost.elift1 f (Ghost.hide ()))

abstract let set_amem_singleton
  (#a: typ)
  (x: pointer a)
  (x': apointer)
: Lemma
  (set_amem x' (set_singleton x) <==> (x' == APointer a x))
  [SMTPat (set_amem x' (set_singleton x))]
= ()

abstract let set_union
  (s1 s2: set)
: Tot set
= let pointers = TSet.union (Set?.pointers s1) (Set?.pointers s2) in
  let union (addrs1:set_addrs_t (Set?.pointers s1)) (addrs2:set_addrs_t (Set?.pointers s2))
    : set_addrs_t pointers
    = Set.union addrs1 addrs2
  in
  Set pointers (Ghost.elift2 union (Set?.addrs s1) (Set?.addrs s2))

abstract let set_amem_union
  (x: apointer)
  (s1 s2: set)
: Lemma
  (set_amem x (set_union s1 s2) <==> set_amem x s1 \/ set_amem x s2)
  [SMTPat (set_amem x (set_union s1 s2))]
= ()

let set_subset
  (s1 s2: set)
: Tot Type0
= forall (x: apointer) . set_amem x s1 ==> set_amem x s2

let set_equal
  (s1 s2: set)
: Tot Type0
= set_subset s1 s2 /\ set_subset s2 s1

abstract
let set_equal_elim
  (s1 s2: set)
: Lemma
  (requires (set_equal s1 s2))
  (ensures (s1 == s2))
= TSet.lemma_equal_intro (Set?.pointers s1) (Set?.pointers s2);
  TSet.lemma_equal_elim (Set?.pointers s1) (Set?.pointers s2);
  let k6 : squash (Set?.addrs s1 == Set?.addrs s2) =
    (* FIXME: WHY WHY WHY do I need to define this trans with explicit squash? Without it, verification fails, even with higher rlimits. With requires instead of squash, verification also fails. *)
    let trans
      (#a: Type)
      (e1 e2 e3: a)
      (k1: squash (e1 == e2))
      (k2: squash (e2 == e3))
    : Lemma
      (ensures (e1 == e3))
    = ()
    in
    let k4 : squash (Set?.addrs s1 == Ghost.hide (Ghost.reveal (Set?.addrs s2))) =
      Set.lemma_equal_elim (Ghost.reveal (Set?.addrs s1)) (Ghost.reveal (Set?.addrs s2));
      Ghost.hide_reveal (Set?.addrs s1)
    in
    let k5: squash (Ghost.hide (Ghost.reveal (Set?.addrs s2)) == Set?.addrs s2) =
      Ghost.hide_reveal (Set?.addrs s2)
    in
    trans (Set?.addrs s1) (Ghost.hide (Ghost.reveal (Set?.addrs s2))) (Set?.addrs s2) k4 k5
  in
  ()

(** NOTE: intersection cannot be easily defined, indeed consider two
different (not necessarily disjoint) pointers p1, p2 coming from the
same root address, intersect (singleton p1) (singleton p2) will be
empty whereas intersect (singleton (as_addr p1)) (singleton (as_addr
p2)) will not.

However, if the pointer type had decidable equality, then it should work, by
recording, for each address, the computational set of pointers in the
global set of pointers, that have that address; and so the set of
addresses will be computed as: every address whose corresponding set of
pointers is nonempty.

Anyway, it seems that we will not need intersection for use with the
modifies clauses.

*)

(** Pointer inclusion lifted to sets of pointers *)

let set_includes
  (s1 s2: set)
: GTot Type0
= forall (ap2: apointer { set_amem ap2 s2 } ) .
  exists (ap1: apointer { set_amem ap1 s1 } ) .
  (APointer?.p ap1) `includes` (APointer?.p ap2)

let set_includes_refl
  (s: set)
: Lemma
  (set_includes s s)
= ()

let set_includes_trans
  (s1 s2 s3: set)
: Lemma
  (requires (set_includes s1 s2 /\ set_includes s2 s3))
  (ensures (set_includes s1 s3))
= ()

let set_subset_includes
  (s1 s2: set)
: Lemma
  (requires (s2 `set_subset` s1))
  (ensures (s1 `set_includes` s2))
= assert (
    forall (ap2: apointer { set_amem ap2 s2 } ) .
    let (ap1: apointer { set_amem ap1 s1 } ) = ap2 in
    (APointer?.p ap1) `includes` (APointer?.p ap2)
  )

let set_includes_singleton
  (#a1: typ)
  (p1: pointer a1)
  (#a2: typ)
  (p2: pointer a2)
: Lemma
  (requires (p1 `includes` p2))
  (ensures (set_singleton p1 `set_includes` set_singleton p2))
= let s1 = set_singleton p1 in
  let (ap1 : apointer { set_amem ap1 s1 } ) = APointer a1 p1 in
  ()

(** The modifies clause proper *)

abstract
let modifies
  (r: HH.rid)
  (s: set)
  (h1 h2: HS.mem)
: GTot Type0
= HS.modifies_ref r (Ghost.reveal (Set?.addrs s)) h1 h2 /\ (
    forall (a': apointer { frameOf (APointer?.p a') == r /\ live h1 (APointer?.p a') } ) . (
      forall (a: apointer { frameOf (APointer?.p a) == r /\ TSet.mem a (Set?.pointers s) } ) .
      disjoint (APointer?.p a) (APointer?.p a')
    ) ==> (
    live h2 (APointer?.p a') /\ gread h1 (APointer?.p a') == gread h2 (APointer?.p a')
  ))

abstract
let modifies_modifies_ref
  (r: HH.rid)
  (s: set)
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies r s h1 h2))
  (ensures (
    exists (rs: Set.set nat) .
    HS.modifies_ref r rs h1 h2 /\ (
    forall (x: nat) . Set.mem x rs <==> (
    exists (a: typ) (p: pointer a) .
    set_mem p s /\
    as_addr p == x
  ))))
= ()

abstract
let modifies_elim
  (r: HH.rid)
  (s: set)
  (h1 h2: HS.mem)
  (#a': typ)
  (p': pointer a')
: Lemma
  (requires (
    modifies r s h1 h2 /\
    frameOf p' == r /\
    live h1 p' /\ (
    forall (ap: apointer { frameOf (APointer?.p ap) == r /\ set_amem ap s } ) .
    disjoint (APointer?.p ap) p'
  )))
  (ensures (
    live h2 p' /\
    gread h1 p' == gread h2 p'
  ))
= let ap' = APointer a' p' in
  assert (p' == APointer?.p ap')

abstract
let modifies_intro
  (r: HH.rid)
  (s: set)
  (h1 h2: HS.mem)
  (rs: Set.set nat)
: Lemma
  (requires (
    HS.modifies_ref r rs h1 h2 /\ (
      forall (n: nat) . Set.mem n rs <==> (
      exists (a: typ) (p: pointer a) .
      set_mem p s /\
      as_addr p == n
    )) /\ (
      forall (a': typ) (p': pointer a' { frameOf p' == r /\ live h1 p' } ) . (
        forall (ap: apointer { frameOf (APointer?.p ap) == r /\ set_amem ap s } ) .
        disjoint (APointer?.p ap) p'
      ) ==> (
        live h2 p' /\
        gread h1 p' == gread h2 p'
  ))))
  (ensures (modifies r s h1 h2))
= Set.lemma_equal_elim rs (Ghost.reveal (Set?.addrs s))

abstract
let modifies_refl
  (r: HH.rid)
  (s: set)
  (h: HS.mem)
: Lemma
  (modifies r s h h)
  [SMTPat (modifies r s h h)]
= ()

abstract
let modifies_subset
  (r: HH.rid)
  (s1: set)
  (h h': HS.mem)
  (s2: set)
: Lemma
  (requires (modifies r s1 h h' /\ set_subset s1 s2))
  (ensures (modifies r s2 h h'))
= ()

abstract
let modifies_trans'
  (r: HH.rid)
  (s12: set)
  (h1 h2: HS.mem)
  (s23: set)
  (h3: HS.mem)
: Lemma
  (requires (modifies r s12 h1 h2 /\ modifies r s23 h2 h3))
  (ensures (modifies r (set_union s12 s23) h1 h3))
= ()

abstract
let modifies_trans
  (r: HH.rid)
  (s12: set)
  (h1 h2: HS.mem)
  (s23: set)
  (h3: HS.mem)
  (s13: set)
: Lemma
  (requires (modifies r s12 h1 h2 /\ modifies r s23 h2 h3 /\ set_subset (set_union s12 s23) s13))
  (ensures (modifies r s13 h1 h3))
= modifies_trans' r s12 h1 h2 s23 h3;
  modifies_subset r (set_union s12 s23) h1 h3 s13

abstract
let modifies_set_includes
  (r: HH.rid)
  (s1 s2: set)
  (h h': HS.mem)
: Lemma
  (requires (modifies r s2 h h' /\ s1 `set_includes` s2))
  (ensures (modifies r s1 h h'))
= ()

(* Specialized clauses for small numbers of pointers *)
let modifies_ptr_0 rid h h' =
  modifies rid set_empty h h'

let modifies_ptr_1 (#t:typ) rid (b:pointer t) h h' = //would be good to drop the rid argument on these, since they can be computed from the pointers
  modifies rid (set_singleton b) h h'

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
  HS.modifies_one h0.HS.tip h0 h1
  /\ modifies_ptr_0 h0.HS.tip h0 h1
  /\ h0.HS.tip=h1.HS.tip

(* This one is very generic: it says
 * - some references have changed in the frame of b, but
 * - among all pointers in this frame, b is the only one that changed. *)
abstract let modifies_1 (#a:typ) (b:pointer a) h0 h1 =
  let rid = frameOf b in
  HS.modifies_one rid h0 h1 /\ modifies_ptr_1 rid b h0 h1

(* Lemmas introducing the 'modifies' predicates *)
let modifies_0_intro h0 h1 : Lemma
  (requires (HS.modifies_one h0.HS.tip h0 h1
  /\ modifies_ptr_0 h0.HS.tip h0 h1
  /\ h0.HS.tip=h1.HS.tip))
  (ensures  (modifies_0 h0 h1))
  = ()

let modifies_1_intro (#a:typ) (b:pointer a) h0 h1 : Lemma
  (requires (let rid = frameOf b in
  HS.modifies_one rid h0 h1 /\ modifies_ptr_1 rid b h0 h1))
  (ensures  (modifies_1 b h0 h1))
  = ()

(* Lemmas revealing the content of the specialized modifies clauses in order to
   be able to generalize them if needs be. *)
let  modifies_0_reveal h0 h1 : Lemma
  (requires (modifies_0 h0 h1))
  (ensures  (HS.modifies_one h0.HS.tip h0 h1 /\ modifies_ptr_0 h0.HS.tip h0 h1 /\ h0.HS.tip=h1.HS.tip))
  = ()

let modifies_1_reveal (#a:typ) (b:pointer a) h0 h1 : Lemma
  (requires (modifies_1 b h0 h1))
  (ensures  (let rid = frameOf b in HS.modifies_one rid h0 h1 /\ modifies_ptr_1 rid b h0 h1))
  = ()

(* STStack effect specific lemmas *)
let lemma_ststack_1 (#a:typ) (b:pointer a) h0 h1 h2 h3 : Lemma
  (requires (live h0 b /\ HS.fresh_frame h0 h1 /\ modifies_1 b h1 h2 /\ HS.popped h2 h3 ))
  (ensures  (modifies_1 b h0 h3))
  [SMTPatT (modifies_1 b h1 h2); SMTPatT (HS.fresh_frame h0 h1); SMTPatT (HS.popped h2 h3)]
= ()

//  assume (modifies_1 b h0 h3)

(** Transitivity lemmas *)
let modifies_0_trans h0 h1 h2 : Lemma
  (requires (modifies_0 h0 h1 /\ modifies_0 h1 h2))
  (ensures  (modifies_0 h0 h2))
  [SMTPatT (modifies_0 h0 h1); SMTPatT (modifies_0 h1 h2)]
  = ()

let modifies_1_trans (#a:typ) (b:pointer a) h0 h1 h2 : Lemma
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

abstract
let modifies_0_1 (#a:typ) (b:pointer a) h0 h1 h2 : Lemma
  (requires (unused_in b h0 /\ modifies_0 h0 h1 /\ live h1 b /\ modifies_1 b h1 h2))
  (ensures  (modifies_0 h0 h2))
  [SMTPatT (modifies_0 h0 h1); SMTPatT (modifies_1 b h1 h2)]
= ()

(** Concrete allocators, getters and setters *)

abstract let screate
  (value:typ)
  (s: type_of_typ value)
: HST.StackInline (pointer value)
  (requires (fun h -> True))
  (ensures (fun (h0:HS.mem) b h1 ->
       unused_in b h0
     /\ live h1 b
     /\ frameOf b = h0.HS.tip
     /\ modifies_0 h0 h1
     /\ Map.domain h1.HS.h == Map.domain h0.HS.h
     /\ gread h1 b == s))
= let content: HS.reference pointer_ref_contents =
     HST.salloc (| value, s |)
  in
  Pointer value (HS.aref_of content) PathBase

// TODO: move to HyperStack?
private let domain_upd (#a:Type) (h:HS.mem) (x:HS.reference a{HS.live_region h x.HS.id}) (v:a) : Lemma
  (requires True)
  (ensures  (Map.domain h.HS.h == Map.domain (HS.upd h x v).HS.h))
  = let m = h.HS.h in
    let m' = Map.upd m x.HS.id (Heap.upd (Map.sel m x.HS.id) (HH.as_ref x.HS.ref) v) in
    Set.lemma_equal_intro (Map.domain m) (Map.domain m')

abstract let ecreate
  (t:typ)
  (r:HH.rid)
  (s: type_of_typ t)
: HST.ST (pointer t)
  (requires (fun h -> HS.is_eternal_region r))
  (ensures (fun (h0:HS.mem) b h1 -> unused_in b h0
    /\ live h1 b
    /\ Map.domain h1.HS.h == Map.domain h0.HS.h
    /\ h1.HS.tip = h0.HS.tip
    /\ HS.modifies (Set.singleton r) h0 h1
    /\ HS.modifies_ref r Set.empty h0 h1
    /\ gread h1 b == s
    /\ ~(is_mm b)))
= let h0 = HST.get() in
  let content: HS.reference pointer_ref_contents =
     HST.ralloc r (| t, s |)
  in
  domain_upd h0 content (| t, s |) ;
  Pointer t (HS.aref_of content) PathBase

abstract let field
 (#l: struct_typ)
 (p: pointer (TStruct l))
 (fd: struct_field l)
: HST.ST (pointer (typ_of_struct_field l fd))
  (requires (fun h -> live h p))
  (ensures (fun h0 p' h1 -> h0 == h1 /\ p' == gfield p fd))
= _field p fd

abstract let cell
 (#length: UInt32.t)
 (#value: typ)
 (p: pointer (TArray length value))
 (i: UInt32.t {UInt32.v i < UInt32.v length})
: HST.ST (pointer value)
  (requires (fun h -> live h p))
  (ensures (fun h0 p' h1 -> h0 == h1 /\ p' == gcell p i))
= _cell p i

abstract let read
 (#value: typ)
 (p: pointer value)
: HST.ST (type_of_typ value)
  (requires (fun h -> live h p))
  (ensures (fun h0 v h1 -> live h0 p /\ h0 == h1 /\ v == gread h0 p))
= let h = HST.get () in
  let r = reference_of h p in
  let (| _ , c |) = !r in
  path_sel c (Pointer?.p p)

#reset-options "--z3rlimit 32"

abstract val write: #a:typ -> b:pointer a -> z:type_of_typ a -> HST.Stack unit
  (requires (fun h -> live h b))
  (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b
    /\ modifies_1 b h0 h1
    /\ gread h1 b == z ))
let write #a b z =
  let h0 = HST.get () in
  let r = reference_of h0 b in
  let (| t , c0 |) = !r in
  let c1 = path_upd c0 (Pointer?.p b) z in
  r := (| t, c1 |)

(** Lemmas and patterns *)

let modifies_one_trans_1 (#a:typ) (b:pointer a) (h0:HS.mem) (h1:HS.mem) (h2:HS.mem): Lemma
  (requires (HS.modifies_one (frameOf b) h0 h1 /\ HS.modifies_one (frameOf b) h1 h2))
  (ensures (HS.modifies_one (frameOf b) h0 h2))
  [SMTPatT (HS.modifies_one (frameOf b) h0 h1); SMTPatT (HS.modifies_one (frameOf b) h1 h2)]
  = ()

val no_upd_lemma_0: #t:typ -> h0:HS.mem -> h1:HS.mem -> b:pointer t -> Lemma
  (requires (live h0 b /\ modifies_0 h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal_values h0 b h1 b))
  [SMTPatT (modifies_0 h0 h1); SMTPatT (live h0 b)]
let no_upd_lemma_0 #t h0 h1 b = ()

val no_upd_lemma_1: #t:typ -> #t':typ -> h0:HS.mem -> h1:HS.mem -> a:pointer t -> b:pointer t' -> Lemma
  (requires (live h0 b /\ disjoint a b /\ modifies_1 a h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal_values h0 b h1 b))
  [SMTPatOr [ [ SMTPatT (modifies_1 a h0 h1); SMTPatT (gread h1 b) ] ; [ SMTPatT (modifies_1 a h0 h1); SMTPatT (live h0 b) ] ] ]
let no_upd_lemma_1 #t #t' h0 h1 a b =
  if frameOf a = frameOf b
  then modifies_elim (frameOf a) (set_singleton a) h0 h1 b
  else ()

val no_upd_fresh: #t:typ -> h0:HS.mem -> h1:HS.mem -> a:pointer t -> Lemma
  (requires (live h0 a /\ HS.fresh_frame h0 h1))
  (ensures  (live h0 a /\ live h1 a /\ equal_values h0 a h1 a))
  [SMTPatT (live h0 a); SMTPatT (HS.fresh_frame h0 h1)]
let no_upd_fresh #t h0 h1 a = ()

val no_upd_popped: #t:typ -> h0:HS.mem -> h1:HS.mem -> b:pointer t -> Lemma
  (requires (live h0 b /\ frameOf b <> h0.HS.tip /\ HS.popped h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal_values h0 b h1 b))
  [SMTPatT (live h0 b); SMTPatT (HS.popped h0 h1)]
let no_upd_popped #t h0 h1 b = ()

let lemma_modifies_sub_1 #t h0 h1 (b:pointer t) : Lemma
  (requires (h1 == h0))
  (ensures  (modifies_1 b h0 h1))
  [SMTPatT (live h0 b); SMTPatT (modifies_1 b h0 h1)]
  = ()

let modifies_substruct_1 (#tsub #ta:typ) h0 h1 (sub:pointer tsub) (a:pointer ta) : Lemma
  (requires (live h0 a /\ modifies_1 sub h0 h1 /\ live h1 sub /\ includes a sub))
  (ensures  (modifies_1 a h0 h1 /\ live h1 a))
  [SMTPatT (modifies_1 sub h0 h1); SMTPatT (includes a sub)]
= let s1 = set_singleton a in
  let s2 = set_singleton sub in
  set_includes_singleton a sub;
  modifies_set_includes (frameOf a) s1 s2 h0 h1

let modifies_popped_1' (#t:typ) (a:pointer t) h0 h1 h2 h3 : Lemma
  (requires (live h0 a /\ HS.fresh_frame h0 h1 /\ HS.popped h2 h3 /\ modifies_1 a h1 h2))
  (ensures  (modifies_1 a h0 h3))
  [SMTPatT (HS.fresh_frame h0 h1); SMTPatT (HS.popped h2 h3); SMTPatT (modifies_1 a h1 h2)]
  = ()

let live_popped (#t:typ) (b:pointer t) h0 h1 : Lemma
  (requires (HS.popped h0 h1 /\ live h0 b /\ frameOf b <> h0.HS.tip))
  (ensures  (live h1 b))
  [SMTPatT (HS.popped h0 h1); SMTPatT (live h0 b)]
  = ()

let live_fresh (#t:typ) (b:pointer t) h0 h1 : Lemma
  (requires (HS.fresh_frame h0 h1 /\ live h0 b))
  (ensures  (live h1 b))
  [SMTPatT (HS.fresh_frame h0 h1); SMTPatT (live h0 b)]
  = ()

let modifies_poppable_1 #t h0 h1 (b:pointer t) : Lemma
  (requires (modifies_1 b h0 h1 /\ HS.poppable h0))
  (ensures  (HS.poppable h1))
  [SMTPatT (modifies_1 b h0 h1)]
  = ()

(* What about other regions? *)

abstract
let modifies_other_regions
  (rs: Set.set HH.rid)
  (h0 h1: HS.mem)
  (#a: typ)
  (p: pointer a)
: Lemma
  (requires (HS.modifies rs h0 h1 /\ (~ (Set.mem (frameOf p) rs)) /\ live h0 p))
  (ensures (live h1 p /\ gread h0 p == gread h1 p))
= ()

abstract
let modifies_one_other_region
  (r: HH.rid)
  (h0 h1: HS.mem)
  (#a: typ)
  (p: pointer a)
: Lemma
  (requires (HS.modifies_one r h0 h1 /\ frameOf p <> r /\ live h0 p))
  (ensures (live h1 p /\ gread h0 p == gread h1 p))
= ()

(*** Semantics of buffers *)

(** Operations on buffers *)

abstract let gsingleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
: GTot (buffer t)
= Buffer (BufferRootSingleton p) 0ul 1ul

abstract let singleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
: HST.Stack (buffer t)
  (requires (fun h -> live h p))
  (ensures (fun h b h' -> h' == h /\ b == gsingleton_buffer_of_pointer p))
= Buffer (BufferRootSingleton p) 0ul 1ul

abstract let gbuffer_of_array_pointer
  (#t: typ)
  (#length: UInt32.t)
  (p: pointer (TArray length t))
: GTot (buffer t)
= Buffer (BufferRootArray p) 0ul length

abstract let buffer_of_array_pointer
  (#t: typ)
  (#length: UInt32.t)
  (p: pointer (TArray length t))
: HST.Stack (buffer t)
  (requires (fun h -> live h p))
  (ensures (fun h b h' -> h' == h /\ b == gbuffer_of_array_pointer p))
= Buffer (BufferRootArray p) 0ul length

abstract let buffer_length
  (#t: typ)
  (b: buffer t)
: GTot UInt32.t
= Buffer?.blength b

abstract let buffer_length_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
: Lemma
  (requires True)
  (ensures (buffer_length (gsingleton_buffer_of_pointer p) == 1ul))
  [SMTPat (buffer_length (gsingleton_buffer_of_pointer p))]
= ()

abstract let buffer_length_gbuffer_of_array_pointer
  (#t: typ)
  (#len: UInt32.t)
  (p: pointer (TArray len t))
: Lemma
  (requires True)
  (ensures (buffer_length (gbuffer_of_array_pointer p) == len))
  [SMTPat (buffer_length (gbuffer_of_array_pointer p))]
= ()

abstract let buffer_live
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: GTot Type0
= UInt32.v (buffer_length b) > 0 /\ ( // needed to preserve liveness through modifies
    match b.broot with
    | BufferRootSingleton p -> live h p
    | BufferRootArray #mlen p -> live h p
  )

abstract let buffer_live_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
  (h: HS.mem)
: Lemma
  (ensures (buffer_live h (gsingleton_buffer_of_pointer p) <==> live h p ))
  [SMTPat (buffer_live h (gsingleton_buffer_of_pointer p))]
= ()

abstract let buffer_live_gbuffer_of_array_pointer
  (#t: typ)
  (#length: UInt32.t)
  (p: pointer (TArray length t))
  (h: HS.mem)
: Lemma
  (requires (UInt32.v length > 0))
  (ensures (buffer_live h (gbuffer_of_array_pointer p) <==> live h p))
  [SMTPat (buffer_live h (gbuffer_of_array_pointer p))]
= ()

abstract let frameOf_buffer
  (#t: typ)
  (b: buffer t)
: GTot HH.rid
= match b.broot with
  | BufferRootSingleton p -> frameOf p
  | BufferRootArray #mlen p -> frameOf p

abstract let frameOf_buffer_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
: Lemma
  (ensures (frameOf_buffer (gsingleton_buffer_of_pointer p) == frameOf p))
  [SMTPat (frameOf_buffer (gsingleton_buffer_of_pointer p))]
= ()

abstract let frameOf_buffer_gbuffer_of_array_pointer
  (#t: typ)
  (#length: UInt32.t)
  (p: pointer (TArray length t))
: Lemma
  (ensures (frameOf_buffer (gbuffer_of_array_pointer p) == frameOf p))
  [SMTPat (frameOf_buffer (gbuffer_of_array_pointer p))]
= ()

abstract let gsub_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) } )
: GTot (buffer t)
= Buffer (Buffer?.broot b) FStar.UInt32.(Buffer?.bidx b +^ i) len

abstract let sub_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) } )
: HST.Stack (buffer t)
  (requires (fun h -> buffer_live h b))
  (ensures (fun h b' h' -> h' == h /\ b' == gsub_buffer b i len ))
= Buffer (Buffer?.broot b) FStar.UInt32.(Buffer?.bidx b +^ i) len

abstract let buffer_length_gsub_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) } )
: Lemma
  (requires True)
  (ensures (buffer_length (gsub_buffer b i len) == len))
  [SMTPat (buffer_length (gsub_buffer b i len))]
= ()

abstract let buffer_live_gsub_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) } )
  (h: HS.mem)
: Lemma
  (requires (UInt32.v len > 0))
  (ensures (buffer_live h (gsub_buffer b i len) <==> buffer_live h b))
  [SMTPat (buffer_live h (gsub_buffer b i len))]
= ()

abstract let gsub_buffer_gsub_buffer
  (#a: typ)
  (b: buffer a)
  (i1: UInt32.t)
  (len1: UInt32.t{UInt32.v i1 + UInt32.v len1 <= UInt32.v (buffer_length b)})
  (i2: UInt32.t)
  (len2: UInt32.t {UInt32.v i2 + UInt32.v len2 <= UInt32.v len1})
: Lemma
  (ensures (gsub_buffer (gsub_buffer b i1 len1) i2 len2 == gsub_buffer b FStar.UInt32.(i1 +^ i2) len2))
  [SMTPat (gsub_buffer (gsub_buffer b i1 len1) i2 len2)]
= ()

abstract let gsub_buffer_zero_buffer_length
  (#a: typ)
  (b: buffer a)
: Lemma
  (ensures (gsub_buffer b 0ul (buffer_length b) == b))
  [SMTPat (gsub_buffer b 0ul (buffer_length b))]
= ()

private let buffer_root_as_seq
  (#t: typ)
  (h: HS.mem)
  (b: buffer_root t)
: GTot (Seq.seq (type_of_typ t))
= match b with
  | BufferRootSingleton p ->
    Seq.create 1 (gread h p)
  | BufferRootArray p ->
    gread h p

private let length_buffer_root_as_seq
  (#t: typ)
  (h: HS.mem)
  (b: buffer_root t)
: Lemma
  (requires True)
  (ensures (Seq.length (buffer_root_as_seq h b) == UInt32.v (buffer_root_length b)))
  [SMTPat (Seq.length (buffer_root_as_seq h b))]
= ()

abstract let buffer_as_seq
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: GTot (Seq.seq (type_of_typ t))
= let i = UInt32.v (Buffer?.bidx b) in
  Seq.slice (buffer_root_as_seq h (Buffer?.broot b)) i (i + UInt32.v (Buffer?.blength b))

abstract let buffer_length_buffer_as_seq
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: Lemma
  (requires True)
  (ensures (Seq.length (buffer_as_seq h b) == UInt32.v (buffer_length b)))
  [SMTPat (Seq.length (buffer_as_seq h b))]
= ()

abstract let buffer_as_seq_gsingleton_buffer_of_pointer
  (#t: typ)
  (h: HS.mem)
  (p: pointer t)
: Lemma
  (requires True)
  (ensures (buffer_as_seq h (gsingleton_buffer_of_pointer p) == Seq.create 1 (gread h p)))
  [SMTPat (buffer_as_seq h (gsingleton_buffer_of_pointer p))]
= Seq.slice_length (Seq.create 1 (gread h p))

abstract let buffer_as_seq_gbuffer_of_array_pointer
  (#length: UInt32.t)
  (#t: typ)
  (h: HS.mem)
  (p: pointer (TArray length t))
: Lemma
  (requires True)
  (ensures (buffer_as_seq h (gbuffer_of_array_pointer p) == gread h p))
  [SMTPat (buffer_as_seq h (gbuffer_of_array_pointer p))]
= let s : array length (type_of_typ t) = gread h p in
  Seq.slice_length s

abstract let buffer_as_seq_gsub_buffer
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) } )
: Lemma
  (requires True)
  (ensures (buffer_as_seq h (gsub_buffer b i len) == Seq.slice (buffer_as_seq h b) (UInt32.v i) (UInt32.v i + UInt32.v len)))
  [SMTPat (buffer_as_seq h (gsub_buffer b i len))]
= Seq.slice_slice (buffer_root_as_seq h (Buffer?.broot b)) (UInt32.v (Buffer?.bidx b)) (UInt32.v (Buffer?.bidx b) + UInt32.v (Buffer?.blength b)) (UInt32.v i) (UInt32.v i + UInt32.v len)

abstract let gpointer_of_buffer_cell
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (buffer_length b) })
: GTot (pointer t)
= match Buffer?.broot b with
  | BufferRootSingleton p -> p
  | BufferRootArray p ->
    gcell p FStar.UInt32.(Buffer?.bidx b +^ i)

abstract let pointer_of_buffer_cell
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (buffer_length b) })
: HST.Stack (pointer t)
  (requires (fun h -> buffer_live h b))
  (ensures (fun h p h' -> h' == h /\ p == gpointer_of_buffer_cell b i))
= match Buffer?.broot b with
  | BufferRootSingleton p -> p
  | BufferRootArray p ->
    cell p FStar.UInt32.(Buffer?.bidx b +^ i)

abstract let gpointer_of_buffer_cell_gsub_buffer
  (#t: typ)
  (b: buffer t)
  (i1: UInt32.t)
  (len: UInt32.t { UInt32.v i1 + UInt32.v len <= UInt32.v (buffer_length b) } )
  (i2: UInt32.t { UInt32.v i2 < UInt32.v len } )
: Lemma
  (requires True)
  (ensures (gpointer_of_buffer_cell (gsub_buffer b i1 len) i2 == gpointer_of_buffer_cell b FStar.UInt32.(i1 +^ i2)))
  [SMTPat (gpointer_of_buffer_cell (gsub_buffer b i1 len) i2)]
= ()

abstract let live_gpointer_of_buffer_cell
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (buffer_length b) })
  (h: HS.mem)
: Lemma
  (ensures (live h (gpointer_of_buffer_cell b i) <==> buffer_live h b))
  [SMTPat (live h (gpointer_of_buffer_cell b i))]
= ()

abstract let gpointer_of_buffer_cell_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
  (i: UInt32.t { UInt32.v i < 1 } )
: Lemma
  (requires True)
  (ensures (gpointer_of_buffer_cell (gsingleton_buffer_of_pointer p) i == p))
  [SMTPat (gpointer_of_buffer_cell (gsingleton_buffer_of_pointer p) i)]
= ()

abstract let gpointer_of_buffer_cell_gbuffer_of_array_pointer
  (#length: UInt32.t)
  (#t: typ)
  (p: pointer (TArray length t))
  (i: UInt32.t { UInt32.v i < UInt32.v length } )
: Lemma
  (requires True)
  (ensures (gpointer_of_buffer_cell (gbuffer_of_array_pointer p) i == gcell p i))
  [SMTPat (gpointer_of_buffer_cell (gbuffer_of_array_pointer p) i)]
= ()

abstract let gread_gpointer_of_buffer_cell
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (buffer_length b) } )
: Lemma
  (ensures (gread h (gpointer_of_buffer_cell b i) == Seq.index (buffer_as_seq h b) (UInt32.v i)))
  [SMTPat (gread h (gpointer_of_buffer_cell b i))]
= ()

abstract let gread_gpointer_of_buffer_cell'
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (buffer_length b) } )
: Lemma
  (ensures (gread h (gpointer_of_buffer_cell b i) == Seq.index (buffer_as_seq h b) (UInt32.v i)))
= ()

abstract let gread_pointer_of_buffer_cell'
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (buffer_length b) } )
: Lemma
  (requires True)
  (ensures (Seq.index (buffer_as_seq h b) (UInt32.v i) == gread h (gpointer_of_buffer_cell b i)))
  [SMTPat (Seq.index (buffer_as_seq h b) (UInt32.v i))]
= ()

(* buffer read: can be defined as a derived operation: pointer_of_buffer_cell ; read *)

let read_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (buffer_length b) } )
: HST.Stack (type_of_typ t)
  (requires (fun h -> buffer_live h b))
  (ensures (fun h v h' -> h' == h /\ v == Seq.index (buffer_as_seq h b) (UInt32.v i)))
= read (pointer_of_buffer_cell b i)

(* buffer write: needs clearer "modifies" clauses *)

abstract let disjoint_gpointer_of_buffer_cell
  (#t: typ)
  (b: buffer t)
  (i1: UInt32.t { UInt32.v i1 < UInt32.v (buffer_length b) } )
  (i2: UInt32.t { UInt32.v i2 < UInt32.v (buffer_length b) } )
: Lemma
  (requires ( UInt32.v i1 <> UInt32.v i2 ) )
  (ensures (disjoint (gpointer_of_buffer_cell b i1) (gpointer_of_buffer_cell b i2)))
  [SMTPat (disjoint (gpointer_of_buffer_cell b i1) (gpointer_of_buffer_cell b i2))]
= ()

(* For a "disjoint" clause on buffers, we could use the following TRANSPARENT definitions: *)

unfold
let disjoint_buffer_vs_pointer
  (#t1 #t2: typ)
  (b: buffer t1)
  (p: pointer t2)
: GTot Type0
= forall (i: UInt32.t { UInt32.v i < UInt32.v (buffer_length b) } ) . disjoint (gpointer_of_buffer_cell b i) p

unfold
let disjoint_buffer_vs_buffer
  (#t1 #t2: typ)
  (b1: buffer t1)
  (b2: buffer t2)
: GTot Type0
= forall
    (i1: UInt32.t { UInt32.v i1 < UInt32.v (buffer_length b1) } )
    (i2: UInt32.t { UInt32.v i2 < UInt32.v (buffer_length b2) } )
  .
    disjoint (gpointer_of_buffer_cell b1 i1) (gpointer_of_buffer_cell b2 i2)

let write_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (buffer_length b) } )
  (v: type_of_typ t)
: HST.Stack unit
  (requires (fun h -> buffer_live h b))
  (ensures (fun h _ h' ->
    modifies_1 (gpointer_of_buffer_cell b i) h h' /\
    buffer_live h' b /\
    Seq.index (buffer_as_seq h' b) (UInt32.v i) == v /\ (
      forall (j: UInt32.t {UInt32.v j < UInt32.v (buffer_length b) /\ UInt32.v j <> UInt32.v i }) .
        Seq.index (buffer_as_seq h' b) (UInt32.v j) == Seq.index (buffer_as_seq h b) (UInt32.v j)
  )))
= write (pointer_of_buffer_cell b i) v

let modifies_1_disjoint_buffer_vs_pointer_live
  (#t1 #t2: typ)
  (b: buffer t1)
  (p: pointer t2)
  (h h': HS.mem)
: Lemma
  (requires (
    disjoint_buffer_vs_pointer b p /\
    buffer_live h b /\
    modifies_1 p h h'
  ))
  (ensures (buffer_live h' b /\ buffer_as_seq h b == buffer_as_seq h' b))
  [SMTPat (modifies_1 p h h'); SMTPat (buffer_live h b)]
= modifies_1_reveal p h h';
  let f
    (i: UInt32.t { UInt32.v i < UInt32.v (buffer_length b) } )
  : Lemma
    (live h' (gpointer_of_buffer_cell b i) /\ gread h (gpointer_of_buffer_cell b i) == gread h' (gpointer_of_buffer_cell b i))
  = if frameOf_buffer b = frameOf p
    then
      let s = set_singleton p in
      let (ap: apointer { set_amem ap s } ) = APointer t2 p in
      modifies_elim (frameOf p) s h h' (gpointer_of_buffer_cell b i)
    else
      modifies_one_other_region (frameOf p) h h' (gpointer_of_buffer_cell b i)
  in
  f 0ul; // for the liveness of the whole buffer
  buffer_length_buffer_as_seq h b;
  buffer_length_buffer_as_seq h' b;
  let g
    (i: nat { i < UInt32.v (buffer_length b) } )
  : Lemma
    (Seq.index (buffer_as_seq h b) i == Seq.index (buffer_as_seq h' b) i)
  = let j = UInt32.uint_to_t i in
    f j;
    gread_gpointer_of_buffer_cell' h b j;
    gread_gpointer_of_buffer_cell' h' b j
  in
  Classical.forall_intro g;
  Seq.lemma_eq_elim (buffer_as_seq h b) (buffer_as_seq h' b)
