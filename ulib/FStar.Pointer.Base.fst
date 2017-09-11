module FStar.Pointer.Base

module DM = FStar.DependentMap
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open HST // for := , !

(*** Definitions *)

(** Pointers to data of type t.

    This defines two main types:
    - `npointer (t: typ)`, a pointer that may be "NULL";
    - `pointer (t: typ)`, a pointer that cannot be "NULL"
      (defined as a refinement of `npointer`).

    `nullptr #t` (of type `npointer t`) represents the "NULL" value.
*)
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

// C11, Sect. 6.2.5 al. 20: arrays must be nonempty
type array_length_t = (length: UInt32.t { UInt32.v length > 0 } )

type typ =
| TBase:
  (b: base_typ) ->
  typ
| TStruct:
  (l: struct_typ) ->
  typ
| TUnion:
  (l: union_typ) ->
  typ
| TArray:
  (length: array_length_t ) ->
  (t: typ) ->
  typ
| TPointer:
  (t: typ) ->
  typ
| TNPointer:
  (t: typ) ->
  typ
| TBuffer:
  (t: typ) ->
  typ
and struct_typ = (l: list (string * typ) {
  Cons? l /\ // C11, 6.2.5 al. 20: structs and unions must have at least one field
  List.Tot.noRepeats (List.Tot.map fst l)
})
and union_typ = struct_typ

let struct_field
  (l: struct_typ)
: Tot eqtype
= (s: string { List.Tot.mem s (List.Tot.map fst l) } )

(** `union_field l` is the type of fields of `TUnion l`
    (i.e. a refinement of `string`).
*)
let union_field = struct_field

let typ_of_struct_field
  (l: struct_typ)
  (f: struct_field l)
: Tot (t: typ {t << l})
= List.Tot.assoc_mem f l;
  let y = Some?.v (List.Tot.assoc f l) in
  List.Tot.assoc_precedes f l y;
  y

(** `typ_of_union_field l f` is the type of data associated with field `f` in
    `TUnion l` (i.e. a refinement of `typ`).
*)
let typ_of_union_field
  (l: union_typ)
  (f: union_field l)
: Tot (t: typ {t << l})
= typ_of_struct_field l f

type step: (from: typ) -> (to: typ) -> Tot Type0 =
  | StepField:
    (l: struct_typ) ->
    (fd: struct_field l) ->
    step (TStruct l) (typ_of_struct_field l fd)
  | StepUField:
    (l: union_typ) ->
    (fd: struct_field l) ->
    step (TUnion l) (typ_of_struct_field l fd)
  | StepCell:
    (length: UInt32.t) ->
    (value: typ) ->
    (index: UInt32.t { UInt32.v index < UInt32.v length } ) ->
    step (TArray length value) value

type path (from: typ) : (to: typ) -> Tot Type0 =
  | PathBase:
    path from from
  | PathStep:
    (through: typ) ->
    (to: typ) ->
    (p: path from through) ->
    (s: step through to) ->
    path from to

// TODO: rename as: prefix_of; use infix notation (p1 `prefix_of` p2)
let rec path_includes
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

let rec path_includes_trans
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
