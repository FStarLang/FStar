module Test

type fd1 =
| A
| B

type fd2 =
| X
| Y

(** Nonempty types with automatic initialization, handy notations (hopefully) *)

unopteq type netype =
  | NEType:
    (carrier:Type) ->
    (dummy: carrier) ->
    netype

unfold
let netype_carrier (t: netype): Tot Type =
  let (NEType carrier _) = t in carrier

unfold
let netype_dummy (t: netype): Tot (netype_carrier t) =
  let (NEType _ dummy) = t in dummy

unfold
let uint32_t: netype = NEType UInt32.t 0ul

unfold
let uint64_t: netype = NEType UInt64.t 0uL

unfold
let struct
  (#a: eqtype)
  (f: a -> Tot netype)
: Tot netype
= let ftypes (x: a): Tot Type = netype_carrier (f x) in
  NEType (DependentMap.t a ftypes) (DependentMap.create #_ #ftypes (fun (x: a) -> netype_dummy (f x)))

unfold
let array
  (len: UInt32.t) 
  (t: netype)
: Tot netype
= NEType (BufferNG.array len (netype_carrier t)) (Seq.create (UInt32.v len) (netype_dummy t))

unfold
let ty: netype =
  struct (function
    | A -> struct (function
	| X -> uint32_t
	| Y -> array 5ul uint32_t
      )
    | B -> array 3ul uint64_t
  )

unfold
let screate
  (ty: netype)
= BufferNG.screate (netype_dummy ty)

let f () =
  let s : BufferNG.pointer (netype_carrier ty) = screate ty in
  let h = ST.get () in
  let p = BufferNG.field (BufferNG.field s A) Y in
  let _ = BufferNG.write (BufferNG.cell p 1ul) 19ul in
  let b = BufferNG.buffer_of_array_pointer p in
  let c = BufferNG.buffer_sub b 1ul 3ul in
  let _ = BufferNG.bwrite c 2ul 21ul in
  let u = BufferNG.read (BufferNG.cell p 1ul) in
  let v = BufferNG.read (BufferNG.cell p 3ul) in
  assert (u == 19ul /\ v == 21ul);
  ()
