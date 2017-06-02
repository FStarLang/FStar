module Test

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
  (f: list (string * netype))
: Tot netype
= let field: eqtype = (s: string { Some? (List.Tot.assoc #string #netype s f) } ) in
  let ftypes (x: field): Tot Type = netype_carrier (Some?.v (List.Tot.assoc #string #netype x f)) in
  NEType (DependentMap.t field ftypes) (DependentMap.create #_ #ftypes (fun (x: field) -> netype_dummy (Some?.v (List.Tot.assoc #string #netype x f))))

unfold
let array
  (len: UInt32.t) 
  (t: netype)
: Tot netype
= NEType (Pointer.array len (netype_carrier t)) (Seq.create (UInt32.v len) (netype_dummy t))

unfold
let ty: netype =
  struct [
    ("A", struct [
        ("X", uint32_t);
        ("Y", array 5ul uint32_t)
    ]);
    ("B", array 3ul uint64_t)
  ]

unfold
let screate
  (ty: netype)
= Pointer.screate (netype_dummy ty)

let f () =
  let s : Pointer.pointer (netype_carrier ty) = screate ty in
  let h = ST.get () in
  let p = Pointer.field (Pointer.field s "A") "Y" in
  let _ = Pointer.write (Pointer.cell p 1ul) 19ul in
  let b = BufferNG.buffer_of_array_pointer p in
  let c = BufferNG.sub b 1ul 3ul in
  let _ = BufferNG.write c 2ul 21ul in
  let u = Pointer.read (Pointer.cell p 1ul) in
  let v = Pointer.read (Pointer.cell p 3ul) in
  assert (u == 19ul /\ v == 21ul);
  ()
