module ExtDatatypesRecord

/// Records and single-constructor inductives.
///
/// Karamel drops the tag for a single-constructor type and emits a bare C
/// struct, so these two shapes are really the same thing at the backend
/// level. What must survive: field order, projectors, pattern matching on a
/// record, and -- the interesting one -- functional record update, which has
/// to *copy* rather than alias, or a mutation is visible through the original
/// binding (severity 2).

module I32 = FStar.Int32
module U32 = FStar.UInt32

let chk (n:I32.t) (b:bool) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let one : U32.t = 1ul
let two : U32.t = 2ul
let three : U32.t = 3ul
let seven : U32.t = 7ul

type color = | Red | Green | Blue

type point = { px : U32.t; py : U32.t; label : color }

type wrapper = | Wrap : v:U32.t -> tag:bool -> wrapper

/// Nested record, so that a struct is passed by value inside another struct.
type segment = { start : point; stop : point }

let mk_point (a b : U32.t) : point = { px = a; py = b; label = Green }

let records () : I32.t =
  let p = mk_point one two in
     chk 1l (U32.eq p.px 1ul)
 &&& chk 2l (U32.eq p.py 2ul)
 &&& chk 3l (p.label = Green)
 &&& chk 4l (U32.eq (Mkpoint?.px p) 1ul)
 &&& chk 5l (match p with | { px = a; py = b } -> U32.eq a 1ul && U32.eq b 2ul)

/// `{ p with px = ... }` must produce a fresh value; `p` must be unchanged.
let functional_update () : I32.t =
  let p = mk_point one two in
  let q = { p with px = three } in
     chk 10l (U32.eq q.px 3ul)
 &&& chk 11l (U32.eq q.py 2ul)
 &&& chk 12l (U32.eq p.px 1ul)
 &&& chk 13l (q.label = Green)

let single_ctor () : I32.t =
  let w = Wrap seven true in
     chk 20l (U32.eq (Wrap?.v w) 7ul)
 &&& chk 21l (Wrap?.tag w)
 &&& chk 22l (match w with | Wrap v t -> U32.eq v 7ul && t)
 &&& chk 23l (Wrap? w)

let nested () : I32.t =
  let s = { start = mk_point one two; stop = mk_point three seven } in
     chk 30l (U32.eq s.start.px 1ul)
 &&& chk 31l (U32.eq s.stop.py 7ul)
 &&& chk 32l (s.start.label = Green)
 &&& chk 33l (let s' = { s with stop = mk_point one one } in
              U32.eq s'.stop.px 1ul && U32.eq s.stop.px 3ul)

let main () : I32.t =
     records ()
 &&& functional_update ()
 &&& single_ctor ()
 &&& nested ()
