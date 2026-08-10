module ExtDatatypesEnum

/// Enum-like inductives: no constructor carries a payload.
///
/// Karamel gives these a special representation -- a C `enum` rather than a
/// tagged union -- so the tag *is* the value. A mistake in the tag ordering
/// therefore shows up as the wrong branch being taken rather than as a
/// compile error, which makes this a severity-2 shape of bug. We check the
/// match, the discriminators, and structural equality.

module I32 = FStar.Int32
module U32 = FStar.UInt32

let chk (n:I32.t) (b:bool) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let one : U32.t = 1ul
let two : U32.t = 2ul
let three : U32.t = 3ul
let seven : U32.t = 7ul

type color = | Red | Green | Blue

let color_code (c:color) : U32.t =
  match c with
  | Red -> 1ul
  | Green -> 2ul
  | Blue -> 3ul

/// A match that reorders the constructors relative to the declaration, to
/// catch a backend that matches positionally instead of by tag.
let is_warm (c:color) : bool =
  match c with
  | Blue -> false
  | Green -> false
  | Red -> true

let red : color = Red
let green : color = Green
let blue : color = Blue

let main () : I32.t =
     chk 1l (U32.eq (color_code red) 1ul)
 &&& chk 2l (U32.eq (color_code green) 2ul)
 &&& chk 3l (U32.eq (color_code blue) 3ul)
 &&& chk 4l (is_warm red)
 &&& chk 5l (not (is_warm green))
 &&& chk 6l (not (is_warm blue))
 &&& chk 7l (red = Red)
 &&& chk 8l (not (red = blue))
 &&& chk 9l (red <> blue)
 &&& chk 10l (Red? red)
 &&& chk 11l (not (Blue? green))
 &&& chk 12l (Green? green)
     (* the default branch of a partial match *)
 &&& chk 13l (match blue with | Red -> false | _ -> true)
