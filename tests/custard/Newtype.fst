module Newtype

module U32 = FStar.UInt32
module U64 = FStar.UInt64

/// Section 108.  §5.2 collapses a one-field record to its field, and §70.1
/// roots a type *abbreviation* declared in an entry module because Custard
/// unfolds one and nothing in the emitted program then refers to the name.
/// A collapsed record is in exactly that position -- the collapse is an
/// unfolding -- so it is rooted on the same grounds, and the abbreviation
/// survives.

type wrapper = { contents : U64.t }

let make (x : U64.t) : wrapper = { contents = x }

let get (w : wrapper) : U64.t = w.contents

/// EverParse's shape: a newtype carrying a refinement, so that the payload
/// is the underlying type and the name is the whole of the interface.
type positive = { pv : (x : U32.t { U32.v x > 0 }) }

let one : positive = { pv = 1ul }

let pval (p : positive) : U32.t = p.pv

/// The payload is a record of this module's, so the abbreviation names it.
type point = { px : U32.t; py : U32.t }

type boxed = { bp : point }

let unbox (b : boxed) : U32.t = b.bp.px

/// A parameter the payload does not mention.  Under
/// [--custard_monomorphize_types] there is no parameter left by the time the
/// collapse happens, so the clone gets its name like any other; it is the
/// unmonomorphized form that has nothing to say, OCaml rejecting
/// [type 'a t = int].
type phantom (a : Type0) = { pc : U32.t }

let unphantom (p : phantom bool) : U32.t = p.pc

/// A record with two fields does not collapse, and one nothing reaches is
/// still not emitted: rooting is for the collapsed case only, a type no live
/// signature mentions never having been asked whether C can represent it.
type unused = { ua : U32.t; ub : U64.t }

let main () : FStar.All.ML FStar.Int32.t =
  let w = make 7uL in
  let b = { bp = { px = 3ul; py = 4ul } } in
  if U64.eq (get w) 7uL && U32.eq (pval one) 1ul &&
     U32.eq (unbox b) 3ul && U32.eq (unphantom { pc = 5ul }) 5ul
  then 0l else 1l
