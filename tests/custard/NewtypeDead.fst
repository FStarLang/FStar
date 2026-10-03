module NewtypeDead

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module G = FStar.Ghost

/// Section 110.  §5.2 collapses a one-field record to its field, and §108
/// gave the name back by rooting the abbreviation the collapse leaves.  The
/// argument was that the collapse had established that the payload was
/// representable.  It had established that the payload has a *layout*, and
/// those are different questions: a [Prims.list] is laid out fine and C
/// cannot hold one by value at all.
///
/// [spect] is COSE's shape reduced.  It reaches the layout table because a
/// monomorphization key asks for it -- the instantiation of an implicit type
/// index has to be known before the clone can be named -- and it reaches no
/// output at all, because the one position holding a value of it is erased.
/// Under §108 the abbreviation for it is rooted, the by-value [typedef] asks
/// the finiteness question for the first time, and the answer is error 368
/// about a type appearing nowhere in the program.
///
/// Note the absence of [--custard_monomorphize_types] here, which is why
/// this case is in its own module.  With type monomorphization on, [spect]
/// does not reach the layout table at all, and the test would pass against
/// the very compiler it exists to catch.
type spect = { st : list U32.t }

let keyed (#t : Type0) (g : G.erased t) (x : U32.t) : U32.t = x

/// The positive direction, in the same run: a payload naming no type is
/// safe vacuously, and the name comes back.
type live = { lv : U64.t }

let mk (x : U64.t) : live = { lv = x }

let get (w : live) : U64.t = w.lv

let main () : FStar.All.ML FStar.Int32.t =
  let k = keyed #spect (G.hide ({ st = [] })) 9ul in
  if U32.eq k 9ul && U64.eq (get (mk 7uL)) 7uL then 0l else 1l
