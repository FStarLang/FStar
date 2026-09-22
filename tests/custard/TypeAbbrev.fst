module TypeAbbrev

module U32 = FStar.UInt32

/// Section 70.1.  A type abbreviation is a library's published C type, and
/// Custard unfolds abbreviations -- so nothing in the extracted code refers
/// to the name, and it is dead by construction.  Only being a root keeps it.
/// [--custard_entry] on a type already did that (section 8.2,
/// [TypeEntry.fst]); this pins the *module* form, which is where a library's
/// interface is actually named.

type cell (a : Type0) = { hd : a; tl : U32.t }

type point = { px : U32.t; py : U32.t }

/// The plain case: another name for a record.
let handle_t = point

/// The case that made it a blocker.  The body is a *monomorphized* instance,
/// so without the typedef a consumer has to write down the mangled name of
/// an internal encoding -- EverParse's section 65.4, where
/// [cbor_det_array_iterator_t] came out as
/// [CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__cbor_raw].
let iter_t = cell point

let count_t = U32.t

/// Proof-level, and not part of any C interface: the abbreviation carries
/// [Erased] and is not printed, so rooting a whole module does not turn its
/// specifications into header noise.
let spec_t : Type0 = squash True

let mk (x y : U32.t) : handle_t = { px = x; py = y }

let it (h : handle_t) : iter_t = { hd = h; tl = 0ul }

let get (i : iter_t) : count_t = i.hd.px

let main () : FStar.All.ML FStar.Int32.t =
  let h = mk 1ul 2ul in
  if U32.eq (get (it h)) 1ul then 0l else 1l
