module EntryRootsLib

module I32 = FStar.Int32

/// A library whose interface is its externals: the target realizes both, and
/// a consumer that uses one of them still expects to be given the other.

assume val used : I32.t -> I32.t

assume val unused : I32.t -> I32.t
