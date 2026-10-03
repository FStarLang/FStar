module KsHi

module I32 = FStar.Int32
module U32 = FStar.UInt32

/// Section 65.  Which karamel file an external belongs to, under
/// [--custard_split].
///
/// A declaration group was assigned to the module of its first *candidate*,
/// and the candidates are the group's own modules followed by the homes of
/// everything it references.  An external emits nothing, so the first list
/// was empty and the group went to the home of the first thing it mentions:
/// [KsExt.sum] was declared in [KsLo]'s header, because its argument is a
/// [KsLo.point].
///
/// A consumer that reads both headers then sees the name declared in a file
/// that another translation unit also claims to define, and karamel, given
/// two inputs that each claim a file of that name, keeps one of them and
/// drops the declaration on the floor.

let main () : I32.t =
  let p = KsLo.flip ({ px = 3ul; py = 4ul }) in
  if U32.eq (KsExt.sum p) 7ul then 0l else 1l
