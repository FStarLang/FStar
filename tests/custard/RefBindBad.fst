module RefBindBad

open FStar.Attributes

/// Section 70.2.  [@@custard_c_reference] is a statement about how the
/// *target* spells a binding, so it means nothing without a target: on a type
/// Custard compiles itself there is no second object for a write to be lost
/// in, and accepting the attribute would promise an aliasing the output does
/// not have.

[@@custard_c_reference]
assume val cell : Type0

[@@custard_extern "rbb_slot"]
assume val slot : cell

[@@custard_extern "rbb_get"]
assume val get (c : cell) : FStar.All.ML FStar.UInt32.t

let main () : FStar.All.ML FStar.Int32.t =
  let c = slot in
  if FStar.UInt32.eq (get c) 0ul then 0l else 1l
