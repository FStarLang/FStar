module RefBindML

open FStar.Attributes

/// Section 70.2.  A reference binding is C++ [T &x = ...], and the OCaml
/// backend has no way to spell it -- emitting a copy instead would compile
/// and be wrong, which is the exact failure the attribute exists to prevent.

[@@custard_extern "rbml_cell"; custard_c_reference]
assume val cell : Type0

[@@custard_extern "rbml_slot"]
assume val slot : cell

[@@custard_extern "rbml_get"]
assume val get (c : cell) : FStar.All.ML FStar.UInt32.t

let main () : FStar.All.ML FStar.Int32.t =
  let c = slot in
  if FStar.UInt32.eq (get c) 0ul then 0l else 1l
