module RefBindCopy

open FStar.Attributes
module U32 = FStar.UInt32

/// Section 70.2.  [@@custard_c_reference] binds a *local* by reference.  It
/// does not change a signature -- a reference parameter would refuse every
/// argument that is not an lvalue -- so a parameter of a function Custard
/// compiles itself is still a copy, and a write the callee makes through it
/// is lost.  Warning 391 is where that is said out loud.

[@@custard_extern "rbc_cell"; custard_c_reference]
assume val cell : Type0

[@@custard_extern "rbc_slot"]
assume val slot : cell

[@@custard_extern "rbc_bump"]
assume val bump (c : cell) : FStar.All.ML unit

let twice (c : cell) : FStar.All.ML unit = bump c; bump c

let main () : FStar.All.ML FStar.Int32.t =
  let c = slot in
  twice c;
  0l
