module EntryIface

(* Section 131.  A module with an interface has a public surface, and it is
   the interface.  [--custard_entry_module] roots the surface: [exported]
   here, and not [private_dead], which the interface does not declare and
   nothing reaches.  [private_live] is equally hidden and is extracted anyway,
   because un-rooting changes only the root set and [exported] calls it. *)

let private_live (n : FStar.UInt32.t) : FStar.UInt32.t =
  FStar.UInt32.add_mod n 1ul

let private_dead (n : FStar.UInt32.t) : FStar.UInt32.t =
  FStar.UInt32.add_mod n 2ul

let exported n = private_live n
