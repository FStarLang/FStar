module ExternErase
module U32 = FStar.UInt32
module I32 = FStar.Int32
module G = FStar.Ghost
open FStar.All
open FStar.Attributes

/// Section 49.3.  An external whose F* signature says more than its C
/// prototype can.  [ee_run] takes a specification-only parameter -- [cb] is
/// a *pure* [unit -> unit], so it computes nothing and Custard drops it --
/// and the emitted call therefore has one argument where the header has two.
/// Custard cannot see the header, so warning 382 is the only place this can
/// be caught.
///
/// The second half is the carve-out: [w] is [erased], which is the author
/// saying "this is not there at run time", and must *not* be warned about,
/// or section 47.2's indexed-external idiom is unusable.

[@@custard_extern "ee_run"; custard_c_header "ExternErase_stubs.h"]
assume val run (cb : unit -> unit) (n : U32.t) : ML U32.t

[@@custard_extern "ee_run"; custard_c_header "ExternErase_stubs.h"]
assume val run_g (w : G.erased nat) (n : U32.t) : ML U32.t

let main () : ML I32.t =
  let a = run (fun () -> ()) 20ul in
  let b = run_g (G.hide 3) 22ul in
  if U32.eq (U32.add_mod a b) 42ul then 0l else 1l
