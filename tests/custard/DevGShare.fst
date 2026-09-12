module DevGShare
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All
open FStar.Attributes

/// Section 53.2.  A global in the device closure that host code also reads.
///
/// The exclusive string is fine on a variable -- CUDA's [__device__] applies
/// to one -- but the shared string is not.  A qualifier meaning "reachable
/// from both" describes a function; CUDA's answer for a shared *variable* is
/// [__managed__], which is unified memory and a runtime cost rather than a
/// decoration.  Worse, [__host__] on a variable is dropped silently, so
/// emitting the shared string would give a device-only variable that compiles
/// with a warning and reads the wrong memory at runtime.
///
/// Custard reads neither string and so cannot tell a target that has an
/// answer here from one that does not.  It refuses.

let g : U32.t = 7ul

[@@CPrologue "/*ENTRY*/"; custard_c_closure_prologue "/*EXCL*/" "/*SHARED*/"]
let kernel (n : U32.t) : U32.t = U32.add_mod g n

let host_side (n : U32.t) : U32.t = U32.add_mod g n

let main () : ML I32.t =
  let a = kernel 3ul in
  let b = host_side 4ul in
  if U32.eq a 10ul && U32.eq b 11ul then 0l else 1l
