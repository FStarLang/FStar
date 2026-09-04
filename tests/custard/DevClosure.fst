module DevClosure
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All
open FStar.Attributes

/// Section 51.3.  A prologue that follows the call graph.
///
/// [CPrologue] decorates one declaration.  CUDA needs more: a [__global__]
/// function may only call [__device__] functions, so marking a kernel says
/// nothing about the ordinary C functions its body calls, and there is no
/// number of per-declaration flags that fixes it -- the set is the transitive
/// callees.
///
/// The three classes a callee can fall into are all here.
///
///  * [only] is reached from the kernel and from nowhere else, so it gets the
///    exclusive string.
///  * [both] is reached from the kernel *and* from [host_side], so it gets
///    the shared one.  This is the case a plugin cannot express at all by
///    setting flags: it is a property of the whole program, not of the
///    declaration.
///  * [host_only] is reached from neither, and must be left alone.
///
/// Section 53.2 adds the fourth node type.  The closure covers *functions*;
/// a global reached from device code was left undecorated, and nvcc is not
/// forgiving about one -- "a host variable cannot be directly read in a
/// device function".  [gk] is device-exclusive and gets the exclusive
/// string.  There is deliberately no shared global here: that case is error
/// 383 and lives in [DevGShare], because the shared string cannot be applied
/// to a variable at all.  [host_g] is the negative: a global the kernel never
/// reaches must be left alone, exactly as [host_only] is.
///
/// The strings here are not CUDA's, deliberately: Custard does not read them,
/// and a test that used [__device__] would be checking a spelling rather than
/// a reachability computation.

let gk : U32.t = 7ul

let host_g : U32.t = 5ul

let only (n : U32.t) : U32.t = U32.add_mod n 1ul

let both (n : U32.t) : U32.t = U32.mul_mod n 2ul

let host_only (n : U32.t) : U32.t = U32.sub_mod n 1ul

[@@CPrologue "/*ENTRY*/"; custard_c_closure_prologue "/*EXCL*/" "/*SHARED*/"]
let kernel (n : U32.t) : U32.t = U32.add_mod gk (U32.add_mod (only n) (both n))

let host_side (n : U32.t) : U32.t = U32.add_mod host_g (U32.add_mod (both n) (host_only n))

let main () : ML I32.t =
  let a = kernel 3ul in
  let b = host_side 4ul in
  if U32.eq a 17ul && U32.eq b 16ul then 0l else 1l
