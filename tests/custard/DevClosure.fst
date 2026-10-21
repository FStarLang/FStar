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
/// Section 51.5.  The callees are copied, once per distinct prologue, and
/// the copies get the prologue; the originals are left alone for everyone
/// else (FStarLang/FStar#4711).
///
///  * [only] and [deep] (through [only]) are reached from the two seeds and
///    from nothing else, so each gets one copy per seed's prologue and the
///    original goes.
///  * [both] is reached from the seeds *and* from [host_side], so it gets the
///    same two copies and the undecorated original stays for [host_side].
///  * [down] is recursive, and its copy must call itself rather than the
///    original, which would otherwise survive.
///  * [host_only] is reached from neither seed, and must be left alone.
///  * [opt_out] carries a [CPrologue] of its own, so it is another entry and
///    is neither copied nor decorated by the closure.
///
/// The two seeds have *different* prologues and share callees, which is the
/// case #4711 was about: each shared callee used to get the first seed's
/// string whatever reached it.
///
/// Globals are left alone (section 51.5): a copy of a variable would be a
/// second variable, and a prologue on one is wrong for a CPU target.  [gk]
/// is read by both seeds -- with different prologues -- and [host_g] by
/// host code only; neither gets a prologue, and neither is refused.
///
/// The strings here are not CUDA's, deliberately: Custard does not read them,
/// and a test that used [__device__] would be checking a spelling rather than
/// a reachability computation.

let gk : U32.t = 7ul

let host_g : U32.t = 5ul

let deep (n : U32.t) : U32.t = U32.add_mod n 1ul

let only (n : U32.t) : U32.t = deep n

let both (n : U32.t) : U32.t = U32.mul_mod n 2ul

let host_only (n : U32.t) : U32.t = U32.sub_mod n 1ul

let rec down (n : U32.t) : Tot U32.t (decreases U32.v n) =
  if U32.eq n 0ul then 0ul else down (U32.sub n 1ul)

[@@CPrologue "/*OPT_OUT*/"]
let opt_out (n : U32.t) : U32.t = U32.add_mod n 3ul

[@@CPrologue "/*ENTRY*/"; custard_c_closure_prologue "/*EXCL*/"]
let kernel (n : U32.t) : U32.t =
  U32.add_mod gk (U32.add_mod (only n) (U32.add_mod (both n) (opt_out n)))

[@@custard_c_closure_prologue "/*target(avx2)*/"]
let kernel2 (n : U32.t) : U32.t =
  U32.add_mod gk (U32.add_mod (both n) (U32.add_mod (only n) (down n)))

let host_side (n : U32.t) : U32.t = U32.add_mod host_g (U32.add_mod (both n) (host_only n))

let main () : ML I32.t =
  let a = kernel 3ul in
  let b = host_side 4ul in
  let c = kernel2 4ul in
  if U32.eq a 23ul && U32.eq b 16ul && U32.eq c 20ul then 0l else 1l
