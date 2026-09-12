module ExtBuf

(* Section 60.2.  The [TBuf] half of the extern-pointer cast of section 57.1.

   That fix casts the result of an extern returning a pointer, because the
   extern's declaration is in a header Custard does not write and a C macro
   over untyped memory naturally yields [void *] -- which C converts
   implicitly and C++ does not.  The fix was first written for [TBuf] alone
   while the only test in the suite, [ExtPtr], returns a [ref] and so
   exercises [TRef]; the guard now covers both, and this is the file that
   holds the half that motivated the report.

   It lives here rather than next to [ExtPtr] because [array] is a Pulse
   library type -- the only types Custard maps to [TBuf] are
   [Pulse.Lib.Array.Core.array], [Pulse.Lib.Vec.vec] and
   [Pulse.Lib.ArrayPtr.ptr] -- and tests/custard is run by [make test-1] and
   [test-2], whose compilers cannot resolve a Pulse module at all
   ("Module Pulse.Lib.Array cannot be found").  No Pulse *syntax* appears
   below, but the library dependency alone is enough to move it.

   [main] binds the returned pointer, and that is the whole point of its
   shape.  Discarding it --- [let _ = base 0sz in 0l] --- emits a cast to
   [void] wrapped around the call, and with the pointer cast removed C++
   accepts that too, because converting a [void] pointer to [void] is not a
   conversion at all.  A test written that way passes on a build with the
   bug reintroduced.  Binding the result to a typed variable is what makes
   the compiler answer the question. *)

module U8 = FStar.UInt8
module I32 = FStar.Int32
module A = Pulse.Lib.Array
open FStar.All
open FStar.Attributes

[@@custard_extern "extbuf_base"; custard_c_header "ExtBuf_stubs.h"]
assume val base (off : FStar.SizeT.t) : ML (A.array U8.t)

[@@custard_extern "extbuf_use"; custard_c_header "ExtBuf_stubs.h"]
assume val use_first (a : A.array U8.t) : ML I32.t

let main () : ML I32.t =
  let a = base 0sz in
  use_first a
