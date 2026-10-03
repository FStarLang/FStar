module RefBind

open FStar.Attributes
module U32 = FStar.UInt32

/// Section 70.2.  An external type whose F* values are *handles*.
///
/// Kuiper's Tensor Core fragment is one: F* holds an [lseq (fragment ...)]
/// and hands each element its own permission, so reading an element yields a
/// handle, and copying a handle is right in F* because the permission travels
/// separately.  In C++ the fragment is a value object, so
/// [auto acc = accFrags[i]; mma_sync(acc, ...)] writes a *copy* that dies at
/// the end of the iteration -- and nothing warns, the class being copyable
/// and a reference to a fresh copy being well-formed.  The accumulator chain
/// folds away and the kernel writes zeros.
///
/// [@@custard_c_reference] says so, and the binding becomes [rb_cell &c].

[@@custard_extern "rb_cell"; custard_c_reference;
    custard_c_header "RefBind_stubs.h"]
assume val cell : Type0

/// An object that lives outside F*, so that a binding of it has something to
/// alias and the test can read the object back rather than the binding.
[@@custard_extern "rb_slot"; custard_c_header "RefBind_stubs.h"]
assume val slot : cell

[@@custard_extern "rb_bump"; custard_c_header "RefBind_stubs.h"]
assume val bump (c : cell) : FStar.All.ML unit

[@@custard_extern "rb_get"; custard_c_header "RefBind_stubs.h"]
assume val get (c : cell) : FStar.All.ML U32.t

[@@custard_extern "rb_make"; custard_c_header "RefBind_stubs.h"]
assume val make (_ : unit) : FStar.All.ML cell

let main () : FStar.All.ML FStar.Int32.t =
  (* The binding that has to alias.  Under a copy the two bumps land in an
     object that dies here and [rb_slot] still reads 0. *)
  let c = slot in
  bump c;
  bump c;
  (* A fresh value is a copy of nothing, so this one is not a reference: a
     reference cannot bind to the result of a call anyway. *)
  let fresh = make () in
  bump fresh;
  if U32.eq (get slot) 2ul && U32.eq (get fresh) 1ul then 0l else 1l
