module CExtern
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.Attributes

(* Two things the direct-to-C backend has to get right that no other backend
   does, and that the DICE example of section 14 is the real user of.

   1. An *external type*: a type with no F* definition, whose C representation
      is fixed by a header the program does not own.  There are two ways to
      say so, and both are covered here: an attribute, when the declaration is
      one the program can edit, and --custard_extern_type, when it is not.

   2. A *global with a computed initializer*, which C cannot express and which
      therefore has to be assigned in a generated custard_init_globals. *)

(* Form 1: the attribute.  Custard emits no definition for [handle] and
   includes CExtern_stubs.h instead. *)
[@@custard_extern "cextern_handle_t"; custard_c_header "CExtern_stubs.h"]
assume val handle : Type0

[@@custard_extern "cextern_make"; custard_c_header "CExtern_stubs.h"]
assume val make (n:U32.t) : handle

[@@custard_extern "cextern_get"; custard_c_header "CExtern_stubs.h"]
assume val get (h:handle) : U32.t

(* Form 2: no attribute at all.  The Makefile passes
     --custard_extern_type CExtern.tag=cextern_tag_t@CExtern_stubs.h
   which is what a type in a library the program cannot edit needs -- ulib's
   FStar.Bytes.bytes, in the DICE case. *)
assume val tag : Type0

[@@custard_extern "cextern_mk_tag"; custard_c_header "CExtern_stubs.h"]
assume val mk_tag (_:unit) : tag

[@@custard_extern "cextern_tag_val"; custard_c_header "CExtern_stubs.h"]
assume val tag_val (t:tag) : U32.t

(* An external type also has to survive being a *field*, which is how DICE
   meets it: the program passes the record around without ever building or
   reading the field. *)
noeq type boxed = { b_h : handle; b_n : U32.t }

(* Computed at run time, so not a C initializer. *)
let gh : boxed = { b_h = make 41ul; b_n = 1ul }
let gt : tag = mk_tag ()

let main () : I32.t =
  let n = U32.add_mod (U32.add_mod (get gh.b_h) gh.b_n) (tag_val gt) in
  if U32.eq n 49ul then 0l else 1l
