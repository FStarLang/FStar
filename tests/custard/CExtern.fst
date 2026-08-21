module CExtern
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All
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

[@@custard_extern "cextern_bump"; custard_c_header "CExtern_stubs.h"]
assume val bump (n:U32.t) : ML unit

[@@custard_extern "cextern_total"; custard_c_header "CExtern_stubs.h"]
assume val get_total (_:unit) : ML U32.t

(* An external type also has to survive being a *field*, which is how DICE
   meets it: the program passes the record around without ever building or
   reading the field. *)
noeq type boxed = { b_h : handle; b_n : U32.t }

(* A unit-valued match most of whose arms do nothing, which is what Pulse
   code looks like: one case of a state does something and the rest return
   [()].  Each of those used to be an empty [else if (...) { }] in the C. *)
type cmd = | Nop | Skip | Bump of U32.t

let apply (c:cmd) : ML unit =
  match c with
  | Bump n -> bump n
  | Nop -> ()
  | Skip -> ()

(* Computed at run time, so not a C initializer. *)
let gh : boxed = { b_h = make 41ul; b_n = 1ul }
let gt : tag = mk_tag ()

(* The other road: a literal, and a width conversion of one, are C constant
   expressions, so these are initialized where they are declared and never
   mentioned in custard_init_globals.  A record is *not*, however constant its
   fields: the compound literal Custard emits for it is not a constant
   expression at file scope. *)
let base : U32.t = 7ul
let low : FStar.UInt8.t = FStar.Int.Cast.uint32_to_uint8 300ul

let main () : ML I32.t =
  apply Nop; apply (Bump 2ul); apply Skip; apply (Bump 3ul);
  let n = U32.add_mod (U32.add_mod (get gh.b_h) gh.b_n) (tag_val gt) in
  if U32.eq n 49ul && U32.eq (get_total ()) 5ul
     && U32.eq base 7ul && FStar.UInt8.eq low 44uy
  then 0l else 1l
