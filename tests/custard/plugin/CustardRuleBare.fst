module CustardRuleBare

(* Section 64.  The rule-authoring mistake the polymorphic-external support
   makes possible: building the call to a polymorphic runtime entry point
   without putting the argument's type on the [EQual] node.

   The instantiations of such an entry point exist nowhere else -- the
   extractor never sees an F* call to it -- so a missing type argument leaves
   nothing to emit a declaration from, and the reference names a symbol that
   does not exist.  Error 388 says so here rather than letting the linker say
   it about generated code.

   Extracted for the diagnostic; there is no output. *)

module U32 = FStar.UInt32

let main () : FStar.All.ML unit = CustardRuleTest.bare_emit 3ul
