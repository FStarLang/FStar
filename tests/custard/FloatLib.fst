module FloatLib

(* Section 63.  A floating-point library that is *not* [FStar.Float32],
   standing in for the Kuiper and EverParse case: the same vocabulary, in a
   namespace Custard has never heard of, opted in by an attribute rather than
   by a hardcoded module name.

   The attribute goes on the type.  The operations carry nothing: what the
   attribute establishes is that this *module* speaks the vocabulary, which is
   what lets [add] below be C's [+] rather than a call to an undefined
   [FloatLib_add].  See section 63.1 for why that is a property of the module
   and not of each name.

   This module is deliberately separate from the one that uses it, because
   that is the arrangement a real library has -- and because it is the case
   that exercises the lookup: the probe has to find [FloatLib.t] from a
   mention of [FloatLib.add] in another module. *)

[@@FStar.Attributes.custard_float 32]
assume val t : Type0

assume val add : t -> t -> t
assume val sub : t -> t -> t
assume val mul : t -> t -> t
assume val div : t -> t -> t
assume val lt  : t -> t -> bool
assume val lte : t -> t -> bool
assume val ieee_eq : t -> t -> bool
assume val of_int : FStar.Int64.t -> t
assume val of_literal : string -> t

(* Section 64.1.  [FStar.Float32] *derives* these ([let zero = of_int 0L]), so
   there is no [val] and nothing to fall through; a library that declares them
   abstract instead -- the natural thing when the axioms are the point -- used
   to get an extern and a link error, with no diagnostic.  They are part of the
   vocabulary now. *)
assume val zero : t
assume val one : t

(* Section 64.1.  Not part of the vocabulary, and its [@@custard_extern] says
   so on purpose: a rule from a definition's own attributes beats the builtin
   table, which is what lets a library that really does realize a constant in
   C keep doing so. *)
[@@FStar.Attributes.custard_extern "FLT_MAX"; FStar.Attributes.custard_c_header "float.h"]
assume val largest : t
