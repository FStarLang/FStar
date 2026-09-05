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
