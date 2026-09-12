module BF16Lib

(* Section 66.  bfloat16 is not an IEEE 754 interchange format, so it is not
   [@@custard_float 16] -- that width means binary16.  This is the other
   spelling, and the vocabulary is identical. *)

[@@FStar.Attributes.custard_bfloat16]
assume val t : Type0

assume val add : t -> t -> t
assume val sub : t -> t -> t
assume val mul : t -> t -> t
assume val div : t -> t -> t
assume val lt  : t -> t -> bool
assume val lte : t -> t -> bool
assume val ieee_eq : t -> t -> bool
assume val of_int : Int64.t -> t
assume val of_literal : string -> t
assume val zero : t
assume val one : t
