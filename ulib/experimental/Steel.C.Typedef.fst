module Steel.C.Typedef

open FStar.List.Tot
open Steel.C.PCM
open Steel.C.Ref
open FStar.FunctionalExtensionality
open Steel.Effect

irreducible let iter_unfold = 0

(** A typedef bundles together the various pieces of information needed to model a C data type in Steel. *)
[@@__reduce__]
noeq type typedef = { 
  (** The PCM used to model values of the corresponding C type. *)
  carrier: Type0;
  pcm: pcm carrier; 
  (** A way to view PCM carrier values as F* values that model the corresponding C values. *)
  view_type: Type0; 
  view: sel_view pcm view_type false;
  (** A way to decide whether a given element of the PCM is unit (needed to determine the case of a union) *)
  is_unit: x:carrier -> b:bool{b <==> x == one pcm};
} 
