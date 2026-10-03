module KeyNamesA
open FStar.Attributes

(* Half of the KeyNames test: an assumed value that [key_norm_steps] cannot
   unfold, whose last identifier is the same as KeyNamesB's. *)
[@@custard_extern "FStar_String.lowercase"]
assume val tweak (s:string) : string
