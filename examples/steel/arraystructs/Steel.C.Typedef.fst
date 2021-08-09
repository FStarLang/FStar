module Steel.C.Typedef

open FStar.List.Tot
open Steel.C.PCM
open Steel.C.Ref
open FStar.FunctionalExtensionality
open Steel.Effect

irreducible let iter_unfold = 0

[@@__reduce__]
noeq type typedef = { 
  carrier: Type0; 
  pcm: pcm carrier; 
  view_type: Type0; 
  view: sel_view pcm view_type false;
} 

let register_typedef_of (_: Type0) = typedef
