module Steel.C.Typedef

open FStar.List.Tot
open Steel.C.PCM
open Steel.C.Ref
open FStar.FunctionalExtensionality

noeq type typedef = { 
  carrier: Type0; 
  pcm: pcm carrier; 
  view_type: Type0; 
  can_view_unit: bool; 
  view: sel_view pcm view_type can_view_unit; 
} 

// assume val malloc: typedef -> ptr typedef.carrier typedef.pcm 

(*
 

let field_name fields = (field: string { field `List.Tot.mem` List.Tot.map fst fields}) 

 

let field_conn: 

  name: string -> 

  fields: list (string & typedef) -> 

  let t = typedef_struct name fields in 

  field_name: field_name fields -> 

  connection t.pcm (List.Tot.assoc field_name fields).pcm 

 

let field_conn_large_to_small: 

  name: string -> 

  fields: list (string & typedef) -> 

  let t = typedef_struct name fields in 

  field_name: field_name fields -> 

  x: t.user -> 

  Lemma 

  t.to_view (field_conn name fields field_name).morph x) == f?? (...) 

 

let addr_of_field_tot: 

  name: string -> 

  fields: list (string & typedef) -> 

  let t = typedef_struct name fields in 

  field_name: field_name fields -> 

  ptr ‘a t.pcm -> 

  ptr ‘a (List.Tot.assoc field_name fields).pcm 

= ... 

 

Page Break
 

val lift_view_struct: 

  #field_name: eqtype -> 

  #carriers: (field_name -> Type) -> 

  pcms: (fn: field_name -> pcm (carriers fn)) -> 

  users: (field_name -> Type) -> 

  can_view_unit_views: bool -> 

  views: (fn: field_name -> view (users fn) can_view_unit_views) -> 

  include: list field_name -> 

Tot (view (struct_pcm pcms) ... (can_view_unit_views || Nil? include)) 

 

val weaken: view ... false -> view ... true 
*)
