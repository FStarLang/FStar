module Pulse.Typing.Metatheory
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Typing

let st_typing_correctness (#g:env) (#t:st_term) (#c:comp_st) 
                          (_:st_typing g t c)
  : comp_typing_u g c
  = admit()

let add_frame_well_typed (#g:env) (#c:comp_st) (ct:comp_typing_u g c)
                         (#f:term) (ft:tot_typing g f Tm_VProp)
  : comp_typing_u g (add_frame c f)
  = admit()

let comp_typing_inversion #g #c ct = admit()

let st_comp_typing_inversion_cofinite (#g:env) (#st:_) (ct:st_comp_typing g st) = admit()

let st_comp_typing_inversion (#g:env) (#st:_) (ct:st_comp_typing g st) = admit()

