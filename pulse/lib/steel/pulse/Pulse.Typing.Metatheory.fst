module Pulse.Typing.Metatheory
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Typing

let admit_st_comp_typing (g:env) (st:st_comp) 
  : st_comp_typing g st
  = admit(); 
    STC g st (fresh g) (admit()) (admit()) (admit())

let admit_comp_typing (g:env) (c:comp_st)
  : comp_typing_u g c
  = match c with
    | C_ST st ->
      CT_ST g st (admit_st_comp_typing g st)
    | C_STAtomic inames st ->
      CT_STAtomic g inames st (admit()) (admit_st_comp_typing g st)
    | C_STGhost inames st ->
      CT_STGhost g inames st (admit()) (admit_st_comp_typing g st)      

let st_typing_correctness (#g:env) (#t:st_term) (#c:comp_st) 
                          (_:st_typing g t c)
  : comp_typing_u g c
  = admit_comp_typing g c
    
let add_frame_well_typed (#g:env) (#c:comp_st) (ct:comp_typing_u g c)
                         (#f:term) (ft:tot_typing g f Tm_VProp)
  : comp_typing_u g (add_frame c f)
  = admit_comp_typing _ _

let comp_typing_inversion #g #c ct = 
  match ct with
  | CT_ST _ _ st
  | CT_STAtomic _ _ _ _ st 
  | CT_STGhost _ _ _ _ st   -> st

let st_comp_typing_inversion_cofinite (#g:env) (#st:_) (ct:st_comp_typing g st) = 
  admit(), admit(), (fun _ -> admit())

let st_comp_typing_inversion (#g:env) (#st:_) (ct:st_comp_typing g st) = 
  let STC g st x ty pre post = ct in
  (| ty, pre, x, post |)

let tm_exists_inversion (#g:env) (#u:universe) (#ty:term) (#p:term) 
                        (_:tot_typing g (Tm_ExistsSL u (as_binder ty) p) Tm_VProp)
                        (x:var { fresh_wrt x g (freevars p) } )
  : universe_of g ty u &
    tot_typing (push_binding g x ppname_default ty) p Tm_VProp
  = admit(), admit()

let tot_typing_weakening #g #t #ty x b d = admit()

let pure_typing_inversion (#g:env) (#p:term) (_:tot_typing g (Tm_Pure p) Tm_VProp)
   : tot_typing g p (Tm_FStar FStar.Reflection.Typing.tm_prop Range.range_0)
   = admit()