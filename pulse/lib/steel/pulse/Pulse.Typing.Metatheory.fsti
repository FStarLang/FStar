module Pulse.Typing.Metatheory
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Typing

let comp_typing_u (g:env) (c:comp_st) = comp_typing g c (comp_u c)

val st_typing_correctness (#g:env) (#t:st_term) (#c:comp_st) 
                          (_:st_typing g t c)
  : comp_typing_u g c

val comp_typing_inversion (#g:env) (#c:comp_st) (ct:comp_typing_u g c)
  : st_comp_typing g (st_comp_of_comp c)

let fresh_wrt (x:var) (g:env) (vars:_) = 
    None? (lookup g x) /\  ~(x `Set.mem` vars)
    
val st_comp_typing_inversion_cofin (#g:env) (#st:_) (ct:st_comp_typing g st)
  : (universe_of g st.res st.u &
     tot_typing g st.pre Tm_VProp &
     (x:var{fresh_wrt x g (freevars st.post)} -> //this part is tricky, to get the quantification on x
       tot_typing (extend x (Inl st.res) g) (open_term st.post x) Tm_VProp))

val st_comp_typing_inversion (#g:env) (#st:_) (ct:st_comp_typing g st)
  : (universe_of g st.res st.u &
     tot_typing g st.pre Tm_VProp &
     x:var{fresh_wrt x g (freevars st.post)} &
     tot_typing (extend x (Inl st.res) g) (open_term st.post x) Tm_VProp)

