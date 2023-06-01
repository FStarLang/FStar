module Pulse.Typing.Metatheory
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Typing

let comp_typing_u (g:env) (c:comp_st) = comp_typing g c (comp_u c)

val admit_comp_typing (g:env) (c:comp_st)
  : comp_typing_u g c
  
val st_typing_correctness (#g:env) (#t:st_term) (#c:comp_st) 
                          (_:st_typing g t c)
  : comp_typing_u g c

val comp_typing_inversion (#g:env) (#c:comp_st) (ct:comp_typing_u g c)
  : st_comp_typing g (st_comp_of_comp c)

let fresh_wrt (x:var) (g:env) (vars:_) = 
    None? (lookup g x) /\  ~(x `Set.mem` vars)
    
val st_comp_typing_inversion_cofinite (#g:env) (#st:_) (ct:st_comp_typing g st)
  : (universe_of g st.res st.u &
     tot_typing g st.pre Tm_VProp &
     (x:var{fresh_wrt x g (freevars st.post)} -> //this part is tricky, to get the quantification on x
       tot_typing (extend x (Inl st.res) g) (open_term st.post x) Tm_VProp))

val st_comp_typing_inversion (#g:env) (#st:_) (ct:st_comp_typing g st)
  : (universe_of g st.res st.u &
     tot_typing g st.pre Tm_VProp &
     x:var{fresh_wrt x g (freevars st.post)} &
     tot_typing (extend x (Inl st.res) g) (open_term st.post x) Tm_VProp)

val tm_exists_inversion (#g:env) (#u:universe) (#ty:term) (#p:term) 
                        (_:tot_typing g (Tm_ExistsSL u ty p should_elim_false) Tm_VProp)
                        (x:var { fresh_wrt x g (freevars p) } )
  : universe_of g ty u &
    tot_typing (extend x (Inl ty) g) p Tm_VProp

val tot_typing_weakening (#g:env) (#t:term) (#ty:term)
                         (x:var { fresh_wrt x g Set.empty })
                         (b:binding)
                         (_:tot_typing g t ty)
   : tot_typing (extend x b g) t ty

val pure_typing_inversion (#g:env) (#p:term) (_:tot_typing g (Tm_Pure p) Tm_VProp)
   : tot_typing g p (Tm_FStar FStar.Reflection.Typing.tm_prop Range.range_0)


let comp_st_with_post (c:comp_st) (post:term) : c':comp_st { st_comp_of_comp c' == ({ st_comp_of_comp c with post} <: st_comp) } =
  match c with
  | C_ST st -> C_ST { st with post }
  | C_STGhost i st -> C_STGhost i { st with post }
  | C_STAtomic i st -> C_STAtomic i {st with post}

let comp_st_with_pre (c:comp_st) (pre:term) : comp_st =
  match c with
  | C_ST st -> C_ST { st with pre }
  | C_STGhost i st -> C_STGhost i { st with pre }
  | C_STAtomic i st -> C_STAtomic i {st with pre }


let vprop_equiv_x g t p1 p2 =
  x:var { fresh_wrt x g (freevars p1) } ->
  vprop_equiv (extend x (Inl t) g) 
              (open_term p1 x)
              (open_term p2 x)

val st_typing_equiv_post (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                         (#post:term )//{ freevars post `Set.subset` freevars (comp_post c)}
                         (veq: vprop_equiv_x g (comp_res c) (comp_post c) post)
  : st_typing g t (comp_st_with_post c post)

val st_typing_equiv_pre (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                        (#pre:term )
                        (veq: vprop_equiv g (comp_pre c) pre)
  : st_typing g t (comp_st_with_pre c pre)