module Pulse.Typing.Metatheory.Base
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

val st_comp_typing_inversion_cofinite (#g:env) (#st:_) (ct:st_comp_typing g st)
  : (universe_of g st.res st.u &
     tot_typing g st.pre tm_vprop &
     (x:var{fresh_wrt x g (freevars st.post)} -> //this part is tricky, to get the quantification on x
       tot_typing (push_binding g x ppname_default st.res) (open_term st.post x) tm_vprop))

val st_comp_typing_inversion (#g:env) (#st:_) (ct:st_comp_typing g st)
  : (universe_of g st.res st.u &
     tot_typing g st.pre tm_vprop &
     x:var{fresh_wrt x g (freevars st.post)} &
     tot_typing (push_binding g x ppname_default st.res) (open_term st.post x) tm_vprop)

val tm_exists_inversion (#g:env) (#u:universe) (#ty:term) (#p:term) 
                        (_:tot_typing g (tm_exists_sl u (as_binder ty) p) tm_vprop)
                        (x:var { fresh_wrt x g (freevars p) } )
  : universe_of g ty u &
    tot_typing (push_binding g x ppname_default ty) p tm_vprop

val pure_typing_inversion (#g:env) (#p:term) (_:tot_typing g (tm_pure p) tm_vprop)
   : tot_typing g p (tm_fstar FStar.Reflection.Typing.tm_prop Range.range_0)

val tot_typing_weakening
  (g:env) (g':env { disjoint g g' })
  (t:term) (ty:typ) (_:tot_typing (push_env g g') t ty)
  (g1:env { pairwise_disjoint g g1 g' })
  : tot_typing (push_env (push_env g g1) g') t ty

val st_typing_weakening
  (g:env) (g':env { disjoint g g' })
  (t:st_term) (c:comp) (_:st_typing (push_env g g') t c)
  (g1:env { pairwise_disjoint g g1 g' })
  : st_typing (push_env (push_env g g1) g') t c

let veq_weakening
  (g:env) (g':env { disjoint g g' })
  (#v1 #v2:vprop) (_:vprop_equiv (push_env g g') v1 v2)
  (g1:env { pairwise_disjoint g g1 g' })
  : vprop_equiv (push_env (push_env g g1) g') v1 v2 = magic ()

let nt (x:var) (t:term) = [ NT x t ]

val st_typing_subst
  (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (#e1:st_term) (#c1:comp_st)
  (e1_typing:st_typing (push_env g (push_env (singleton_env (fstar_env g) x t) g')) e1 c1)

  : st_typing (push_env g (subst_env g' (nt x e)))
              (subst_st_term e1 (nt x e))
              (subst_comp c1 (nt x e))

let vprop_equiv_subst
  (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (#p1:term) (#p2:term)
  (veq:vprop_equiv (push_env g (push_env (singleton_env (fstar_env g) x t) g')) p1 p2)

: vprop_equiv (push_env g (subst_env g' (nt x e)))
              (subst_term p1 (nt x e))
              (subst_term p2 (nt x e)) =
  admit ()
