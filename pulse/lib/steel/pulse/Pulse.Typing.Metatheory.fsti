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

val tot_typing_weakening (#g:env) (#t:term) (#ty:term)
                         (x:var { fresh_wrt x g Set.empty })
                         (x_t:typ)
                         (_:tot_typing g t ty)
   : tot_typing (push_binding g x ppname_default x_t) t ty

val pure_typing_inversion (#g:env) (#p:term) (_:tot_typing g (tm_pure p) tm_vprop)
   : tot_typing g p (tm_fstar FStar.Reflection.Typing.tm_prop Range.range_0)


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
  vprop_equiv (push_binding g x ppname_default t)
              (open_term p1 x)
              (open_term p2 x)

let st_typing_equiv_post (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                         (#post:term )//{ freevars post `Set.subset` freevars (comp_post c)}
                         (veq: vprop_equiv_x g (comp_res c) (comp_post c) post)
  : st_typing g t (comp_st_with_post c post)
  = admit()

let st_typing_equiv_pre (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                        (#pre:term )
                        (veq: vprop_equiv g (comp_pre c) pre)
  : st_typing g t (comp_st_with_pre c pre)
  = admit()

let pairwise_disjoint (g g' g'':env) =
  disjoint g g' /\ disjoint g' g'' /\ disjoint g g''

let st_typing_weakening
  (g:env) (g':env { disjoint g g' })
  (t:st_term) (c:comp_st) (_:st_typing (push_env g g') t c)
  (g1:env { pairwise_disjoint g g1 g' })
  : st_typing (push_env (push_env g g1) g') t c = magic ()

let veq_weakening
  (g:env) (g':env { disjoint g g' })
  (#v1 #v2:vprop) (_:vprop_equiv (push_env g g') v1 v2)
  (g1:env { pairwise_disjoint g g1 g' })
  : vprop_equiv (push_env (push_env g g1) g') v1 v2 = magic ()

// move to Env
let singleton_env (f:_) (x:var) (t:typ) = push_binding (mk_env f) x ppname_default t

let nt (x:var) (t:term) = [ NT x t ]

let subst_env (en:env) (ss:subst)
  : en':env { fstar_env en == fstar_env en' /\
              dom en == dom en' } =
  admit ()

let st_typing_subst
  (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (#e1:st_term) (#c1:comp_st)
  (e1_typing:st_typing (push_env g (push_env (singleton_env (fstar_env g) x t) g')) e1 c1)

  : st_typing (push_env g (subst_env g' (nt x e)))
              (subst_st_term e1 (nt x e))
              (subst_comp c1 (nt x e)) =
  admit ()

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
