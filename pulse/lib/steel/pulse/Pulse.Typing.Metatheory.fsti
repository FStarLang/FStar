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
       tot_typing (push_binding g x st.res) (open_term st.post x) Tm_VProp))

val st_comp_typing_inversion (#g:env) (#st:_) (ct:st_comp_typing g st)
  : (universe_of g st.res st.u &
     tot_typing g st.pre Tm_VProp &
     x:var{fresh_wrt x g (freevars st.post)} &
     tot_typing (push_binding g x st.res) (open_term st.post x) Tm_VProp)

val tm_exists_inversion (#g:env) (#u:universe) (#ty:term) (#p:term) 
                        (_:tot_typing g (Tm_ExistsSL u (as_binder ty) p) Tm_VProp)
                        (x:var { fresh_wrt x g (freevars p) } )
  : universe_of g ty u &
    tot_typing (push_binding g x ty) p Tm_VProp

val tot_typing_weakening (#g:env) (#t:term) (#ty:term)
                         (x:var { fresh_wrt x g Set.empty })
                         (x_t:typ)
                         (_:tot_typing g t ty)
   : tot_typing (push_binding g x x_t) t ty

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
  vprop_equiv (push_binding g x t)
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


///// Substitution lemma /////

module L = FStar.List.Tot
let map_opt (#a #b:Type) (f:a -> b) (x:option a) : option b =
  match x with
  | None -> None
  | Some x -> Some (f x)

let subst_flip (ss:subst) (t:term) = subst_term t ss

let subst_env (en:env) (ss:subst)
  : en':env { forall (x:var). lookup en' x ==
                              map_opt (subst_flip ss) (lookup en x) }
  = admit ()

type nt_subst = s:subst {
  forall (elt:subst_elt). List.Tot.memP elt s ==> NT? elt
}

let pairwise_disjoint (g g' g'':env) =
  disjoint g g' /\ disjoint g' g'' /\ disjoint g g''

let rec lookup_nt_subst (ss:nt_subst) (x:var) : option term =
  match ss with
  | [] -> None
  | (NT y t)::ss -> if x = y then Some t else lookup_nt_subst ss x

let well_typed_ss (g:env) (g':env) (ss:nt_subst) =

  forall (elt:subst_elt).
  L.memP elt ss ==> (let NT x e = elt in
                     x `Set.mem` dom g' /\
                     (let Some t = lookup g' x in
                      tot_typing g e t))

let ss_covers_g' (ss:nt_subst) (g':env) =
  forall (x:var). x `Set.mem` dom g' ==> Some? (lookup_nt_subst ss x)

let tot_typing_subst (g:env) (g':env) (g'':env { pairwise_disjoint g g' g'' })
  (#e1:term) (#t1:typ)
  (e1_typing:tot_typing (push_env g (push_env g' g'')) e1 t1)
  (ss:nt_subst { well_typed_ss g g' ss /\ ss_covers_g' ss g' })
  : tot_typing (push_env g g'') (subst_term e1 ss) (subst_term t1 ss) = admit ()
  
let rec st_typing_subst (g:env) (g':env) (g'':env { pairwise_disjoint g g' g'' })
  (#e1:st_term) (#c1:comp_st)
  (e1_typing:st_typing (push_env g (push_env g' g'')) e1 c1)
  (ss:nt_subst { well_typed_ss g g' ss /\ ss_covers_g' ss g' })
  : st_typing (push_env g g'') (subst_st_term e1 ss) (subst_comp c1 ss) =

  match e1_typing with
  | T_Abs _ x q b u body c b_ty_typing body_typing ->
    let b_ty_typing
      : tot_typing (push_env g g'')
                   (subst_term b.binder_ty ss)
                   (tm_type u) = tot_typing_subst g g' g'' b_ty_typing ss in
    
    let g1 : env = push_binding (push_env g (push_env g' g'')) x (subst_term b.binder_ty ss) in
    let g2 : env = push_env g (push_env g' (push_binding g'' x (subst_term b.binder_ty ss))) in
    assume (bindings g1 == bindings g2);
  
    let body_typing
      : st_typing g1 (open_st_term_nv (subst_st_term body ss) (b.binder_ppname, x)) (subst_comp c ss)
      = st_typing_subst g g' (push_binding g'' x (subst_term b.binder_ty ss)) body_typing ss in

    T_Abs (push_env g g') x q (subst_binder b ss) u (subst_st_term body ss) (subst_comp c ss)
          b_ty_typing body_typing

  | T_STApp _ head ty q res arg head_typing arg_typing ->
    assume (subst_term (tm_arrow (as_binder ty) q res) ss ==
            tm_arrow (as_binder (subst_term ty ss)) q (subst_comp res ss));
    assume (subst_comp (open_comp_with res arg) ss ==
            open_comp_with (subst_comp res ss) (subst_term arg ss));
    T_STApp (push_env g g'') (subst_term head ss) (subst_term ty ss) q
            (subst_comp res ss) (subst_term arg ss)
            (tot_typing_subst g g' g'' head_typing ss)
            (tot_typing_subst g g' g'' arg_typing ss)

  | _ -> admit ()
