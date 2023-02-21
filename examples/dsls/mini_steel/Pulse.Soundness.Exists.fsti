module Pulse.Soundness.Exists

open FStar.Reflection
open Refl.Typing
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Soundness.Common

module EPure = Pulse.Elaborate.Pure

val exists_inversion
  (#f:stt_env)
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (e_typing:typing (extend_env_l f g)
                   (mk_exists u a p)
                   vprop_tm)

  : GTot (typing (extend_env_l f g) p
                 (mk_arrow (a, Q_Explicit) vprop_tm))

(*

 g |- a : Type u
 g |- p : a -> vprop
 ----------------------------------------------------------------
 g |- elim_exists<u> #a p : stt_ghost<u> a empty (exists_<u> p) (fun x -> p (reveal x))

*)

let elim_exists_post_body (u:universe) (a:term) (p:term) =
  let erased_a = EPure.mk_erased u a in
  let bv_0 = pack_ln (Tv_BVar (pack_bv (make_bv 0 tun))) in
  let reveal_0 = EPure.mk_reveal u a bv_0 in
  pack_ln (Tv_App p (reveal_0, Q_Explicit))

let elim_exists_post (u:universe) (a:term) (p:term) =
  let erased_a = EPure.mk_erased u a in
  mk_abs erased_a Q_Explicit (elim_exists_post_body u a p)

val elim_exists_soundness
  (#f:stt_env)
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (a_typing:typing (extend_env_l f g) a (pack_ln (Tv_Type u)))
  (p_typing:typing (extend_env_l f g) p (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (typing (extend_env_l f g)
                 (mk_elim_exists u a p)
                 (mk_stt_ghost_comp
                    u
                    (EPure.mk_erased u a) 
                    emp_inames_tm
                    (mk_exists u a p)
                    (elim_exists_post u a p)))

(*

 g |- a : Type u
 g |- p : a -> vprop
 g |- e : vprop
 -------------------------------------------------------------------------
 g |- intro_exists<u> #a p e : stt_ghost<0> unit empty (p e) (fun _ -> exists_ p)

*)
val intro_exists_soundness
  (#f:stt_env)
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (#e:term)
  (a_typing:typing (extend_env_l f g) a (pack_ln (Tv_Type u)))
  (p_typing:typing (extend_env_l f g) p (mk_arrow (a, Q_Explicit) vprop_tm))
  (e_typing:typing (extend_env_l f g) e a)

  : GTot (typing (extend_env_l f g)
                 (mk_intro_exists u a p e)
                 (mk_stt_ghost_comp uzero unit_tm emp_inames_tm
                    (pack_ln (Tv_App p (e, Q_Explicit)))
                    (mk_abs unit_tm Q_Explicit (mk_exists u a p))))
