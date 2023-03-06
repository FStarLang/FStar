module Pulse.Soundness.Exists

open FStar.Reflection
open Pulse.Reflection.Util

module RT = Refl.Typing

val exists_inversion
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (e_typing:RT.typing g
                      (mk_exists u a p)
                      vprop_tm)
  : GTot (RT.typing g
                    p
                   (mk_arrow (a, Q_Explicit) vprop_tm))

(*

 g |- a : Type u
 g |- p : a -> vprop
 ----------------------------------------------------------------
 g |- elim_exists<u> #a p : stt_ghost<u> a empty (exists_<u> p) (fun x -> p (reveal x))

*)

let elim_exists_post_body (u:universe) (a:term) (p:term) (x:var) =
  let x_tm = RT.var_as_term x in
  let reveal_x = mk_reveal u a x_tm in
  let post = pack_ln (Tv_App p (reveal_x, Q_Explicit)) in
  RT.open_or_close_term' post (RT.CloseVar x) 0

let elim_exists_post (u:universe) (a:term) (p:term) (x:var) =
  let erased_a = mk_erased u a in
  mk_abs erased_a Q_Explicit (elim_exists_post_body u a p x)

val elim_exists_soundness
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (x:var{None? (RT.lookup_bvar g x)})
  (a_typing:RT.typing g a (pack_ln (Tv_Type u)))
  (p_typing:RT.typing g p (mk_arrow (a, Q_Explicit) vprop_tm))
  : GTot (RT.typing g
                 (mk_elim_exists u a p)
                 (mk_stt_ghost_comp
                    u
                    (mk_erased u a) 
                    emp_inames_tm
                    (mk_exists u a p)
                    (elim_exists_post u a p x)))

(*

 g |- a : Type u
 g |- p : a -> vprop
 g |- e : vprop
 -------------------------------------------------------------------------
 g |- intro_exists<u> #a p e : stt_ghost<0> unit empty (p e) (fun _ -> exists_ p)

*)
val intro_exists_soundness
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (#e:term)
  (a_typing:RT.typing g a (pack_ln (Tv_Type u)))
  (p_typing:RT.typing g p (mk_arrow (a, Q_Explicit) vprop_tm))
  (e_typing:RT.typing g e a)
  : GTot (RT.typing g
                 (mk_intro_exists u a p e)
                 (mk_stt_ghost_comp uzero unit_tm emp_inames_tm
                    (pack_ln (Tv_App p (e, Q_Explicit)))
                    (mk_abs unit_tm Q_Explicit (mk_exists u a p))))

(*

 g |- a : Type u
 g |- p : a -> vprop
 g |- e : vprop
 -------------------------------------------------------------------------
 g |- intro_exists<u> #a p e : stt_ghost<0> unit empty (p e) (fun _ -> exists_ p)

*)
val intro_exists_erased_soundness
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (#e:term)
  (a_typing:RT.typing g a (pack_ln (Tv_Type u)))
  (p_typing:RT.typing g p (mk_arrow (a, Q_Explicit) vprop_tm))
  (e_typing:RT.typing g e (mk_erased u a))
  : GTot (RT.typing g
                 (mk_intro_exists_erased u a p e)
                 (mk_stt_ghost_comp uzero unit_tm emp_inames_tm
                    (pack_ln (Tv_App p (mk_reveal u a e, Q_Explicit)))
                    (mk_abs unit_tm Q_Explicit (mk_exists u a p))))
