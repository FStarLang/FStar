module Pulse.Soundness.While

open FStar.Reflection
open Refl.Typing
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Soundness.Common
module RT = Refl.Typing
(*

 g |- inv  : bool -> vprop
 g |- cond : stt<0> bool (exists_ inv) inv
 g |- body : stt<0> unit (inv true) (fun _ -> exists_ inv)
 -------------------------------------------------------------------------
 g |- while inv cond body : stt<0> unit (exists_ inv) (fun _ -> inv false)

*)

val while_soundness
  (#f:stt_env)
  (#g:env)
  (#inv:term)
  (#cond:term)
  (#body:term)
  (inv_typing:RT.typing (extend_env_l f g)
                     inv
                     (mk_arrow (bool_tm, Q_Explicit) vprop_tm))
  (cond_typing:RT.typing (extend_env_l f g)
                      cond
                      (mk_stt_comp uzero bool_tm (mk_exists uzero bool_tm inv) inv))
  (body_typing:RT.typing (extend_env_l f g)
                      body
                      (mk_stt_comp uzero unit_tm
                         (pack_ln (Tv_App inv (true_tm, Q_Explicit)))
                         (mk_abs unit_tm Q_Explicit (mk_exists uzero bool_tm inv))))
  : RT.typing (extend_env_l f g)
           (mk_while inv cond body)
           (mk_stt_comp uzero unit_tm (mk_exists uzero bool_tm inv)
              (mk_abs unit_tm Q_Explicit (pack_ln (Tv_App inv (false_tm, Q_Explicit)))))
