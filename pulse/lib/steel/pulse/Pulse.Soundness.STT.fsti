module Pulse.Soundness.STT

module R = FStar.Reflection
module RT = FStar.Reflection.Typing

open Pulse.Reflection.Util

let post_type t = mk_arrow (t, R.Q_Explicit) vprop_tm
let inames_tm = R.(pack_ln (Tv_FVar (pack_fv inames_lid)))

val stt_typing (#f:RT.fstar_env)//needs to bind stt
               (#u:R.universe)
               (#t:R.term)
               (#pre:R.term)
               (#post:R.term)
               (_:RT.tot_typing f t (RT.tm_type u))
               (_:RT.tot_typing f pre vprop_tm)
               (_:RT.tot_typing f post (post_type t))
  : GTot (RT.tot_typing f (mk_stt_comp u t pre post) (RT.tm_type u))

val stt_atomic_typing (#f:RT.fstar_env)//needs to bind stt
                      (#u:R.universe)
                      (#inames:R.term)
                      (#t:R.term)
                      (#pre:R.term)
                      (#post:R.term)
                      (_:RT.tot_typing f t (RT.tm_type u))
                      (_:RT.tot_typing f inames inames_tm)
                      (_:RT.tot_typing f pre vprop_tm)
                      (_:RT.tot_typing f post (post_type t))
  : GTot (RT.tot_typing f (mk_stt_atomic_comp u t inames pre post) (RT.tm_type u))

               
val stt_ghost_typing (#f:RT.fstar_env)//needs to bind stt
                     (#u:R.universe)
                     (#inames:R.term)
                     (#t:R.term)
                     (#pre:R.term)
                     (#post:R.term)
                     (_:RT.tot_typing f t (RT.tm_type u))
                     (_:RT.tot_typing f inames inames_tm)
                     (_:RT.tot_typing f pre vprop_tm)
                     (_:RT.tot_typing f post (post_type t))
  : GTot (RT.tot_typing f (mk_stt_ghost_comp u t inames pre post) (RT.tm_type u))
