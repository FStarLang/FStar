open Prims
let (return_post_with_eq :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_V2_Data.var -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun e ->
        fun p ->
          fun x ->
            let x_tm = FStar_Reflection_Typing.var_as_term x in
            let eq2_tm = Pulse_Reflection_Util.mk_eq2 u a x_tm e in
            let p_app_x =
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_App
                   (p, (x_tm, FStar_Reflection_V2_Data.Q_Explicit))) in
            let star_tm =
              Pulse_Reflection_Util.mk_star p_app_x
                (Pulse_Reflection_Util.mk_pure eq2_tm) in
            Pulse_Reflection_Util.mk_abs a
              FStar_Reflection_V2_Data.Q_Explicit
              (FStar_Reflection_Typing.subst_term star_tm
                 [FStar_Reflection_Typing.ND (x, Prims.int_zero)])
let (return_stt_comp :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_V2_Data.var -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun e ->
        fun p ->
          fun x ->
            Pulse_Reflection_Util.mk_stt_comp u a
              (FStar_Reflection_V2_Builtins.pack_ln
                 (FStar_Reflection_V2_Data.Tv_App
                    (p, (e, FStar_Reflection_V2_Data.Q_Explicit))))
              (return_post_with_eq u a e p x)
let (return_stt_noeq_comp :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun x ->
        fun p ->
          Pulse_Reflection_Util.mk_stt_comp u a
            (FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_App
                  (p, (x, FStar_Reflection_V2_Data.Q_Explicit)))) p
let (neutral_fv : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_FVar
       (FStar_Reflection_V2_Builtins.pack_fv
          Pulse_Reflection_Util.neutral_lid))
let (return_stt_atomic_comp :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_V2_Data.var -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun e ->
        fun p ->
          fun x ->
            Pulse_Reflection_Util.mk_stt_atomic_comp neutral_fv u a
              Pulse_Reflection_Util.emp_inames_tm
              (FStar_Reflection_V2_Builtins.pack_ln
                 (FStar_Reflection_V2_Data.Tv_App
                    (p, (e, FStar_Reflection_V2_Data.Q_Explicit))))
              (return_post_with_eq u a e p x)
let (return_stt_atomic_noeq_comp :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun x ->
        fun p ->
          Pulse_Reflection_Util.mk_stt_atomic_comp neutral_fv u a
            Pulse_Reflection_Util.emp_inames_tm
            (FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_App
                  (p, (x, FStar_Reflection_V2_Data.Q_Explicit)))) p
let (return_stt_ghost_comp :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_V2_Data.var -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun e ->
        fun p ->
          fun x ->
            Pulse_Reflection_Util.mk_stt_ghost_comp u a
              (FStar_Reflection_V2_Builtins.pack_ln
                 (FStar_Reflection_V2_Data.Tv_App
                    (p, (e, FStar_Reflection_V2_Data.Q_Explicit))))
              (return_post_with_eq u a e p x)
let (return_stt_ghost_noeq_comp :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun x ->
        fun p ->
          Pulse_Reflection_Util.mk_stt_ghost_comp u a
            (FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_App
                  (p, (x, FStar_Reflection_V2_Data.Q_Explicit)))) p
let (while_typing :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          (unit, unit, unit) FStar_Reflection_Typing.tot_typing ->
            (unit, unit, unit) FStar_Reflection_Typing.tot_typing ->
              (unit, unit, unit) FStar_Reflection_Typing.tot_typing ->
                (unit, unit, unit) FStar_Reflection_Typing.tot_typing)
  =
  fun g ->
    fun inv ->
      fun cond ->
        fun body -> fun uu___ -> fun uu___1 -> fun uu___2 -> Prims.admit ()
let (par_post :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_V2_Data.var -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun aL ->
      fun aR ->
        fun postL ->
          fun postR ->
            fun x ->
              let x_tm = FStar_Reflection_Typing.var_as_term x in
              let postL1 =
                FStar_Reflection_V2_Builtins.pack_ln
                  (FStar_Reflection_V2_Data.Tv_App
                     (postL,
                       ((Pulse_Reflection_Util.mk_fst u u aL aR x_tm),
                         FStar_Reflection_V2_Data.Q_Explicit))) in
              let postR1 =
                FStar_Reflection_V2_Builtins.pack_ln
                  (FStar_Reflection_V2_Data.Tv_App
                     (postR,
                       ((Pulse_Reflection_Util.mk_snd u u aL aR x_tm),
                         FStar_Reflection_V2_Data.Q_Explicit))) in
              let post = Pulse_Reflection_Util.mk_star postL1 postR1 in
              FStar_Reflection_Typing.subst_term post
                [FStar_Reflection_Typing.ND (x, Prims.int_zero)]
let (elim_exists_post_body :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_V2_Data.var -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun p ->
        fun x ->
          let x_tm = FStar_Reflection_Typing.var_as_term x in
          let reveal_x = Pulse_Reflection_Util.mk_reveal u a x_tm in
          let post =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (p, (reveal_x, FStar_Reflection_V2_Data.Q_Explicit))) in
          FStar_Reflection_Typing.subst_term post
            [FStar_Reflection_Typing.ND (x, Prims.int_zero)]
let (elim_exists_post :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_V2_Data.var -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun p ->
        fun x ->
          let erased_a = Pulse_Reflection_Util.mk_erased u a in
          Pulse_Reflection_Util.mk_abs erased_a
            FStar_Reflection_V2_Data.Q_Explicit
            (elim_exists_post_body u a p x)
let intro_exists_erased_typing :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 . 'uuuuu -> 'uuuuu1 -> 'uuuuu2 -> 'uuuuu3 =
  fun uu___ -> fun uu___1 -> fun uu___2 -> Prims.admit ()
let (with_local_body_pre :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun pre ->
    fun a ->
      fun x ->
        fun init ->
          let pts_to =
            Pulse_Reflection_Util.mk_pts_to a x
              Pulse_Reflection_Util.full_perm_tm init in
          Pulse_Reflection_Util.mk_star pre pts_to
let (with_local_body_post_body :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun post ->
    fun a ->
      fun x ->
        let exists_tm =
          Pulse_Reflection_Util.mk_exists
            (FStar_Reflection_V2_Builtins.pack_universe
               FStar_Reflection_V2_Data.Uv_Zero) a
            (Pulse_Reflection_Util.mk_abs a
               FStar_Reflection_V2_Data.Q_Explicit
               (Pulse_Reflection_Util.mk_pts_to a x
                  Pulse_Reflection_Util.full_perm_tm
                  (FStar_Reflection_Typing.bound_var Prims.int_zero))) in
        Pulse_Reflection_Util.mk_star post exists_tm
let (with_local_body_post :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun post ->
    fun a ->
      fun ret_t ->
        fun x ->
          Pulse_Reflection_Util.mk_abs ret_t
            FStar_Reflection_V2_Data.Q_Explicit
            (with_local_body_post_body post a x)
let (with_localarray_body_pre :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun pre ->
    fun a ->
      fun arr ->
        fun init ->
          fun len ->
            let pts_to =
              Pulse_Reflection_Util.mk_array_pts_to a arr
                Pulse_Reflection_Util.full_perm_tm
                (Pulse_Reflection_Util.mk_seq_create
                   Pulse_Reflection_Util.uzero a
                   (Pulse_Reflection_Util.mk_szv len) init) in
            let len_vp =
              Pulse_Reflection_Util.mk_pure
                (Pulse_Reflection_Util.mk_eq2 Pulse_Reflection_Util.uzero
                   Pulse_Reflection_Util.nat_tm
                   (Pulse_Reflection_Util.mk_array_length a arr)
                   (Pulse_Reflection_Util.mk_szv len)) in
            Pulse_Reflection_Util.mk_star pre
              (Pulse_Reflection_Util.mk_star pts_to len_vp)
let (with_localarray_body_post_body :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun post ->
    fun a ->
      fun arr ->
        let exists_tm =
          Pulse_Reflection_Util.mk_exists Pulse_Reflection_Util.uzero
            (Pulse_Reflection_Util.mk_seq Pulse_Reflection_Util.uzero a)
            (Pulse_Reflection_Util.mk_abs
               (Pulse_Reflection_Util.mk_seq Pulse_Reflection_Util.uzero a)
               FStar_Reflection_V2_Data.Q_Explicit
               (Pulse_Reflection_Util.mk_array_pts_to a arr
                  Pulse_Reflection_Util.full_perm_tm
                  (FStar_Reflection_Typing.bound_var Prims.int_zero))) in
        Pulse_Reflection_Util.mk_star post exists_tm
let (with_localarray_body_post :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun post ->
    fun a ->
      fun ret_t ->
        fun arr ->
          Pulse_Reflection_Util.mk_abs ret_t
            FStar_Reflection_V2_Data.Q_Explicit
            (with_localarray_body_post_body post a arr)