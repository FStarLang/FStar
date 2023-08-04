open Prims
type ln_comp = Pulse_Syntax_Base.comp_st
let (elab_term_opt :
  Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
    FStar_Reflection_Types.term FStar_Pervasives_Native.option)
  =
  fun b ->
    match b with
    | FStar_Pervasives_Native.Some b1 ->
        FStar_Pervasives_Native.Some (Pulse_Elaborate_Pure.elab_term b1)
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (bind_res :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u2 ->
    fun t2 ->
      fun pre ->
        fun post2 -> Pulse_Reflection_Util.mk_stt_comp u2 t2 pre post2
let (g_type_bind :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u2 ->
    fun t1 ->
      fun t2 ->
        fun post1 ->
          fun post2 ->
            Pulse_Reflection_Util.mk_arrow
              (t1, FStar_Reflection_V2_Data.Q_Explicit)
              (bind_res u2 t2
                 (FStar_Reflection_V2_Derived.mk_app post1
                    [((Pulse_Reflection_Util.bound_var Prims.int_zero),
                       FStar_Reflection_V2_Data.Q_Explicit)]) post2)
let (bind_type_t1_t2_pre_post1_post2_f :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.universe ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u1 ->
    fun u2 ->
      fun t1 ->
        fun t2 ->
          fun pre ->
            fun post1 ->
              fun post2 ->
                Pulse_Reflection_Util.mk_arrow
                  ((g_type_bind u2 t1 t2 post1 post2),
                    FStar_Reflection_V2_Data.Q_Explicit)
                  (bind_res u2 t2 pre post2)
let (bind_type_t1_t2_pre_post1_post2 :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.universe ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u1 ->
    fun u2 ->
      fun t1 ->
        fun t2 ->
          fun pre ->
            fun post1 ->
              fun post2 ->
                let f_type =
                  Pulse_Reflection_Util.mk_stt_comp u1 t1 pre post1 in
                Pulse_Reflection_Util.mk_arrow
                  (f_type, FStar_Reflection_V2_Data.Q_Explicit)
                  (bind_type_t1_t2_pre_post1_post2_f u1 u2 t1 t2 pre post1
                     post2)
let (post2_type_bind :
  FStar_Reflection_Types.term -> FStar_Reflection_Types.term) =
  fun t2 ->
    Pulse_Reflection_Util.mk_arrow (t2, FStar_Reflection_V2_Data.Q_Explicit)
      Pulse_Reflection_Util.vprop_tm
let (bind_type_t1_t2_pre_post1 :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.universe ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u1 ->
    fun u2 ->
      fun t1 ->
        fun t2 ->
          fun pre ->
            fun post1 ->
              let var = Prims.int_zero in
              let post2 = Pulse_Reflection_Util.mk_name var in
              Pulse_Reflection_Util.mk_arrow
                ((post2_type_bind t2), FStar_Reflection_V2_Data.Q_Implicit)
                (FStar_Reflection_Typing.subst_term
                   (bind_type_t1_t2_pre_post1_post2 u1 u2 t1 t2 pre post1
                      post2)
                   [FStar_Reflection_Typing.ND (var, Prims.int_zero)])
let (post1_type_bind :
  FStar_Reflection_Types.term -> FStar_Reflection_Types.term) =
  fun t1 ->
    Pulse_Reflection_Util.mk_arrow (t1, FStar_Reflection_V2_Data.Q_Explicit)
      Pulse_Reflection_Util.vprop_tm
let (bind_type_t1_t2_pre :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.universe ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u1 ->
    fun u2 ->
      fun t1 ->
        fun t2 ->
          fun pre ->
            let var = Prims.int_one in
            let post1 = Pulse_Reflection_Util.mk_name var in
            Pulse_Reflection_Util.mk_arrow
              ((post1_type_bind t1), FStar_Reflection_V2_Data.Q_Implicit)
              (FStar_Reflection_Typing.subst_term
                 (bind_type_t1_t2_pre_post1 u1 u2 t1 t2 pre post1)
                 [FStar_Reflection_Typing.ND (var, Prims.int_zero)])
let (bind_type_t1_t2 :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.universe ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u1 ->
    fun u2 ->
      fun t1 ->
        fun t2 ->
          let var = (Prims.of_int (2)) in
          let pre = Pulse_Reflection_Util.mk_name var in
          let pre_type = Pulse_Reflection_Util.vprop_tm in
          Pulse_Reflection_Util.mk_arrow
            (pre_type, FStar_Reflection_V2_Data.Q_Implicit)
            (FStar_Reflection_Typing.subst_term
               (bind_type_t1_t2_pre u1 u2 t1 t2 pre)
               [FStar_Reflection_Typing.ND (var, Prims.int_zero)])
let (bind_type_t1 :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.universe ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u1 ->
    fun u2 ->
      fun t1 ->
        let var = (Prims.of_int (3)) in
        let t2 = Pulse_Reflection_Util.mk_name var in
        let t2_type = FStar_Reflection_Typing.tm_type u2 in
        Pulse_Reflection_Util.mk_arrow
          (t2_type, FStar_Reflection_V2_Data.Q_Implicit)
          (FStar_Reflection_Typing.subst_term (bind_type_t1_t2 u1 u2 t1 t2)
             [FStar_Reflection_Typing.ND (var, Prims.int_zero)])
let (bind_type :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.universe -> FStar_Reflection_Types.term)
  =
  fun u1 ->
    fun u2 ->
      let var = (Prims.of_int (4)) in
      let t1 = Pulse_Reflection_Util.mk_name var in
      let t1_type = FStar_Reflection_Typing.tm_type u1 in
      Pulse_Reflection_Util.mk_arrow
        (t1_type, FStar_Reflection_V2_Data.Q_Implicit)
        (FStar_Reflection_Typing.subst_term (bind_type_t1 u1 u2 t1)
           [FStar_Reflection_Typing.ND (var, Prims.int_zero)])
let (mk_star :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun l ->
    fun r ->
      let head =
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                Pulse_Reflection_Util.star_lid)) in
      FStar_Reflection_V2_Derived.mk_app head
        [(l, FStar_Reflection_V2_Data.Q_Explicit);
        (r, FStar_Reflection_V2_Data.Q_Explicit)]
let (frame_res :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun t ->
      fun pre ->
        fun post ->
          fun frame ->
            Pulse_Reflection_Util.mk_stt_comp u t (mk_star pre frame)
              (Pulse_Reflection_Util.mk_abs t
                 FStar_Reflection_V2_Data.Q_Explicit
                 (mk_star
                    (FStar_Reflection_V2_Derived.mk_app post
                       [((Pulse_Reflection_Util.bound_var Prims.int_zero),
                          FStar_Reflection_V2_Data.Q_Explicit)]) frame))
let (frame_type_t_pre_post_frame :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun t ->
      fun pre ->
        fun post ->
          fun frame ->
            let f_type = Pulse_Reflection_Util.mk_stt_comp u t pre post in
            Pulse_Reflection_Util.mk_arrow
              (f_type, FStar_Reflection_V2_Data.Q_Explicit)
              (frame_res u t pre post frame)
let (frame_type_t_pre_post :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun t ->
      fun pre ->
        fun post ->
          let var = Prims.int_zero in
          let frame = Pulse_Reflection_Util.mk_name var in
          Pulse_Reflection_Util.mk_arrow
            (Pulse_Reflection_Util.vprop_tm,
              FStar_Reflection_V2_Data.Q_Explicit)
            (FStar_Reflection_Typing.close_term
               (frame_res u t pre post frame) var)
let (frame_type_t_pre :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun t ->
      fun pre ->
        let var = Prims.int_one in
        let post = Pulse_Reflection_Util.mk_name var in
        let post_type =
          Pulse_Reflection_Util.mk_arrow
            (t, FStar_Reflection_V2_Data.Q_Explicit)
            Pulse_Reflection_Util.vprop_tm in
        Pulse_Reflection_Util.mk_arrow
          (post_type, FStar_Reflection_V2_Data.Q_Implicit)
          (FStar_Reflection_Typing.close_term
             (frame_type_t_pre_post u t pre post) var)
let (frame_type_t :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun t ->
      let var = (Prims.of_int (2)) in
      let pre = Pulse_Reflection_Util.mk_name var in
      let pre_type = Pulse_Reflection_Util.vprop_tm in
      Pulse_Reflection_Util.mk_arrow
        (pre_type, FStar_Reflection_V2_Data.Q_Implicit)
        (FStar_Reflection_Typing.close_term (frame_type_t_pre u t pre) var)
let (frame_type :
  FStar_Reflection_Types.universe -> FStar_Reflection_Types.term) =
  fun u ->
    let var = (Prims.of_int (3)) in
    let t = Pulse_Reflection_Util.mk_name var in
    let t_type = FStar_Reflection_Typing.tm_type u in
    Pulse_Reflection_Util.mk_arrow
      (t_type, FStar_Reflection_V2_Data.Q_Implicit)
      (FStar_Reflection_Typing.close_term (frame_type_t u t) var)
let (stt_vprop_post_equiv_fv : FStar_Reflection_Types.fv) =
  FStar_Reflection_V2_Builtins.pack_fv
    (Pulse_Reflection_Util.mk_pulse_lib_core_lid "vprop_post_equiv")
let (stt_vprop_post_equiv_univ_inst :
  FStar_Reflection_Types.universe -> FStar_Reflection_Types.term) =
  fun u ->
    FStar_Reflection_V2_Builtins.pack_ln
      (FStar_Reflection_V2_Data.Tv_UInst (stt_vprop_post_equiv_fv, [u]))
let (stt_vprop_post_equiv :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun t ->
      fun t1 ->
        fun t2 ->
          FStar_Reflection_V2_Derived.mk_app
            (stt_vprop_post_equiv_univ_inst u)
            [(t, FStar_Reflection_V2_Data.Q_Implicit);
            (t1, FStar_Reflection_V2_Data.Q_Explicit);
            (t2, FStar_Reflection_V2_Data.Q_Explicit)]
let (sub_stt_res :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun t ->
      fun pre -> fun post -> Pulse_Reflection_Util.mk_stt_comp u t pre post
let sub_stt_equiv_post :
  'uuuuu .
    FStar_Reflection_Types.universe ->
      FStar_Reflection_Types.term ->
        'uuuuu ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term -> FStar_Reflection_Types.term
  =
  fun u ->
    fun t ->
      fun pre1 ->
        fun post1 ->
          fun pre2 ->
            fun post2 ->
              Pulse_Reflection_Util.mk_arrow
                ((stt_vprop_post_equiv u t post1 post2),
                  FStar_Reflection_V2_Data.Q_Explicit)
                (sub_stt_res u t pre2 post2)
let (sub_stt_equiv_pre :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun t ->
      fun pre1 ->
        fun post1 ->
          fun pre2 ->
            fun post2 ->
              Pulse_Reflection_Util.mk_arrow
                ((Pulse_Reflection_Util.stt_vprop_equiv pre1 pre2),
                  FStar_Reflection_V2_Data.Q_Explicit)
                (sub_stt_equiv_post u t pre1 pre2 post1 post2)
let (sub_stt_post2 :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun t ->
      fun pre1 ->
        fun post1 ->
          fun pre2 ->
            let var = Prims.int_zero in
            let post2 = Pulse_Reflection_Util.mk_name var in
            let post2_type =
              Pulse_Reflection_Util.mk_arrow
                (t, FStar_Reflection_V2_Data.Q_Explicit)
                Pulse_Reflection_Util.vprop_tm in
            Pulse_Reflection_Util.mk_arrow
              (post2_type, FStar_Reflection_V2_Data.Q_Explicit)
              (FStar_Reflection_Typing.close_term
                 (sub_stt_equiv_pre u t pre1 pre2 post1 post2) var)
let (sub_stt_pre2 :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun t ->
      fun pre1 ->
        fun post1 ->
          let var = Prims.int_one in
          let pre2 = Pulse_Reflection_Util.mk_name var in
          let pre2_type = Pulse_Reflection_Util.vprop_tm in
          Pulse_Reflection_Util.mk_arrow
            (pre2_type, FStar_Reflection_V2_Data.Q_Explicit)
            (FStar_Reflection_Typing.close_term
               (sub_stt_post2 u t pre1 post1 pre2) var)
let (sub_stt_post1 :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun t ->
      fun pre1 ->
        let var = (Prims.of_int (2)) in
        let post1 = Pulse_Reflection_Util.mk_name var in
        let post1_type =
          Pulse_Reflection_Util.mk_arrow
            (t, FStar_Reflection_V2_Data.Q_Explicit)
            Pulse_Reflection_Util.vprop_tm in
        Pulse_Reflection_Util.mk_arrow
          (post1_type, FStar_Reflection_V2_Data.Q_Explicit)
          (FStar_Reflection_Typing.close_term (sub_stt_pre2 u t pre1 post1)
             var)
let (sub_stt_pre1 :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun t ->
      let var = (Prims.of_int (3)) in
      let pre1 = Pulse_Reflection_Util.mk_name var in
      let pre1_type = Pulse_Reflection_Util.vprop_tm in
      Pulse_Reflection_Util.mk_arrow
        (pre1_type, FStar_Reflection_V2_Data.Q_Explicit)
        (FStar_Reflection_Typing.close_term (sub_stt_post1 u t pre1) var)
let (sub_stt_type :
  FStar_Reflection_Types.universe -> FStar_Reflection_Types.term) =
  fun u ->
    let var = (Prims.of_int (4)) in
    let t = Pulse_Reflection_Util.mk_name var in
    let ty_typ = FStar_Reflection_Typing.tm_type u in
    Pulse_Reflection_Util.mk_arrow
      (ty_typ, FStar_Reflection_V2_Data.Q_Explicit)
      (FStar_Reflection_Typing.close_term (sub_stt_pre1 u t) var)
type 'f has_stt_bindings = unit
type stt_env = Pulse_Typing_Env.env
let (check_top_level_environment :
  FStar_Reflection_Typing.fstar_top_env ->
    stt_env FStar_Pervasives_Native.option)
  = fun f -> FStar_Pervasives_Native.Some (Pulse_Typing_Env.mk_env f)
let (elab_comp_post :
  Pulse_Syntax_Base.comp_st -> FStar_Reflection_Types.term) =
  fun c ->
    let t = Pulse_Elaborate_Pure.elab_term (Pulse_Syntax_Base.comp_res c) in
    let post = Pulse_Elaborate_Pure.elab_term (Pulse_Syntax_Base.comp_post c) in
    Pulse_Reflection_Util.mk_abs t FStar_Reflection_V2_Data.Q_Explicit post
let (comp_post_type :
  Pulse_Syntax_Base.comp_st -> FStar_Reflection_Types.term) =
  fun c ->
    let t = Pulse_Elaborate_Pure.elab_term (Pulse_Syntax_Base.comp_res c) in
    Pulse_Reflection_Util.mk_arrow (t, FStar_Reflection_V2_Data.Q_Explicit)
      Pulse_Reflection_Util.vprop_tm
type ('a, 'd) soundness_t = unit