open Prims
let (pulse_lib_core : Prims.string Prims.list) = ["Pulse"; "Lib"; "Core"]
let (mk_pulse_lib_core_lid : Prims.string -> Prims.string Prims.list) =
  fun s -> FStar_List_Tot_Base.op_At pulse_lib_core [s]
let (tun : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln FStar_Reflection_V2_Data.Tv_Unknown
let (unit_lid : Prims.string Prims.list) = FStar_Reflection_Const.unit_lid
let (bool_lid : Prims.string Prims.list) = FStar_Reflection_Const.bool_lid
let (int_lid : Prims.string Prims.list) = FStar_Reflection_Const.int_lid
let (erased_lid : Prims.string Prims.list) = ["FStar"; "Ghost"; "erased"]
let (hide_lid : Prims.string Prims.list) = ["FStar"; "Ghost"; "hide"]
let (reveal_lid : Prims.string Prims.list) = ["FStar"; "Ghost"; "reveal"]
let (vprop_lid : Prims.string Prims.list) = mk_pulse_lib_core_lid "vprop"
let (vprop_fv : FStar_Reflection_Types.fv) =
  FStar_Reflection_V2_Builtins.pack_fv vprop_lid
let (vprop_tm : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_FVar vprop_fv)
let (unit_fv : FStar_Reflection_Types.fv) =
  FStar_Reflection_V2_Builtins.pack_fv unit_lid
let (unit_tm : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_FVar unit_fv)
let (bool_fv : FStar_Reflection_Types.fv) =
  FStar_Reflection_V2_Builtins.pack_fv bool_lid
let (bool_tm : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_FVar bool_fv)
let (tuple2_lid : Prims.string Prims.list) =
  ["FStar"; "Pervasives"; "Native"; "tuple2"]
let (fst_lid : Prims.string Prims.list) =
  ["FStar"; "Pervasives"; "Native"; "fst"]
let (snd_lid : Prims.string Prims.list) =
  ["FStar"; "Pervasives"; "Native"; "snd"]
let (mk_tuple2 :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.universe ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u1 ->
    fun u2 ->
      fun a1 ->
        fun a2 ->
          let t =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_UInst
                 ((FStar_Reflection_V2_Builtins.pack_fv tuple2_lid),
                   [u1; u2])) in
          let t1 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t, (a1, FStar_Reflection_V2_Data.Q_Explicit))) in
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t1, (a2, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_fst :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.universe ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u1 ->
    fun u2 ->
      fun a1 ->
        fun a2 ->
          fun e ->
            let t =
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_UInst
                   ((FStar_Reflection_V2_Builtins.pack_fv fst_lid), [u1; u2])) in
            let t1 =
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_App
                   (t, (a1, FStar_Reflection_V2_Data.Q_Implicit))) in
            let t2 =
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_App
                   (t1, (a2, FStar_Reflection_V2_Data.Q_Implicit))) in
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t2, (e, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_snd :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.universe ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u1 ->
    fun u2 ->
      fun a1 ->
        fun a2 ->
          fun e ->
            let t =
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_UInst
                   ((FStar_Reflection_V2_Builtins.pack_fv snd_lid), [u1; u2])) in
            let t1 =
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_App
                   (t, (a1, FStar_Reflection_V2_Data.Q_Implicit))) in
            let t2 =
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_App
                   (t1, (a2, FStar_Reflection_V2_Data.Q_Implicit))) in
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t2, (e, FStar_Reflection_V2_Data.Q_Explicit)))
let (true_tm : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_Const FStar_Reflection_V2_Data.C_True)
let (false_tm : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_Const FStar_Reflection_V2_Data.C_False)
let (emp_lid : Prims.string Prims.list) = mk_pulse_lib_core_lid "emp"
let (inames_lid : Prims.string Prims.list) = mk_pulse_lib_core_lid "inames"
let (star_lid : Prims.string Prims.list) =
  mk_pulse_lib_core_lid "op_Star_Star"
let (mk_star :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun l ->
    fun r ->
      let t =
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv star_lid)) in
      let t1 =
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_App
             (t, (l, FStar_Reflection_V2_Data.Q_Explicit))) in
      FStar_Reflection_V2_Builtins.pack_ln
        (FStar_Reflection_V2_Data.Tv_App
           (t1, (r, FStar_Reflection_V2_Data.Q_Explicit)))
let (pure_lid : Prims.string Prims.list) = mk_pulse_lib_core_lid "pure"
let (exists_lid : Prims.string Prims.list) = mk_pulse_lib_core_lid "exists_"
let (forall_lid : Prims.string Prims.list) = mk_pulse_lib_core_lid "forall_"
let (args_of :
  FStar_Reflection_Types.term Prims.list ->
    (FStar_Reflection_Types.term * FStar_Reflection_V2_Data.aqualv)
      Prims.list)
  =
  fun tms ->
    FStar_List_Tot_Base.map
      (fun x -> (x, FStar_Reflection_V2_Data.Q_Explicit)) tms
let (mk_pure : FStar_Reflection_Types.term -> FStar_Reflection_Types.term) =
  fun p ->
    let t =
      FStar_Reflection_V2_Builtins.pack_ln
        (FStar_Reflection_V2_Data.Tv_FVar
           (FStar_Reflection_V2_Builtins.pack_fv pure_lid)) in
    FStar_Reflection_V2_Builtins.pack_ln
      (FStar_Reflection_V2_Data.Tv_App
         (t, (p, FStar_Reflection_V2_Data.Q_Explicit)))
let (uzero : FStar_Reflection_Types.universe) =
  FStar_Reflection_V2_Builtins.pack_universe FStar_Reflection_V2_Data.Uv_Zero
let (pulse_lib_reference : Prims.string Prims.list) =
  ["Pulse"; "Lib"; "Reference"]
let (mk_pulse_lib_reference_lid : Prims.string -> Prims.string Prims.list) =
  fun s -> FStar_List_Tot_Base.op_At pulse_lib_reference [s]
let (mk_squash :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun ty ->
      let t =
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_UInst
             ((FStar_Reflection_V2_Builtins.pack_fv
                 FStar_Reflection_Const.squash_qn), [u])) in
      FStar_Reflection_V2_Builtins.pack_ln
        (FStar_Reflection_V2_Data.Tv_App
           (t, (ty, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_eq2 :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun ty ->
      fun e1 ->
        fun e2 ->
          let t =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_UInst
                 ((FStar_Reflection_V2_Builtins.pack_fv
                     (mk_pulse_lib_core_lid "eq2_prop")), [u])) in
          let t1 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t, (ty, FStar_Reflection_V2_Data.Q_Implicit))) in
          let t2 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t1, (e1, FStar_Reflection_V2_Data.Q_Explicit))) in
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t2, (e2, FStar_Reflection_V2_Data.Q_Explicit)))
let (stt_admit_lid : Prims.string Prims.list) =
  mk_pulse_lib_core_lid "stt_admit"
let (mk_stt_admit :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun t ->
      fun pre ->
        fun post ->
          let t1 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_UInst
                 ((FStar_Reflection_V2_Builtins.pack_fv stt_admit_lid), [u])) in
          let t2 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t1, (t1, FStar_Reflection_V2_Data.Q_Explicit))) in
          let t3 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t2, (pre, FStar_Reflection_V2_Data.Q_Explicit))) in
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t3, (post, FStar_Reflection_V2_Data.Q_Explicit)))
let (stt_atomic_admit_lid : Prims.string Prims.list) =
  mk_pulse_lib_core_lid "stt_atomic_admit"
let (mk_stt_atomic_admit :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun t ->
      fun pre ->
        fun post ->
          let t1 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_UInst
                 ((FStar_Reflection_V2_Builtins.pack_fv stt_atomic_admit_lid),
                   [u])) in
          let t2 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t1, (t1, FStar_Reflection_V2_Data.Q_Explicit))) in
          let t3 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t2, (pre, FStar_Reflection_V2_Data.Q_Explicit))) in
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t3, (post, FStar_Reflection_V2_Data.Q_Explicit)))
let (stt_ghost_admit_lid : Prims.string Prims.list) =
  mk_pulse_lib_core_lid "stt_ghost_admit"
let (mk_stt_ghost_admit :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun t ->
      fun pre ->
        fun post ->
          let t1 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_UInst
                 ((FStar_Reflection_V2_Builtins.pack_fv stt_ghost_admit_lid),
                   [u])) in
          let t2 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t1, (t1, FStar_Reflection_V2_Data.Q_Explicit))) in
          let t3 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t2, (pre, FStar_Reflection_V2_Data.Q_Explicit))) in
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t3, (post, FStar_Reflection_V2_Data.Q_Explicit)))
let (emp_inames_lid : Prims.string Prims.list) =
  mk_pulse_lib_core_lid "emp_inames"
let (elim_pure_lid : Prims.string Prims.list) =
  mk_pulse_lib_core_lid "elim_pure"
let (stt_lid : Prims.string Prims.list) = mk_pulse_lib_core_lid "stt"
let (stt_fv : FStar_Reflection_Types.fv) =
  FStar_Reflection_V2_Builtins.pack_fv stt_lid
let (stt_tm : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_FVar stt_fv)
let (mk_stt_comp :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun res ->
      fun pre ->
        fun post ->
          let t =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_UInst (stt_fv, [u])) in
          let t1 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t, (res, FStar_Reflection_V2_Data.Q_Explicit))) in
          let t2 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t1, (pre, FStar_Reflection_V2_Data.Q_Explicit))) in
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t2, (post, FStar_Reflection_V2_Data.Q_Explicit)))
let (stt_atomic_lid : Prims.string Prims.list) =
  mk_pulse_lib_core_lid "stt_atomic"
let (stt_atomic_fv : FStar_Reflection_Types.fv) =
  FStar_Reflection_V2_Builtins.pack_fv stt_atomic_lid
let (stt_atomic_tm : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_FVar stt_atomic_fv)
let (mk_stt_atomic_comp :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun inames ->
        fun pre ->
          fun post ->
            let t =
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_UInst (stt_atomic_fv, [u])) in
            let t1 =
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_App
                   (t, (a, FStar_Reflection_V2_Data.Q_Explicit))) in
            let t2 =
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_App
                   (t1, (inames, FStar_Reflection_V2_Data.Q_Explicit))) in
            let t3 =
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_App
                   (t2, (pre, FStar_Reflection_V2_Data.Q_Explicit))) in
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t3, (post, FStar_Reflection_V2_Data.Q_Explicit)))
let (stt_ghost_lid : Prims.string Prims.list) =
  mk_pulse_lib_core_lid "stt_ghost"
let (stt_ghost_fv : FStar_Reflection_Types.fv) =
  FStar_Reflection_V2_Builtins.pack_fv stt_ghost_lid
let (stt_ghost_tm : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_FVar stt_ghost_fv)
let (mk_stt_ghost_comp :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun inames ->
        fun pre ->
          fun post ->
            let t =
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_UInst (stt_ghost_fv, [u])) in
            let t1 =
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_App
                   (t, (a, FStar_Reflection_V2_Data.Q_Explicit))) in
            let t2 =
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_App
                   (t1, (inames, FStar_Reflection_V2_Data.Q_Explicit))) in
            let t3 =
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_App
                   (t2, (pre, FStar_Reflection_V2_Data.Q_Explicit))) in
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t3, (post, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_stt_ghost_comp_post_equiv :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.universe ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                (unit, unit, unit) FStar_Reflection_Typing.equiv ->
                  (unit, unit, unit) FStar_Reflection_Typing.equiv)
  =
  fun g ->
    fun u ->
      fun a ->
        fun inames ->
          fun pre ->
            fun post1 ->
              fun post2 ->
                fun posts_equiv ->
                  let t =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_UInst (stt_ghost_fv, [u])) in
                  let t1 =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t, (a, FStar_Reflection_V2_Data.Q_Explicit))) in
                  let t2 =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t1, (inames, FStar_Reflection_V2_Data.Q_Explicit))) in
                  let t3 =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t2, (pre, FStar_Reflection_V2_Data.Q_Explicit))) in
                  FStar_Reflection_Typing.EQ_Ctxt
                    (g, post1, post2,
                      (FStar_Reflection_Typing.Ctxt_app_arg
                         (t3, FStar_Reflection_V2_Data.Q_Explicit,
                           FStar_Reflection_Typing.Ctxt_hole)), posts_equiv)
let (mk_total :
  FStar_Reflection_Types.typ -> FStar_Reflection_V2_Data.comp_view) =
  fun t -> FStar_Reflection_V2_Data.C_Total t
let (mk_ghost :
  FStar_Reflection_Types.typ -> FStar_Reflection_V2_Data.comp_view) =
  fun t -> FStar_Reflection_V2_Data.C_GTotal t
let (binder_of_t_q :
  FStar_Reflection_Types.term ->
    FStar_Reflection_V2_Data.aqualv -> FStar_Reflection_Types.binder)
  = fun t -> fun q -> FStar_Reflection_Typing.binder_of_t_q t q
let (binder_of_t_q_s :
  FStar_Reflection_Types.term ->
    FStar_Reflection_V2_Data.aqualv ->
      FStar_Reflection_Typing.pp_name_t -> FStar_Reflection_Types.binder)
  = fun t -> fun q -> fun s -> FStar_Reflection_Typing.mk_binder s t q
let (bound_var : Prims.nat -> FStar_Reflection_Types.term) =
  fun i -> FStar_Reflection_Typing.bound_var i
let (mk_name : Prims.nat -> FStar_Reflection_Types.term) =
  fun i ->
    FStar_Reflection_V2_Builtins.pack_ln
      (FStar_Reflection_V2_Data.Tv_Var
         (FStar_Reflection_V2_Builtins.pack_namedv
            (FStar_Reflection_Typing.make_namedv i)))
type arrow_dom =
  (FStar_Reflection_Types.term * FStar_Reflection_V2_Data.aqualv)
let (mk_arrow :
  arrow_dom -> FStar_Reflection_Types.term -> FStar_Reflection_Types.term) =
  fun f ->
    fun out ->
      let uu___ = f in
      match uu___ with
      | (ty, q) ->
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_Arrow
               ((binder_of_t_q ty q),
                 (FStar_Reflection_V2_Builtins.pack_comp (mk_total out))))
let (mk_arrow_with_name :
  FStar_Reflection_Typing.pp_name_t ->
    arrow_dom -> FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun s ->
    fun f ->
      fun out ->
        let uu___ = f in
        match uu___ with
        | (ty, q) ->
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_Arrow
                 ((binder_of_t_q_s ty q s),
                   (FStar_Reflection_V2_Builtins.pack_comp (mk_total out))))
let (mk_ghost_arrow_with_name :
  FStar_Reflection_Typing.pp_name_t ->
    arrow_dom -> FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun s ->
    fun f ->
      fun out ->
        let uu___ = f in
        match uu___ with
        | (ty, q) ->
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_Arrow
                 ((binder_of_t_q_s ty q s),
                   (FStar_Reflection_V2_Builtins.pack_comp (mk_ghost out))))
let (mk_abs :
  FStar_Reflection_Types.term ->
    FStar_Reflection_V2_Data.aqualv ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  = fun ty -> fun qual -> fun t -> FStar_Reflection_Typing.mk_abs ty qual t
let (mk_abs_with_name :
  FStar_Reflection_Typing.pp_name_t ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_V2_Data.aqualv ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun s ->
    fun ty ->
      fun qual ->
        fun t ->
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_Abs ((binder_of_t_q_s ty qual s), t))
let (mk_abs_with_name_and_range :
  FStar_Reflection_Typing.pp_name_t ->
    FStar_Range.range ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_V2_Data.aqualv ->
          FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun s ->
    fun r ->
      fun ty ->
        fun qual ->
          fun t ->
            let b = binder_of_t_q_s ty qual s in
            let b1 = Pulse_RuntimeUtils.binder_set_range b r in
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_Abs (b1, t))
let (mk_erased :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun t ->
      let hd =
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_UInst
             ((FStar_Reflection_V2_Builtins.pack_fv erased_lid), [u])) in
      FStar_Reflection_V2_Builtins.pack_ln
        (FStar_Reflection_V2_Data.Tv_App
           (hd, (t, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_reveal :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun t ->
      fun e ->
        let hd =
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_UInst
               ((FStar_Reflection_V2_Builtins.pack_fv reveal_lid), [u])) in
        let hd1 =
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (hd, (t, FStar_Reflection_V2_Data.Q_Implicit))) in
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_App
             (hd1, (e, FStar_Reflection_V2_Data.Q_Explicit)))
let (elim_exists_lid : Prims.string Prims.list) =
  mk_pulse_lib_core_lid "elim_exists"
let (intro_exists_lid : Prims.string Prims.list) =
  mk_pulse_lib_core_lid "intro_exists"
let (intro_exists_erased_lid : Prims.string Prims.list) =
  mk_pulse_lib_core_lid "intro_exists_erased"
let (mk_exists :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun p ->
        let t =
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_UInst
               ((FStar_Reflection_V2_Builtins.pack_fv exists_lid), [u])) in
        let t1 =
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t, (a, FStar_Reflection_V2_Data.Q_Implicit))) in
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_App
             (t1, (p, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_forall :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun p ->
        let t =
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_UInst
               ((FStar_Reflection_V2_Builtins.pack_fv forall_lid), [u])) in
        let t1 =
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t, (a, FStar_Reflection_V2_Data.Q_Implicit))) in
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_App
             (t1, (p, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_elim_exists :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun p ->
        let t =
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_UInst
               ((FStar_Reflection_V2_Builtins.pack_fv elim_exists_lid), [u])) in
        let t1 =
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t, (a, FStar_Reflection_V2_Data.Q_Implicit))) in
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_App
             (t1, (p, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_intro_exists :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun p ->
        fun e ->
          let t =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_UInst
                 ((FStar_Reflection_V2_Builtins.pack_fv intro_exists_lid),
                   [u])) in
          let t1 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t, (a, FStar_Reflection_V2_Data.Q_Implicit))) in
          let t2 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t1, (p, FStar_Reflection_V2_Data.Q_Explicit))) in
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t2, (e, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_intro_exists_erased :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun p ->
        fun e ->
          let t =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_UInst
                 ((FStar_Reflection_V2_Builtins.pack_fv
                     intro_exists_erased_lid), [u])) in
          let t1 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t, (a, FStar_Reflection_V2_Data.Q_Implicit))) in
          let t2 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t1, (p, FStar_Reflection_V2_Data.Q_Explicit))) in
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t2, (e, FStar_Reflection_V2_Data.Q_Explicit)))
let (while_lid : Prims.string Prims.list) =
  mk_pulse_lib_core_lid "while_loop"
let (mk_while :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun inv ->
    fun cond ->
      fun body ->
        let t =
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_FVar
               (FStar_Reflection_V2_Builtins.pack_fv while_lid)) in
        let t1 =
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t, (inv, FStar_Reflection_V2_Data.Q_Explicit))) in
        let t2 =
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t1, (cond, FStar_Reflection_V2_Data.Q_Explicit))) in
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_App
             (t2, (body, FStar_Reflection_V2_Data.Q_Explicit)))
let (vprop_eq_tm :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun t1 ->
    fun t2 ->
      let u2 =
        FStar_Reflection_V2_Builtins.pack_universe
          (FStar_Reflection_V2_Data.Uv_Succ
             (FStar_Reflection_V2_Builtins.pack_universe
                (FStar_Reflection_V2_Data.Uv_Succ
                   (FStar_Reflection_V2_Builtins.pack_universe
                      FStar_Reflection_V2_Data.Uv_Zero)))) in
      let t =
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_UInst
             ((FStar_Reflection_V2_Builtins.pack_fv
                 FStar_Reflection_Const.eq2_qn), [u2])) in
      let t3 =
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_App
             (t,
               ((FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv vprop_lid))),
                 FStar_Reflection_V2_Data.Q_Implicit))) in
      let t4 =
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_App
             (t3, (t1, FStar_Reflection_V2_Data.Q_Explicit))) in
      let t5 =
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_App
             (t4, (t2, FStar_Reflection_V2_Data.Q_Explicit))) in
      t5
let (emp_inames_tm : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_FVar
       (FStar_Reflection_V2_Builtins.pack_fv emp_inames_lid))
let (non_informative_witness_lid : Prims.string Prims.list) =
  mk_pulse_lib_core_lid "non_informative_witness"
let (non_informative_witness_rt :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      let t =
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_UInst
             ((FStar_Reflection_V2_Builtins.pack_fv
                 non_informative_witness_lid), [u])) in
      let t1 =
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_App
             (t, (a, FStar_Reflection_V2_Data.Q_Explicit))) in
      t1
let (stt_vprop_equiv_fv : FStar_Reflection_Types.fv) =
  FStar_Reflection_V2_Builtins.pack_fv (mk_pulse_lib_core_lid "vprop_equiv")
let (stt_vprop_equiv_tm : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_FVar stt_vprop_equiv_fv)
let (stt_vprop_equiv :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun t1 ->
    fun t2 ->
      let t =
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_App
             (stt_vprop_equiv_tm, (t1, FStar_Reflection_V2_Data.Q_Explicit))) in
      FStar_Reflection_V2_Builtins.pack_ln
        (FStar_Reflection_V2_Data.Tv_App
           (t, (t2, FStar_Reflection_V2_Data.Q_Explicit)))
let (return_stt_lid : Prims.string Prims.list) =
  mk_pulse_lib_core_lid "return_stt"
let (return_stt_noeq_lid : Prims.string Prims.list) =
  mk_pulse_lib_core_lid "return"
let (return_stt_atomic_lid : Prims.string Prims.list) =
  mk_pulse_lib_core_lid "return_stt_atomic"
let (return_stt_atomic_noeq_lid : Prims.string Prims.list) =
  mk_pulse_lib_core_lid "return_stt_atomic_noeq"
let (return_stt_ghost_lid : Prims.string Prims.list) =
  mk_pulse_lib_core_lid "return_stt_ghost"
let (return_stt_ghost_noeq_lid : Prims.string Prims.list) =
  mk_pulse_lib_core_lid "return_stt_ghost_noeq"
let (mk_stt_return :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun ty ->
      fun t ->
        fun post ->
          let t1 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_UInst
                 ((FStar_Reflection_V2_Builtins.pack_fv return_stt_lid), [u])) in
          let t2 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t1, (ty, FStar_Reflection_V2_Data.Q_Implicit))) in
          let t3 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t2, (t2, FStar_Reflection_V2_Data.Q_Explicit))) in
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t3, (post, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_stt_return_noeq :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun ty ->
      fun t ->
        fun post ->
          let t1 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_UInst
                 ((FStar_Reflection_V2_Builtins.pack_fv return_stt_noeq_lid),
                   [u])) in
          let t2 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t1, (ty, FStar_Reflection_V2_Data.Q_Implicit))) in
          let t3 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t2, (t2, FStar_Reflection_V2_Data.Q_Explicit))) in
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t3, (post, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_stt_atomic_return :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun ty ->
      fun t ->
        fun post ->
          let t1 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_UInst
                 ((FStar_Reflection_V2_Builtins.pack_fv return_stt_atomic_lid),
                   [u])) in
          let t2 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t1, (ty, FStar_Reflection_V2_Data.Q_Implicit))) in
          let t3 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t2, (t2, FStar_Reflection_V2_Data.Q_Explicit))) in
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t3, (post, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_stt_atomic_return_noeq :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun ty ->
      fun t ->
        fun post ->
          let t1 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_UInst
                 ((FStar_Reflection_V2_Builtins.pack_fv
                     return_stt_atomic_noeq_lid), [u])) in
          let t2 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t1, (ty, FStar_Reflection_V2_Data.Q_Implicit))) in
          let t3 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t2, (t2, FStar_Reflection_V2_Data.Q_Explicit))) in
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t3, (post, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_stt_ghost_return :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun ty ->
      fun t ->
        fun post ->
          let t1 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_UInst
                 ((FStar_Reflection_V2_Builtins.pack_fv return_stt_ghost_lid),
                   [u])) in
          let t2 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t1, (ty, FStar_Reflection_V2_Data.Q_Implicit))) in
          let t3 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t2, (t2, FStar_Reflection_V2_Data.Q_Explicit))) in
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t3, (post, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_stt_ghost_return_noeq :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun ty ->
      fun t ->
        fun post ->
          let t1 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_UInst
                 ((FStar_Reflection_V2_Builtins.pack_fv
                     return_stt_ghost_noeq_lid), [u])) in
          let t2 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t1, (ty, FStar_Reflection_V2_Data.Q_Implicit))) in
          let t3 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t2, (t2, FStar_Reflection_V2_Data.Q_Explicit))) in
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t3, (post, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_lift_atomic_stt :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun pre ->
        fun post ->
          fun e ->
            let lid = mk_pulse_lib_core_lid "lift_stt_atomic" in
            let t =
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_UInst
                   ((FStar_Reflection_V2_Builtins.pack_fv lid), [u])) in
            let t1 =
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_App
                   (t, (a, FStar_Reflection_V2_Data.Q_Implicit))) in
            let t2 =
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_App
                   (t1, (pre, FStar_Reflection_V2_Data.Q_Implicit))) in
            let t3 =
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_App
                   (t2, (post, FStar_Reflection_V2_Data.Q_Implicit))) in
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t3, (e, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_lift_ghost_atomic :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun opened ->
        fun pre ->
          fun post ->
            fun e ->
              fun reveal_a ->
                let lid = mk_pulse_lib_core_lid "lift_stt_ghost" in
                let t =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_UInst
                       ((FStar_Reflection_V2_Builtins.pack_fv lid), [u])) in
                let t1 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t, (a, FStar_Reflection_V2_Data.Q_Implicit))) in
                let t2 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t1, (opened, FStar_Reflection_V2_Data.Q_Implicit))) in
                let t3 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t2, (pre, FStar_Reflection_V2_Data.Q_Implicit))) in
                let t4 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t3, (post, FStar_Reflection_V2_Data.Q_Implicit))) in
                let t5 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t4, (e, FStar_Reflection_V2_Data.Q_Explicit))) in
                FStar_Reflection_V2_Builtins.pack_ln
                  (FStar_Reflection_V2_Data.Tv_App
                     (t5, (reveal_a, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_bind_stt :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.universe ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                FStar_Reflection_Types.term ->
                  FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u1 ->
    fun u2 ->
      fun ty1 ->
        fun ty2 ->
          fun pre1 ->
            fun post1 ->
              fun post2 ->
                fun t1 ->
                  fun t2 ->
                    let bind_lid = mk_pulse_lib_core_lid "bind_stt" in
                    let head =
                      FStar_Reflection_V2_Builtins.pack_ln
                        (FStar_Reflection_V2_Data.Tv_UInst
                           ((FStar_Reflection_V2_Builtins.pack_fv bind_lid),
                             [u1; u2])) in
                    FStar_Reflection_V2_Derived.mk_app
                      (FStar_Reflection_V2_Derived.mk_app
                         (FStar_Reflection_V2_Derived.mk_app
                            (FStar_Reflection_V2_Derived.mk_app
                               (FStar_Reflection_V2_Derived.mk_app
                                  (FStar_Reflection_V2_Derived.mk_app
                                     (FStar_Reflection_V2_Derived.mk_app head
                                        [(ty1,
                                           FStar_Reflection_V2_Data.Q_Implicit)])
                                     [(ty2,
                                        FStar_Reflection_V2_Data.Q_Implicit)])
                                  [(pre1,
                                     FStar_Reflection_V2_Data.Q_Implicit)])
                               [(post1, FStar_Reflection_V2_Data.Q_Implicit)])
                            [(post2, FStar_Reflection_V2_Data.Q_Implicit)])
                         [(t1, FStar_Reflection_V2_Data.Q_Explicit)])
                      [(t2, FStar_Reflection_V2_Data.Q_Explicit)]
let (mk_bind_ghost :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.universe ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                FStar_Reflection_Types.term ->
                  FStar_Reflection_Types.term ->
                    FStar_Reflection_Types.term ->
                      FStar_Reflection_Types.term)
  =
  fun u1 ->
    fun u2 ->
      fun a ->
        fun b ->
          fun opened ->
            fun pre1 ->
              fun post1 ->
                fun post2 ->
                  fun e1 ->
                    fun e2 ->
                      let bind_lid = mk_pulse_lib_core_lid "bind_sttg" in
                      let t =
                        FStar_Reflection_V2_Builtins.pack_ln
                          (FStar_Reflection_V2_Data.Tv_UInst
                             ((FStar_Reflection_V2_Builtins.pack_fv bind_lid),
                               [u1; u2])) in
                      let t1 =
                        FStar_Reflection_V2_Builtins.pack_ln
                          (FStar_Reflection_V2_Data.Tv_App
                             (t, (a, FStar_Reflection_V2_Data.Q_Implicit))) in
                      let t2 =
                        FStar_Reflection_V2_Builtins.pack_ln
                          (FStar_Reflection_V2_Data.Tv_App
                             (t1, (b, FStar_Reflection_V2_Data.Q_Implicit))) in
                      let t3 =
                        FStar_Reflection_V2_Builtins.pack_ln
                          (FStar_Reflection_V2_Data.Tv_App
                             (t2,
                               (opened, FStar_Reflection_V2_Data.Q_Implicit))) in
                      let t4 =
                        FStar_Reflection_V2_Builtins.pack_ln
                          (FStar_Reflection_V2_Data.Tv_App
                             (t3,
                               (pre1, FStar_Reflection_V2_Data.Q_Implicit))) in
                      let t5 =
                        FStar_Reflection_V2_Builtins.pack_ln
                          (FStar_Reflection_V2_Data.Tv_App
                             (t4,
                               (post1, FStar_Reflection_V2_Data.Q_Implicit))) in
                      let t6 =
                        FStar_Reflection_V2_Builtins.pack_ln
                          (FStar_Reflection_V2_Data.Tv_App
                             (t5,
                               (post2, FStar_Reflection_V2_Data.Q_Implicit))) in
                      let t7 =
                        FStar_Reflection_V2_Builtins.pack_ln
                          (FStar_Reflection_V2_Data.Tv_App
                             (t6, (e1, FStar_Reflection_V2_Data.Q_Explicit))) in
                      FStar_Reflection_V2_Builtins.pack_ln
                        (FStar_Reflection_V2_Data.Tv_App
                           (t7, (e2, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_bind_ghost_atomic :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.universe ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                FStar_Reflection_Types.term ->
                  FStar_Reflection_Types.term ->
                    FStar_Reflection_Types.term ->
                      FStar_Reflection_Types.term ->
                        FStar_Reflection_Types.term)
  =
  fun u1 ->
    fun u2 ->
      fun a ->
        fun b ->
          fun opened ->
            fun pre1 ->
              fun post1 ->
                fun post2 ->
                  fun e1 ->
                    fun e2 ->
                      fun reveal_a ->
                        let bind_lid =
                          mk_pulse_lib_core_lid "bind_stt_ghost_atomic" in
                        let t =
                          FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_UInst
                               ((FStar_Reflection_V2_Builtins.pack_fv
                                   bind_lid), [u1; u2])) in
                        let t1 =
                          FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_App
                               (t, (a, FStar_Reflection_V2_Data.Q_Implicit))) in
                        let t2 =
                          FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_App
                               (t1, (b, FStar_Reflection_V2_Data.Q_Implicit))) in
                        let t3 =
                          FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_App
                               (t2,
                                 (opened,
                                   FStar_Reflection_V2_Data.Q_Implicit))) in
                        let t4 =
                          FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_App
                               (t3,
                                 (pre1, FStar_Reflection_V2_Data.Q_Implicit))) in
                        let t5 =
                          FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_App
                               (t4,
                                 (post1, FStar_Reflection_V2_Data.Q_Implicit))) in
                        let t6 =
                          FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_App
                               (t5,
                                 (post2, FStar_Reflection_V2_Data.Q_Implicit))) in
                        let t7 =
                          FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_App
                               (t6,
                                 (e1, FStar_Reflection_V2_Data.Q_Explicit))) in
                        let t8 =
                          FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_App
                               (t7,
                                 (e2, FStar_Reflection_V2_Data.Q_Explicit))) in
                        FStar_Reflection_V2_Builtins.pack_ln
                          (FStar_Reflection_V2_Data.Tv_App
                             (t8,
                               (reveal_a,
                                 FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_bind_atomic_ghost :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.universe ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                FStar_Reflection_Types.term ->
                  FStar_Reflection_Types.term ->
                    FStar_Reflection_Types.term ->
                      FStar_Reflection_Types.term ->
                        FStar_Reflection_Types.term)
  =
  fun u1 ->
    fun u2 ->
      fun a ->
        fun b ->
          fun opened ->
            fun pre1 ->
              fun post1 ->
                fun post2 ->
                  fun e1 ->
                    fun e2 ->
                      fun reveal_b ->
                        let bind_lid =
                          mk_pulse_lib_core_lid "bind_stt_atomic_ghost" in
                        let t =
                          FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_UInst
                               ((FStar_Reflection_V2_Builtins.pack_fv
                                   bind_lid), [u1; u2])) in
                        let t1 =
                          FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_App
                               (t, (a, FStar_Reflection_V2_Data.Q_Implicit))) in
                        let t2 =
                          FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_App
                               (t1, (b, FStar_Reflection_V2_Data.Q_Implicit))) in
                        let t3 =
                          FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_App
                               (t2,
                                 (opened,
                                   FStar_Reflection_V2_Data.Q_Implicit))) in
                        let t4 =
                          FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_App
                               (t3,
                                 (pre1, FStar_Reflection_V2_Data.Q_Implicit))) in
                        let t5 =
                          FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_App
                               (t4,
                                 (post1, FStar_Reflection_V2_Data.Q_Implicit))) in
                        let t6 =
                          FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_App
                               (t5,
                                 (post2, FStar_Reflection_V2_Data.Q_Implicit))) in
                        let t7 =
                          FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_App
                               (t6,
                                 (e1, FStar_Reflection_V2_Data.Q_Explicit))) in
                        let t8 =
                          FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_App
                               (t7,
                                 (e2, FStar_Reflection_V2_Data.Q_Explicit))) in
                        FStar_Reflection_V2_Builtins.pack_ln
                          (FStar_Reflection_V2_Data.Tv_App
                             (t8,
                               (reveal_b,
                                 FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_frame_stt :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun ty ->
      fun pre ->
        fun post ->
          fun frame ->
            fun t ->
              let frame_lid = mk_pulse_lib_core_lid "frame_stt" in
              let frame_fv = FStar_Reflection_V2_Builtins.pack_fv frame_lid in
              let frame_univ_inst u1 =
                FStar_Reflection_V2_Builtins.pack_ln
                  (FStar_Reflection_V2_Data.Tv_UInst
                     ((FStar_Reflection_V2_Builtins.pack_fv frame_lid), [u1])) in
              let head = frame_univ_inst u in
              FStar_Reflection_V2_Derived.mk_app
                (FStar_Reflection_V2_Derived.mk_app
                   (FStar_Reflection_V2_Derived.mk_app
                      (FStar_Reflection_V2_Derived.mk_app
                         (FStar_Reflection_V2_Derived.mk_app head
                            [(ty, FStar_Reflection_V2_Data.Q_Implicit)])
                         [(pre, FStar_Reflection_V2_Data.Q_Implicit)])
                      [(post, FStar_Reflection_V2_Data.Q_Implicit)])
                   [(frame, FStar_Reflection_V2_Data.Q_Explicit)])
                [(t, FStar_Reflection_V2_Data.Q_Explicit)]
let (mk_frame_stt_atomic :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun opened ->
        fun pre ->
          fun post ->
            fun frame ->
              fun e ->
                let lid = mk_pulse_lib_core_lid "frame_stt_atomic" in
                let t =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_UInst
                       ((FStar_Reflection_V2_Builtins.pack_fv lid), [u])) in
                let t1 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t, (a, FStar_Reflection_V2_Data.Q_Implicit))) in
                let t2 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t1, (opened, FStar_Reflection_V2_Data.Q_Implicit))) in
                let t3 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t2, (pre, FStar_Reflection_V2_Data.Q_Implicit))) in
                let t4 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t3, (post, FStar_Reflection_V2_Data.Q_Implicit))) in
                let t5 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t4, (frame, FStar_Reflection_V2_Data.Q_Explicit))) in
                FStar_Reflection_V2_Builtins.pack_ln
                  (FStar_Reflection_V2_Data.Tv_App
                     (t5, (e, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_frame_stt_ghost :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun opened ->
        fun pre ->
          fun post ->
            fun frame ->
              fun e ->
                let lid = mk_pulse_lib_core_lid "frame_stt_ghost" in
                let t =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_UInst
                       ((FStar_Reflection_V2_Builtins.pack_fv lid), [u])) in
                let t1 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t, (a, FStar_Reflection_V2_Data.Q_Implicit))) in
                let t2 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t1, (opened, FStar_Reflection_V2_Data.Q_Implicit))) in
                let t3 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t2, (pre, FStar_Reflection_V2_Data.Q_Implicit))) in
                let t4 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t3, (post, FStar_Reflection_V2_Data.Q_Implicit))) in
                let t5 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t4, (frame, FStar_Reflection_V2_Data.Q_Explicit))) in
                FStar_Reflection_V2_Builtins.pack_ln
                  (FStar_Reflection_V2_Data.Tv_App
                     (t5, (e, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_sub_stt :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun ty ->
      fun pre1 ->
        fun pre2 ->
          fun post1 ->
            fun post2 ->
              fun t ->
                let subsumption_lid = mk_pulse_lib_core_lid "sub_stt" in
                let subsumption_fv =
                  FStar_Reflection_V2_Builtins.pack_fv subsumption_lid in
                let subsumption_univ_inst u1 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_UInst (subsumption_fv, [u1])) in
                let head = subsumption_univ_inst u in
                FStar_Reflection_V2_Derived.mk_app
                  (FStar_Reflection_V2_Derived.mk_app
                     (FStar_Reflection_V2_Derived.mk_app
                        (FStar_Reflection_V2_Derived.mk_app
                           (FStar_Reflection_V2_Derived.mk_app
                              (FStar_Reflection_V2_Derived.mk_app
                                 (FStar_Reflection_V2_Derived.mk_app
                                    (FStar_Reflection_V2_Derived.mk_app head
                                       [(ty,
                                          FStar_Reflection_V2_Data.Q_Implicit)])
                                    [(pre1,
                                       FStar_Reflection_V2_Data.Q_Implicit)])
                                 [(pre2, FStar_Reflection_V2_Data.Q_Explicit)])
                              [(post1, FStar_Reflection_V2_Data.Q_Implicit)])
                           [(post2, FStar_Reflection_V2_Data.Q_Explicit)])
                        [((FStar_Reflection_V2_Builtins.pack_ln
                             (FStar_Reflection_V2_Data.Tv_Const
                                FStar_Reflection_V2_Data.C_Unit)),
                           FStar_Reflection_V2_Data.Q_Explicit)])
                     [((FStar_Reflection_V2_Builtins.pack_ln
                          (FStar_Reflection_V2_Data.Tv_Const
                             FStar_Reflection_V2_Data.C_Unit)),
                        FStar_Reflection_V2_Data.Q_Explicit)])
                  [(t, FStar_Reflection_V2_Data.Q_Explicit)]
let (mk_sub_stt_atomic :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun opened ->
        fun pre1 ->
          fun pre2 ->
            fun post1 ->
              fun post2 ->
                fun e ->
                  let lid = mk_pulse_lib_core_lid "sub_stt_atomic" in
                  let t =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_UInst
                         ((FStar_Reflection_V2_Builtins.pack_fv lid), [u])) in
                  let t1 =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t, (a, FStar_Reflection_V2_Data.Q_Implicit))) in
                  let t2 =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t1, (opened, FStar_Reflection_V2_Data.Q_Implicit))) in
                  let t3 =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t2, (pre1, FStar_Reflection_V2_Data.Q_Implicit))) in
                  let t4 =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t3, (pre2, FStar_Reflection_V2_Data.Q_Explicit))) in
                  let t5 =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t4, (post1, FStar_Reflection_V2_Data.Q_Implicit))) in
                  let t6 =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t5, (post2, FStar_Reflection_V2_Data.Q_Explicit))) in
                  let t7 =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t6,
                           ((FStar_Reflection_V2_Builtins.pack_ln
                               (FStar_Reflection_V2_Data.Tv_Const
                                  FStar_Reflection_V2_Data.C_Unit)),
                             FStar_Reflection_V2_Data.Q_Explicit))) in
                  let t8 =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t7,
                           ((FStar_Reflection_V2_Builtins.pack_ln
                               (FStar_Reflection_V2_Data.Tv_Const
                                  FStar_Reflection_V2_Data.C_Unit)),
                             FStar_Reflection_V2_Data.Q_Explicit))) in
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t8, (e, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_sub_stt_ghost :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun a ->
      fun opened ->
        fun pre1 ->
          fun pre2 ->
            fun post1 ->
              fun post2 ->
                fun e ->
                  let lid = mk_pulse_lib_core_lid "sub_stt_ghost" in
                  let t =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_UInst
                         ((FStar_Reflection_V2_Builtins.pack_fv lid), [u])) in
                  let t1 =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t, (a, FStar_Reflection_V2_Data.Q_Implicit))) in
                  let t2 =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t1, (opened, FStar_Reflection_V2_Data.Q_Implicit))) in
                  let t3 =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t2, (pre1, FStar_Reflection_V2_Data.Q_Implicit))) in
                  let t4 =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t3, (pre2, FStar_Reflection_V2_Data.Q_Explicit))) in
                  let t5 =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t4, (post1, FStar_Reflection_V2_Data.Q_Implicit))) in
                  let t6 =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t5, (post2, FStar_Reflection_V2_Data.Q_Explicit))) in
                  let t7 =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t6,
                           ((FStar_Reflection_V2_Builtins.pack_ln
                               (FStar_Reflection_V2_Data.Tv_Const
                                  FStar_Reflection_V2_Data.C_Unit)),
                             FStar_Reflection_V2_Data.Q_Explicit))) in
                  let t8 =
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t7,
                           ((FStar_Reflection_V2_Builtins.pack_ln
                               (FStar_Reflection_V2_Data.Tv_Const
                                  FStar_Reflection_V2_Data.C_Unit)),
                             FStar_Reflection_V2_Data.Q_Explicit))) in
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t8, (e, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_par :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                FStar_Reflection_Types.term ->
                  FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun u ->
    fun aL ->
      fun aR ->
        fun preL ->
          fun postL ->
            fun preR ->
              fun postR ->
                fun eL ->
                  fun eR ->
                    let lid = mk_pulse_lib_core_lid "stt_par" in
                    let t =
                      FStar_Reflection_V2_Builtins.pack_ln
                        (FStar_Reflection_V2_Data.Tv_UInst
                           ((FStar_Reflection_V2_Builtins.pack_fv lid), [u])) in
                    let t1 =
                      FStar_Reflection_V2_Builtins.pack_ln
                        (FStar_Reflection_V2_Data.Tv_App
                           (t, (aL, FStar_Reflection_V2_Data.Q_Implicit))) in
                    let t2 =
                      FStar_Reflection_V2_Builtins.pack_ln
                        (FStar_Reflection_V2_Data.Tv_App
                           (t1, (aR, FStar_Reflection_V2_Data.Q_Implicit))) in
                    let t3 =
                      FStar_Reflection_V2_Builtins.pack_ln
                        (FStar_Reflection_V2_Data.Tv_App
                           (t2, (preL, FStar_Reflection_V2_Data.Q_Implicit))) in
                    let t4 =
                      FStar_Reflection_V2_Builtins.pack_ln
                        (FStar_Reflection_V2_Data.Tv_App
                           (t3, (postL, FStar_Reflection_V2_Data.Q_Implicit))) in
                    let t5 =
                      FStar_Reflection_V2_Builtins.pack_ln
                        (FStar_Reflection_V2_Data.Tv_App
                           (t4, (preR, FStar_Reflection_V2_Data.Q_Implicit))) in
                    let t6 =
                      FStar_Reflection_V2_Builtins.pack_ln
                        (FStar_Reflection_V2_Data.Tv_App
                           (t5, (postR, FStar_Reflection_V2_Data.Q_Implicit))) in
                    let t7 =
                      FStar_Reflection_V2_Builtins.pack_ln
                        (FStar_Reflection_V2_Data.Tv_App
                           (t6, (eL, FStar_Reflection_V2_Data.Q_Explicit))) in
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_App
                         (t7, (eR, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_rewrite :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun p ->
    fun q ->
      let t =
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                (mk_pulse_lib_core_lid "rewrite"))) in
      let t1 =
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_App
             (t, (p, FStar_Reflection_V2_Data.Q_Explicit))) in
      let t2 =
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_App
             (t1, (q, FStar_Reflection_V2_Data.Q_Explicit))) in
      FStar_Reflection_V2_Builtins.pack_ln
        (FStar_Reflection_V2_Data.Tv_App
           (t2,
             ((FStar_Reflection_V2_Builtins.pack_ln
                 (FStar_Reflection_V2_Data.Tv_Const
                    FStar_Reflection_V2_Data.C_Unit)),
               FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_withlocal :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun ret_u ->
    fun a ->
      fun init ->
        fun pre ->
          fun ret_t ->
            fun post ->
              fun body ->
                let lid = mk_pulse_lib_reference_lid "with_local" in
                let t =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_UInst
                       ((FStar_Reflection_V2_Builtins.pack_fv lid), [ret_u])) in
                let t1 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t, (a, FStar_Reflection_V2_Data.Q_Implicit))) in
                let t2 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t1, (init, FStar_Reflection_V2_Data.Q_Explicit))) in
                let t3 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t2, (pre, FStar_Reflection_V2_Data.Q_Implicit))) in
                let t4 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t3, (ret_t, FStar_Reflection_V2_Data.Q_Implicit))) in
                let t5 =
                  FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       (t4, (post, FStar_Reflection_V2_Data.Q_Implicit))) in
                FStar_Reflection_V2_Builtins.pack_ln
                  (FStar_Reflection_V2_Data.Tv_App
                     (t5, (body, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_star_equiv :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            (unit, unit, unit) FStar_Reflection_Typing.equiv ->
              (unit, unit, unit) FStar_Reflection_Typing.equiv ->
                (unit, unit, unit) FStar_Reflection_Typing.equiv)
  =
  fun g ->
    fun t1 ->
      fun t2 -> fun t3 -> fun t4 -> fun eq1 -> fun eq2 -> Prims.admit ()
let (mk_stt_comp_equiv :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.universe ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                (unit, unit, unit) FStar_Reflection_Typing.equiv ->
                  (unit, unit, unit) FStar_Reflection_Typing.equiv ->
                    (unit, unit, unit) FStar_Reflection_Typing.equiv)
  =
  fun g ->
    fun u ->
      fun res ->
        fun pre1 ->
          fun post1 ->
            fun pre2 ->
              fun post2 -> fun pre_eq -> fun post_eq -> Prims.admit ()
let (mk_stt_atomic_comp_equiv :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.universe ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                FStar_Reflection_Types.term ->
                  (unit, unit, unit) FStar_Reflection_Typing.equiv ->
                    (unit, unit, unit) FStar_Reflection_Typing.equiv ->
                      (unit, unit, unit) FStar_Reflection_Typing.equiv)
  =
  fun g ->
    fun u ->
      fun res ->
        fun inames ->
          fun pre1 ->
            fun post1 ->
              fun pre2 ->
                fun post2 -> fun pre_eq -> fun post_eq -> Prims.admit ()
let (mk_stt_ghost_comp_equiv :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.universe ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                FStar_Reflection_Types.term ->
                  (unit, unit, unit) FStar_Reflection_Typing.equiv ->
                    (unit, unit, unit) FStar_Reflection_Typing.equiv ->
                      (unit, unit, unit) FStar_Reflection_Typing.equiv)
  =
  fun g ->
    fun u ->
      fun res ->
        fun inames ->
          fun pre1 ->
            fun post1 ->
              fun pre2 ->
                fun post2 -> fun pre_eq -> fun post_eq -> Prims.admit ()
let (ref_lid : Prims.string Prims.list) = mk_pulse_lib_reference_lid "ref"
let (pts_to_lid : Prims.string Prims.list) =
  mk_pulse_lib_reference_lid "pts_to"
let (full_perm_lid : Prims.string Prims.list) =
  ["Steel"; "FractionalPermission"; "full_perm"]
let (mk_ref : FStar_Reflection_Types.term -> FStar_Reflection_Types.term) =
  fun a ->
    let t =
      FStar_Reflection_V2_Builtins.pack_ln
        (FStar_Reflection_V2_Data.Tv_FVar
           (FStar_Reflection_V2_Builtins.pack_fv ref_lid)) in
    FStar_Reflection_V2_Builtins.pack_ln
      (FStar_Reflection_V2_Data.Tv_App
         (t, (a, FStar_Reflection_V2_Data.Q_Explicit)))
let (mk_pts_to :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun a ->
    fun r ->
      fun perm ->
        fun v ->
          let t =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_FVar
                 (FStar_Reflection_V2_Builtins.pack_fv pts_to_lid)) in
          let t1 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t, (a, FStar_Reflection_V2_Data.Q_Implicit))) in
          let t2 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t1, (r, FStar_Reflection_V2_Data.Q_Explicit))) in
          let t3 =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (t2, (perm, FStar_Reflection_V2_Data.Q_Implicit))) in
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t3, (v, FStar_Reflection_V2_Data.Q_Explicit)))
let (full_perm_tm : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_FVar
       (FStar_Reflection_V2_Builtins.pack_fv full_perm_lid))