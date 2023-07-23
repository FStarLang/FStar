open Prims
let (debug_log :
  Prims.string ->
    Pulse_Typing_Env.env ->
      (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
        (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun level ->
           fun g ->
             fun f ->
               if
                 Pulse_RuntimeUtils.debug_at_level
                   (Pulse_Typing_Env.fstar_env g) level
               then
                 Obj.magic
                   (Obj.repr
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Typing.fst"
                                  (Prims.of_int (16)) (Prims.of_int (15))
                                  (Prims.of_int (16)) (Prims.of_int (64)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Typing.fst"
                                  (Prims.of_int (16)) (Prims.of_int (7))
                                  (Prims.of_int (16)) (Prims.of_int (64)))))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Pulse.Typing.fst"
                                        (Prims.of_int (16))
                                        (Prims.of_int (57))
                                        (Prims.of_int (16))
                                        (Prims.of_int (63)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "prims.fst"
                                        (Prims.of_int (590))
                                        (Prims.of_int (19))
                                        (Prims.of_int (590))
                                        (Prims.of_int (31)))))
                               (Obj.magic (f ()))
                               (fun uu___ ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 ->
                                       Prims.strcat
                                         (Prims.strcat "Debug@"
                                            (Prims.strcat level ":{ "))
                                         (Prims.strcat uu___ " }\n")))))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_V2_Builtins.print uu___))
                              uu___)))
               else
                 Obj.magic
                   (Obj.repr
                      (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
          uu___2 uu___1 uu___
let (tm_unit : Pulse_Syntax_Base.term) =
  Pulse_Syntax_Pure.tm_fvar
    (Pulse_Syntax_Base.as_fv Pulse_Reflection_Util.unit_lid)
let (tm_bool : Pulse_Syntax_Base.term) =
  Pulse_Syntax_Pure.tm_fvar
    (Pulse_Syntax_Base.as_fv Pulse_Reflection_Util.bool_lid)
let (tm_int : Pulse_Syntax_Base.term) =
  Pulse_Syntax_Pure.tm_fvar
    (Pulse_Syntax_Base.as_fv Pulse_Reflection_Util.int_lid)
let (tm_true : Pulse_Syntax_Base.term) =
  Pulse_Syntax_Pure.tm_constant FStar_Reflection_V2_Data.C_True
let (tm_false : Pulse_Syntax_Base.term) =
  Pulse_Syntax_Pure.tm_constant FStar_Reflection_V2_Data.C_False
let (tm_prop : Pulse_Syntax_Base.term) =
  Pulse_Syntax_Base.with_range
    (Pulse_Syntax_Base.Tm_FStar FStar_Reflection_Typing.tm_prop)
    FStar_Range.range_0
let (mk_erased :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun u ->
    fun t ->
      let hd =
        Pulse_Syntax_Pure.tm_uinst
          (Pulse_Syntax_Base.as_fv Pulse_Reflection_Util.erased_lid) 
          [u] in
      Pulse_Syntax_Pure.tm_pureapp hd FStar_Pervasives_Native.None t
let (mk_reveal :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun u ->
    fun t ->
      fun e ->
        let hd =
          Pulse_Syntax_Pure.tm_uinst
            (Pulse_Syntax_Base.as_fv Pulse_Reflection_Util.reveal_lid) 
            [u] in
        let hd1 =
          Pulse_Syntax_Pure.tm_pureapp hd
            (FStar_Pervasives_Native.Some Pulse_Syntax_Base.Implicit) t in
        Pulse_Syntax_Pure.tm_pureapp hd1 FStar_Pervasives_Native.None e
let (mk_hide :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun u ->
    fun t ->
      fun e ->
        let hd =
          Pulse_Syntax_Pure.tm_uinst
            (Pulse_Syntax_Base.as_fv Pulse_Reflection_Util.hide_lid) 
            [u] in
        let hd1 =
          Pulse_Syntax_Pure.tm_pureapp hd
            (FStar_Pervasives_Native.Some Pulse_Syntax_Base.Implicit) t in
        Pulse_Syntax_Pure.tm_pureapp hd1 FStar_Pervasives_Native.None e
let (mk_eq2 :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun u ->
    fun t ->
      fun e0 ->
        fun e1 ->
          Pulse_Syntax_Pure.tm_pureapp
            (Pulse_Syntax_Pure.tm_pureapp
               (Pulse_Syntax_Pure.tm_pureapp
                  (Pulse_Syntax_Pure.tm_uinst
                     (Pulse_Syntax_Base.as_fv FStar_Reflection_Const.eq2_qn)
                     [u])
                  (FStar_Pervasives_Native.Some Pulse_Syntax_Base.Implicit) t)
               FStar_Pervasives_Native.None e0) FStar_Pervasives_Native.None
            e1
let (mk_sq_eq2 :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun u ->
    fun t ->
      fun e0 ->
        fun e1 ->
          let eq = mk_eq2 u t e0 e1 in
          Pulse_Syntax_Pure.tm_pureapp
            (Pulse_Syntax_Pure.tm_uinst
               (Pulse_Syntax_Base.as_fv FStar_Reflection_Const.squash_qn) 
               [u]) FStar_Pervasives_Native.None eq
let (mk_eq2_prop :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun u ->
    fun t ->
      fun e0 ->
        fun e1 ->
          Pulse_Syntax_Pure.tm_pureapp
            (Pulse_Syntax_Pure.tm_pureapp
               (Pulse_Syntax_Pure.tm_pureapp
                  (Pulse_Syntax_Pure.tm_uinst
                     (Pulse_Syntax_Base.as_fv
                        (Pulse_Reflection_Util.mk_steel_wrapper_lid
                           "eq2_prop")) [u])
                  (FStar_Pervasives_Native.Some Pulse_Syntax_Base.Implicit) t)
               FStar_Pervasives_Native.None e0) FStar_Pervasives_Native.None
            e1
let (mk_vprop_eq :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun e0 ->
    fun e1 -> mk_eq2 Pulse_Syntax_Pure.u2 Pulse_Syntax_Base.tm_vprop e0 e1
let (mk_ref : Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term) =
  fun t ->
    Pulse_Syntax_Pure.tm_pureapp
      (Pulse_Syntax_Pure.tm_fvar
         (Pulse_Syntax_Base.as_fv Pulse_Reflection_Util.ref_lid))
      FStar_Pervasives_Native.None t
let (mk_pts_to :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun ty ->
    fun r ->
      fun v ->
        let t =
          Pulse_Syntax_Pure.tm_fvar
            (Pulse_Syntax_Base.as_fv Pulse_Reflection_Util.pts_to_lid) in
        let t1 =
          Pulse_Syntax_Pure.tm_pureapp t
            (FStar_Pervasives_Native.Some Pulse_Syntax_Base.Implicit) ty in
        let t2 =
          Pulse_Syntax_Pure.tm_pureapp t1 FStar_Pervasives_Native.None r in
        let t3 =
          Pulse_Syntax_Pure.tm_pureapp t2 FStar_Pervasives_Native.None
            (Pulse_Syntax_Pure.tm_fvar
               (Pulse_Syntax_Base.as_fv Pulse_Reflection_Util.full_perm_lid)) in
        Pulse_Syntax_Pure.tm_pureapp t3 FStar_Pervasives_Native.None v
let (comp_return :
  Pulse_Syntax_Base.ctag ->
    Prims.bool ->
      Pulse_Syntax_Base.universe ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            Pulse_Syntax_Base.term ->
              Pulse_Syntax_Base.var -> Pulse_Syntax_Base.comp)
  =
  fun c ->
    fun use_eq ->
      fun u ->
        fun t ->
          fun e ->
            fun post ->
              fun x ->
                let post_maybe_eq =
                  if use_eq
                  then
                    let post1 =
                      Pulse_Syntax_Naming.open_term' post
                        (Pulse_Syntax_Pure.null_var x) Prims.int_zero in
                    let post2 =
                      Pulse_Syntax_Base.tm_star post1
                        (Pulse_Syntax_Base.tm_pure
                           (mk_eq2_prop u t (Pulse_Syntax_Pure.null_var x) e)) in
                    Pulse_Syntax_Naming.close_term post2 x
                  else post in
                match c with
                | Pulse_Syntax_Base.STT ->
                    Pulse_Syntax_Base.C_ST
                      {
                        Pulse_Syntax_Base.u = u;
                        Pulse_Syntax_Base.res = t;
                        Pulse_Syntax_Base.pre =
                          (Pulse_Syntax_Naming.open_term' post e
                             Prims.int_zero);
                        Pulse_Syntax_Base.post = post_maybe_eq
                      }
                | Pulse_Syntax_Base.STT_Atomic ->
                    Pulse_Syntax_Base.C_STAtomic
                      (Pulse_Syntax_Base.tm_emp_inames,
                        {
                          Pulse_Syntax_Base.u = u;
                          Pulse_Syntax_Base.res = t;
                          Pulse_Syntax_Base.pre =
                            (Pulse_Syntax_Naming.open_term' post e
                               Prims.int_zero);
                          Pulse_Syntax_Base.post = post_maybe_eq
                        })
                | Pulse_Syntax_Base.STT_Ghost ->
                    Pulse_Syntax_Base.C_STGhost
                      (Pulse_Syntax_Base.tm_emp_inames,
                        {
                          Pulse_Syntax_Base.u = u;
                          Pulse_Syntax_Base.res = t;
                          Pulse_Syntax_Base.pre =
                            (Pulse_Syntax_Naming.open_term' post e
                               Prims.int_zero);
                          Pulse_Syntax_Base.post = post_maybe_eq
                        })
let (extend_env_l :
  FStar_Reflection_Types.env ->
    Pulse_Typing_Env.env_bindings -> FStar_Reflection_Types.env)
  =
  fun f ->
    fun g ->
      FStar_List_Tot_Base.fold_right
        (fun uu___ ->
           fun g1 ->
             match uu___ with
             | (x, b) ->
                 let t = Pulse_Elaborate_Pure.elab_term b in
                 FStar_Reflection_Typing.extend_env g1 x t) g f
let (elab_env : Pulse_Typing_Env.env -> FStar_Reflection_Types.env) =
  fun e ->
    extend_env_l (Pulse_Typing_Env.fstar_env e) (Pulse_Typing_Env.bindings e)
type ('g, 'x) freshv = unit
type ('g, 'xs) all_fresh = Obj.t
let rec (push_bindings :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.binding Prims.list -> Pulse_Typing_Env.env)
  =
  fun g ->
    fun bs ->
      match bs with
      | [] -> g
      | (x, t)::bs1 ->
          push_bindings
            (Pulse_Typing_Env.push_binding g x
               Pulse_Syntax_Base.ppname_default t) bs1
let (add_frame :
  Pulse_Syntax_Base.comp_st ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp_st)
  =
  fun s ->
    fun frame ->
      let add_frame_s s1 =
        {
          Pulse_Syntax_Base.u = (s1.Pulse_Syntax_Base.u);
          Pulse_Syntax_Base.res = (s1.Pulse_Syntax_Base.res);
          Pulse_Syntax_Base.pre =
            (Pulse_Syntax_Base.tm_star s1.Pulse_Syntax_Base.pre frame);
          Pulse_Syntax_Base.post =
            (Pulse_Syntax_Base.tm_star s1.Pulse_Syntax_Base.post frame)
        } in
      match s with
      | Pulse_Syntax_Base.C_ST s1 -> Pulse_Syntax_Base.C_ST (add_frame_s s1)
      | Pulse_Syntax_Base.C_STAtomic (inames, s1) ->
          Pulse_Syntax_Base.C_STAtomic (inames, (add_frame_s s1))
      | Pulse_Syntax_Base.C_STGhost (inames, s1) ->
          Pulse_Syntax_Base.C_STGhost (inames, (add_frame_s s1))
type ('c1, 'c2) bind_comp_compatible = Obj.t
type ('x, 'c1, 'c2) bind_comp_pre = unit
let (bind_comp_out :
  Pulse_Syntax_Base.comp_st ->
    Pulse_Syntax_Base.comp_st -> Pulse_Syntax_Base.comp_st)
  =
  fun c1 ->
    fun c2 ->
      let s =
        {
          Pulse_Syntax_Base.u = (Pulse_Syntax_Base.comp_u c2);
          Pulse_Syntax_Base.res = (Pulse_Syntax_Base.comp_res c2);
          Pulse_Syntax_Base.pre = (Pulse_Syntax_Base.comp_pre c1);
          Pulse_Syntax_Base.post = (Pulse_Syntax_Base.comp_post c2)
        } in
      match (c1, c2) with
      | (Pulse_Syntax_Base.C_STGhost (inames, uu___),
         Pulse_Syntax_Base.C_STGhost (uu___1, uu___2)) ->
          Pulse_Syntax_Base.C_STGhost (inames, s)
      | (Pulse_Syntax_Base.C_ST uu___, Pulse_Syntax_Base.C_ST uu___1) ->
          Pulse_Syntax_Base.C_ST s
type ('c1, 'c2) bind_comp_ghost_l_compatible = Obj.t
type ('x, 'c1, 'c2) bind_comp_ghost_l_pre = unit
let (bind_comp_ghost_l_out :
  Pulse_Syntax_Base.comp_st ->
    Pulse_Syntax_Base.comp_st -> Pulse_Syntax_Base.comp_st)
  =
  fun c1 ->
    fun c2 ->
      let s =
        {
          Pulse_Syntax_Base.u = (Pulse_Syntax_Base.comp_u c2);
          Pulse_Syntax_Base.res = (Pulse_Syntax_Base.comp_res c2);
          Pulse_Syntax_Base.pre = (Pulse_Syntax_Base.comp_pre c1);
          Pulse_Syntax_Base.post = (Pulse_Syntax_Base.comp_post c2)
        } in
      match (c1, c2) with
      | (Pulse_Syntax_Base.C_STGhost (inames, uu___),
         Pulse_Syntax_Base.C_STAtomic (uu___1, uu___2)) ->
          Pulse_Syntax_Base.C_STAtomic (inames, s)
type ('c1, 'c2) bind_comp_ghost_r_compatible = Obj.t
type ('x, 'c1, 'c2) bind_comp_ghost_r_pre = unit
let (bind_comp_ghost_r_out :
  Pulse_Syntax_Base.comp_st ->
    Pulse_Syntax_Base.comp_st -> Pulse_Syntax_Base.comp_st)
  =
  fun c1 ->
    fun c2 ->
      let s =
        {
          Pulse_Syntax_Base.u = (Pulse_Syntax_Base.comp_u c2);
          Pulse_Syntax_Base.res = (Pulse_Syntax_Base.comp_res c2);
          Pulse_Syntax_Base.pre = (Pulse_Syntax_Base.comp_pre c1);
          Pulse_Syntax_Base.post = (Pulse_Syntax_Base.comp_post c2)
        } in
      match (c1, c2) with
      | (Pulse_Syntax_Base.C_STAtomic (inames, uu___),
         Pulse_Syntax_Base.C_STGhost (uu___1, uu___2)) ->
          Pulse_Syntax_Base.C_STAtomic (inames, s)
type ('c1, 'c2) st_equiv_pre = unit
let (non_informative_witness_t :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun u ->
    fun t ->
      Pulse_Syntax_Pure.tm_pureapp
        (Pulse_Syntax_Pure.tm_uinst
           (Pulse_Syntax_Base.as_fv
              Pulse_Reflection_Util.non_informative_witness_lid) [u])
        FStar_Pervasives_Native.None t
let (elim_exists_post :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.nvar -> Pulse_Syntax_Base.term)
  =
  fun u ->
    fun t ->
      fun p ->
        fun x ->
          let x_tm = Pulse_Syntax_Pure.term_of_nvar x in
          let p1 =
            Pulse_Syntax_Naming.open_term' p (mk_reveal u t x_tm)
              Prims.int_zero in
          Pulse_Syntax_Naming.close_term p1 (FStar_Pervasives_Native.snd x)
let (comp_elim_exists :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.nvar -> Pulse_Syntax_Base.comp)
  =
  fun u ->
    fun t ->
      fun p ->
        fun x ->
          Pulse_Syntax_Base.C_STGhost
            (Pulse_Syntax_Base.tm_emp_inames,
              {
                Pulse_Syntax_Base.u = u;
                Pulse_Syntax_Base.res = (mk_erased u t);
                Pulse_Syntax_Base.pre =
                  (Pulse_Syntax_Base.tm_exists_sl u
                     (Pulse_Syntax_Base.as_binder t) p);
                Pulse_Syntax_Base.post = (elim_exists_post u t p x)
              })
let (comp_intro_pure : Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp) =
  fun p ->
    Pulse_Syntax_Base.C_STGhost
      (Pulse_Syntax_Base.tm_emp_inames,
        {
          Pulse_Syntax_Base.u = Pulse_Syntax_Pure.u_zero;
          Pulse_Syntax_Base.res = tm_unit;
          Pulse_Syntax_Base.pre = Pulse_Syntax_Base.tm_emp;
          Pulse_Syntax_Base.post = (Pulse_Syntax_Base.tm_pure p)
        })
let (named_binder :
  Pulse_Syntax_Base.ppname ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.binder)
  =
  fun x ->
    fun t ->
      { Pulse_Syntax_Base.binder_ty = t; Pulse_Syntax_Base.binder_ppname = x
      }
let (comp_intro_exists :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.binder ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp)
  =
  fun u ->
    fun b ->
      fun p ->
        fun e ->
          Pulse_Syntax_Base.C_STGhost
            (Pulse_Syntax_Base.tm_emp_inames,
              {
                Pulse_Syntax_Base.u = Pulse_Syntax_Pure.u0;
                Pulse_Syntax_Base.res = tm_unit;
                Pulse_Syntax_Base.pre =
                  (Pulse_Syntax_Naming.open_term' p e Prims.int_zero);
                Pulse_Syntax_Base.post =
                  (Pulse_Syntax_Base.tm_exists_sl u b p)
              })
let (comp_intro_exists_erased :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.binder ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp)
  =
  fun u ->
    fun b ->
      fun p ->
        fun e ->
          Pulse_Syntax_Base.C_STGhost
            (Pulse_Syntax_Base.tm_emp_inames,
              {
                Pulse_Syntax_Base.u = Pulse_Syntax_Pure.u0;
                Pulse_Syntax_Base.res = tm_unit;
                Pulse_Syntax_Base.pre =
                  (Pulse_Syntax_Naming.open_term' p
                     (mk_reveal u b.Pulse_Syntax_Base.binder_ty e)
                     Prims.int_zero);
                Pulse_Syntax_Base.post =
                  (Pulse_Syntax_Base.tm_exists_sl u b p)
              })
let (comp_while_cond :
  Pulse_Syntax_Base.ppname ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp)
  =
  fun x ->
    fun inv ->
      Pulse_Syntax_Base.C_ST
        {
          Pulse_Syntax_Base.u = Pulse_Syntax_Pure.u0;
          Pulse_Syntax_Base.res = tm_bool;
          Pulse_Syntax_Base.pre =
            (Pulse_Syntax_Base.tm_exists_sl Pulse_Syntax_Pure.u0
               (named_binder x tm_bool) inv);
          Pulse_Syntax_Base.post = inv
        }
let (comp_while_body :
  Pulse_Syntax_Base.ppname ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp)
  =
  fun x ->
    fun inv ->
      Pulse_Syntax_Base.C_ST
        {
          Pulse_Syntax_Base.u = Pulse_Syntax_Pure.u0;
          Pulse_Syntax_Base.res = tm_unit;
          Pulse_Syntax_Base.pre =
            (Pulse_Syntax_Naming.open_term' inv tm_true Prims.int_zero);
          Pulse_Syntax_Base.post =
            (Pulse_Syntax_Base.tm_exists_sl Pulse_Syntax_Pure.u0
               (named_binder x tm_bool) inv)
        }
let (comp_while :
  Pulse_Syntax_Base.ppname ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp)
  =
  fun x ->
    fun inv ->
      Pulse_Syntax_Base.C_ST
        {
          Pulse_Syntax_Base.u = Pulse_Syntax_Pure.u0;
          Pulse_Syntax_Base.res = tm_unit;
          Pulse_Syntax_Base.pre =
            (Pulse_Syntax_Base.tm_exists_sl Pulse_Syntax_Pure.u0
               (named_binder x tm_bool) inv);
          Pulse_Syntax_Base.post =
            (Pulse_Syntax_Naming.open_term' inv tm_false Prims.int_zero)
        }
let (mk_tuple2 :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun u1 ->
    fun u2 ->
      fun t1 ->
        fun t2 ->
          Pulse_Syntax_Pure.tm_pureapp
            (Pulse_Syntax_Pure.tm_pureapp
               (Pulse_Syntax_Pure.tm_uinst
                  (Pulse_Syntax_Base.as_fv Pulse_Reflection_Util.tuple2_lid)
                  [u1; u2]) FStar_Pervasives_Native.None t1)
            FStar_Pervasives_Native.None t2
let (mk_fst :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun u1 ->
    fun u2 ->
      fun a1 ->
        fun a2 ->
          fun e ->
            Pulse_Syntax_Pure.tm_pureapp
              (Pulse_Syntax_Pure.tm_pureapp
                 (Pulse_Syntax_Pure.tm_pureapp
                    (Pulse_Syntax_Pure.tm_uinst
                       (Pulse_Syntax_Base.as_fv Pulse_Reflection_Util.fst_lid)
                       [u1; u2])
                    (FStar_Pervasives_Native.Some Pulse_Syntax_Base.Implicit)
                    a1)
                 (FStar_Pervasives_Native.Some Pulse_Syntax_Base.Implicit) a2)
              FStar_Pervasives_Native.None e
let (mk_snd :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun u1 ->
    fun u2 ->
      fun a1 ->
        fun a2 ->
          fun e ->
            Pulse_Syntax_Pure.tm_pureapp
              (Pulse_Syntax_Pure.tm_pureapp
                 (Pulse_Syntax_Pure.tm_pureapp
                    (Pulse_Syntax_Pure.tm_uinst
                       (Pulse_Syntax_Base.as_fv Pulse_Reflection_Util.snd_lid)
                       [u1; u2])
                    (FStar_Pervasives_Native.Some Pulse_Syntax_Base.Implicit)
                    a1)
                 (FStar_Pervasives_Native.Some Pulse_Syntax_Base.Implicit) a2)
              FStar_Pervasives_Native.None e
let (par_post :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            Pulse_Syntax_Base.term ->
              Pulse_Syntax_Base.var -> Pulse_Syntax_Base.term)
  =
  fun uL ->
    fun uR ->
      fun aL ->
        fun aR ->
          fun postL ->
            fun postR ->
              fun x ->
                let x_tm = Pulse_Syntax_Pure.term_of_no_name_var x in
                let postL1 =
                  Pulse_Syntax_Naming.open_term' postL
                    (mk_fst uL uR aL aR x_tm) Prims.int_zero in
                let postR1 =
                  Pulse_Syntax_Naming.open_term' postR
                    (mk_snd uL uR aL aR x_tm) Prims.int_zero in
                let post = Pulse_Syntax_Base.tm_star postL1 postR1 in
                Pulse_Syntax_Naming.close_term post x
let (comp_par :
  Pulse_Syntax_Base.comp ->
    Pulse_Syntax_Base.comp -> Pulse_Syntax_Base.var -> Pulse_Syntax_Base.comp)
  =
  fun cL ->
    fun cR ->
      fun x ->
        let uL = Pulse_Syntax_Base.comp_u cL in
        let uR = Pulse_Syntax_Base.comp_u cR in
        let aL = Pulse_Syntax_Base.comp_res cL in
        let aR = Pulse_Syntax_Base.comp_res cR in
        let post =
          par_post uL uR aL aR (Pulse_Syntax_Base.comp_post cL)
            (Pulse_Syntax_Base.comp_post cR) x in
        Pulse_Syntax_Base.C_ST
          {
            Pulse_Syntax_Base.u = uL;
            Pulse_Syntax_Base.res = (mk_tuple2 uL uR aL aR);
            Pulse_Syntax_Base.pre =
              (Pulse_Syntax_Base.tm_star (Pulse_Syntax_Base.comp_pre cL)
                 (Pulse_Syntax_Base.comp_pre cR));
            Pulse_Syntax_Base.post = post
          }
let (comp_withlocal_body_pre :
  Pulse_Syntax_Base.vprop ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term -> Pulse_Syntax_Base.vprop)
  =
  fun pre ->
    fun init_t ->
      fun r ->
        fun init -> Pulse_Syntax_Base.tm_star pre (mk_pts_to init_t r init)
let (comp_withlocal_body_post :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun post ->
    fun init_t ->
      fun r ->
        Pulse_Syntax_Base.tm_star post
          (Pulse_Syntax_Base.tm_exists_sl Pulse_Syntax_Pure.u0
             (Pulse_Syntax_Base.as_binder init_t)
             (mk_pts_to init_t r (Pulse_Syntax_Pure.null_bvar Prims.int_zero)))
let (comp_withlocal_body :
  Pulse_Syntax_Base.var ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.comp -> Pulse_Syntax_Base.comp)
  =
  fun r ->
    fun init_t ->
      fun init ->
        fun c ->
          let r1 = Pulse_Syntax_Pure.null_var r in
          Pulse_Syntax_Base.C_ST
            {
              Pulse_Syntax_Base.u = (Pulse_Syntax_Base.comp_u c);
              Pulse_Syntax_Base.res = (Pulse_Syntax_Base.comp_res c);
              Pulse_Syntax_Base.pre =
                (comp_withlocal_body_pre (Pulse_Syntax_Base.comp_pre c)
                   init_t r1 init);
              Pulse_Syntax_Base.post =
                (comp_withlocal_body_post (Pulse_Syntax_Base.comp_post c)
                   init_t r1)
            }
let (comp_rewrite :
  Pulse_Syntax_Base.vprop ->
    Pulse_Syntax_Base.vprop -> Pulse_Syntax_Base.comp)
  =
  fun p ->
    fun q ->
      Pulse_Syntax_Base.C_STGhost
        (Pulse_Syntax_Base.tm_emp_inames,
          {
            Pulse_Syntax_Base.u = Pulse_Syntax_Pure.u0;
            Pulse_Syntax_Base.res = tm_unit;
            Pulse_Syntax_Base.pre = p;
            Pulse_Syntax_Base.post = q
          })
let (comp_admit :
  Pulse_Syntax_Base.ctag ->
    Pulse_Syntax_Base.st_comp -> Pulse_Syntax_Base.comp)
  =
  fun c ->
    fun s ->
      match c with
      | Pulse_Syntax_Base.STT -> Pulse_Syntax_Base.C_ST s
      | Pulse_Syntax_Base.STT_Atomic ->
          Pulse_Syntax_Base.C_STAtomic (Pulse_Syntax_Base.tm_emp_inames, s)
      | Pulse_Syntax_Base.STT_Ghost ->
          Pulse_Syntax_Base.C_STGhost (Pulse_Syntax_Base.tm_emp_inames, s)
type ('g, 'e, 't) typing =
  (unit, unit, unit) FStar_Reflection_Typing.tot_typing
type ('g, 'e, 't) tot_typing = unit
type ('g, 't, 'u) universe_of = unit
type ('g, 'u, 't) non_informative_t =
  (Pulse_Syntax_Base.term, unit) Prims.dtuple2
type ('g, 'c) non_informative_c = (unit, unit, unit) non_informative_t
let (as_binder : Pulse_Syntax_Base.term -> Pulse_Syntax_Base.binder) =
  fun t ->
    {
      Pulse_Syntax_Base.binder_ty = t;
      Pulse_Syntax_Base.binder_ppname = Pulse_Syntax_Base.ppname_default
    }
type ('dummyV0, 'dummyV1, 'dummyV2) st_equiv =
  | ST_VPropEquiv of Pulse_Typing_Env.env * Pulse_Syntax_Base.comp_st *
  Pulse_Syntax_Base.comp_st * Pulse_Syntax_Base.var * unit * unit * unit *
  unit * unit 
let uu___is_ST_VPropEquiv uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | ST_VPropEquiv _ -> true | _ -> false
type ('dummyV0, 'dummyV1, 'dummyV2, 'dummyV3, 'dummyV4) bind_comp =
  | Bind_comp of Pulse_Typing_Env.env * Pulse_Syntax_Base.var *
  Pulse_Syntax_Base.comp_st * Pulse_Syntax_Base.comp_st * unit *
  Pulse_Syntax_Base.var * unit 
  | Bind_comp_ghost_l of Pulse_Typing_Env.env * Pulse_Syntax_Base.var *
  Pulse_Syntax_Base.comp_st * Pulse_Syntax_Base.comp_st * (unit, unit)
  non_informative_c * unit * Pulse_Syntax_Base.var * unit 
  | Bind_comp_ghost_r of Pulse_Typing_Env.env * Pulse_Syntax_Base.var *
  Pulse_Syntax_Base.comp_st * Pulse_Syntax_Base.comp_st * (unit, unit)
  non_informative_c * unit * Pulse_Syntax_Base.var * unit 
let uu___is_Bind_comp uu___4 uu___3 uu___2 uu___1 uu___ uu___5 =
  match uu___5 with | Bind_comp _ -> true | _ -> false
let uu___is_Bind_comp_ghost_l uu___4 uu___3 uu___2 uu___1 uu___ uu___5 =
  match uu___5 with | Bind_comp_ghost_l _ -> true | _ -> false
let uu___is_Bind_comp_ghost_r uu___4 uu___3 uu___2 uu___1 uu___ uu___5 =
  match uu___5 with | Bind_comp_ghost_r _ -> true | _ -> false
type ('dummyV0, 'dummyV1, 'dummyV2) lift_comp =
  | Lift_STAtomic_ST of Pulse_Typing_Env.env * Pulse_Syntax_Base.comp_st 
  | Lift_STGhost_STAtomic of Pulse_Typing_Env.env * Pulse_Syntax_Base.comp_st
  * (unit, unit) non_informative_c 
let uu___is_Lift_STAtomic_ST uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | Lift_STAtomic_ST _ -> true | _ -> false
let uu___is_Lift_STGhost_STAtomic uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | Lift_STGhost_STAtomic _ -> true | _ -> false
let (wr : Pulse_Syntax_Base.st_term' -> Pulse_Syntax_Base.st_term) =
  fun t ->
    {
      Pulse_Syntax_Base.term1 = t;
      Pulse_Syntax_Base.range2 = FStar_Range.range_0
    }
type ('dummyV0, 'dummyV1) st_comp_typing =
  | STC of Pulse_Typing_Env.env * Pulse_Syntax_Base.st_comp *
  Pulse_Syntax_Base.var * unit * unit * unit 
let uu___is_STC uu___1 uu___ uu___2 =
  match uu___2 with | STC _ -> true | _ -> false
let (tr_binding :
  (Pulse_Syntax_Base.var * Pulse_Syntax_Base.typ) ->
    FStar_Reflection_V2_Data.binding)
  =
  fun vt ->
    let uu___ = vt in
    match uu___ with
    | (v, t) ->
        {
          FStar_Reflection_V2_Data.uniq1 = v;
          FStar_Reflection_V2_Data.sort3 = (Pulse_Elaborate_Pure.elab_term t);
          FStar_Reflection_V2_Data.ppname3 =
            (Pulse_Syntax_Base.ppname_default.Pulse_Syntax_Base.name)
        }
let (tr_bindings :
  (Pulse_Syntax_Base.var * Pulse_Syntax_Base.typ) Prims.list ->
    FStar_Reflection_V2_Data.binding Prims.list)
  = FStar_List_Tot_Base.map tr_binding
type ('dummyV0, 'dummyV1, 'dummyV2) comp_typing =
  | CT_Tot of Pulse_Typing_Env.env * Pulse_Syntax_Base.term *
  Pulse_Syntax_Base.universe * unit 
  | CT_ST of Pulse_Typing_Env.env * Pulse_Syntax_Base.st_comp * (unit, 
  unit) st_comp_typing 
  | CT_STAtomic of Pulse_Typing_Env.env * Pulse_Syntax_Base.term *
  Pulse_Syntax_Base.st_comp * unit * (unit, unit) st_comp_typing 
  | CT_STGhost of Pulse_Typing_Env.env * Pulse_Syntax_Base.term *
  Pulse_Syntax_Base.st_comp * unit * (unit, unit) st_comp_typing 
let uu___is_CT_Tot uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | CT_Tot _ -> true | _ -> false
let uu___is_CT_ST uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | CT_ST _ -> true | _ -> false
let uu___is_CT_STAtomic uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | CT_STAtomic _ -> true | _ -> false
let uu___is_CT_STGhost uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | CT_STGhost _ -> true | _ -> false
type ('g, 't) prop_validity =
  (unit, unit) FStar_Tactics_V2_Builtins.prop_validity_token
let (readback_binding :
  FStar_Reflection_V2_Data.binding -> Pulse_Typing_Env.binding) =
  fun b ->
    match Pulse_Readback.readback_ty b.FStar_Reflection_V2_Data.sort3 with
    | FStar_Pervasives_Native.Some sort ->
        ((b.FStar_Reflection_V2_Data.uniq1), sort)
    | FStar_Pervasives_Native.None ->
        let sort =
          {
            Pulse_Syntax_Base.t =
              (Pulse_Syntax_Base.Tm_FStar (b.FStar_Reflection_V2_Data.sort3));
            Pulse_Syntax_Base.range1 =
              (FStar_Reflection_V2_Builtins.range_of_term
                 b.FStar_Reflection_V2_Data.sort3)
          } in
        ((b.FStar_Reflection_V2_Data.uniq1), sort)
type ('dummyV0, 'dummyV1, 'dummyV2) st_typing =
  | T_Abs of Pulse_Typing_Env.env * Pulse_Syntax_Base.var *
  Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option *
  Pulse_Syntax_Base.binder * Pulse_Syntax_Base.universe *
  Pulse_Syntax_Base.st_term * Pulse_Syntax_Base.comp * unit * (unit, 
  unit, unit) st_typing 
  | T_STApp of Pulse_Typing_Env.env * Pulse_Syntax_Base.term *
  Pulse_Syntax_Base.term * Pulse_Syntax_Base.qualifier
  FStar_Pervasives_Native.option * Pulse_Syntax_Base.comp_st *
  Pulse_Syntax_Base.term * unit * unit 
  | T_Return of Pulse_Typing_Env.env * Pulse_Syntax_Base.ctag * Prims.bool *
  Pulse_Syntax_Base.universe * Pulse_Syntax_Base.term *
  Pulse_Syntax_Base.term * Pulse_Syntax_Base.term * Pulse_Syntax_Base.var *
  unit * unit * unit 
  | T_Lift of Pulse_Typing_Env.env * Pulse_Syntax_Base.st_term *
  Pulse_Syntax_Base.comp_st * Pulse_Syntax_Base.comp_st * (unit, unit, 
  unit) st_typing * (unit, unit, unit) lift_comp 
  | T_Bind of Pulse_Typing_Env.env * Pulse_Syntax_Base.st_term *
  Pulse_Syntax_Base.st_term * Pulse_Syntax_Base.comp_st *
  Pulse_Syntax_Base.comp_st * Pulse_Syntax_Base.binder *
  Pulse_Syntax_Base.var * Pulse_Syntax_Base.comp * (unit, unit, unit)
  st_typing * unit * (unit, unit, unit) st_typing * (unit, unit, unit, 
  unit, unit) bind_comp 
  | T_TotBind of Pulse_Typing_Env.env * Pulse_Syntax_Base.term *
  Pulse_Syntax_Base.st_term * Pulse_Syntax_Base.term *
  Pulse_Syntax_Base.comp_st * Pulse_Syntax_Base.var * unit * (unit, unit,
  unit) st_typing 
  | T_If of Pulse_Typing_Env.env * Pulse_Syntax_Base.term *
  Pulse_Syntax_Base.st_term * Pulse_Syntax_Base.st_term *
  Pulse_Syntax_Base.comp_st * Pulse_Syntax_Base.universe *
  Pulse_Syntax_Base.var * unit * (unit, unit, unit) st_typing * (unit, 
  unit, unit) st_typing * unit 
  | T_Match of Pulse_Typing_Env.env * Pulse_Syntax_Base.universe *
  Pulse_Syntax_Base.typ * Pulse_Syntax_Base.term * unit * unit *
  Pulse_Syntax_Base.comp_st * (Pulse_Syntax_Base.pattern *
  Pulse_Syntax_Base.st_term) Prims.list * (unit, unit, unit, unit, unit,
  unit) brs_typing * (unit, unit, unit, unit) pats_complete 
  | T_Frame of Pulse_Typing_Env.env * Pulse_Syntax_Base.st_term *
  Pulse_Syntax_Base.comp_st * Pulse_Syntax_Base.term * unit * (unit, 
  unit, unit) st_typing 
  | T_Equiv of Pulse_Typing_Env.env * Pulse_Syntax_Base.st_term *
  Pulse_Syntax_Base.comp * Pulse_Syntax_Base.comp * (unit, unit, unit)
  st_typing * (unit, unit, unit) st_equiv 
  | T_IntroPure of Pulse_Typing_Env.env * Pulse_Syntax_Base.term * unit *
  (unit, unit) prop_validity 
  | T_ElimExists of Pulse_Typing_Env.env * Pulse_Syntax_Base.universe *
  Pulse_Syntax_Base.term * Pulse_Syntax_Base.term * Pulse_Syntax_Base.var *
  unit * unit 
  | T_IntroExists of Pulse_Typing_Env.env * Pulse_Syntax_Base.universe *
  Pulse_Syntax_Base.binder * Pulse_Syntax_Base.term * Pulse_Syntax_Base.term
  * unit * unit * unit 
  | T_IntroExistsErased of Pulse_Typing_Env.env * Pulse_Syntax_Base.universe
  * Pulse_Syntax_Base.binder * Pulse_Syntax_Base.term *
  Pulse_Syntax_Base.term * unit * unit * unit 
  | T_While of Pulse_Typing_Env.env * Pulse_Syntax_Base.term *
  Pulse_Syntax_Base.st_term * Pulse_Syntax_Base.st_term * unit * (unit, 
  unit, unit) st_typing * (unit, unit, unit) st_typing 
  | T_Par of Pulse_Typing_Env.env * Pulse_Syntax_Base.st_term *
  Pulse_Syntax_Base.comp * Pulse_Syntax_Base.st_term * Pulse_Syntax_Base.comp
  * Pulse_Syntax_Base.var * (unit, unit, unit) comp_typing * (unit, unit,
  unit) comp_typing * (unit, unit, unit) st_typing * (unit, unit, unit)
  st_typing 
  | T_WithLocal of Pulse_Typing_Env.env * Pulse_Syntax_Base.term *
  Pulse_Syntax_Base.st_term * Pulse_Syntax_Base.term * Pulse_Syntax_Base.comp
  * Pulse_Syntax_Base.var * unit * unit * (unit, unit, unit) comp_typing *
  (unit, unit, unit) st_typing 
  | T_Rewrite of Pulse_Typing_Env.env * Pulse_Syntax_Base.vprop *
  Pulse_Syntax_Base.vprop * unit * unit 
  | T_Admit of Pulse_Typing_Env.env * Pulse_Syntax_Base.st_comp *
  Pulse_Syntax_Base.ctag * (unit, unit) st_comp_typing 
and ('dummyV0, 'dummyV1, 'dummyV2, 'dummyV3) pats_complete =
  | PC_Elab of Pulse_Typing_Env.env * Pulse_Syntax_Base.term *
  Pulse_Syntax_Base.typ * FStar_Reflection_V2_Data.pattern Prims.list *
  FStar_Reflection_V2_Data.binding Prims.list Prims.list * (unit, unit, 
  unit, unit, unit) FStar_Reflection_Typing.match_is_complete 
and ('g, 'scuu, 'scuty, 'sc, 'dummyV0, 'dummyV1) brs_typing =
  | TBRS_0 of Pulse_Syntax_Base.comp_st 
  | TBRS_1 of Pulse_Syntax_Base.comp_st * Pulse_Syntax_Base.pattern *
  Pulse_Syntax_Base.st_term * (unit, unit, unit, unit, unit, unit, unit)
  br_typing * Pulse_Syntax_Base.branch Prims.list * (unit, unit, unit, 
  unit, unit, unit) brs_typing 
and ('dummyV0, 'dummyV1, 'dummyV2, 'dummyV3, 'dummyV4, 'dummyV5,
  'dummyV6) br_typing =
  | TBR of Pulse_Typing_Env.env * Pulse_Syntax_Base.universe *
  Pulse_Syntax_Base.typ * Pulse_Syntax_Base.term * Pulse_Syntax_Base.comp_st
  * Pulse_Syntax_Base.pattern * Pulse_Syntax_Base.st_term *
  FStar_Reflection_V2_Data.binding Prims.list * unit * unit * unit *
  Pulse_Syntax_Base.var * (unit, unit, unit) st_typing 
let uu___is_T_Abs uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_Abs _ -> true | _ -> false
let uu___is_T_STApp uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_STApp _ -> true | _ -> false
let uu___is_T_Return uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_Return _ -> true | _ -> false
let uu___is_T_Lift uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_Lift _ -> true | _ -> false
let uu___is_T_Bind uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_Bind _ -> true | _ -> false
let uu___is_T_TotBind uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_TotBind _ -> true | _ -> false
let uu___is_T_If uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_If _ -> true | _ -> false
let uu___is_T_Match uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_Match _ -> true | _ -> false
let uu___is_T_Frame uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_Frame _ -> true | _ -> false
let uu___is_T_Equiv uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_Equiv _ -> true | _ -> false
let uu___is_T_IntroPure uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_IntroPure _ -> true | _ -> false
let uu___is_T_ElimExists uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_ElimExists _ -> true | _ -> false
let uu___is_T_IntroExists uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_IntroExists _ -> true | _ -> false
let uu___is_T_IntroExistsErased uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_IntroExistsErased _ -> true | _ -> false
let uu___is_T_While uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_While _ -> true | _ -> false
let uu___is_T_Par uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_Par _ -> true | _ -> false
let uu___is_T_WithLocal uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_WithLocal _ -> true | _ -> false
let uu___is_T_Rewrite uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_Rewrite _ -> true | _ -> false
let uu___is_T_Admit uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | T_Admit _ -> true | _ -> false
let uu___is_PC_Elab uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | PC_Elab _ -> true | _ -> false
let uu___is_TBRS_0 uu___5 uu___4 uu___3 uu___2 uu___1 uu___ uu___6 =
  match uu___6 with | TBRS_0 _ -> true | _ -> false
let uu___is_TBRS_1 uu___5 uu___4 uu___3 uu___2 uu___1 uu___ uu___6 =
  match uu___6 with | TBRS_1 _ -> true | _ -> false
let uu___is_TBR uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___ uu___7 =
  match uu___7 with | TBR _ -> true | _ -> false




type post_hint_t =
  {
  g: Pulse_Typing_Env.env ;
  ctag_hint: Pulse_Syntax_Base.ctag FStar_Pervasives_Native.option ;
  ret_ty: Pulse_Syntax_Base.term ;
  u: Pulse_Syntax_Base.universe ;
  ty_typing: unit ;
  post: Pulse_Syntax_Base.term ;
  post_typing: unit }
let (__proj__Mkpost_hint_t__item__g : post_hint_t -> Pulse_Typing_Env.env) =
  fun projectee ->
    match projectee with
    | { g; ctag_hint; ret_ty; u; ty_typing; post; post_typing;_} -> g
let (__proj__Mkpost_hint_t__item__ctag_hint :
  post_hint_t -> Pulse_Syntax_Base.ctag FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { g; ctag_hint; ret_ty; u; ty_typing; post; post_typing;_} -> ctag_hint
let (__proj__Mkpost_hint_t__item__ret_ty :
  post_hint_t -> Pulse_Syntax_Base.term) =
  fun projectee ->
    match projectee with
    | { g; ctag_hint; ret_ty; u; ty_typing; post; post_typing;_} -> ret_ty
let (__proj__Mkpost_hint_t__item__u :
  post_hint_t -> Pulse_Syntax_Base.universe) =
  fun projectee ->
    match projectee with
    | { g; ctag_hint; ret_ty; u; ty_typing; post; post_typing;_} -> u

let (__proj__Mkpost_hint_t__item__post :
  post_hint_t -> Pulse_Syntax_Base.term) =
  fun projectee ->
    match projectee with
    | { g; ctag_hint; ret_ty; u; ty_typing; post; post_typing;_} -> post
type ('g, 'p) post_hint_for_env_p = unit
type 'g post_hint_for_env = post_hint_t
type 'g post_hint_opt = post_hint_t FStar_Pervasives_Native.option
type ('g, 'p, 'x) post_hint_typing_t =
  {
  ty_typing1: unit ;
  post_typing1: unit }


type ('x, 'g, 'vars) fresh_wrt = unit
let (post_hint_typing :
  Pulse_Typing_Env.env ->
    unit post_hint_for_env ->
      Pulse_Syntax_Base.var -> (unit, unit, unit) post_hint_typing_t)
  = fun g -> fun p -> fun x -> { ty_typing1 = (); post_typing1 = () }
type ('c, 'postuhint) comp_post_matches_hint = Obj.t