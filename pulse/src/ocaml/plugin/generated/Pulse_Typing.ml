open Prims
let (tm_unit : Pulse_Syntax.term) =
  Pulse_Syntax.Tm_FVar (Pulse_Syntax.as_fv Pulse_Reflection_Util.unit_lid)
let (tm_bool : Pulse_Syntax.term) =
  Pulse_Syntax.Tm_FVar (Pulse_Syntax.as_fv Pulse_Reflection_Util.bool_lid)
let (tm_true : Pulse_Syntax.term) =
  Pulse_Syntax.Tm_Constant (Pulse_Syntax.Bool true)
let (tm_false : Pulse_Syntax.term) =
  Pulse_Syntax.Tm_Constant (Pulse_Syntax.Bool false)
let (mk_erased :
  Pulse_Syntax.universe -> Pulse_Syntax.term -> Pulse_Syntax.term) =
  fun u ->
    fun t ->
      let hd =
        Pulse_Syntax.Tm_UInst
          ((Pulse_Syntax.as_fv Pulse_Reflection_Util.erased_lid), [u]) in
      Pulse_Syntax.Tm_PureApp (hd, FStar_Pervasives_Native.None, t)
let (mk_reveal :
  Pulse_Syntax.universe ->
    Pulse_Syntax.term -> Pulse_Syntax.term -> Pulse_Syntax.term)
  =
  fun u ->
    fun t ->
      fun e ->
        let hd =
          Pulse_Syntax.Tm_UInst
            ((Pulse_Syntax.as_fv Pulse_Reflection_Util.reveal_lid), [u]) in
        let hd1 =
          Pulse_Syntax.Tm_PureApp
            (hd, (FStar_Pervasives_Native.Some Pulse_Syntax.Implicit), t) in
        Pulse_Syntax.Tm_PureApp (hd1, FStar_Pervasives_Native.None, e)
let (mk_hide :
  Pulse_Syntax.universe ->
    Pulse_Syntax.term -> Pulse_Syntax.term -> Pulse_Syntax.term)
  =
  fun u ->
    fun t ->
      fun e ->
        let hd = Pulse_Syntax.Tm_UInst (Pulse_Reflection_Util.hide_lid, [u]) in
        let hd1 =
          Pulse_Syntax.Tm_PureApp
            (hd, (FStar_Pervasives_Native.Some Pulse_Syntax.Implicit), t) in
        Pulse_Syntax.Tm_PureApp (hd1, FStar_Pervasives_Native.None, e)
let (mk_eq2 :
  Pulse_Syntax.universe ->
    Pulse_Syntax.term ->
      Pulse_Syntax.term -> Pulse_Syntax.term -> Pulse_Syntax.term)
  =
  fun u ->
    fun t ->
      fun e0 ->
        fun e1 ->
          Pulse_Syntax.Tm_PureApp
            ((Pulse_Syntax.Tm_PureApp
                ((Pulse_Syntax.Tm_PureApp
                    ((Pulse_Syntax.Tm_UInst
                        ((Pulse_Syntax.as_fv FStar_Reflection_Const.eq2_qn),
                          [u])),
                      (FStar_Pervasives_Native.Some Pulse_Syntax.Implicit),
                      t)), FStar_Pervasives_Native.None, e0)),
              FStar_Pervasives_Native.None, e1)
let (mk_eq2_prop :
  Pulse_Syntax.universe ->
    Pulse_Syntax.term ->
      Pulse_Syntax.term -> Pulse_Syntax.term -> Pulse_Syntax.term)
  =
  fun u ->
    fun t ->
      fun e0 ->
        fun e1 ->
          Pulse_Syntax.Tm_PureApp
            ((Pulse_Syntax.Tm_PureApp
                ((Pulse_Syntax.Tm_PureApp
                    ((Pulse_Syntax.Tm_UInst
                        ((Pulse_Syntax.as_fv
                            (Pulse_Reflection_Util.mk_steel_wrapper_lid
                               "eq2_prop")), [u])),
                      (FStar_Pervasives_Native.Some Pulse_Syntax.Implicit),
                      t)), FStar_Pervasives_Native.None, e0)),
              FStar_Pervasives_Native.None, e1)
let (mk_vprop_eq :
  Pulse_Syntax.term -> Pulse_Syntax.term -> Pulse_Syntax.term) =
  fun e0 ->
    fun e1 ->
      mk_eq2 (Pulse_Syntax.U_succ (Pulse_Syntax.U_succ Pulse_Syntax.U_zero))
        Pulse_Syntax.Tm_VProp e0 e1
let (mk_ref : Pulse_Syntax.term -> Pulse_Syntax.term) =
  fun t ->
    Pulse_Syntax.Tm_PureApp
      ((Pulse_Syntax.Tm_FVar
          (Pulse_Syntax.as_fv Pulse_Reflection_Util.ref_lid)),
        FStar_Pervasives_Native.None, t)
let (mk_pts_to :
  Pulse_Syntax.term ->
    Pulse_Syntax.term -> Pulse_Syntax.term -> Pulse_Syntax.term)
  =
  fun ty ->
    fun r ->
      fun v ->
        let t =
          Pulse_Syntax.Tm_FVar
            (Pulse_Syntax.as_fv Pulse_Reflection_Util.pts_to_lid) in
        let t1 =
          Pulse_Syntax.Tm_PureApp
            (t, (FStar_Pervasives_Native.Some Pulse_Syntax.Implicit), ty) in
        let t2 =
          Pulse_Syntax.Tm_PureApp (t1, FStar_Pervasives_Native.None, r) in
        let t3 =
          Pulse_Syntax.Tm_PureApp
            (t2, FStar_Pervasives_Native.None,
              (Pulse_Syntax.Tm_FVar
                 (Pulse_Syntax.as_fv Pulse_Reflection_Util.full_perm_lid))) in
        Pulse_Syntax.Tm_PureApp (t3, FStar_Pervasives_Native.None, v)
let (comp_return :
  Pulse_Syntax.ctag ->
    Prims.bool ->
      Pulse_Syntax.universe ->
        Pulse_Syntax.term ->
          Pulse_Syntax.term ->
            Pulse_Syntax.term -> Pulse_Syntax.var -> Pulse_Syntax.comp)
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
                      Pulse_Syntax.open_term' post (Pulse_Syntax.null_var x)
                        Prims.int_zero in
                    let post2 =
                      Pulse_Syntax.Tm_Star
                        (post1,
                          (Pulse_Syntax.Tm_Pure
                             (mk_eq2_prop u t (Pulse_Syntax.null_var x) e))) in
                    Pulse_Syntax.close_term post2 x
                  else post in
                match c with
                | Pulse_Syntax.STT ->
                    Pulse_Syntax.C_ST
                      {
                        Pulse_Syntax.u = u;
                        Pulse_Syntax.res = t;
                        Pulse_Syntax.pre =
                          (Pulse_Syntax.open_term' post e Prims.int_zero);
                        Pulse_Syntax.post = post_maybe_eq
                      }
                | Pulse_Syntax.STT_Atomic ->
                    Pulse_Syntax.C_STAtomic
                      (Pulse_Syntax.Tm_EmpInames,
                        {
                          Pulse_Syntax.u = u;
                          Pulse_Syntax.res = t;
                          Pulse_Syntax.pre =
                            (Pulse_Syntax.open_term' post e Prims.int_zero);
                          Pulse_Syntax.post = post_maybe_eq
                        })
                | Pulse_Syntax.STT_Ghost ->
                    Pulse_Syntax.C_STGhost
                      (Pulse_Syntax.Tm_EmpInames,
                        {
                          Pulse_Syntax.u = u;
                          Pulse_Syntax.res = t;
                          Pulse_Syntax.pre =
                            (Pulse_Syntax.open_term' post e Prims.int_zero);
                          Pulse_Syntax.post = post_maybe_eq
                        })
type eqn = (Pulse_Syntax.term * Pulse_Syntax.term * Pulse_Syntax.term)
type binding = (Pulse_Syntax.term, eqn) FStar_Pervasives.either
type env = (Pulse_Syntax.var * binding) Prims.list
let (elab_eqn : eqn -> FStar_Reflection_Types.term) =
  fun e ->
    let uu___ = e in
    match uu___ with
    | (ty, l, r) ->
        let ty1 = Pulse_Elaborate_Pure.elab_term ty in
        let l1 = Pulse_Elaborate_Pure.elab_term l in
        let r1 = Pulse_Elaborate_Pure.elab_term r in
        FStar_Reflection_Typing.eq2
          (FStar_Reflection_Builtins.pack_universe
             FStar_Reflection_Data.Uv_Zero) ty1 l1 r1
let (elab_binding : binding -> FStar_Reflection_Types.term) =
  fun b ->
    match b with
    | FStar_Pervasives.Inl t -> Pulse_Elaborate_Pure.elab_term t
    | FStar_Pervasives.Inr eqn1 -> elab_eqn eqn1
let (extend_env_l :
  FStar_Reflection_Types.env -> env -> FStar_Reflection_Types.env) =
  fun f ->
    fun g ->
      FStar_List_Tot_Base.fold_right
        (fun uu___ ->
           fun g1 ->
             match uu___ with
             | (x, b) ->
                 let t = elab_binding b in
                 FStar_Reflection_Typing.extend_env g1 x t) g f
let rec lookup :
  'a .
    (Pulse_Syntax.var * 'a) Prims.list ->
      Pulse_Syntax.var -> 'a FStar_Pervasives_Native.option
  =
  fun e ->
    fun x ->
      match e with
      | [] -> FStar_Pervasives_Native.None
      | (y, v)::tl ->
          if x = y then FStar_Pervasives_Native.Some v else lookup tl x
let (lookup_ty :
  env -> Pulse_Syntax.var -> Pulse_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e ->
    fun x ->
      match lookup e x with
      | FStar_Pervasives_Native.Some (FStar_Pervasives.Inl t) ->
          FStar_Pervasives_Native.Some t
      | uu___ -> FStar_Pervasives_Native.None
let (max : Prims.nat -> Prims.nat -> Prims.nat) =
  fun n1 -> fun n2 -> if n1 < n2 then n2 else n1
let rec fresh : 'a . (Pulse_Syntax.var * 'a) Prims.list -> Pulse_Syntax.var =
  fun e ->
    match e with
    | [] -> Prims.int_zero
    | (y, uu___)::tl -> (max (fresh tl) y) + Prims.int_one
    | uu___::tl -> fresh tl
let (add_frame :
  Pulse_Syntax.comp_st -> Pulse_Syntax.term -> Pulse_Syntax.comp_st) =
  fun s ->
    fun frame ->
      let add_frame_s s1 =
        {
          Pulse_Syntax.u = (s1.Pulse_Syntax.u);
          Pulse_Syntax.res = (s1.Pulse_Syntax.res);
          Pulse_Syntax.pre =
            (Pulse_Syntax.Tm_Star ((s1.Pulse_Syntax.pre), frame));
          Pulse_Syntax.post =
            (Pulse_Syntax.Tm_Star ((s1.Pulse_Syntax.post), frame))
        } in
      match s with
      | Pulse_Syntax.C_ST s1 -> Pulse_Syntax.C_ST (add_frame_s s1)
      | Pulse_Syntax.C_STAtomic (inames, s1) ->
          Pulse_Syntax.C_STAtomic (inames, (add_frame_s s1))
      | Pulse_Syntax.C_STGhost (inames, s1) ->
          Pulse_Syntax.C_STGhost (inames, (add_frame_s s1))
type ('c1, 'c2) bind_comp_compatible = Obj.t
type ('x, 'c1, 'c2) bind_comp_pre = unit
let (bind_comp_out :
  Pulse_Syntax.comp_st -> Pulse_Syntax.comp_st -> Pulse_Syntax.comp_st) =
  fun c1 ->
    fun c2 ->
      let s =
        {
          Pulse_Syntax.u = (Pulse_Syntax.comp_u c2);
          Pulse_Syntax.res = (Pulse_Syntax.comp_res c2);
          Pulse_Syntax.pre = (Pulse_Syntax.comp_pre c1);
          Pulse_Syntax.post = (Pulse_Syntax.comp_post c2)
        } in
      match (c1, c2) with
      | (Pulse_Syntax.C_STGhost (inames, uu___), Pulse_Syntax.C_STGhost
         (uu___1, uu___2)) -> Pulse_Syntax.C_STGhost (inames, s)
      | (Pulse_Syntax.C_ST uu___, Pulse_Syntax.C_ST uu___1) ->
          Pulse_Syntax.C_ST s
type ('c1, 'c2) bind_comp_ghost_l_compatible = Obj.t
type ('x, 'c1, 'c2) bind_comp_ghost_l_pre = unit
let (bind_comp_ghost_l_out :
  Pulse_Syntax.comp_st -> Pulse_Syntax.comp_st -> Pulse_Syntax.comp_st) =
  fun c1 ->
    fun c2 ->
      let s =
        {
          Pulse_Syntax.u = (Pulse_Syntax.comp_u c2);
          Pulse_Syntax.res = (Pulse_Syntax.comp_res c2);
          Pulse_Syntax.pre = (Pulse_Syntax.comp_pre c1);
          Pulse_Syntax.post = (Pulse_Syntax.comp_post c2)
        } in
      match (c1, c2) with
      | (Pulse_Syntax.C_STGhost (inames, uu___), Pulse_Syntax.C_STAtomic
         (uu___1, uu___2)) -> Pulse_Syntax.C_STAtomic (inames, s)
type ('c1, 'c2) bind_comp_ghost_r_compatible = Obj.t
type ('x, 'c1, 'c2) bind_comp_ghost_r_pre = unit
let (bind_comp_ghost_r_out :
  Pulse_Syntax.comp_st -> Pulse_Syntax.comp_st -> Pulse_Syntax.comp_st) =
  fun c1 ->
    fun c2 ->
      let s =
        {
          Pulse_Syntax.u = (Pulse_Syntax.comp_u c2);
          Pulse_Syntax.res = (Pulse_Syntax.comp_res c2);
          Pulse_Syntax.pre = (Pulse_Syntax.comp_pre c1);
          Pulse_Syntax.post = (Pulse_Syntax.comp_post c2)
        } in
      match (c1, c2) with
      | (Pulse_Syntax.C_STAtomic (inames, uu___), Pulse_Syntax.C_STGhost
         (uu___1, uu___2)) -> Pulse_Syntax.C_STAtomic (inames, s)
type ('c1, 'c2) st_equiv_pre = unit
let (non_informative_witness_t :
  Pulse_Syntax.universe -> Pulse_Syntax.term -> Pulse_Syntax.term) =
  fun u ->
    fun t ->
      Pulse_Syntax.Tm_PureApp
        ((Pulse_Syntax.Tm_UInst
            ((Pulse_Syntax.as_fv
                Pulse_Reflection_Util.non_informative_witness_lid), [u])),
          FStar_Pervasives_Native.None, t)
let (elim_exists_post :
  Pulse_Syntax.universe ->
    Pulse_Syntax.term ->
      Pulse_Syntax.term -> Pulse_Syntax.var -> Pulse_Syntax.term)
  =
  fun u ->
    fun t ->
      fun p ->
        fun x ->
          let x_tm = Pulse_Syntax.null_var x in
          let p1 =
            Pulse_Syntax.open_term' p (mk_reveal u t x_tm) Prims.int_zero in
          Pulse_Syntax.close_term p1 x
let (comp_elim_exists :
  Pulse_Syntax.universe ->
    Pulse_Syntax.term ->
      Pulse_Syntax.term -> Pulse_Syntax.var -> Pulse_Syntax.comp)
  =
  fun u ->
    fun t ->
      fun p ->
        fun x ->
          Pulse_Syntax.C_STGhost
            (Pulse_Syntax.Tm_EmpInames,
              {
                Pulse_Syntax.u = u;
                Pulse_Syntax.res = (mk_erased u t);
                Pulse_Syntax.pre =
                  (Pulse_Syntax.Tm_ExistsSL
                     (u, t, p, Pulse_Syntax.should_elim_true));
                Pulse_Syntax.post = (elim_exists_post u t p x)
              })
let (comp_intro_exists :
  Pulse_Syntax.universe ->
    Pulse_Syntax.term ->
      Pulse_Syntax.term -> Pulse_Syntax.term -> Pulse_Syntax.comp)
  =
  fun u ->
    fun t ->
      fun p ->
        fun e ->
          Pulse_Syntax.C_STGhost
            (Pulse_Syntax.Tm_EmpInames,
              {
                Pulse_Syntax.u = Pulse_Syntax.U_zero;
                Pulse_Syntax.res = tm_unit;
                Pulse_Syntax.pre =
                  (Pulse_Syntax.open_term' p e Prims.int_zero);
                Pulse_Syntax.post =
                  (Pulse_Syntax.Tm_ExistsSL
                     (u, t, p, Pulse_Syntax.should_elim_false))
              })
let (comp_intro_exists_erased :
  Pulse_Syntax.universe ->
    Pulse_Syntax.term ->
      Pulse_Syntax.term -> Pulse_Syntax.term -> Pulse_Syntax.comp)
  =
  fun u ->
    fun t ->
      fun p ->
        fun e ->
          Pulse_Syntax.C_STGhost
            (Pulse_Syntax.Tm_EmpInames,
              {
                Pulse_Syntax.u = Pulse_Syntax.U_zero;
                Pulse_Syntax.res = tm_unit;
                Pulse_Syntax.pre =
                  (Pulse_Syntax.open_term' p (mk_reveal u t e) Prims.int_zero);
                Pulse_Syntax.post =
                  (Pulse_Syntax.Tm_ExistsSL
                     (u, t, p, Pulse_Syntax.should_elim_false))
              })
let (comp_while_cond : Pulse_Syntax.term -> Pulse_Syntax.comp) =
  fun inv ->
    Pulse_Syntax.C_ST
      {
        Pulse_Syntax.u = Pulse_Syntax.U_zero;
        Pulse_Syntax.res = tm_bool;
        Pulse_Syntax.pre =
          (Pulse_Syntax.Tm_ExistsSL
             (Pulse_Syntax.U_zero, tm_bool, inv,
               Pulse_Syntax.should_elim_false));
        Pulse_Syntax.post = inv
      }
let (comp_while_body : Pulse_Syntax.term -> Pulse_Syntax.comp) =
  fun inv ->
    Pulse_Syntax.C_ST
      {
        Pulse_Syntax.u = Pulse_Syntax.U_zero;
        Pulse_Syntax.res = tm_unit;
        Pulse_Syntax.pre =
          (Pulse_Syntax.open_term' inv tm_true Prims.int_zero);
        Pulse_Syntax.post =
          (Pulse_Syntax.Tm_ExistsSL
             (Pulse_Syntax.U_zero, tm_bool, inv,
               Pulse_Syntax.should_elim_true))
      }
let (comp_while : Pulse_Syntax.term -> Pulse_Syntax.comp) =
  fun inv ->
    Pulse_Syntax.C_ST
      {
        Pulse_Syntax.u = Pulse_Syntax.U_zero;
        Pulse_Syntax.res = tm_unit;
        Pulse_Syntax.pre =
          (Pulse_Syntax.Tm_ExistsSL
             (Pulse_Syntax.U_zero, tm_bool, inv,
               Pulse_Syntax.should_elim_true));
        Pulse_Syntax.post =
          (Pulse_Syntax.open_term' inv tm_false Prims.int_zero)
      }
let (mk_tuple2 :
  Pulse_Syntax.universe ->
    Pulse_Syntax.universe ->
      Pulse_Syntax.term -> Pulse_Syntax.term -> Pulse_Syntax.term)
  =
  fun u1 ->
    fun u2 ->
      fun t1 ->
        fun t2 ->
          Pulse_Syntax.Tm_PureApp
            ((Pulse_Syntax.Tm_PureApp
                ((Pulse_Syntax.Tm_UInst
                    ((Pulse_Syntax.as_fv Pulse_Reflection_Util.tuple2_lid),
                      [u1; u2])), FStar_Pervasives_Native.None, t1)),
              FStar_Pervasives_Native.None, t2)
let (mk_fst :
  Pulse_Syntax.universe ->
    Pulse_Syntax.universe ->
      Pulse_Syntax.term ->
        Pulse_Syntax.term -> Pulse_Syntax.term -> Pulse_Syntax.term)
  =
  fun u1 ->
    fun u2 ->
      fun a1 ->
        fun a2 ->
          fun e ->
            Pulse_Syntax.Tm_PureApp
              ((Pulse_Syntax.Tm_PureApp
                  ((Pulse_Syntax.Tm_PureApp
                      ((Pulse_Syntax.Tm_UInst
                          ((Pulse_Syntax.as_fv Pulse_Reflection_Util.fst_lid),
                            [u1; u2])),
                        (FStar_Pervasives_Native.Some Pulse_Syntax.Implicit),
                        a1)),
                    (FStar_Pervasives_Native.Some Pulse_Syntax.Implicit), a2)),
                FStar_Pervasives_Native.None, e)
let (mk_snd :
  Pulse_Syntax.universe ->
    Pulse_Syntax.universe ->
      Pulse_Syntax.term ->
        Pulse_Syntax.term -> Pulse_Syntax.term -> Pulse_Syntax.term)
  =
  fun u1 ->
    fun u2 ->
      fun a1 ->
        fun a2 ->
          fun e ->
            Pulse_Syntax.Tm_PureApp
              ((Pulse_Syntax.Tm_PureApp
                  ((Pulse_Syntax.Tm_PureApp
                      ((Pulse_Syntax.Tm_UInst
                          ((Pulse_Syntax.as_fv Pulse_Reflection_Util.snd_lid),
                            [u1; u2])),
                        (FStar_Pervasives_Native.Some Pulse_Syntax.Implicit),
                        a1)),
                    (FStar_Pervasives_Native.Some Pulse_Syntax.Implicit), a2)),
                FStar_Pervasives_Native.None, e)
let (par_post :
  Pulse_Syntax.universe ->
    Pulse_Syntax.universe ->
      Pulse_Syntax.term ->
        Pulse_Syntax.term ->
          Pulse_Syntax.term ->
            Pulse_Syntax.term -> Pulse_Syntax.var -> Pulse_Syntax.term)
  =
  fun uL ->
    fun uR ->
      fun aL ->
        fun aR ->
          fun postL ->
            fun postR ->
              fun x ->
                let x_tm = Pulse_Syntax.term_of_var x in
                let postL1 =
                  Pulse_Syntax.open_term' postL (mk_fst uL uR aL aR x_tm)
                    Prims.int_zero in
                let postR1 =
                  Pulse_Syntax.open_term' postR (mk_snd uL uR aL aR x_tm)
                    Prims.int_zero in
                let post = Pulse_Syntax.Tm_Star (postL1, postR1) in
                Pulse_Syntax.close_term post x
let (comp_par :
  Pulse_Syntax.comp ->
    Pulse_Syntax.comp -> Pulse_Syntax.var -> Pulse_Syntax.comp)
  =
  fun cL ->
    fun cR ->
      fun x ->
        let uL = Pulse_Syntax.comp_u cL in
        let uR = Pulse_Syntax.comp_u cR in
        let aL = Pulse_Syntax.comp_res cL in
        let aR = Pulse_Syntax.comp_res cR in
        let post =
          par_post uL uR aL aR (Pulse_Syntax.comp_post cL)
            (Pulse_Syntax.comp_post cR) x in
        Pulse_Syntax.C_ST
          {
            Pulse_Syntax.u = uL;
            Pulse_Syntax.res = (mk_tuple2 uL uR aL aR);
            Pulse_Syntax.pre =
              (Pulse_Syntax.Tm_Star
                 ((Pulse_Syntax.comp_pre cL), (Pulse_Syntax.comp_pre cR)));
            Pulse_Syntax.post = post
          }
let (comp_withlocal_body_pre :
  Pulse_Syntax.vprop ->
    Pulse_Syntax.term ->
      Pulse_Syntax.term -> Pulse_Syntax.term -> Pulse_Syntax.vprop)
  =
  fun pre ->
    fun init_t ->
      fun r ->
        fun init -> Pulse_Syntax.Tm_Star (pre, (mk_pts_to init_t r init))
let (comp_withlocal_body_post :
  Pulse_Syntax.term ->
    Pulse_Syntax.term -> Pulse_Syntax.term -> Pulse_Syntax.term)
  =
  fun post ->
    fun init_t ->
      fun r ->
        Pulse_Syntax.Tm_Star
          (post,
            (Pulse_Syntax.Tm_ExistsSL
               (Pulse_Syntax.U_zero, init_t,
                 (mk_pts_to init_t r (Pulse_Syntax.null_bvar Prims.int_zero)),
                 Pulse_Syntax.should_elim_false)))
let (comp_withlocal_body :
  Pulse_Syntax.var ->
    Pulse_Syntax.term ->
      Pulse_Syntax.term -> Pulse_Syntax.comp -> Pulse_Syntax.comp)
  =
  fun r ->
    fun init_t ->
      fun init ->
        fun c ->
          let r1 = Pulse_Syntax.null_var r in
          Pulse_Syntax.C_ST
            {
              Pulse_Syntax.u = (Pulse_Syntax.comp_u c);
              Pulse_Syntax.res = (Pulse_Syntax.comp_res c);
              Pulse_Syntax.pre =
                (comp_withlocal_body_pre (Pulse_Syntax.comp_pre c) init_t r1
                   init);
              Pulse_Syntax.post =
                (comp_withlocal_body_post (Pulse_Syntax.comp_post c) init_t
                   r1)
            }
let (comp_rewrite :
  Pulse_Syntax.vprop -> Pulse_Syntax.vprop -> Pulse_Syntax.comp) =
  fun p ->
    fun q ->
      Pulse_Syntax.C_STGhost
        (Pulse_Syntax.Tm_EmpInames,
          {
            Pulse_Syntax.u = Pulse_Syntax.U_zero;
            Pulse_Syntax.res = tm_unit;
            Pulse_Syntax.pre = p;
            Pulse_Syntax.post = q
          })
let (comp_admit :
  Pulse_Syntax.ctag -> Pulse_Syntax.st_comp -> Pulse_Syntax.comp) =
  fun c ->
    fun s ->
      match c with
      | Pulse_Syntax.STT -> Pulse_Syntax.C_ST s
      | Pulse_Syntax.STT_Atomic ->
          Pulse_Syntax.C_STAtomic (Pulse_Syntax.Tm_EmpInames, s)
      | Pulse_Syntax.STT_Ghost ->
          Pulse_Syntax.C_STGhost (Pulse_Syntax.Tm_EmpInames, s)
type ('f, 'g, 'e, 't) typing =
  (unit, unit, unit) FStar_Reflection_Typing.typing
type ('f, 'g, 'e, 't) tot_typing = unit
type ('f, 'g, 't, 'u) universe_of = unit
type ('f, 'g, 'u, 't) non_informative_t =
  (Pulse_Syntax.term, unit) Prims.dtuple2
type ('f, 'g, 'c) non_informative_c =
  (unit, unit, unit, unit) non_informative_t
let (as_binder : Pulse_Syntax.term -> Pulse_Syntax.binder) =
  fun t ->
    {
      Pulse_Syntax.binder_ty = t;
      Pulse_Syntax.binder_ppname = FStar_Reflection_Typing.pp_name_default
    }
type ('f, 'dummyV0, 'dummyV1, 'dummyV2) st_equiv =
  | ST_VPropEquiv of env * Pulse_Syntax.comp_st * Pulse_Syntax.comp_st *
  Pulse_Syntax.var * unit * unit * unit * unit * unit 
let uu___is_ST_VPropEquiv uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | ST_VPropEquiv _ -> true | _ -> false
type ('f, 'dummyV0, 'dummyV1, 'dummyV2, 'dummyV3, 'dummyV4) bind_comp =
  | Bind_comp of env * Pulse_Syntax.var * Pulse_Syntax.comp_st *
  Pulse_Syntax.comp_st * unit * Pulse_Syntax.var * unit 
  | Bind_comp_ghost_l of env * Pulse_Syntax.var * Pulse_Syntax.comp_st *
  Pulse_Syntax.comp_st * (unit, unit, unit) non_informative_c * unit *
  Pulse_Syntax.var * unit 
  | Bind_comp_ghost_r of env * Pulse_Syntax.var * Pulse_Syntax.comp_st *
  Pulse_Syntax.comp_st * (unit, unit, unit) non_informative_c * unit *
  Pulse_Syntax.var * unit 
let uu___is_Bind_comp uu___5 uu___4 uu___3 uu___2 uu___1 uu___ uu___6 =
  match uu___6 with | Bind_comp _ -> true | _ -> false
let uu___is_Bind_comp_ghost_l uu___5 uu___4 uu___3 uu___2 uu___1 uu___ uu___6
  = match uu___6 with | Bind_comp_ghost_l _ -> true | _ -> false
let uu___is_Bind_comp_ghost_r uu___5 uu___4 uu___3 uu___2 uu___1 uu___ uu___6
  = match uu___6 with | Bind_comp_ghost_r _ -> true | _ -> false
type ('f, 'dummyV0, 'dummyV1, 'dummyV2) lift_comp =
  | Lift_STAtomic_ST of env * Pulse_Syntax.comp_st 
  | Lift_STGhost_STAtomic of env * Pulse_Syntax.comp_st * (unit, unit, 
  unit) non_informative_c 
let uu___is_Lift_STAtomic_ST uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | Lift_STAtomic_ST _ -> true | _ -> false
let uu___is_Lift_STGhost_STAtomic uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | Lift_STGhost_STAtomic _ -> true | _ -> false
type ('f, 'dummyV0, 'dummyV1) st_comp_typing =
  | STC of env * Pulse_Syntax.st_comp * Pulse_Syntax.var * unit * unit * unit 
and ('f, 'dummyV0, 'dummyV1, 'dummyV2) comp_typing =
  | CT_Tot of env * Pulse_Syntax.term * Pulse_Syntax.universe * unit 
  | CT_ST of env * Pulse_Syntax.st_comp * (unit, unit, unit) st_comp_typing 
  | CT_STAtomic of env * Pulse_Syntax.term * Pulse_Syntax.st_comp * unit *
  (unit, unit, unit) st_comp_typing 
  | CT_STGhost of env * Pulse_Syntax.term * Pulse_Syntax.st_comp * unit *
  (unit, unit, unit) st_comp_typing 
and ('f, 'dummyV0, 'dummyV1, 'dummyV2) st_typing =
  | T_Abs of env * Pulse_Syntax.var * Pulse_Syntax.qualifier
  FStar_Pervasives_Native.option * Pulse_Syntax.term * Pulse_Syntax.universe
  * Pulse_Syntax.st_term * Pulse_Syntax.comp * unit * (unit, unit, unit,
  unit) st_typing 
  | T_STApp of env * Pulse_Syntax.term * Pulse_Syntax.term *
  Pulse_Syntax.qualifier FStar_Pervasives_Native.option *
  Pulse_Syntax.comp_st * Pulse_Syntax.term * unit * unit 
  | T_Return of env * Pulse_Syntax.ctag * Prims.bool * Pulse_Syntax.universe
  * Pulse_Syntax.term * Pulse_Syntax.term * Pulse_Syntax.term *
  Pulse_Syntax.var * unit * unit * unit 
  | T_Lift of env * Pulse_Syntax.st_term * Pulse_Syntax.comp_st *
  Pulse_Syntax.comp_st * (unit, unit, unit, unit) st_typing * (unit, 
  unit, unit, unit) lift_comp 
  | T_Bind of env * Pulse_Syntax.st_term * Pulse_Syntax.st_term *
  Pulse_Syntax.comp_st * Pulse_Syntax.comp_st * Pulse_Syntax.var *
  Pulse_Syntax.comp * (unit, unit, unit, unit) st_typing * unit * (unit,
  unit, unit, unit) st_typing * (unit, unit, unit, unit, unit, unit)
  bind_comp 
  | T_If of env * Pulse_Syntax.term * Pulse_Syntax.st_term *
  Pulse_Syntax.st_term * Pulse_Syntax.comp_st * Pulse_Syntax.universe *
  Pulse_Syntax.var * unit * (unit, unit, unit, unit) st_typing * (unit, 
  unit, unit, unit) st_typing * unit 
  | T_Frame of env * Pulse_Syntax.st_term * Pulse_Syntax.comp_st *
  Pulse_Syntax.term * unit * (unit, unit, unit, unit) st_typing 
  | T_Equiv of env * Pulse_Syntax.st_term * Pulse_Syntax.comp *
  Pulse_Syntax.comp * (unit, unit, unit, unit) st_typing * (unit, unit, 
  unit, unit) st_equiv 
  | T_ElimExists of env * Pulse_Syntax.universe * Pulse_Syntax.term *
  Pulse_Syntax.term * Pulse_Syntax.var * unit * unit 
  | T_IntroExists of env * Pulse_Syntax.universe * Pulse_Syntax.term *
  Pulse_Syntax.term * Pulse_Syntax.term * unit * unit * unit 
  | T_IntroExistsErased of env * Pulse_Syntax.universe * Pulse_Syntax.term *
  Pulse_Syntax.term * Pulse_Syntax.term * unit * unit * unit 
  | T_While of env * Pulse_Syntax.term * Pulse_Syntax.st_term *
  Pulse_Syntax.st_term * unit * (unit, unit, unit, unit) st_typing * (
  unit, unit, unit, unit) st_typing 
  | T_Par of env * Pulse_Syntax.st_term * Pulse_Syntax.comp *
  Pulse_Syntax.st_term * Pulse_Syntax.comp * Pulse_Syntax.var * (unit, 
  unit, unit, unit) comp_typing * (unit, unit, unit, unit) comp_typing *
  (unit, unit, unit, unit) st_typing * (unit, unit, unit, unit) st_typing 
  | T_WithLocal of env * Pulse_Syntax.term * Pulse_Syntax.st_term *
  Pulse_Syntax.term * Pulse_Syntax.comp * Pulse_Syntax.var * unit * unit *
  (unit, unit, unit, unit) comp_typing * (unit, unit, unit, unit) st_typing 
  | T_Rewrite of env * Pulse_Syntax.vprop * Pulse_Syntax.vprop * unit * unit
  
  | T_Admit of env * Pulse_Syntax.st_comp * Pulse_Syntax.ctag * (unit, 
  unit, unit) st_comp_typing 
let uu___is_STC uu___2 uu___1 uu___ uu___3 =
  match uu___3 with | STC _ -> true | _ -> false
let uu___is_CT_Tot uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | CT_Tot _ -> true | _ -> false
let uu___is_CT_ST uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | CT_ST _ -> true | _ -> false
let uu___is_CT_STAtomic uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | CT_STAtomic _ -> true | _ -> false
let uu___is_CT_STGhost uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | CT_STGhost _ -> true | _ -> false
let uu___is_T_Abs uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | T_Abs _ -> true | _ -> false
let uu___is_T_STApp uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | T_STApp _ -> true | _ -> false
let uu___is_T_Return uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | T_Return _ -> true | _ -> false
let uu___is_T_Lift uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | T_Lift _ -> true | _ -> false
let uu___is_T_Bind uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | T_Bind _ -> true | _ -> false
let uu___is_T_If uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | T_If _ -> true | _ -> false
let uu___is_T_Frame uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | T_Frame _ -> true | _ -> false
let uu___is_T_Equiv uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | T_Equiv _ -> true | _ -> false
let uu___is_T_ElimExists uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | T_ElimExists _ -> true | _ -> false
let uu___is_T_IntroExists uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | T_IntroExists _ -> true | _ -> false
let uu___is_T_IntroExistsErased uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | T_IntroExistsErased _ -> true | _ -> false
let uu___is_T_While uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | T_While _ -> true | _ -> false
let uu___is_T_Par uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | T_Par _ -> true | _ -> false
let uu___is_T_WithLocal uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | T_WithLocal _ -> true | _ -> false
let uu___is_T_Rewrite uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | T_Rewrite _ -> true | _ -> false
let uu___is_T_Admit uu___3 uu___2 uu___1 uu___ uu___4 =
  match uu___4 with | T_Admit _ -> true | _ -> false
let (star_typing_inversion :
  FStar_Reflection_Typing.fstar_top_env ->
    env -> Pulse_Syntax.term -> Pulse_Syntax.term -> unit -> (unit * unit))
  = fun f -> fun g -> fun t0 -> fun t1 -> fun d -> Prims.admit ()
let (vprop_eq_typing_inversion :
  FStar_Reflection_Typing.fstar_top_env ->
    env ->
      Pulse_Syntax.term ->
        Pulse_Syntax.term ->
          (unit, unit, unit) FStar_Tactics_Builtins.equiv_token ->
            (unit * unit))
  = fun f -> fun g -> fun t0 -> fun t1 -> fun token -> Prims.admit ()

