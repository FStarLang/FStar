open Prims
let op_let_Question :
  'a 'b .
    'a FStar_Pervasives_Native.option ->
      ('a -> 'b FStar_Pervasives_Native.option) ->
        'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun g ->
      match f with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some x -> g x
let (try_readback_st_comp :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term ->
       Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
      -> Pulse_Syntax_Base.comp FStar_Pervasives_Native.option)
  =
  fun t ->
    fun readback_ty ->
      let uu___ = FStar_Reflection_Derived.collect_app_ln t in
      match uu___ with
      | (hd, args) ->
          (match FStar_Reflection_Builtins.inspect_ln hd with
           | FStar_Reflection_Data.Tv_UInst (fv, u::[]) ->
               let fv_lid = FStar_Reflection_Builtins.inspect_fv fv in
               if fv_lid = Pulse_Reflection_Util.stt_lid
               then
                 (match args with
                  | res::pre::post::[] ->
                      (match FStar_Reflection_Builtins.inspect_ln
                               (FStar_Pervasives_Native.fst post)
                       with
                       | FStar_Reflection_Data.Tv_Abs (b, body) ->
                           let uu___1 =
                             FStar_Reflection_Builtins.inspect_binder b in
                           (match uu___1 with
                            | { FStar_Reflection_Data.binder_bv = bv;
                                FStar_Reflection_Data.binder_qual = aq;
                                FStar_Reflection_Data.binder_attrs = attrs;
                                FStar_Reflection_Data.binder_sort = sort;_}
                                ->
                                let bv_view =
                                  FStar_Reflection_Builtins.inspect_bv bv in
                                op_let_Question
                                  (readback_ty
                                     (FStar_Pervasives_Native.fst res))
                                  (fun res' ->
                                     op_let_Question
                                       (readback_ty
                                          (FStar_Pervasives_Native.fst pre))
                                       (fun pre' ->
                                          op_let_Question (readback_ty body)
                                            (fun post' ->
                                               let c =
                                                 Pulse_Syntax_Base.C_ST
                                                   {
                                                     Pulse_Syntax_Base.u = u;
                                                     Pulse_Syntax_Base.res =
                                                       res';
                                                     Pulse_Syntax_Base.pre =
                                                       pre';
                                                     Pulse_Syntax_Base.post =
                                                       post'
                                                   } in
                                               FStar_Pervasives_Native.Some c))))
                       | uu___1 -> FStar_Pervasives_Native.None)
                  | uu___1 -> FStar_Pervasives_Native.None)
               else
                 if
                   (fv_lid = Pulse_Reflection_Util.stt_atomic_lid) ||
                     (fv_lid = Pulse_Reflection_Util.stt_ghost_lid)
                 then
                   (match args with
                    | res::opened::pre::post::[] ->
                        (match FStar_Reflection_Builtins.inspect_ln
                                 (FStar_Pervasives_Native.fst post)
                         with
                         | FStar_Reflection_Data.Tv_Abs (b, body) ->
                             let uu___2 =
                               FStar_Reflection_Builtins.inspect_binder b in
                             (match uu___2 with
                              | { FStar_Reflection_Data.binder_bv = bv;
                                  FStar_Reflection_Data.binder_qual = aq;
                                  FStar_Reflection_Data.binder_attrs = attrs;
                                  FStar_Reflection_Data.binder_sort = uu___3;_}
                                  ->
                                  let bv_view =
                                    FStar_Reflection_Builtins.inspect_bv bv in
                                  op_let_Question
                                    (readback_ty
                                       (FStar_Pervasives_Native.fst res))
                                    (fun res' ->
                                       op_let_Question
                                         (readback_ty
                                            (FStar_Pervasives_Native.fst
                                               opened))
                                         (fun opened' ->
                                            op_let_Question
                                              (readback_ty
                                                 (FStar_Pervasives_Native.fst
                                                    pre))
                                              (fun pre' ->
                                                 op_let_Question
                                                   (readback_ty body)
                                                   (fun post' ->
                                                      if
                                                        fv_lid =
                                                          Pulse_Reflection_Util.stt_atomic_lid
                                                      then
                                                        let c =
                                                          Pulse_Syntax_Base.C_STAtomic
                                                            (opened',
                                                              {
                                                                Pulse_Syntax_Base.u
                                                                  = u;
                                                                Pulse_Syntax_Base.res
                                                                  = res';
                                                                Pulse_Syntax_Base.pre
                                                                  = pre';
                                                                Pulse_Syntax_Base.post
                                                                  = post'
                                                              }) in
                                                        FStar_Pervasives_Native.Some
                                                          c
                                                      else
                                                        (let c =
                                                           Pulse_Syntax_Base.C_STGhost
                                                             (opened',
                                                               {
                                                                 Pulse_Syntax_Base.u
                                                                   = u;
                                                                 Pulse_Syntax_Base.res
                                                                   = res';
                                                                 Pulse_Syntax_Base.pre
                                                                   = pre';
                                                                 Pulse_Syntax_Base.post
                                                                   = post'
                                                               }) in
                                                         FStar_Pervasives_Native.Some
                                                           c))))))
                         | uu___2 -> FStar_Pervasives_Native.None)
                    | uu___2 -> FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None
           | uu___1 -> FStar_Pervasives_Native.None)
let (readback_qual :
  FStar_Reflection_Data.aqualv ->
    Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Reflection_Data.Q_Implicit ->
        FStar_Pervasives_Native.Some Pulse_Syntax_Base.Implicit
    | uu___1 -> FStar_Pervasives_Native.None
let (collect_app_refined :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term * FStar_Reflection_Data.argv Prims.list))
  = fun t -> FStar_Reflection_Derived.collect_app_ln t
let (readback_ty_ascribed :
  FStar_Reflection_Types.term ->
    Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
  =
  fun t ->
    match FStar_Reflection_Builtins.inspect_ln t with
    | FStar_Reflection_Data.Tv_AscribedT (t1, uu___, uu___1, uu___2) ->
        FStar_Pervasives_Native.Some
          (Pulse_Syntax_Base.tm_fstar t1
             (FStar_Reflection_Builtins.range_of_term t1))
    | FStar_Reflection_Data.Tv_AscribedC (t1, uu___, uu___1, uu___2) ->
        FStar_Pervasives_Native.Some
          (Pulse_Syntax_Base.tm_fstar t1
             (FStar_Reflection_Builtins.range_of_term t1))
let rec (readback_ty :
  FStar_Reflection_Types.term ->
    Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
  =
  fun t ->
    let w res =
      Pulse_Syntax_Base.with_range res (Pulse_RuntimeUtils.range_of_term t) in
    let return res = FStar_Pervasives_Native.Some (w res) in
    match FStar_Reflection_Builtins.inspect_ln t with
    | FStar_Reflection_Data.Tv_FVar fv ->
        let fv_lid = FStar_Reflection_Builtins.inspect_fv fv in
        if fv_lid = Pulse_Reflection_Util.vprop_lid
        then return Pulse_Syntax_Base.Tm_VProp
        else
          if fv_lid = Pulse_Reflection_Util.emp_lid
          then return Pulse_Syntax_Base.Tm_Emp
          else
            if fv_lid = Pulse_Reflection_Util.inames_lid
            then return Pulse_Syntax_Base.Tm_Inames
            else
              if fv_lid = Pulse_Reflection_Util.emp_inames_lid
              then return Pulse_Syntax_Base.Tm_EmpInames
              else return (Pulse_Syntax_Base.Tm_FStar t)
    | FStar_Reflection_Data.Tv_App (hd, (a, q)) ->
        let aux uu___ =
          match q with
          | FStar_Reflection_Data.Q_Meta uu___1 ->
              FStar_Pervasives_Native.None
          | uu___1 -> return (Pulse_Syntax_Base.Tm_FStar t) in
        let uu___ = collect_app_refined t in
        (match uu___ with
         | (head, args) ->
             (match ((FStar_Reflection_Builtins.inspect_ln head), args) with
              | (FStar_Reflection_Data.Tv_FVar fv,
                 (a1, uu___1)::(a2, uu___2)::[]) ->
                  if
                    (FStar_Reflection_Builtins.inspect_fv fv) =
                      Pulse_Reflection_Util.star_lid
                  then
                    op_let_Question (readback_ty a1)
                      (fun t1 ->
                         op_let_Question (readback_ty a2)
                           (fun t2 ->
                              return (Pulse_Syntax_Base.Tm_Star (t1, t2))))
                  else aux ()
              | (FStar_Reflection_Data.Tv_UInst (fv, u::[]),
                 (a1, uu___1)::(a2, uu___2)::[]) ->
                  if
                    ((FStar_Reflection_Builtins.inspect_fv fv) =
                       Pulse_Reflection_Util.exists_lid)
                      ||
                      ((FStar_Reflection_Builtins.inspect_fv fv) =
                         Pulse_Reflection_Util.forall_lid)
                  then
                    op_let_Question (readback_ty a1)
                      (fun ty ->
                         op_let_Question
                           (match FStar_Reflection_Builtins.inspect_ln a2
                            with
                            | FStar_Reflection_Data.Tv_Abs (b, body) ->
                                op_let_Question (readback_ty body)
                                  (fun p ->
                                     let bview =
                                       FStar_Reflection_Builtins.inspect_binder
                                         b in
                                     let bv =
                                       FStar_Reflection_Builtins.inspect_bv
                                         bview.FStar_Reflection_Data.binder_bv in
                                     FStar_Pervasives_Native.Some
                                       ((bv.FStar_Reflection_Data.bv_ppname),
                                         (Pulse_RuntimeUtils.binder_range b),
                                         p))
                            | uu___3 -> FStar_Pervasives_Native.None)
                           (fun uu___3 ->
                              match uu___3 with
                              | (ppname, range, p) ->
                                  let b =
                                    {
                                      Pulse_Syntax_Base.binder_ty = ty;
                                      Pulse_Syntax_Base.binder_ppname =
                                        (Pulse_Syntax_Base.mk_ppname ppname
                                           range)
                                    } in
                                  if
                                    (FStar_Reflection_Builtins.inspect_fv fv)
                                      = Pulse_Reflection_Util.exists_lid
                                  then
                                    return
                                      (Pulse_Syntax_Base.Tm_ExistsSL
                                         (u, b, p))
                                  else
                                    return
                                      (Pulse_Syntax_Base.Tm_ForallSL
                                         (u, b, p))))
                  else aux ()
              | (FStar_Reflection_Data.Tv_FVar fv, (a1, uu___1)::[]) ->
                  if
                    (FStar_Reflection_Builtins.inspect_fv fv) =
                      Pulse_Reflection_Util.pure_lid
                  then
                    op_let_Question (readback_ty a1)
                      (fun t1 -> return (Pulse_Syntax_Base.Tm_Pure t1))
                  else aux ()
              | uu___1 -> aux ()))
    | FStar_Reflection_Data.Tv_Refine (uu___, uu___1, uu___2) ->
        return (Pulse_Syntax_Base.Tm_FStar t)
    | FStar_Reflection_Data.Tv_Arrow (uu___, uu___1) ->
        return (Pulse_Syntax_Base.Tm_FStar t)
    | FStar_Reflection_Data.Tv_Type uu___ ->
        return (Pulse_Syntax_Base.Tm_FStar t)
    | FStar_Reflection_Data.Tv_Const uu___ ->
        return (Pulse_Syntax_Base.Tm_FStar t)
    | FStar_Reflection_Data.Tv_Let
        (uu___, uu___1, uu___2, uu___3, uu___4, uu___5) ->
        return (Pulse_Syntax_Base.Tm_FStar t)
    | FStar_Reflection_Data.Tv_Var uu___ ->
        return (Pulse_Syntax_Base.Tm_FStar t)
    | FStar_Reflection_Data.Tv_BVar uu___ ->
        return (Pulse_Syntax_Base.Tm_FStar t)
    | FStar_Reflection_Data.Tv_UInst (uu___, uu___1) ->
        return (Pulse_Syntax_Base.Tm_FStar t)
    | FStar_Reflection_Data.Tv_Match (uu___, uu___1, uu___2) ->
        return (Pulse_Syntax_Base.Tm_FStar t)
    | FStar_Reflection_Data.Tv_Abs (uu___, uu___1) ->
        FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Uvar (uu___, uu___1) ->
        FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_AscribedT (uu___, uu___1, uu___2, uu___3) ->
        readback_ty_ascribed t
    | FStar_Reflection_Data.Tv_AscribedC (uu___, uu___1, uu___2, uu___3) ->
        readback_ty_ascribed t
    | FStar_Reflection_Data.Tv_Unknown -> return Pulse_Syntax_Base.Tm_Unknown
    | FStar_Reflection_Data.Tv_Unsupp -> FStar_Pervasives_Native.None
let (readback_comp :
  FStar_Reflection_Types.term ->
    Pulse_Syntax_Base.comp FStar_Pervasives_Native.option)
  =
  fun t ->
    let ropt = try_readback_st_comp t readback_ty in
    match ropt with
    | FStar_Pervasives_Native.Some uu___ -> ropt
    | uu___ ->
        op_let_Question (readback_ty t)
          (fun t' ->
             FStar_Pervasives_Native.Some (Pulse_Syntax_Base.C_Tot t'))