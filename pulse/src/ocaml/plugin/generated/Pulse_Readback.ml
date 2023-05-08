open Prims
let op_let_Question :
  'a 'b .
    'a FStar_Pervasives_Native.option ->
      ('a ->
         ('b FStar_Pervasives_Native.option, unit)
           FStar_Tactics_Effect.tac_repr)
        ->
        ('b FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun g ->
           match f with
           | FStar_Pervasives_Native.None ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> FStar_Pervasives_Native.None)))
           | FStar_Pervasives_Native.Some x -> Obj.magic (Obj.repr (g x)))
        uu___1 uu___
let rec (readback_universe :
  FStar_Reflection_Types.universe ->
    Pulse_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u ->
    match FStar_Reflection_Builtins.inspect_universe u with
    | FStar_Reflection_Data.Uv_Zero ->
        FStar_Pervasives_Native.Some Pulse_Syntax.U_zero
    | FStar_Reflection_Data.Uv_Succ u' ->
        (match readback_universe u' with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some u'1 ->
             FStar_Pervasives_Native.Some (Pulse_Syntax.U_succ u'1))
    | FStar_Reflection_Data.Uv_Name (s, r) ->
        FStar_Pervasives_Native.Some (Pulse_Syntax.U_var s)
    | FStar_Reflection_Data.Uv_Max (u1::u2::[]) ->
        let u1' = readback_universe u1 in
        let u2' = readback_universe u2 in
        (match (u1', u2') with
         | (FStar_Pervasives_Native.Some u1'1, FStar_Pervasives_Native.Some
            u2'1) ->
             FStar_Pervasives_Native.Some (Pulse_Syntax.U_max (u1'1, u2'1))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let rec (readback_universes :
  FStar_Reflection_Types.universe Prims.list ->
    Pulse_Syntax.universe Prims.list FStar_Pervasives_Native.option)
  =
  fun us ->
    match us with
    | [] -> FStar_Pervasives_Native.Some []
    | hd::tl ->
        (match readback_universe hd with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some hd1 ->
             (match readback_universes tl with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some tl1 ->
                  FStar_Pervasives_Native.Some (hd1 :: tl1)))
let (try_readback_st_comp :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term ->
       (Pulse_Syntax.term FStar_Pervasives_Native.option, unit)
         FStar_Tactics_Effect.tac_repr)
      ->
      (Pulse_Syntax.comp FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun readback_ty ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Readback.fst" (Prims.of_int (66))
           (Prims.of_int (17)) (Prims.of_int (66)) (Prims.of_int (32)))
        (FStar_Range.mk_range "Pulse.Readback.fst" (Prims.of_int (66))
           (Prims.of_int (2)) (Prims.of_int (129)) (Prims.of_int (13)))
        (Obj.magic (FStar_Tactics_SyntaxHelpers.collect_app t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (hd, args) ->
                  (match FStar_Reflection_Builtins.inspect_ln hd with
                   | FStar_Reflection_Data.Tv_UInst (fv, u::[]) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range "Pulse.Readback.fst"
                                  (Prims.of_int (69)) (Prims.of_int (17))
                                  (Prims.of_int (69)) (Prims.of_int (30)))
                               (FStar_Range.mk_range "Pulse.Readback.fst"
                                  (Prims.of_int (70)) (Prims.of_int (4))
                                  (Prims.of_int (128)) (Prims.of_int (13)))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     FStar_Reflection_Builtins.inspect_fv fv))
                               (fun uu___1 ->
                                  (fun fv_lid ->
                                     if
                                       fv_lid = Pulse_Reflection_Util.stt_lid
                                     then
                                       match args with
                                       | res::pre::post::[] ->
                                           Obj.magic
                                             (Obj.repr
                                                (match FStar_Reflection_Builtins.inspect_ln
                                                         (FStar_Pervasives_Native.fst
                                                            post)
                                                 with
                                                 | FStar_Reflection_Data.Tv_Abs
                                                     (b, body) ->
                                                     Obj.repr
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Range.mk_range
                                                             "Pulse.Readback.fst"
                                                             (Prims.of_int (76))
                                                             (Prims.of_int (18))
                                                             (Prims.of_int (76))
                                                             (Prims.of_int (34)))
                                                          (FStar_Range.mk_range
                                                             "Pulse.Readback.fst"
                                                             (Prims.of_int (75))
                                                             (Prims.of_int (14))
                                                             (Prims.of_int (96))
                                                             (Prims.of_int (65)))
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___1 ->
                                                                FStar_Reflection_Builtins.inspect_binder
                                                                  b))
                                                          (fun uu___1 ->
                                                             (fun uu___1 ->
                                                                match uu___1
                                                                with
                                                                | {
                                                                    FStar_Reflection_Data.binder_bv
                                                                    = bv;
                                                                    FStar_Reflection_Data.binder_qual
                                                                    = aq;
                                                                    FStar_Reflection_Data.binder_attrs
                                                                    = attrs;
                                                                    FStar_Reflection_Data.binder_sort
                                                                    = sort;_}
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Reflection_Builtins.inspect_bv
                                                                    bv))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    bv_view
                                                                    ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    (readback_universe
                                                                    u)
                                                                    (fun u''
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (47)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (65)))
                                                                    (Obj.magic
                                                                    (readback_ty
                                                                    (FStar_Pervasives_Native.fst
                                                                    res)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___2
                                                                    (fun res'
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (47)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (65)))
                                                                    (Obj.magic
                                                                    (readback_ty
                                                                    (FStar_Pervasives_Native.fst
                                                                    pre)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___3
                                                                    (fun pre'
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (43)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (65)))
                                                                    (Obj.magic
                                                                    (readback_ty
                                                                    body))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___4
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    post' ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax.C_ST
                                                                    {
                                                                    Pulse_Syntax.u
                                                                    = u'';
                                                                    Pulse_Syntax.res
                                                                    = res';
                                                                    Pulse_Syntax.pre
                                                                    = pre';
                                                                    Pulse_Syntax.post
                                                                    = post'
                                                                    }))))
                                                                    uu___5)))
                                                                    uu___4))))
                                                                    uu___3))))
                                                                    uu___2))))
                                                                    uu___2)))
                                                               uu___1))
                                                 | uu___1 ->
                                                     Obj.repr
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___2 ->
                                                             FStar_Pervasives_Native.None))))
                                       | uu___1 ->
                                           Obj.magic
                                             (Obj.repr
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___2 ->
                                                      FStar_Pervasives_Native.None)))
                                     else
                                       if
                                         (fv_lid =
                                            Pulse_Reflection_Util.stt_atomic_lid)
                                           ||
                                           (fv_lid =
                                              Pulse_Reflection_Util.stt_ghost_lid)
                                       then
                                         Obj.magic
                                           (Obj.repr
                                              (match args with
                                               | res::opened::pre::post::[]
                                                   ->
                                                   Obj.repr
                                                     (match FStar_Reflection_Builtins.inspect_ln
                                                              (FStar_Pervasives_Native.fst
                                                                 post)
                                                      with
                                                      | FStar_Reflection_Data.Tv_Abs
                                                          (b, body) ->
                                                          Obj.repr
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Readback.fst"
                                                                  (Prims.of_int (105))
                                                                  (Prims.of_int (20))
                                                                  (Prims.of_int (105))
                                                                  (Prims.of_int (36)))
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Readback.fst"
                                                                  (Prims.of_int (104))
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (125))
                                                                  (Prims.of_int (17)))
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___2
                                                                    ->
                                                                    FStar_Reflection_Builtins.inspect_binder
                                                                    b))
                                                               (fun uu___2 ->
                                                                  (fun uu___2
                                                                    ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStar_Reflection_Data.binder_bv
                                                                    = bv;
                                                                    FStar_Reflection_Data.binder_qual
                                                                    = aq;
                                                                    FStar_Reflection_Data.binder_attrs
                                                                    = attrs;
                                                                    FStar_Reflection_Data.binder_sort
                                                                    = uu___3;_}
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (17)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Reflection_Builtins.inspect_bv
                                                                    bv))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    bv_view
                                                                    ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    (readback_universe
                                                                    u)
                                                                    (fun u''
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (47)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (17)))
                                                                    (Obj.magic
                                                                    (readback_ty
                                                                    (FStar_Pervasives_Native.fst
                                                                    res)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___4
                                                                    (fun res'
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (53)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (17)))
                                                                    (Obj.magic
                                                                    (readback_ty
                                                                    (FStar_Pervasives_Native.fst
                                                                    opened)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___5
                                                                    (fun
                                                                    opened'
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (47)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (17)))
                                                                    (Obj.magic
                                                                    (readback_ty
                                                                    (FStar_Pervasives_Native.fst
                                                                    pre)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___6
                                                                    (fun pre'
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (43)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (17)))
                                                                    (Obj.magic
                                                                    (readback_ty
                                                                    body))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___7
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    post' ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    if
                                                                    fv_lid =
                                                                    Pulse_Reflection_Util.stt_atomic_lid
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax.C_STAtomic
                                                                    (opened',
                                                                    {
                                                                    Pulse_Syntax.u
                                                                    = u'';
                                                                    Pulse_Syntax.res
                                                                    = res';
                                                                    Pulse_Syntax.pre
                                                                    = pre';
                                                                    Pulse_Syntax.post
                                                                    = post'
                                                                    }))
                                                                    else
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax.C_STGhost
                                                                    (opened',
                                                                    {
                                                                    Pulse_Syntax.u
                                                                    = u'';
                                                                    Pulse_Syntax.res
                                                                    = res';
                                                                    Pulse_Syntax.pre
                                                                    = pre';
                                                                    Pulse_Syntax.post
                                                                    = post'
                                                                    })))))
                                                                    uu___8)))
                                                                    uu___7))))
                                                                    uu___6))))
                                                                    uu___5))))
                                                                    uu___4))))
                                                                    uu___4)))
                                                                    uu___2))
                                                      | uu___2 ->
                                                          Obj.repr
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___3 ->
                                                                  FStar_Pervasives_Native.None)))
                                               | uu___2 ->
                                                   Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___3 ->
                                                           FStar_Pervasives_Native.None))))
                                       else
                                         Obj.magic
                                           (Obj.repr
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___3 ->
                                                    FStar_Pervasives_Native.None))))
                                    uu___1)))
                   | uu___1 ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 -> FStar_Pervasives_Native.None)))))
             uu___)
let (readback_qual :
  FStar_Reflection_Data.aqualv ->
    Pulse_Syntax.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Reflection_Data.Q_Implicit ->
        FStar_Pervasives_Native.Some Pulse_Syntax.Implicit
    | uu___1 -> FStar_Pervasives_Native.None
let rec (readback_ty :
  FStar_Reflection_Types.term ->
    (Pulse_Syntax.term FStar_Pervasives_Native.option, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       match FStar_Reflection_Builtins.inspect_ln t with
       | FStar_Reflection_Data.Tv_Var bv ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      FStar_Pervasives_Native.Some
                        (Pulse_Syntax.Tm_Var
                           {
                             Pulse_Syntax.nm_index =
                               ((FStar_Reflection_Builtins.inspect_bv bv).FStar_Reflection_Data.bv_index);
                             Pulse_Syntax.nm_ppname =
                               ((FStar_Reflection_Builtins.inspect_bv bv).FStar_Reflection_Data.bv_ppname);
                             Pulse_Syntax.nm_range =
                               (FStar_Reflection_Builtins.range_of_term t)
                           }))))
       | FStar_Reflection_Data.Tv_BVar bv ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      FStar_Pervasives_Native.Some
                        (Pulse_Syntax.Tm_BVar
                           {
                             Pulse_Syntax.bv_index =
                               ((FStar_Reflection_Builtins.inspect_bv bv).FStar_Reflection_Data.bv_index);
                             Pulse_Syntax.bv_ppname =
                               ((FStar_Reflection_Builtins.inspect_bv bv).FStar_Reflection_Data.bv_ppname);
                             Pulse_Syntax.bv_range =
                               (FStar_Reflection_Builtins.range_of_term t)
                           }))))
       | FStar_Reflection_Data.Tv_FVar fv ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      if
                        (FStar_Reflection_Builtins.inspect_fv fv) =
                          Pulse_Reflection_Util.vprop_lid
                      then FStar_Pervasives_Native.Some Pulse_Syntax.Tm_VProp
                      else
                        if
                          (FStar_Reflection_Builtins.inspect_fv fv) =
                            Pulse_Reflection_Util.emp_lid
                        then FStar_Pervasives_Native.Some Pulse_Syntax.Tm_Emp
                        else
                          if
                            (FStar_Reflection_Builtins.inspect_fv fv) =
                              Pulse_Reflection_Util.inames_lid
                          then
                            FStar_Pervasives_Native.Some
                              Pulse_Syntax.Tm_Inames
                          else
                            if
                              (FStar_Reflection_Builtins.inspect_fv fv) =
                                Pulse_Reflection_Util.emp_inames_lid
                            then
                              FStar_Pervasives_Native.Some
                                Pulse_Syntax.Tm_EmpInames
                            else
                              FStar_Pervasives_Native.Some
                                (Pulse_Syntax.Tm_FVar
                                   {
                                     Pulse_Syntax.fv_name =
                                       (FStar_Reflection_Builtins.inspect_fv
                                          fv);
                                     Pulse_Syntax.fv_range =
                                       (FStar_Reflection_Builtins.range_of_term
                                          t)
                                   }))))
       | FStar_Reflection_Data.Tv_UInst (fv, us) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      match readback_universes us with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some us' ->
                          FStar_Pervasives_Native.Some
                            (Pulse_Syntax.Tm_UInst
                               ({
                                  Pulse_Syntax.fv_name =
                                    (FStar_Reflection_Builtins.inspect_fv fv);
                                  Pulse_Syntax.fv_range =
                                    (FStar_Reflection_Builtins.range_of_term
                                       t)
                                }, us')))))
       | FStar_Reflection_Data.Tv_App (hd, (a, q)) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Readback.fst"
                      (Prims.of_int (183)) (Prims.of_int (6))
                      (Prims.of_int (188)) (Prims.of_int (83)))
                   (FStar_Range.mk_range "Pulse.Readback.fst"
                      (Prims.of_int (190)) (Prims.of_int (4))
                      (Prims.of_int (239)) (Prims.of_int (7)))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ ->
                         fun uu___1 ->
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range "Pulse.Readback.fst"
                                (Prims.of_int (183)) (Prims.of_int (17))
                                (Prims.of_int (183)) (Prims.of_int (31)))
                             (FStar_Range.mk_range "Pulse.Readback.fst"
                                (Prims.of_int (183)) (Prims.of_int (6))
                                (Prims.of_int (188)) (Prims.of_int (83)))
                             (Obj.magic (readback_ty hd))
                             (fun uu___2 ->
                                (fun uu___2 ->
                                   Obj.magic
                                     (op_let_Question uu___2
                                        (fun uu___3 ->
                                           (fun hd' ->
                                              match q with
                                              | FStar_Reflection_Data.Q_Meta
                                                  uu___3 ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___4 ->
                                                             FStar_Pervasives_Native.None)))
                                              | uu___3 ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Range.mk_range
                                                             "Pulse.Readback.fst"
                                                             (Prims.of_int (187))
                                                             (Prims.of_int (20))
                                                             (Prims.of_int (187))
                                                             (Prims.of_int (33)))
                                                          (FStar_Range.mk_range
                                                             "Pulse.Readback.fst"
                                                             (Prims.of_int (187))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (188))
                                                             (Prims.of_int (83)))
                                                          (Obj.magic
                                                             (readback_ty a))
                                                          (fun uu___4 ->
                                                             (fun uu___4 ->
                                                                Obj.magic
                                                                  (op_let_Question
                                                                    uu___4
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun arg'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax.Tm_PureApp
                                                                    (hd',
                                                                    (readback_qual
                                                                    q), arg')))))
                                                                    uu___5)))
                                                               uu___4))))
                                             uu___3))) uu___2)))
                   (fun uu___ ->
                      (fun aux ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "Pulse.Readback.fst"
                                 (Prims.of_int (190)) (Prims.of_int (21))
                                 (Prims.of_int (190)) (Prims.of_int (36)))
                              (FStar_Range.mk_range "Pulse.Readback.fst"
                                 (Prims.of_int (190)) (Prims.of_int (4))
                                 (Prims.of_int (239)) (Prims.of_int (7)))
                              (Obj.magic
                                 (FStar_Tactics_SyntaxHelpers.collect_app t))
                              (fun uu___ ->
                                 (fun uu___ ->
                                    match uu___ with
                                    | (head, args) ->
                                        (match ((FStar_Reflection_Builtins.inspect_ln
                                                   head), args)
                                         with
                                         | (FStar_Reflection_Data.Tv_FVar fv,
                                            (a1, uu___1)::(a2, uu___2)::[])
                                             ->
                                             if
                                               (FStar_Reflection_Builtins.inspect_fv
                                                  fv)
                                                 =
                                                 Pulse_Reflection_Util.star_lid
                                             then
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Range.mk_range
                                                       "Pulse.Readback.fst"
                                                       (Prims.of_int (196))
                                                       (Prims.of_int (18))
                                                       (Prims.of_int (196))
                                                       (Prims.of_int (32)))
                                                    (FStar_Range.mk_range
                                                       "Pulse.Readback.fst"
                                                       (Prims.of_int (195))
                                                       (Prims.of_int (11))
                                                       (Prims.of_int (200))
                                                       (Prims.of_int (7)))
                                                    (Obj.magic
                                                       (readback_ty a1))
                                                    (fun uu___3 ->
                                                       (fun uu___3 ->
                                                          Obj.magic
                                                            (op_let_Question
                                                               uu___3
                                                               (fun t1 ->
                                                                  FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (32)))
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (72)))
                                                                    (
                                                                    Obj.magic
                                                                    (readback_ty
                                                                    a2))
                                                                    (
                                                                    fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___4
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun t2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax.Tm_Star
                                                                    (t1, t2)))))
                                                                    uu___5)))
                                                                    uu___4))))
                                                         uu___3))
                                             else Obj.magic (aux ())
                                         | (FStar_Reflection_Data.Tv_UInst
                                            (fv, u::[]),
                                            (a1, uu___1)::(a2, uu___2)::[])
                                             ->
                                             if
                                               ((FStar_Reflection_Builtins.inspect_fv
                                                   fv)
                                                  =
                                                  Pulse_Reflection_Util.exists_lid)
                                                 ||
                                                 ((FStar_Reflection_Builtins.inspect_fv
                                                     fv)
                                                    =
                                                    Pulse_Reflection_Util.forall_lid)
                                             then
                                               Obj.magic
                                                 (op_let_Question
                                                    (readback_universe u)
                                                    (fun u1 ->
                                                       FStar_Tactics_Effect.tac_bind
                                                         (FStar_Range.mk_range
                                                            "Pulse.Readback.fst"
                                                            (Prims.of_int (207))
                                                            (Prims.of_int (18))
                                                            (Prims.of_int (207))
                                                            (Prims.of_int (32)))
                                                         (FStar_Range.mk_range
                                                            "Pulse.Readback.fst"
                                                            (Prims.of_int (207))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (227))
                                                            (Prims.of_int (20)))
                                                         (Obj.magic
                                                            (readback_ty a1))
                                                         (fun uu___3 ->
                                                            (fun uu___3 ->
                                                               Obj.magic
                                                                 (op_let_Question
                                                                    uu___3
                                                                    (
                                                                    fun ty ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (97)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (20)))
                                                                    (match 
                                                                    FStar_Reflection_Builtins.inspect_ln
                                                                    a2
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Abs
                                                                    (uu___4,
                                                                    body) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (37)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (33)))
                                                                    (Obj.magic
                                                                    (readback_ty
                                                                    body))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___5
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun p ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    p)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "readback_ty: only lambda expressions allowed when reading back exists/forall")))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___4
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun p ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (if
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv) =
                                                                    Pulse_Reflection_Util.exists_lid
                                                                    then
                                                                    Pulse_Syntax.Tm_ExistsSL
                                                                    (u1, ty,
                                                                    p,
                                                                    Pulse_Syntax.should_elim_true)
                                                                    else
                                                                    Pulse_Syntax.Tm_ForallSL
                                                                    (u1, ty,
                                                                    p)))))
                                                                    uu___5)))
                                                                    uu___4))))
                                                              uu___3)))
                                             else Obj.magic (aux ())
                                         | (FStar_Reflection_Data.Tv_FVar fv,
                                            (a1, uu___1)::[]) ->
                                             if
                                               (FStar_Reflection_Builtins.inspect_fv
                                                  fv)
                                                 =
                                                 Pulse_Reflection_Util.pure_lid
                                             then
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Range.mk_range
                                                       "Pulse.Readback.fst"
                                                       (Prims.of_int (233))
                                                       (Prims.of_int (18))
                                                       (Prims.of_int (233))
                                                       (Prims.of_int (31)))
                                                    (FStar_Range.mk_range
                                                       "Pulse.Readback.fst"
                                                       (Prims.of_int (232))
                                                       (Prims.of_int (11))
                                                       (Prims.of_int (236))
                                                       (Prims.of_int (7)))
                                                    (Obj.magic
                                                       (readback_ty a1))
                                                    (fun uu___2 ->
                                                       (fun uu___2 ->
                                                          Obj.magic
                                                            (op_let_Question
                                                               uu___2
                                                               (fun uu___3 ->
                                                                  (fun t1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax.Tm_Pure
                                                                    t1))))
                                                                    uu___3)))
                                                         uu___2))
                                             else Obj.magic (aux ())
                                         | uu___1 -> Obj.magic (aux ())))
                                   uu___))) uu___)))
       | FStar_Reflection_Data.Tv_Refine (bv, sort, phi) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Readback.fst"
                      (Prims.of_int (242)) (Prims.of_int (18))
                      (Prims.of_int (242)) (Prims.of_int (31)))
                   (FStar_Range.mk_range "Pulse.Readback.fst"
                      (Prims.of_int (243)) (Prims.of_int (4))
                      (Prims.of_int (247)) (Prims.of_int (43)))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> FStar_Reflection_Builtins.inspect_bv bv))
                   (fun uu___ ->
                      (fun bv_view ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "Pulse.Readback.fst"
                                 (Prims.of_int (243)) (Prims.of_int (14))
                                 (Prims.of_int (243)) (Prims.of_int (30)))
                              (FStar_Range.mk_range "Pulse.Readback.fst"
                                 (Prims.of_int (243)) (Prims.of_int (4))
                                 (Prims.of_int (247)) (Prims.of_int (43)))
                              (Obj.magic (readback_ty sort))
                              (fun uu___ ->
                                 (fun uu___ ->
                                    Obj.magic
                                      (op_let_Question uu___
                                         (fun ty ->
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Range.mk_range
                                                 "Pulse.Readback.fst"
                                                 (Prims.of_int (244))
                                                 (Prims.of_int (15))
                                                 (Prims.of_int (244))
                                                 (Prims.of_int (30)))
                                              (FStar_Range.mk_range
                                                 "Pulse.Readback.fst"
                                                 (Prims.of_int (244))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (247))
                                                 (Prims.of_int (43)))
                                              (Obj.magic (readback_ty phi))
                                              (fun uu___1 ->
                                                 (fun uu___1 ->
                                                    Obj.magic
                                                      (op_let_Question uu___1
                                                         (fun uu___2 ->
                                                            (fun phi1 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax.Tm_Refine
                                                                    ({
                                                                    Pulse_Syntax.binder_ty
                                                                    = ty;
                                                                    Pulse_Syntax.binder_ppname
                                                                    =
                                                                    (bv_view.FStar_Reflection_Data.bv_ppname)
                                                                    }, phi1)))))
                                                              uu___2)))
                                                   uu___1)))) uu___))) uu___)))
       | FStar_Reflection_Data.Tv_Abs (uu___, uu___1) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 -> FStar_Pervasives_Native.None)))
       | FStar_Reflection_Data.Tv_Arrow (b, c) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Readback.fst"
                      (Prims.of_int (253)) (Prims.of_int (8))
                      (Prims.of_int (253)) (Prims.of_int (24)))
                   (FStar_Range.mk_range "Pulse.Readback.fst"
                      (Prims.of_int (251)) (Prims.of_int (20))
                      (Prims.of_int (270)) (Prims.of_int (5)))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ ->
                         FStar_Reflection_Builtins.inspect_binder b))
                   (fun uu___ ->
                      (fun uu___ ->
                         match uu___ with
                         | { FStar_Reflection_Data.binder_bv = bv;
                             FStar_Reflection_Data.binder_qual = aq;
                             FStar_Reflection_Data.binder_attrs = attrs;
                             FStar_Reflection_Data.binder_sort = sort;_} ->
                             (match aq with
                              | FStar_Reflection_Data.Q_Meta uu___1 ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___2 ->
                                             FStar_Pervasives_Native.None)))
                              | uu___1 ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Readback.fst"
                                             (Prims.of_int (259))
                                             (Prims.of_int (14))
                                             (Prims.of_int (259))
                                             (Prims.of_int (30)))
                                          (FStar_Range.mk_range
                                             "Pulse.Readback.fst"
                                             (Prims.of_int (261))
                                             (Prims.of_int (6))
                                             (Prims.of_int (269))
                                             (Prims.of_int (18)))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 -> readback_qual aq))
                                          (fun uu___2 ->
                                             (fun q ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "Pulse.Readback.fst"
                                                        (Prims.of_int (261))
                                                        (Prims.of_int (20))
                                                        (Prims.of_int (261))
                                                        (Prims.of_int (33)))
                                                     (FStar_Range.mk_range
                                                        "Pulse.Readback.fst"
                                                        (Prims.of_int (263))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (269))
                                                        (Prims.of_int (18)))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           FStar_Reflection_Builtins.inspect_bv
                                                             bv))
                                                     (fun uu___2 ->
                                                        (fun bv_view ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Readback.fst"
                                                                   (Prims.of_int (263))
                                                                   (Prims.of_int (19))
                                                                   (Prims.of_int (263))
                                                                   (Prims.of_int (33)))
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Readback.fst"
                                                                   (Prims.of_int (264))
                                                                   (Prims.of_int (6))
                                                                   (Prims.of_int (269))
                                                                   (Prims.of_int (18)))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___2 ->
                                                                    FStar_Reflection_Builtins.inspect_comp
                                                                    c))
                                                                (fun uu___2
                                                                   ->
                                                                   (fun
                                                                    c_view ->
                                                                    match c_view
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.C_Total
                                                                    c_t ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (38)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (110)))
                                                                    (Obj.magic
                                                                    (readback_ty
                                                                    sort))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___2
                                                                    (fun
                                                                    b_ty' ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (36)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (110)))
                                                                    (Obj.magic
                                                                    (readback_comp
                                                                    c_t))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___3
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun c'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax.Tm_Arrow
                                                                    ({
                                                                    Pulse_Syntax.binder_ty
                                                                    = b_ty';
                                                                    Pulse_Syntax.binder_ppname
                                                                    =
                                                                    (bv_view.FStar_Reflection_Data.bv_ppname)
                                                                    }, q, c')))))
                                                                    uu___4)))
                                                                    uu___3))))
                                                                    uu___2)))
                                                                    | 
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives_Native.None))))
                                                                    uu___2)))
                                                          uu___2))) uu___2)))))
                        uu___)))
       | FStar_Reflection_Data.Tv_Type u ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      match readback_universe u with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some u' ->
                          FStar_Pervasives_Native.Some
                            (Pulse_Syntax.Tm_Type u'))))
       | FStar_Reflection_Data.Tv_Const c ->
           Obj.magic
             (Obj.repr
                (match c with
                 | FStar_Reflection_Data.C_Unit ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          FStar_Pervasives_Native.Some
                            (Pulse_Syntax.Tm_Constant Pulse_Syntax.Unit))
                 | FStar_Reflection_Data.C_True ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          FStar_Pervasives_Native.Some
                            (Pulse_Syntax.Tm_Constant
                               (Pulse_Syntax.Bool true)))
                 | FStar_Reflection_Data.C_False ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          FStar_Pervasives_Native.Some
                            (Pulse_Syntax.Tm_Constant
                               (Pulse_Syntax.Bool false)))
                 | FStar_Reflection_Data.C_Int n ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          FStar_Pervasives_Native.Some
                            (Pulse_Syntax.Tm_Constant (Pulse_Syntax.Int n)))
                 | uu___ ->
                     FStar_Tactics_Derived.fail
                       "readback_ty: constant not supported"))
       | FStar_Reflection_Data.Tv_Uvar (uu___, uu___1) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Derived.fail "readback_ty: unexpected Tv_Uvar"))
       | FStar_Reflection_Data.Tv_Let (recf, attrs, bv, ty, def, body) ->
           Obj.magic
             (Obj.repr
                (if recf
                 then
                   Obj.repr
                     (FStar_Tactics_Derived.fail
                        "readback_ty: unexpected recursive Tv_Let")
                 else
                   Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "Pulse.Readback.fst"
                           (Prims.of_int (293)) (Prims.of_int (20))
                           (Prims.of_int (293)) (Prims.of_int (33)))
                        (FStar_Range.mk_range "Pulse.Readback.fst"
                           (Prims.of_int (295)) (Prims.of_int (6))
                           (Prims.of_int (299)) (Prims.of_int (69)))
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 ->
                              FStar_Reflection_Builtins.inspect_bv bv))
                        (fun uu___1 ->
                           (fun bv_view ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range "Pulse.Readback.fst"
                                      (Prims.of_int (295))
                                      (Prims.of_int (19))
                                      (Prims.of_int (295))
                                      (Prims.of_int (33)))
                                   (FStar_Range.mk_range "Pulse.Readback.fst"
                                      (Prims.of_int (295)) (Prims.of_int (6))
                                      (Prims.of_int (299))
                                      (Prims.of_int (69)))
                                   (Obj.magic (readback_ty ty))
                                   (fun uu___1 ->
                                      (fun uu___1 ->
                                         Obj.magic
                                           (op_let_Question uu___1
                                              (fun bv_t' ->
                                                 FStar_Tactics_Effect.tac_bind
                                                   (FStar_Range.mk_range
                                                      "Pulse.Readback.fst"
                                                      (Prims.of_int (296))
                                                      (Prims.of_int (18))
                                                      (Prims.of_int (296))
                                                      (Prims.of_int (33)))
                                                   (FStar_Range.mk_range
                                                      "Pulse.Readback.fst"
                                                      (Prims.of_int (296))
                                                      (Prims.of_int (6))
                                                      (Prims.of_int (299))
                                                      (Prims.of_int (69)))
                                                   (Obj.magic
                                                      (readback_ty def))
                                                   (fun uu___2 ->
                                                      (fun uu___2 ->
                                                         Obj.magic
                                                           (op_let_Question
                                                              uu___2
                                                              (fun def' ->
                                                                 FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (35)))
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Readback.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (69)))
                                                                   (Obj.magic
                                                                    (readback_ty
                                                                    body))
                                                                   (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___3
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    body' ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax.Tm_Let
                                                                    (bv_t',
                                                                    def',
                                                                    body')))))
                                                                    uu___4)))
                                                                    uu___3))))
                                                        uu___2)))) uu___1)))
                             uu___1))))
       | FStar_Reflection_Data.Tv_Match (uu___, uu___1, uu___2) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___3 ->
                      FStar_Pervasives_Native.Some (Pulse_Syntax.Tm_FStar t))))
       | FStar_Reflection_Data.Tv_AscribedT (t1, uu___, uu___1, uu___2) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___3 ->
                      FStar_Pervasives_Native.Some (Pulse_Syntax.Tm_FStar t1))))
       | FStar_Reflection_Data.Tv_AscribedC (t1, uu___, uu___1, uu___2) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___3 ->
                      FStar_Pervasives_Native.Some (Pulse_Syntax.Tm_FStar t1))))
       | FStar_Reflection_Data.Tv_Unknown ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      FStar_Pervasives_Native.Some Pulse_Syntax.Tm_Unknown)))
       | FStar_Reflection_Data.Tv_Unsupp ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> FStar_Pervasives_Native.None)))) uu___
and (readback_comp :
  FStar_Reflection_Types.term ->
    (Pulse_Syntax.comp FStar_Pervasives_Native.option, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "Pulse.Readback.fst" (Prims.of_int (327))
         (Prims.of_int (13)) (Prims.of_int (327)) (Prims.of_int (47)))
      (FStar_Range.mk_range "Pulse.Readback.fst" (Prims.of_int (328))
         (Prims.of_int (2)) (Prims.of_int (332)) (Prims.of_int (49)))
      (Obj.magic (try_readback_st_comp t readback_ty))
      (fun uu___ ->
         (fun ropt ->
            match ropt with
            | FStar_Pervasives_Native.Some uu___ ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ropt)))
            | uu___ ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "Pulse.Readback.fst"
                           (Prims.of_int (331)) (Prims.of_int (14))
                           (Prims.of_int (331)) (Prims.of_int (27)))
                        (FStar_Range.mk_range "Pulse.Readback.fst"
                           (Prims.of_int (331)) (Prims.of_int (4))
                           (Prims.of_int (332)) (Prims.of_int (49)))
                        (Obj.magic (readback_ty t))
                        (fun uu___1 ->
                           (fun uu___1 ->
                              Obj.magic
                                (op_let_Question uu___1
                                   (fun uu___2 ->
                                      (fun t' ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 FStar_Pervasives_Native.Some
                                                   (Pulse_Syntax.C_Tot t'))))
                                        uu___2))) uu___1)))) uu___)