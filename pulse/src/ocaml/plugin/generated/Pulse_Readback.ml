open Prims
let (debug_log :
  (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun f ->
       if Pulse_RuntimeUtils.debug_at_level_no_module "readback"
       then Obj.magic (Obj.repr (f ()))
       else
         Obj.magic
           (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
      uu___
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
let (readback_observability :
  FStarC_Reflection_Types.term ->
    Pulse_Syntax_Base.observability FStar_Pervasives_Native.option)
  =
  fun t ->
    match FStarC_Reflection_V2_Builtins.inspect_ln t with
    | FStarC_Reflection_V2_Data.Tv_FVar fv ->
        let fv_lid = FStarC_Reflection_V2_Builtins.inspect_fv fv in
        if fv_lid = Pulse_Reflection_Util.observable_lid
        then FStar_Pervasives_Native.Some Pulse_Syntax_Base.Observable
        else
          if fv_lid = Pulse_Reflection_Util.neutral_lid
          then FStar_Pervasives_Native.Some Pulse_Syntax_Base.Neutral
          else FStar_Pervasives_Native.None
    | uu___ -> FStar_Pervasives_Native.None
let (try_readback_st_comp :
  FStarC_Reflection_Types.term ->
    Pulse_Syntax_Base.comp FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = FStar_Reflection_V2_Collect.collect_app_ln t in
    match uu___ with
    | (hd, args) ->
        (match FStarC_Reflection_V2_Builtins.inspect_ln hd with
         | FStarC_Reflection_V2_Data.Tv_UInst (fv, u::[]) ->
             let fv_lid = FStarC_Reflection_V2_Builtins.inspect_fv fv in
             if fv_lid = Pulse_Reflection_Util.stt_lid
             then
               (match args with
                | res::pre::post::[] ->
                    (match FStarC_Reflection_V2_Builtins.inspect_ln
                             (FStar_Pervasives_Native.fst post)
                     with
                     | FStarC_Reflection_V2_Data.Tv_Abs (b, body) ->
                         let uu___1 =
                           FStarC_Reflection_V2_Builtins.inspect_binder b in
                         (match uu___1 with
                          | { FStarC_Reflection_V2_Data.sort2 = sort;
                              FStarC_Reflection_V2_Data.qual = aq;
                              FStarC_Reflection_V2_Data.attrs = attrs;
                              FStarC_Reflection_V2_Data.ppname2 = uu___2;_} ->
                              let res' = FStar_Pervasives_Native.fst res in
                              let pre' = FStar_Pervasives_Native.fst pre in
                              let post' = body in
                              let c =
                                Pulse_Syntax_Base.C_ST
                                  {
                                    Pulse_Syntax_Base.u = u;
                                    Pulse_Syntax_Base.res = res';
                                    Pulse_Syntax_Base.pre = pre';
                                    Pulse_Syntax_Base.post = post'
                                  } in
                              FStar_Pervasives_Native.Some c)
                     | uu___1 -> FStar_Pervasives_Native.None)
                | uu___1 -> FStar_Pervasives_Native.None)
             else
               if fv_lid = Pulse_Reflection_Util.stt_atomic_lid
               then
                 (match args with
                  | res::obs::opened::pre::post::[] ->
                      (match FStarC_Reflection_V2_Builtins.inspect_ln
                               (FStar_Pervasives_Native.fst post)
                       with
                       | FStarC_Reflection_V2_Data.Tv_Abs (b, body) ->
                           let uu___2 =
                             FStarC_Reflection_V2_Builtins.inspect_binder b in
                           (match uu___2 with
                            | { FStarC_Reflection_V2_Data.sort2 = uu___3;
                                FStarC_Reflection_V2_Data.qual = aq;
                                FStarC_Reflection_V2_Data.attrs = attrs;
                                FStarC_Reflection_V2_Data.ppname2 = uu___4;_}
                                ->
                                let res' = FStar_Pervasives_Native.fst res in
                                op_let_Question
                                  (readback_observability
                                     (FStar_Pervasives_Native.fst obs))
                                  (fun obs' ->
                                     let opened' =
                                       FStar_Pervasives_Native.fst opened in
                                     let pre' =
                                       FStar_Pervasives_Native.fst pre in
                                     let post' = body in
                                     let c =
                                       Pulse_Syntax_Base.C_STAtomic
                                         (opened', obs',
                                           {
                                             Pulse_Syntax_Base.u = u;
                                             Pulse_Syntax_Base.res = res';
                                             Pulse_Syntax_Base.pre = pre';
                                             Pulse_Syntax_Base.post = post'
                                           }) in
                                     FStar_Pervasives_Native.Some c))
                       | uu___2 -> FStar_Pervasives_Native.None)
                  | uu___2 -> FStar_Pervasives_Native.None)
               else
                 if fv_lid = Pulse_Reflection_Util.stt_ghost_lid
                 then
                   (match args with
                    | res::inames::pre::post::[] ->
                        (match FStarC_Reflection_V2_Builtins.inspect_ln
                                 (FStar_Pervasives_Native.fst post)
                         with
                         | FStarC_Reflection_V2_Data.Tv_Abs (b, body) ->
                             let uu___3 =
                               FStarC_Reflection_V2_Builtins.inspect_binder b in
                             (match uu___3 with
                              | { FStarC_Reflection_V2_Data.sort2 = uu___4;
                                  FStarC_Reflection_V2_Data.qual = aq;
                                  FStarC_Reflection_V2_Data.attrs = attrs;
                                  FStarC_Reflection_V2_Data.ppname2 = uu___5;_}
                                  ->
                                  let res' = FStar_Pervasives_Native.fst res in
                                  let inames' =
                                    FStar_Pervasives_Native.fst inames in
                                  let pre' = FStar_Pervasives_Native.fst pre in
                                  let post' = body in
                                  let c =
                                    Pulse_Syntax_Base.C_STGhost
                                      (inames',
                                        {
                                          Pulse_Syntax_Base.u = u;
                                          Pulse_Syntax_Base.res = res';
                                          Pulse_Syntax_Base.pre = pre';
                                          Pulse_Syntax_Base.post = post'
                                        }) in
                                  FStar_Pervasives_Native.Some c)
                         | uu___3 -> FStar_Pervasives_Native.None)
                    | uu___3 -> FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None
         | uu___1 -> FStar_Pervasives_Native.None)
let (readback_comp :
  FStarC_Reflection_Types.term ->
    Pulse_Syntax_Base.comp FStar_Pervasives_Native.option)
  =
  fun t ->
    let ropt = try_readback_st_comp t in
    match ropt with
    | FStar_Pervasives_Native.Some c -> ropt
    | uu___ ->
        let t' = t in
        FStar_Pervasives_Native.Some (Pulse_Syntax_Base.C_Tot t')