open Prims
type name = FStarC_Syntax_Syntax.bv
let (fstar_tactics_lid' : Prims.string Prims.list -> FStarC_Ident.lid) =
  fun s -> FStarC_Parser_Const.fstar_tactics_lid' s
let (fstar_stubs_tactics_lid' : Prims.string Prims.list -> FStarC_Ident.lid)
  = fun s -> FStarC_Parser_Const.fstar_stubs_tactics_lid' s
let (lid_as_tm : FStarC_Ident.lident -> FStarC_Syntax_Syntax.term) =
  fun l ->
    let uu___ = FStarC_Syntax_Syntax.lid_as_fv l FStar_Pervasives_Native.None in
    FStarC_Syntax_Syntax.fv_to_tm uu___
let (mk_tactic_lid_as_term : Prims.string -> FStarC_Syntax_Syntax.term) =
  fun s -> let uu___ = fstar_tactics_lid' ["Effect"; s] in lid_as_tm uu___
type tac_constant =
  {
  lid: FStarC_Ident.lid ;
  fv: FStarC_Syntax_Syntax.fv ;
  t: FStarC_Syntax_Syntax.term }
let (__proj__Mktac_constant__item__lid : tac_constant -> FStarC_Ident.lid) =
  fun projectee -> match projectee with | { lid; fv; t;_} -> lid
let (__proj__Mktac_constant__item__fv :
  tac_constant -> FStarC_Syntax_Syntax.fv) =
  fun projectee -> match projectee with | { lid; fv; t;_} -> fv
let (__proj__Mktac_constant__item__t :
  tac_constant -> FStarC_Syntax_Syntax.term) =
  fun projectee -> match projectee with | { lid; fv; t;_} -> t
let (lid_as_data_fv : FStarC_Ident.lident -> FStarC_Syntax_Syntax.fv) =
  fun l ->
    FStarC_Syntax_Syntax.lid_as_fv l
      (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor)
let (lid_as_data_tm : FStarC_Ident.lident -> FStarC_Syntax_Syntax.term) =
  fun l ->
    let uu___ = lid_as_data_fv l in FStarC_Syntax_Syntax.fv_to_tm uu___
let (fstar_tactics_data : Prims.string Prims.list -> tac_constant) =
  fun ns ->
    let lid = fstar_stubs_tactics_lid' ns in
    let uu___ = lid_as_data_fv lid in
    let uu___1 = lid_as_data_tm lid in { lid; fv = uu___; t = uu___1 }
let (fstar_tactics_const : Prims.string Prims.list -> tac_constant) =
  fun ns ->
    let lid = fstar_stubs_tactics_lid' ns in
    let uu___ = FStarC_Syntax_Syntax.fvconst lid in
    let uu___1 = FStarC_Syntax_Syntax.tconst lid in
    { lid; fv = uu___; t = uu___1 }
let (fstar_tc_core_lid : Prims.string -> FStarC_Ident.lid) =
  fun s ->
    FStarC_Ident.lid_of_path
      (FStarC_Compiler_List.op_At ["FStar"; "Stubs"; "TypeChecker"; "Core"]
         [s]) FStarC_Compiler_Range_Type.dummyRange
let (fstar_tc_core_data : Prims.string -> tac_constant) =
  fun s ->
    let lid = fstar_tc_core_lid s in
    let uu___ = lid_as_data_fv lid in
    let uu___1 = lid_as_data_tm lid in { lid; fv = uu___; t = uu___1 }
let (fstar_tc_core_const : Prims.string -> tac_constant) =
  fun s ->
    let lid = fstar_tc_core_lid s in
    let uu___ = FStarC_Syntax_Syntax.fvconst lid in
    let uu___1 = FStarC_Syntax_Syntax.tconst lid in
    { lid; fv = uu___; t = uu___1 }
let (fstar_tactics_proofstate : tac_constant) =
  fstar_tactics_const ["Types"; "proofstate"]
let (fstar_tactics_goal : tac_constant) =
  fstar_tactics_const ["Types"; "goal"]
let (fstar_tactics_TacticFailure : tac_constant) =
  fstar_tactics_data ["Common"; "TacticFailure"]
let (fstar_tactics_SKIP : tac_constant) =
  fstar_tactics_data ["Common"; "SKIP"]
let (fstar_tactics_result : tac_constant) =
  fstar_tactics_const ["Result"; "__result"]
let (fstar_tactics_Success : tac_constant) =
  fstar_tactics_data ["Result"; "Success"]
let (fstar_tactics_Failed : tac_constant) =
  fstar_tactics_data ["Result"; "Failed"]
let (fstar_tactics_direction : tac_constant) =
  fstar_tactics_const ["Types"; "direction"]
let (fstar_tactics_topdown : tac_constant) =
  fstar_tactics_data ["Types"; "TopDown"]
let (fstar_tactics_bottomup : tac_constant) =
  fstar_tactics_data ["Types"; "BottomUp"]
let (fstar_tactics_ctrl_flag : tac_constant) =
  fstar_tactics_const ["Types"; "ctrl_flag"]
let (fstar_tactics_Continue : tac_constant) =
  fstar_tactics_data ["Types"; "Continue"]
let (fstar_tactics_Skip : tac_constant) =
  fstar_tactics_data ["Types"; "Skip"]
let (fstar_tactics_Abort : tac_constant) =
  fstar_tactics_data ["Types"; "Abort"]
let (fstar_tc_core_unfold_side : tac_constant) =
  fstar_tc_core_const "unfold_side"
let (fstar_tc_core_unfold_side_Left : tac_constant) =
  fstar_tc_core_data "Left"
let (fstar_tc_core_unfold_side_Right : tac_constant) =
  fstar_tc_core_data "Right"
let (fstar_tc_core_unfold_side_Both : tac_constant) =
  fstar_tc_core_data "Both"
let (fstar_tc_core_unfold_side_Neither : tac_constant) =
  fstar_tc_core_data "Neither"
let (fstar_tc_core_tot_or_ghost : tac_constant) =
  fstar_tc_core_const "tot_or_ghost"
let (fstar_tc_core_tot_or_ghost_ETotal : tac_constant) =
  fstar_tc_core_data "E_Total"
let (fstar_tc_core_tot_or_ghost_EGhost : tac_constant) =
  fstar_tc_core_data "E_Ghost"
let (fstar_tactics_guard_policy : tac_constant) =
  fstar_tactics_const ["Types"; "guard_policy"]
let (fstar_tactics_SMT : tac_constant) = fstar_tactics_data ["Types"; "SMT"]
let (fstar_tactics_SMTSync : tac_constant) =
  fstar_tactics_data ["Types"; "SMTSync"]
let (fstar_tactics_Goal : tac_constant) =
  fstar_tactics_data ["Types"; "Goal"]
let (fstar_tactics_Drop : tac_constant) =
  fstar_tactics_data ["Types"; "Drop"]
let (fstar_tactics_Force : tac_constant) =
  fstar_tactics_data ["Types"; "Force"]
let mk_emb :
  'a .
    (FStarC_Compiler_Range_Type.range -> 'a -> FStarC_Syntax_Syntax.term) ->
      (FStarC_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option) ->
        FStarC_Syntax_Syntax.term ->
          'a FStarC_Syntax_Embeddings_Base.embedding
  =
  fun em ->
    fun un ->
      fun t ->
        let uu___ = FStarC_Syntax_Embeddings_Base.term_as_fv t in
        FStarC_Syntax_Embeddings_Base.mk_emb
          (fun x -> fun r -> fun _topt -> fun _norm -> em r x)
          (fun x -> fun _norm -> un x) uu___
let embed :
  'a .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      FStarC_Compiler_Range_Type.range -> 'a -> FStarC_Syntax_Syntax.term
  =
  fun uu___ ->
    fun r ->
      fun x ->
        let uu___1 = FStarC_Syntax_Embeddings_Base.embed uu___ x in
        uu___1 r FStar_Pervasives_Native.None
          FStarC_Syntax_Embeddings_Base.id_norm_cb
let unembed' :
  'a .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      FStarC_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun uu___ ->
    fun x ->
      FStarC_Syntax_Embeddings_Base.unembed uu___ x
        FStarC_Syntax_Embeddings_Base.id_norm_cb
let (t_result_of :
  FStarC_Syntax_Syntax.term ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun t ->
    let uu___ = let uu___1 = FStarC_Syntax_Syntax.as_arg t in [uu___1] in
    FStarC_Syntax_Util.mk_app fstar_tactics_result.t uu___
let (hd'_and_args :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.term' * (FStarC_Syntax_Syntax.term'
      FStarC_Syntax_Syntax.syntax * FStarC_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun tm ->
    let tm1 = FStarC_Syntax_Util.unascribe tm in
    let uu___ = FStarC_Syntax_Util.head_and_args tm1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 = FStarC_Syntax_Util.un_uinst hd in
          uu___2.FStarC_Syntax_Syntax.n in
        (uu___1, args)
let (e_proofstate :
  FStarC_Tactics_Types.proofstate FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings_Base.e_lazy FStarC_Syntax_Syntax.Lazy_proofstate
    fstar_tactics_proofstate.t
let (e_goal :
  FStarC_Tactics_Types.goal FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings_Base.e_lazy FStarC_Syntax_Syntax.Lazy_goal
    fstar_tactics_goal.t
let (unfold_lazy_proofstate :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i -> FStarC_Syntax_Util.exp_string "(((proofstate)))"
let (unfold_lazy_goal :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i -> FStarC_Syntax_Util.exp_string "(((goal)))"
let (mkFV :
  FStarC_Syntax_Syntax.fv ->
    FStarC_Syntax_Syntax.universe Prims.list ->
      (FStarC_TypeChecker_NBETerm.t * FStarC_Syntax_Syntax.aqual) Prims.list
        -> FStarC_TypeChecker_NBETerm.t)
  =
  fun fv ->
    fun us ->
      fun ts ->
        FStarC_TypeChecker_NBETerm.mkFV fv (FStarC_Compiler_List.rev us)
          (FStarC_Compiler_List.rev ts)
let (mkConstruct :
  FStarC_Syntax_Syntax.fv ->
    FStarC_Syntax_Syntax.universe Prims.list ->
      (FStarC_TypeChecker_NBETerm.t * FStarC_Syntax_Syntax.aqual) Prims.list
        -> FStarC_TypeChecker_NBETerm.t)
  =
  fun fv ->
    fun us ->
      fun ts ->
        FStarC_TypeChecker_NBETerm.mkConstruct fv
          (FStarC_Compiler_List.rev us) (FStarC_Compiler_List.rev ts)
let (fv_as_emb_typ : FStarC_Syntax_Syntax.fv -> FStarC_Syntax_Syntax.emb_typ)
  =
  fun fv ->
    let uu___ =
      let uu___1 =
        FStarC_Class_Show.show FStarC_Ident.showable_lident
          (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
      (uu___1, []) in
    FStarC_Syntax_Syntax.ET_app uu___
let (e_proofstate_nbe :
  FStarC_Tactics_Types.proofstate FStarC_TypeChecker_NBETerm.embedding) =
  let embed_proofstate _cb ps =
    let li =
      let uu___ = FStarC_Dyn.mkdyn ps in
      {
        FStarC_Syntax_Syntax.blob = uu___;
        FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_proofstate;
        FStarC_Syntax_Syntax.ltyp = (fstar_tactics_proofstate.t);
        FStarC_Syntax_Syntax.rng = FStarC_Compiler_Range_Type.dummyRange
      } in
    let thunk =
      FStarC_Thunk.mk
        (fun uu___ ->
           FStarC_TypeChecker_NBETerm.mk_t
             (FStarC_TypeChecker_NBETerm.Constant
                (FStarC_TypeChecker_NBETerm.String
                   ("(((proofstate.nbe)))",
                     FStarC_Compiler_Range_Type.dummyRange)))) in
    FStarC_TypeChecker_NBETerm.mk_t
      (FStarC_TypeChecker_NBETerm.Lazy ((FStar_Pervasives.Inl li), thunk)) in
  let unembed_proofstate _cb t =
    let uu___ = FStarC_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu___ with
    | FStarC_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStarC_Syntax_Syntax.blob = b;
           FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_proofstate;
           FStarC_Syntax_Syntax.ltyp = uu___1;
           FStarC_Syntax_Syntax.rng = uu___2;_},
         uu___3)
        ->
        let uu___4 = FStarC_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___4
    | uu___1 ->
        ((let uu___3 =
            FStarC_Compiler_Effect.op_Bang FStarC_Options.debug_embedding in
          if uu___3
          then
            let uu___4 =
              let uu___5 = FStarC_TypeChecker_NBETerm.t_to_string t in
              FStarC_Compiler_Util.format1
                "Not an embedded NBE proofstate: %s\n" uu___5 in
            FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded
              () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___4)
          else ());
         FStar_Pervasives_Native.None) in
  {
    FStarC_TypeChecker_NBETerm.em = embed_proofstate;
    FStarC_TypeChecker_NBETerm.un = unembed_proofstate;
    FStarC_TypeChecker_NBETerm.typ =
      (fun uu___ -> mkFV fstar_tactics_proofstate.fv [] []);
    FStarC_TypeChecker_NBETerm.e_typ =
      (fun uu___ -> fv_as_emb_typ fstar_tactics_proofstate.fv)
  }
let (e_goal_nbe :
  FStarC_Tactics_Types.goal FStarC_TypeChecker_NBETerm.embedding) =
  let embed_goal _cb ps =
    let li =
      let uu___ = FStarC_Dyn.mkdyn ps in
      {
        FStarC_Syntax_Syntax.blob = uu___;
        FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_goal;
        FStarC_Syntax_Syntax.ltyp = (fstar_tactics_goal.t);
        FStarC_Syntax_Syntax.rng = FStarC_Compiler_Range_Type.dummyRange
      } in
    let thunk =
      FStarC_Thunk.mk
        (fun uu___ ->
           FStarC_TypeChecker_NBETerm.mk_t
             (FStarC_TypeChecker_NBETerm.Constant
                (FStarC_TypeChecker_NBETerm.String
                   ("(((goal.nbe)))", FStarC_Compiler_Range_Type.dummyRange)))) in
    FStarC_TypeChecker_NBETerm.mk_t
      (FStarC_TypeChecker_NBETerm.Lazy ((FStar_Pervasives.Inl li), thunk)) in
  let unembed_goal _cb t =
    let uu___ = FStarC_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu___ with
    | FStarC_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStarC_Syntax_Syntax.blob = b;
           FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_goal;
           FStarC_Syntax_Syntax.ltyp = uu___1;
           FStarC_Syntax_Syntax.rng = uu___2;_},
         uu___3)
        ->
        let uu___4 = FStarC_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___4
    | uu___1 ->
        ((let uu___3 =
            FStarC_Compiler_Effect.op_Bang FStarC_Options.debug_embedding in
          if uu___3
          then
            let uu___4 =
              let uu___5 = FStarC_TypeChecker_NBETerm.t_to_string t in
              FStarC_Compiler_Util.format1 "Not an embedded NBE goal: %s"
                uu___5 in
            FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded
              () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___4)
          else ());
         FStar_Pervasives_Native.None) in
  {
    FStarC_TypeChecker_NBETerm.em = embed_goal;
    FStarC_TypeChecker_NBETerm.un = unembed_goal;
    FStarC_TypeChecker_NBETerm.typ =
      (fun uu___ -> mkFV fstar_tactics_goal.fv [] []);
    FStarC_TypeChecker_NBETerm.e_typ =
      (fun uu___ -> fv_as_emb_typ fstar_tactics_goal.fv)
  }
let (e_exn : Prims.exn FStarC_Syntax_Embeddings_Base.embedding) =
  let embed_exn e rng uu___ uu___1 =
    match e with
    | FStarC_Tactics_Common.TacticFailure s ->
        let uu___2 =
          let uu___3 =
            let uu___4 =
              embed
                (FStarC_Syntax_Embeddings.e_tuple2
                   (FStarC_Syntax_Embeddings.e_list
                      FStarC_Syntax_Embeddings.e_document)
                   (FStarC_Syntax_Embeddings.e_option
                      FStarC_Syntax_Embeddings.e_range)) rng s in
            FStarC_Syntax_Syntax.as_arg uu___4 in
          [uu___3] in
        FStarC_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure.t uu___2
          rng
    | FStarC_Tactics_Common.SKIP ->
        let uu___2 = fstar_tactics_SKIP.t in
        {
          FStarC_Syntax_Syntax.n = (uu___2.FStarC_Syntax_Syntax.n);
          FStarC_Syntax_Syntax.pos = rng;
          FStarC_Syntax_Syntax.vars = (uu___2.FStarC_Syntax_Syntax.vars);
          FStarC_Syntax_Syntax.hash_code =
            (uu___2.FStarC_Syntax_Syntax.hash_code)
        }
    | FStarC_Tactics_Common.EExn t ->
        {
          FStarC_Syntax_Syntax.n = (t.FStarC_Syntax_Syntax.n);
          FStarC_Syntax_Syntax.pos = rng;
          FStarC_Syntax_Syntax.vars = (t.FStarC_Syntax_Syntax.vars);
          FStarC_Syntax_Syntax.hash_code = (t.FStarC_Syntax_Syntax.hash_code)
        }
    | e1 ->
        let msg =
          let uu___2 = FStarC_Errors_Msg.text "Uncaught exception" in
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_Compiler_Util.message_of_exn e1 in
              FStarC_Pprint.arbitrary_string uu___5 in
            [uu___4] in
          uu___2 :: uu___3 in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              embed
                (FStarC_Syntax_Embeddings.e_tuple2
                   (FStarC_Syntax_Embeddings.e_list
                      FStarC_Syntax_Embeddings.e_document)
                   (FStarC_Syntax_Embeddings.e_option
                      FStarC_Syntax_Embeddings.e_range)) rng
                (msg, FStar_Pervasives_Native.None) in
            FStarC_Syntax_Syntax.as_arg uu___4 in
          [uu___3] in
        FStarC_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure.t uu___2
          rng in
  let unembed_exn t uu___ =
    let uu___1 = hd'_and_args t in
    match uu___1 with
    | (FStarC_Syntax_Syntax.Tm_fvar fv, (s, uu___2)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure.lid ->
        let uu___3 =
          unembed'
            (FStarC_Syntax_Embeddings.e_tuple2
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Syntax_Embeddings.e_document)
               (FStarC_Syntax_Embeddings.e_option
                  FStarC_Syntax_Embeddings.e_range)) s in
        FStarC_Compiler_Util.bind_opt uu___3
          (fun s1 ->
             FStar_Pervasives_Native.Some
               (FStarC_Tactics_Common.TacticFailure s1))
    | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SKIP.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Common.SKIP
    | uu___2 -> FStar_Pervasives_Native.Some (FStarC_Tactics_Common.EExn t) in
  FStarC_Syntax_Embeddings_Base.mk_emb_full embed_exn unembed_exn
    (fun uu___ -> FStarC_Syntax_Syntax.t_exn) (fun uu___ -> "(exn)")
    (fun uu___ ->
       let uu___1 =
         let uu___2 =
           FStarC_Class_Show.show FStarC_Ident.showable_lident
             FStarC_Parser_Const.exn_lid in
         (uu___2, []) in
       FStarC_Syntax_Syntax.ET_app uu___1)
let (e_exn_nbe : Prims.exn FStarC_TypeChecker_NBETerm.embedding) =
  let embed_exn cb e =
    match e with
    | FStarC_Tactics_Common.TacticFailure s ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_TypeChecker_NBETerm.embed
                (FStarC_TypeChecker_NBETerm.e_tuple2
                   (FStarC_TypeChecker_NBETerm.e_list
                      FStarC_TypeChecker_NBETerm.e_document)
                   (FStarC_TypeChecker_NBETerm.e_option
                      FStarC_TypeChecker_NBETerm.e_range)) cb s in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct fstar_tactics_TacticFailure.fv [] uu___
    | FStarC_Tactics_Common.SKIP -> mkConstruct fstar_tactics_SKIP.fv [] []
    | uu___ ->
        let uu___1 =
          let uu___2 = FStarC_Compiler_Util.message_of_exn e in
          FStarC_Compiler_Util.format1 "cannot embed exn (NBE) : %s" uu___2 in
        failwith uu___1 in
  let unembed_exn cb t =
    let uu___ = FStarC_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu___ with
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___1, (s, uu___2)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure.lid ->
        let uu___3 =
          FStarC_TypeChecker_NBETerm.unembed
            (FStarC_TypeChecker_NBETerm.e_tuple2
               (FStarC_TypeChecker_NBETerm.e_list
                  FStarC_TypeChecker_NBETerm.e_document)
               (FStarC_TypeChecker_NBETerm.e_option
                  FStarC_TypeChecker_NBETerm.e_range)) cb s in
        FStarC_Compiler_Util.bind_opt uu___3
          (fun s1 ->
             FStar_Pervasives_Native.Some
               (FStarC_Tactics_Common.TacticFailure s1))
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SKIP.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Common.SKIP
    | uu___1 -> FStar_Pervasives_Native.None in
  let fv_exn = FStarC_Syntax_Syntax.fvconst FStarC_Parser_Const.exn_lid in
  {
    FStarC_TypeChecker_NBETerm.em = embed_exn;
    FStarC_TypeChecker_NBETerm.un = unembed_exn;
    FStarC_TypeChecker_NBETerm.typ = (fun uu___ -> mkFV fv_exn [] []);
    FStarC_TypeChecker_NBETerm.e_typ = (fun uu___ -> fv_as_emb_typ fv_exn)
  }
let e_result :
  'a .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'a FStarC_Tactics_Result.__result
        FStarC_Syntax_Embeddings_Base.embedding
  =
  fun ea ->
    let embed_result res rng sh cbs =
      match res with
      | FStarC_Tactics_Result.Success (a1, ps) ->
          let uu___ =
            FStarC_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success.t
              [FStarC_Syntax_Syntax.U_zero] in
          let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_Syntax_Embeddings_Base.type_of ea in
              FStarC_Syntax_Syntax.iarg uu___3 in
            let uu___3 =
              let uu___4 =
                let uu___5 = embed ea rng a1 in
                FStarC_Syntax_Syntax.as_arg uu___5 in
              let uu___5 =
                let uu___6 =
                  let uu___7 = embed e_proofstate rng ps in
                  FStarC_Syntax_Syntax.as_arg uu___7 in
                [uu___6] in
              uu___4 :: uu___5 in
            uu___2 :: uu___3 in
          FStarC_Syntax_Syntax.mk_Tm_app uu___ uu___1 rng
      | FStarC_Tactics_Result.Failed (e, ps) ->
          let uu___ =
            FStarC_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed.t
              [FStarC_Syntax_Syntax.U_zero] in
          let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_Syntax_Embeddings_Base.type_of ea in
              FStarC_Syntax_Syntax.iarg uu___3 in
            let uu___3 =
              let uu___4 =
                let uu___5 = embed e_exn rng e in
                FStarC_Syntax_Syntax.as_arg uu___5 in
              let uu___5 =
                let uu___6 =
                  let uu___7 = embed e_proofstate rng ps in
                  FStarC_Syntax_Syntax.as_arg uu___7 in
                [uu___6] in
              uu___4 :: uu___5 in
            uu___2 :: uu___3 in
          FStarC_Syntax_Syntax.mk_Tm_app uu___ uu___1 rng in
    let unembed_result t uu___ =
      let uu___1 = hd'_and_args t in
      match uu___1 with
      | (FStarC_Syntax_Syntax.Tm_fvar fv, _t::(a1, uu___2)::(ps, uu___3)::[])
          when FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success.lid ->
          let uu___4 = unembed' ea a1 in
          FStarC_Compiler_Util.bind_opt uu___4
            (fun a2 ->
               let uu___5 = unembed' e_proofstate ps in
               FStarC_Compiler_Util.bind_opt uu___5
                 (fun ps1 ->
                    FStar_Pervasives_Native.Some
                      (FStarC_Tactics_Result.Success (a2, ps1))))
      | (FStarC_Syntax_Syntax.Tm_fvar fv, _t::(e, uu___2)::(ps, uu___3)::[])
          when FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed.lid ->
          let uu___4 = unembed' e_exn e in
          FStarC_Compiler_Util.bind_opt uu___4
            (fun e1 ->
               let uu___5 = unembed' e_proofstate ps in
               FStarC_Compiler_Util.bind_opt uu___5
                 (fun ps1 ->
                    FStar_Pervasives_Native.Some
                      (FStarC_Tactics_Result.Failed (e1, ps1))))
      | uu___2 -> FStar_Pervasives_Native.None in
    FStarC_Syntax_Embeddings_Base.mk_emb_full embed_result unembed_result
      (fun uu___ ->
         let uu___1 = FStarC_Syntax_Embeddings_Base.type_of ea in
         t_result_of uu___1) (fun uu___ -> "")
      (fun uu___ ->
         let uu___1 =
           let uu___2 =
             FStarC_Class_Show.show FStarC_Ident.showable_lident
               fstar_tactics_result.lid in
           let uu___3 =
             let uu___4 = FStarC_Syntax_Embeddings_Base.emb_typ_of ea () in
             [uu___4] in
           (uu___2, uu___3) in
         FStarC_Syntax_Syntax.ET_app uu___1)
let e_result_nbe :
  'a .
    'a FStarC_TypeChecker_NBETerm.embedding ->
      'a FStarC_Tactics_Result.__result FStarC_TypeChecker_NBETerm.embedding
  =
  fun ea ->
    let embed_result cb res =
      match res with
      | FStarC_Tactics_Result.Failed (e, ps) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_TypeChecker_NBETerm.type_of ea in
              FStarC_TypeChecker_NBETerm.as_iarg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = FStarC_TypeChecker_NBETerm.embed e_exn_nbe cb e in
                FStarC_TypeChecker_NBETerm.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    FStarC_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps in
                  FStarC_TypeChecker_NBETerm.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          mkConstruct fstar_tactics_Failed.fv [FStarC_Syntax_Syntax.U_zero]
            uu___
      | FStarC_Tactics_Result.Success (a1, ps) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_TypeChecker_NBETerm.type_of ea in
              FStarC_TypeChecker_NBETerm.as_iarg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = FStarC_TypeChecker_NBETerm.embed ea cb a1 in
                FStarC_TypeChecker_NBETerm.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    FStarC_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps in
                  FStarC_TypeChecker_NBETerm.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          mkConstruct fstar_tactics_Success.fv [FStarC_Syntax_Syntax.U_zero]
            uu___ in
    let unembed_result cb t =
      let uu___ = FStarC_TypeChecker_NBETerm.nbe_t_of_t t in
      match uu___ with
      | FStarC_TypeChecker_NBETerm.Construct
          (fv, uu___1, (ps, uu___2)::(a1, uu___3)::_t::[]) when
          FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success.lid ->
          let uu___4 = FStarC_TypeChecker_NBETerm.unembed ea cb a1 in
          FStarC_Compiler_Util.bind_opt uu___4
            (fun a2 ->
               let uu___5 =
                 FStarC_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps in
               FStarC_Compiler_Util.bind_opt uu___5
                 (fun ps1 ->
                    FStar_Pervasives_Native.Some
                      (FStarC_Tactics_Result.Success (a2, ps1))))
      | FStarC_TypeChecker_NBETerm.Construct
          (fv, uu___1, (ps, uu___2)::(e, uu___3)::_t::[]) when
          FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed.lid ->
          let uu___4 = FStarC_TypeChecker_NBETerm.unembed e_exn_nbe cb e in
          FStarC_Compiler_Util.bind_opt uu___4
            (fun e1 ->
               let uu___5 =
                 FStarC_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps in
               FStarC_Compiler_Util.bind_opt uu___5
                 (fun ps1 ->
                    FStar_Pervasives_Native.Some
                      (FStarC_Tactics_Result.Failed (e1, ps1))))
      | uu___1 -> FStar_Pervasives_Native.None in
    {
      FStarC_TypeChecker_NBETerm.em = embed_result;
      FStarC_TypeChecker_NBETerm.un = unembed_result;
      FStarC_TypeChecker_NBETerm.typ =
        (fun uu___ -> mkFV fstar_tactics_result.fv [] []);
      FStarC_TypeChecker_NBETerm.e_typ =
        (fun uu___ -> fv_as_emb_typ fstar_tactics_result.fv)
    }
let (e_direction :
  FStarC_Tactics_Types.direction FStarC_Syntax_Embeddings_Base.embedding) =
  let embed_direction rng d =
    match d with
    | FStarC_Tactics_Types.TopDown -> fstar_tactics_topdown.t
    | FStarC_Tactics_Types.BottomUp -> fstar_tactics_bottomup.t in
  let unembed_direction t =
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_fvar fv when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.TopDown
    | FStarC_Syntax_Syntax.Tm_fvar fv when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.BottomUp
    | uu___1 -> FStar_Pervasives_Native.None in
  mk_emb embed_direction unembed_direction fstar_tactics_direction.t
let (e_direction_nbe :
  FStarC_Tactics_Types.direction FStarC_TypeChecker_NBETerm.embedding) =
  let embed_direction cb res =
    match res with
    | FStarC_Tactics_Types.TopDown ->
        mkConstruct fstar_tactics_topdown.fv [] []
    | FStarC_Tactics_Types.BottomUp ->
        mkConstruct fstar_tactics_bottomup.fv [] [] in
  let unembed_direction cb t =
    let uu___ = FStarC_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu___ with
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.TopDown
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.BottomUp
    | uu___1 ->
        ((let uu___3 =
            FStarC_Compiler_Effect.op_Bang FStarC_Options.debug_embedding in
          if uu___3
          then
            let uu___4 =
              let uu___5 = FStarC_TypeChecker_NBETerm.t_to_string t in
              FStarC_Compiler_Util.format1 "Not an embedded direction: %s"
                uu___5 in
            FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded
              () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___4)
          else ());
         FStar_Pervasives_Native.None) in
  {
    FStarC_TypeChecker_NBETerm.em = embed_direction;
    FStarC_TypeChecker_NBETerm.un = unembed_direction;
    FStarC_TypeChecker_NBETerm.typ =
      (fun uu___ -> mkFV fstar_tactics_direction.fv [] []);
    FStarC_TypeChecker_NBETerm.e_typ =
      (fun uu___ -> fv_as_emb_typ fstar_tactics_direction.fv)
  }
let (e_ctrl_flag :
  FStarC_Tactics_Types.ctrl_flag FStarC_Syntax_Embeddings_Base.embedding) =
  let embed_ctrl_flag rng d =
    match d with
    | FStarC_Tactics_Types.Continue -> fstar_tactics_Continue.t
    | FStarC_Tactics_Types.Skip -> fstar_tactics_Skip.t
    | FStarC_Tactics_Types.Abort -> fstar_tactics_Abort.t in
  let unembed_ctrl_flag t =
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_fvar fv when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Continue.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.Continue
    | FStarC_Syntax_Syntax.Tm_fvar fv when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Skip.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.Skip
    | FStarC_Syntax_Syntax.Tm_fvar fv when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Abort.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.Abort
    | uu___1 -> FStar_Pervasives_Native.None in
  mk_emb embed_ctrl_flag unembed_ctrl_flag fstar_tactics_ctrl_flag.t
let (e_ctrl_flag_nbe :
  FStarC_Tactics_Types.ctrl_flag FStarC_TypeChecker_NBETerm.embedding) =
  let embed_ctrl_flag cb res =
    match res with
    | FStarC_Tactics_Types.Continue ->
        mkConstruct fstar_tactics_Continue.fv [] []
    | FStarC_Tactics_Types.Skip -> mkConstruct fstar_tactics_Skip.fv [] []
    | FStarC_Tactics_Types.Abort -> mkConstruct fstar_tactics_Abort.fv [] [] in
  let unembed_ctrl_flag cb t =
    let uu___ = FStarC_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu___ with
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Continue.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.Continue
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Skip.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.Skip
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Abort.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.Abort
    | uu___1 ->
        ((let uu___3 =
            FStarC_Compiler_Effect.op_Bang FStarC_Options.debug_embedding in
          if uu___3
          then
            let uu___4 =
              let uu___5 = FStarC_TypeChecker_NBETerm.t_to_string t in
              FStarC_Compiler_Util.format1 "Not an embedded ctrl_flag: %s"
                uu___5 in
            FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded
              () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___4)
          else ());
         FStar_Pervasives_Native.None) in
  {
    FStarC_TypeChecker_NBETerm.em = embed_ctrl_flag;
    FStarC_TypeChecker_NBETerm.un = unembed_ctrl_flag;
    FStarC_TypeChecker_NBETerm.typ =
      (fun uu___ -> mkFV fstar_tactics_ctrl_flag.fv [] []);
    FStarC_TypeChecker_NBETerm.e_typ =
      (fun uu___ -> fv_as_emb_typ fstar_tactics_ctrl_flag.fv)
  }
let (e_unfold_side :
  FStarC_TypeChecker_Core.side FStarC_Syntax_Embeddings_Base.embedding) =
  let embed_unfold_side rng s =
    match s with
    | FStarC_TypeChecker_Core.Left -> fstar_tc_core_unfold_side_Left.t
    | FStarC_TypeChecker_Core.Right -> fstar_tc_core_unfold_side_Right.t
    | FStarC_TypeChecker_Core.Both -> fstar_tc_core_unfold_side_Both.t
    | FStarC_TypeChecker_Core.Neither -> fstar_tc_core_unfold_side_Neither.t in
  let unembed_unfold_side t =
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_fvar fv when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tc_core_unfold_side_Left.lid
        -> FStar_Pervasives_Native.Some FStarC_TypeChecker_Core.Left
    | FStarC_Syntax_Syntax.Tm_fvar fv when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tc_core_unfold_side_Right.lid
        -> FStar_Pervasives_Native.Some FStarC_TypeChecker_Core.Right
    | FStarC_Syntax_Syntax.Tm_fvar fv when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tc_core_unfold_side_Both.lid
        -> FStar_Pervasives_Native.Some FStarC_TypeChecker_Core.Both
    | FStarC_Syntax_Syntax.Tm_fvar fv when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          fstar_tc_core_unfold_side_Neither.lid
        -> FStar_Pervasives_Native.Some FStarC_TypeChecker_Core.Neither
    | uu___1 -> FStar_Pervasives_Native.None in
  mk_emb embed_unfold_side unembed_unfold_side fstar_tc_core_unfold_side.t
let (e_unfold_side_nbe :
  FStarC_TypeChecker_Core.side FStarC_TypeChecker_NBETerm.embedding) =
  let embed_unfold_side cb res =
    match res with
    | FStarC_TypeChecker_Core.Left ->
        mkConstruct fstar_tc_core_unfold_side_Left.fv [] []
    | FStarC_TypeChecker_Core.Right ->
        mkConstruct fstar_tc_core_unfold_side_Right.fv [] []
    | FStarC_TypeChecker_Core.Both ->
        mkConstruct fstar_tc_core_unfold_side_Both.fv [] []
    | FStarC_TypeChecker_Core.Neither ->
        mkConstruct fstar_tc_core_unfold_side_Neither.fv [] [] in
  let unembed_unfold_side cb t =
    let uu___ = FStarC_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu___ with
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tc_core_unfold_side_Left.lid
        -> FStar_Pervasives_Native.Some FStarC_TypeChecker_Core.Left
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tc_core_unfold_side_Right.lid
        -> FStar_Pervasives_Native.Some FStarC_TypeChecker_Core.Right
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tc_core_unfold_side_Both.lid
        -> FStar_Pervasives_Native.Some FStarC_TypeChecker_Core.Both
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          fstar_tc_core_unfold_side_Neither.lid
        -> FStar_Pervasives_Native.Some FStarC_TypeChecker_Core.Neither
    | uu___1 ->
        ((let uu___3 =
            FStarC_Compiler_Effect.op_Bang FStarC_Options.debug_embedding in
          if uu___3
          then
            let uu___4 =
              let uu___5 = FStarC_TypeChecker_NBETerm.t_to_string t in
              FStarC_Compiler_Util.format1 "Not an embedded unfold_side: %s"
                uu___5 in
            FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded
              () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___4)
          else ());
         FStar_Pervasives_Native.None) in
  {
    FStarC_TypeChecker_NBETerm.em = embed_unfold_side;
    FStarC_TypeChecker_NBETerm.un = unembed_unfold_side;
    FStarC_TypeChecker_NBETerm.typ =
      (fun uu___ -> mkFV fstar_tc_core_unfold_side.fv [] []);
    FStarC_TypeChecker_NBETerm.e_typ =
      (fun uu___ -> fv_as_emb_typ fstar_tc_core_unfold_side.fv)
  }
let (e_tot_or_ghost :
  FStarC_TypeChecker_Core.tot_or_ghost
    FStarC_Syntax_Embeddings_Base.embedding)
  =
  let embed_tot_or_ghost rng s =
    match s with
    | FStarC_TypeChecker_Core.E_Total -> fstar_tc_core_tot_or_ghost_ETotal.t
    | FStarC_TypeChecker_Core.E_Ghost -> fstar_tc_core_tot_or_ghost_EGhost.t in
  let unembed_tot_or_ghost t =
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_fvar fv when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          fstar_tc_core_tot_or_ghost_ETotal.lid
        -> FStar_Pervasives_Native.Some FStarC_TypeChecker_Core.E_Total
    | FStarC_Syntax_Syntax.Tm_fvar fv when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          fstar_tc_core_tot_or_ghost_EGhost.lid
        -> FStar_Pervasives_Native.Some FStarC_TypeChecker_Core.E_Ghost
    | uu___1 -> FStar_Pervasives_Native.None in
  mk_emb embed_tot_or_ghost unembed_tot_or_ghost fstar_tc_core_tot_or_ghost.t
let (e_tot_or_ghost_nbe :
  FStarC_TypeChecker_Core.tot_or_ghost FStarC_TypeChecker_NBETerm.embedding)
  =
  let embed_tot_or_ghost cb res =
    match res with
    | FStarC_TypeChecker_Core.E_Total ->
        mkConstruct fstar_tc_core_tot_or_ghost_ETotal.fv [] []
    | FStarC_TypeChecker_Core.E_Ghost ->
        mkConstruct fstar_tc_core_tot_or_ghost_EGhost.fv [] [] in
  let unembed_tot_or_ghost cb t =
    let uu___ = FStarC_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu___ with
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          fstar_tc_core_tot_or_ghost_ETotal.lid
        -> FStar_Pervasives_Native.Some FStarC_TypeChecker_Core.E_Total
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          fstar_tc_core_tot_or_ghost_EGhost.lid
        -> FStar_Pervasives_Native.Some FStarC_TypeChecker_Core.E_Ghost
    | uu___1 ->
        ((let uu___3 =
            FStarC_Compiler_Effect.op_Bang FStarC_Options.debug_embedding in
          if uu___3
          then
            let uu___4 =
              let uu___5 = FStarC_TypeChecker_NBETerm.t_to_string t in
              FStarC_Compiler_Util.format1 "Not an embedded tot_or_ghost: %s"
                uu___5 in
            FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded
              () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___4)
          else ());
         FStar_Pervasives_Native.None) in
  {
    FStarC_TypeChecker_NBETerm.em = embed_tot_or_ghost;
    FStarC_TypeChecker_NBETerm.un = unembed_tot_or_ghost;
    FStarC_TypeChecker_NBETerm.typ =
      (fun uu___ -> mkFV fstar_tc_core_tot_or_ghost.fv [] []);
    FStarC_TypeChecker_NBETerm.e_typ =
      (fun uu___ -> fv_as_emb_typ fstar_tc_core_tot_or_ghost.fv)
  }
let (t_tref : FStarC_Syntax_Syntax.term) =
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.tref_lid
          FStar_Pervasives_Native.None in
      FStarC_Syntax_Syntax.fv_to_tm uu___2 in
    FStarC_Syntax_Syntax.mk_Tm_uinst uu___1 [FStarC_Syntax_Syntax.U_zero] in
  let uu___1 =
    let uu___2 = FStarC_Syntax_Syntax.iarg FStarC_Syntax_Syntax.t_term in
    [uu___2] in
  FStarC_Syntax_Syntax.mk_Tm_app uu___ uu___1
    FStarC_Compiler_Range_Type.dummyRange
let e_tref :
  'a .
    unit ->
      'a FStarC_Tactics_Types.tref FStarC_Syntax_Embeddings_Base.embedding
  =
  fun uu___ ->
    let em r rng _shadow _norm =
      FStarC_Syntax_Util.mk_lazy r t_tref FStarC_Syntax_Syntax.Lazy_tref
        (FStar_Pervasives_Native.Some rng) in
    let un t uu___1 =
      let uu___2 =
        let uu___3 = FStarC_Syntax_Subst.compress t in
        uu___3.FStarC_Syntax_Syntax.n in
      match uu___2 with
      | FStarC_Syntax_Syntax.Tm_lazy
          { FStarC_Syntax_Syntax.blob = blob;
            FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_tref;
            FStarC_Syntax_Syntax.ltyp = uu___3;
            FStarC_Syntax_Syntax.rng = uu___4;_}
          ->
          let uu___5 = FStarC_Dyn.undyn blob in
          FStar_Pervasives_Native.Some uu___5
      | uu___3 -> FStar_Pervasives_Native.None in
    FStarC_Syntax_Embeddings_Base.mk_emb_full em un (fun uu___1 -> t_tref)
      (fun i -> "tref")
      (fun uu___1 ->
         let uu___2 =
           let uu___3 =
             FStarC_Ident.string_of_lid FStarC_Parser_Const.tref_lid in
           (uu___3, [FStarC_Syntax_Syntax.ET_abstract]) in
         FStarC_Syntax_Syntax.ET_app uu___2)
let e_tref_nbe :
  'a .
    unit -> 'a FStarC_Tactics_Types.tref FStarC_TypeChecker_NBETerm.embedding
  =
  fun uu___ ->
    let embed_tref _cb r =
      let li =
        let uu___1 = FStarC_Dyn.mkdyn r in
        {
          FStarC_Syntax_Syntax.blob = uu___1;
          FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_tref;
          FStarC_Syntax_Syntax.ltyp = t_tref;
          FStarC_Syntax_Syntax.rng = FStarC_Compiler_Range_Type.dummyRange
        } in
      let thunk =
        FStarC_Thunk.mk
          (fun uu___1 ->
             FStarC_TypeChecker_NBETerm.mk_t
               (FStarC_TypeChecker_NBETerm.Constant
                  (FStarC_TypeChecker_NBETerm.String
                     ("(((tref.nbe)))",
                       FStarC_Compiler_Range_Type.dummyRange)))) in
      FStarC_TypeChecker_NBETerm.mk_t
        (FStarC_TypeChecker_NBETerm.Lazy ((FStar_Pervasives.Inl li), thunk)) in
    let unembed_tref _cb t =
      let uu___1 = FStarC_TypeChecker_NBETerm.nbe_t_of_t t in
      match uu___1 with
      | FStarC_TypeChecker_NBETerm.Lazy
          (FStar_Pervasives.Inl
           { FStarC_Syntax_Syntax.blob = b;
             FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_tref;
             FStarC_Syntax_Syntax.ltyp = uu___2;
             FStarC_Syntax_Syntax.rng = uu___3;_},
           uu___4)
          ->
          let uu___5 = FStarC_Dyn.undyn b in
          FStar_Pervasives_Native.Some uu___5
      | uu___2 ->
          ((let uu___4 =
              FStarC_Compiler_Effect.op_Bang FStarC_Options.debug_embedding in
            if uu___4
            then
              let uu___5 =
                let uu___6 = FStarC_TypeChecker_NBETerm.t_to_string t in
                FStarC_Compiler_Util.format1 "Not an embedded NBE tref: %s\n"
                  uu___6 in
              FStarC_Errors.log_issue0
                FStarC_Errors_Codes.Warning_NotEmbedded ()
                (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                (Obj.magic uu___5)
            else ());
           FStar_Pervasives_Native.None) in
    {
      FStarC_TypeChecker_NBETerm.em = embed_tref;
      FStarC_TypeChecker_NBETerm.un = unembed_tref;
      FStarC_TypeChecker_NBETerm.typ =
        (fun uu___1 ->
           let term_t =
             let uu___2 =
               FStarC_Syntax_Syntax.lid_as_fv
                 FStarC_Parser_Const.fstar_syntax_syntax_term
                 FStar_Pervasives_Native.None in
             mkFV uu___2 [] [] in
           let uu___2 =
             FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.tref_lid
               FStar_Pervasives_Native.None in
           let uu___3 =
             let uu___4 = FStarC_TypeChecker_NBETerm.as_arg term_t in
             [uu___4] in
           mkFV uu___2 [FStarC_Syntax_Syntax.U_zero] uu___3);
      FStarC_TypeChecker_NBETerm.e_typ =
        (fun uu___1 ->
           let uu___2 =
             let uu___3 =
               FStarC_Ident.string_of_lid FStarC_Parser_Const.tref_lid in
             (uu___3, [FStarC_Syntax_Syntax.ET_abstract]) in
           FStarC_Syntax_Syntax.ET_app uu___2)
    }
let (e_guard_policy :
  FStarC_Tactics_Types.guard_policy FStarC_Syntax_Embeddings_Base.embedding)
  =
  let embed_guard_policy rng p =
    match p with
    | FStarC_Tactics_Types.SMT -> fstar_tactics_SMT.t
    | FStarC_Tactics_Types.SMTSync -> fstar_tactics_SMTSync.t
    | FStarC_Tactics_Types.Goal -> fstar_tactics_Goal.t
    | FStarC_Tactics_Types.Force -> fstar_tactics_Force.t
    | FStarC_Tactics_Types.Drop -> fstar_tactics_Drop.t in
  let unembed_guard_policy t =
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_fvar fv when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.SMT
    | FStarC_Syntax_Syntax.Tm_fvar fv when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMTSync.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.SMTSync
    | FStarC_Syntax_Syntax.Tm_fvar fv when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.Goal
    | FStarC_Syntax_Syntax.Tm_fvar fv when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.Force
    | FStarC_Syntax_Syntax.Tm_fvar fv when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.Drop
    | uu___1 -> FStar_Pervasives_Native.None in
  mk_emb embed_guard_policy unembed_guard_policy fstar_tactics_guard_policy.t
let (e_guard_policy_nbe :
  FStarC_Tactics_Types.guard_policy FStarC_TypeChecker_NBETerm.embedding) =
  let embed_guard_policy cb p =
    match p with
    | FStarC_Tactics_Types.SMT -> mkConstruct fstar_tactics_SMT.fv [] []
    | FStarC_Tactics_Types.SMTSync ->
        mkConstruct fstar_tactics_SMTSync.fv [] []
    | FStarC_Tactics_Types.Goal -> mkConstruct fstar_tactics_Goal.fv [] []
    | FStarC_Tactics_Types.Force -> mkConstruct fstar_tactics_Force.fv [] []
    | FStarC_Tactics_Types.Drop -> mkConstruct fstar_tactics_Drop.fv [] [] in
  let unembed_guard_policy cb t =
    let uu___ = FStarC_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu___ with
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.SMT
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMTSync.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.SMTSync
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.Goal
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.Force
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Types.Drop
    | uu___1 -> FStar_Pervasives_Native.None in
  {
    FStarC_TypeChecker_NBETerm.em = embed_guard_policy;
    FStarC_TypeChecker_NBETerm.un = unembed_guard_policy;
    FStarC_TypeChecker_NBETerm.typ =
      (fun uu___ -> mkFV fstar_tactics_guard_policy.fv [] []);
    FStarC_TypeChecker_NBETerm.e_typ =
      (fun uu___ -> fv_as_emb_typ fstar_tactics_guard_policy.fv)
  }