open Prims
type name = FStarC_Syntax_Syntax.bv
let fstar_tactics_lid' (s : Prims.string Prims.list) : FStarC_Ident.lid=
  FStarC_Parser_Const.fstar_tactics_lid' s
let fstar_stubs_tactics_lid' (s : Prims.string Prims.list) :
  FStarC_Ident.lid= FStarC_Parser_Const.fstar_stubs_tactics_lid' s
let lid_as_tm (l : FStarC_Ident.lident) : FStarC_Syntax_Syntax.term=
  let uu___ = FStarC_Syntax_Syntax.lid_as_fv l FStar_Pervasives_Native.None in
  FStarC_Syntax_Syntax.fv_to_tm uu___
let mk_tactic_lid_as_term (s : Prims.string) : FStarC_Syntax_Syntax.term=
  let uu___ = fstar_tactics_lid' ["Effect"; s] in lid_as_tm uu___
type tac_constant =
  {
  lid: FStarC_Ident.lid ;
  fv: FStarC_Syntax_Syntax.fv ;
  t: FStarC_Syntax_Syntax.term }
let __proj__Mktac_constant__item__lid (projectee : tac_constant) :
  FStarC_Ident.lid= match projectee with | { lid; fv; t;_} -> lid
let __proj__Mktac_constant__item__fv (projectee : tac_constant) :
  FStarC_Syntax_Syntax.fv= match projectee with | { lid; fv; t;_} -> fv
let __proj__Mktac_constant__item__t (projectee : tac_constant) :
  FStarC_Syntax_Syntax.term= match projectee with | { lid; fv; t;_} -> t
let lid_as_data_fv (l : FStarC_Ident.lident) : FStarC_Syntax_Syntax.fv=
  FStarC_Syntax_Syntax.lid_as_fv l
    (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor)
let lid_as_data_tm (l : FStarC_Ident.lident) : FStarC_Syntax_Syntax.term=
  let uu___ = lid_as_data_fv l in FStarC_Syntax_Syntax.fv_to_tm uu___
let fstar_tactics_data (ns : Prims.string Prims.list) : tac_constant=
  let lid = fstar_stubs_tactics_lid' ns in
  let uu___ = lid_as_data_fv lid in
  let uu___1 = lid_as_data_tm lid in { lid; fv = uu___; t = uu___1 }
let fstar_tactics_const (ns : Prims.string Prims.list) : tac_constant=
  let lid = fstar_stubs_tactics_lid' ns in
  let uu___ = FStarC_Syntax_Syntax.fvconst lid in
  let uu___1 = FStarC_Syntax_Syntax.tconst lid in
  { lid; fv = uu___; t = uu___1 }
let fstar_tc_core_lid (s : Prims.string) : FStarC_Ident.lid=
  FStarC_Ident.lid_of_path
    (FStarC_List.op_At ["FStar"; "Stubs"; "TypeChecker"; "Core"] [s])
    FStarC_Range_Type.dummyRange
let fstar_tc_core_data (s : Prims.string) : tac_constant=
  let lid = fstar_tc_core_lid s in
  let uu___ = lid_as_data_fv lid in
  let uu___1 = lid_as_data_tm lid in { lid; fv = uu___; t = uu___1 }
let fstar_tc_core_const (s : Prims.string) : tac_constant=
  let lid = fstar_tc_core_lid s in
  let uu___ = FStarC_Syntax_Syntax.fvconst lid in
  let uu___1 = FStarC_Syntax_Syntax.tconst lid in
  { lid; fv = uu___; t = uu___1 }
let fstar_tactics_proofstate : tac_constant=
  fstar_tactics_const ["Types"; "proofstate"]
let fstar_tactics_ref_proofstate : tac_constant=
  fstar_tactics_const ["Types"; "ref_proofstate"]
let fstar_tactics_goal : tac_constant= fstar_tactics_const ["Types"; "goal"]
let fstar_tactics_TacticFailure : tac_constant=
  fstar_tactics_data ["Common"; "TacticFailure"]
let fstar_tactics_SKIP : tac_constant= fstar_tactics_data ["Common"; "SKIP"]
let fstar_tactics_Stop : tac_constant= fstar_tactics_data ["Common"; "Stop"]
let fstar_tactics_direction : tac_constant=
  fstar_tactics_const ["Types"; "direction"]
let fstar_tactics_topdown : tac_constant=
  fstar_tactics_data ["Types"; "TopDown"]
let fstar_tactics_bottomup : tac_constant=
  fstar_tactics_data ["Types"; "BottomUp"]
let fstar_tactics_ctrl_flag : tac_constant=
  fstar_tactics_const ["Types"; "ctrl_flag"]
let fstar_tactics_Continue : tac_constant=
  fstar_tactics_data ["Types"; "Continue"]
let fstar_tactics_Skip : tac_constant= fstar_tactics_data ["Types"; "Skip"]
let fstar_tactics_Abort : tac_constant= fstar_tactics_data ["Types"; "Abort"]
let fstar_tc_core_unfold_side : tac_constant=
  fstar_tc_core_const "unfold_side"
let fstar_tc_core_unfold_side_Left : tac_constant= fstar_tc_core_data "Left"
let fstar_tc_core_unfold_side_Right : tac_constant=
  fstar_tc_core_data "Right"
let fstar_tc_core_unfold_side_Both : tac_constant= fstar_tc_core_data "Both"
let fstar_tc_core_unfold_side_Neither : tac_constant=
  fstar_tc_core_data "Neither"
let fstar_tc_core_tot_or_ghost : tac_constant=
  fstar_tc_core_const "tot_or_ghost"
let fstar_tc_core_tot_or_ghost_ETotal : tac_constant=
  fstar_tc_core_data "E_Total"
let fstar_tc_core_tot_or_ghost_EGhost : tac_constant=
  fstar_tc_core_data "E_Ghost"
let fstar_tactics_guard_policy : tac_constant=
  fstar_tactics_const ["Types"; "guard_policy"]
let fstar_tactics_SMT : tac_constant= fstar_tactics_data ["Types"; "SMT"]
let fstar_tactics_SMTSync : tac_constant=
  fstar_tactics_data ["Types"; "SMTSync"]
let fstar_tactics_Goal : tac_constant= fstar_tactics_data ["Types"; "Goal"]
let fstar_tactics_Drop : tac_constant= fstar_tactics_data ["Types"; "Drop"]
let fstar_tactics_Force : tac_constant= fstar_tactics_data ["Types"; "Force"]
let mk_emb (em : FStarC_Range_Type.t -> 'a -> FStarC_Syntax_Syntax.term)
  (un : FStarC_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option)
  (t : FStarC_Syntax_Syntax.term) :
  'a FStarC_Syntax_Embeddings_Base.embedding=
  let uu___ = FStarC_Syntax_Embeddings_Base.term_as_fv t in
  FStarC_Syntax_Embeddings_Base.mk_emb (fun x r _topt _norm -> em r x)
    (fun x _norm -> un x) uu___
let embed (uu___ : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (r : FStarC_Range_Type.t) (x : 'a) : FStarC_Syntax_Syntax.term=
  let uu___1 = FStarC_Syntax_Embeddings_Base.embed uu___ x in
  uu___1 r FStar_Pervasives_Native.None
    FStarC_Syntax_Embeddings_Base.id_norm_cb
let unembed' (uu___ : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (x : FStarC_Syntax_Syntax.term) : 'a FStar_Pervasives_Native.option=
  FStarC_Syntax_Embeddings_Base.unembed uu___ x
    FStarC_Syntax_Embeddings_Base.id_norm_cb
let hd'_and_args (tm : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.term' * FStarC_Syntax_Syntax.args)=
  let tm1 = FStarC_Syntax_Util.unascribe tm in
  let uu___ = FStarC_Syntax_Util.head_and_args tm1 in
  match uu___ with
  | (hd, args) ->
      let uu___1 =
        let uu___2 = FStarC_Syntax_Util.un_uinst hd in
        uu___2.FStarC_Syntax_Syntax.n in
      (uu___1, args)
let e_ref_proofstate :
  FStarC_Tactics_Types.ref_proofstate FStarC_Syntax_Embeddings_Base.embedding=
  FStarC_Syntax_Embeddings_Base.e_lazy
    FStarC_Syntax_Syntax.Lazy_ref_proofstate fstar_tactics_ref_proofstate.t
let e_proofstate :
  FStarC_Tactics_Types.proofstate FStarC_Syntax_Embeddings_Base.embedding=
  FStarC_Syntax_Embeddings_Base.e_lazy FStarC_Syntax_Syntax.Lazy_proofstate
    fstar_tactics_proofstate.t
let e_goal :
  FStarC_Tactics_Types.goal FStarC_Syntax_Embeddings_Base.embedding=
  FStarC_Syntax_Embeddings_Base.e_lazy FStarC_Syntax_Syntax.Lazy_goal
    fstar_tactics_goal.t
let unfold_lazy_ref_proofstate (i : FStarC_Syntax_Syntax.lazyinfo) :
  FStarC_Syntax_Syntax.term=
  FStarC_Syntax_Util.exp_string "(((ref proofstate)))"
let unfold_lazy_proofstate (i : FStarC_Syntax_Syntax.lazyinfo) :
  FStarC_Syntax_Syntax.term= FStarC_Syntax_Util.exp_string "(((proofstate)))"
let unfold_lazy_goal (i : FStarC_Syntax_Syntax.lazyinfo) :
  FStarC_Syntax_Syntax.term= FStarC_Syntax_Util.exp_string "(((goal)))"
let mkFV (fv : FStarC_Syntax_Syntax.fv)
  (us : FStarC_Syntax_Syntax.universe Prims.list)
  (ts :
    (FStarC_TypeChecker_NBETerm.t * FStarC_Syntax_Syntax.aqual) Prims.list)
  : FStarC_TypeChecker_NBETerm.t=
  FStarC_TypeChecker_NBETerm.mkFV fv (FStarC_List.rev us)
    (FStarC_List.rev ts)
let mkConstruct (fv : FStarC_Syntax_Syntax.fv)
  (us : FStarC_Syntax_Syntax.universe Prims.list)
  (ts :
    (FStarC_TypeChecker_NBETerm.t * FStarC_Syntax_Syntax.aqual) Prims.list)
  : FStarC_TypeChecker_NBETerm.t=
  FStarC_TypeChecker_NBETerm.mkConstruct fv (FStarC_List.rev us)
    (FStarC_List.rev ts)
let fv_as_emb_typ (fv : FStarC_Syntax_Syntax.fv) :
  FStarC_Syntax_Syntax.emb_typ=
  let uu___ =
    let uu___1 =
      FStarC_Class_Show.show FStarC_Ident.showable_lident
        fv.FStarC_Syntax_Syntax.fv_name in
    (uu___1, []) in
  FStarC_Syntax_Syntax.ET_app uu___
let e_ref_proofstate_nbe :
  FStarC_Tactics_Types.ref_proofstate FStarC_TypeChecker_NBETerm.embedding=
  let embed_ref_proofstate _cb ps =
    let li =
      let uu___ = FStarC_Dyn.mkdyn ps in
      {
        FStarC_Syntax_Syntax.blob = uu___;
        FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_ref_proofstate;
        FStarC_Syntax_Syntax.ltyp = (fstar_tactics_ref_proofstate.t);
        FStarC_Syntax_Syntax.rng = FStarC_Range_Type.dummyRange
      } in
    let thunk =
      FStarC_Thunk.mk
        (fun uu___ ->
           FStarC_TypeChecker_NBETerm.mk_t
             (FStarC_TypeChecker_NBETerm.Constant
                (FStarC_TypeChecker_NBETerm.String
                   ("(((ref_proofstate.nbe)))", FStarC_Range_Type.dummyRange)))) in
    FStarC_TypeChecker_NBETerm.mk_t
      (FStarC_TypeChecker_NBETerm.Lazy ((FStar_Pervasives.Inl li), thunk)) in
  let unembed_ref_proofstate _cb t =
    let uu___ = FStarC_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu___ with
    | FStarC_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStarC_Syntax_Syntax.blob = b;
           FStarC_Syntax_Syntax.lkind =
             FStarC_Syntax_Syntax.Lazy_ref_proofstate;
           FStarC_Syntax_Syntax.ltyp = uu___1;
           FStarC_Syntax_Syntax.rng = uu___2;_},
         uu___3)
        ->
        let uu___4 = FStarC_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___4
    | uu___1 ->
        ((let uu___3 = FStarC_Effect.op_Bang FStarC_Options.debug_embedding in
          if uu___3
          then
            let uu___4 =
              let uu___5 = FStarC_TypeChecker_NBETerm.t_to_string t in
              FStarC_Format.fmt1 "Not an embedded NBE ref_proofstate: %s\n"
                uu___5 in
            FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded
              () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___4)
          else ());
         FStar_Pervasives_Native.None) in
  {
    FStarC_TypeChecker_NBETerm.em = embed_ref_proofstate;
    FStarC_TypeChecker_NBETerm.un = unembed_ref_proofstate;
    FStarC_TypeChecker_NBETerm.typ =
      (fun uu___ -> mkFV fstar_tactics_ref_proofstate.fv [] []);
    FStarC_TypeChecker_NBETerm.e_typ =
      (fun uu___ -> fv_as_emb_typ fstar_tactics_ref_proofstate.fv)
  }
let e_proofstate_nbe :
  FStarC_Tactics_Types.proofstate FStarC_TypeChecker_NBETerm.embedding=
  let embed_proofstate _cb ps =
    let li =
      let uu___ = FStarC_Dyn.mkdyn ps in
      {
        FStarC_Syntax_Syntax.blob = uu___;
        FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_proofstate;
        FStarC_Syntax_Syntax.ltyp = (fstar_tactics_proofstate.t);
        FStarC_Syntax_Syntax.rng = FStarC_Range_Type.dummyRange
      } in
    let thunk =
      FStarC_Thunk.mk
        (fun uu___ ->
           FStarC_TypeChecker_NBETerm.mk_t
             (FStarC_TypeChecker_NBETerm.Constant
                (FStarC_TypeChecker_NBETerm.String
                   ("(((proofstate.nbe)))", FStarC_Range_Type.dummyRange)))) in
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
        ((let uu___3 = FStarC_Effect.op_Bang FStarC_Options.debug_embedding in
          if uu___3
          then
            let uu___4 =
              let uu___5 = FStarC_TypeChecker_NBETerm.t_to_string t in
              FStarC_Format.fmt1 "Not an embedded NBE proofstate: %s\n"
                uu___5 in
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
let e_goal_nbe :
  FStarC_Tactics_Types.goal FStarC_TypeChecker_NBETerm.embedding=
  let embed_goal _cb ps =
    let li =
      let uu___ = FStarC_Dyn.mkdyn ps in
      {
        FStarC_Syntax_Syntax.blob = uu___;
        FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_goal;
        FStarC_Syntax_Syntax.ltyp = (fstar_tactics_goal.t);
        FStarC_Syntax_Syntax.rng = FStarC_Range_Type.dummyRange
      } in
    let thunk =
      FStarC_Thunk.mk
        (fun uu___ ->
           FStarC_TypeChecker_NBETerm.mk_t
             (FStarC_TypeChecker_NBETerm.Constant
                (FStarC_TypeChecker_NBETerm.String
                   ("(((goal.nbe)))", FStarC_Range_Type.dummyRange)))) in
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
        ((let uu___3 = FStarC_Effect.op_Bang FStarC_Options.debug_embedding in
          if uu___3
          then
            let uu___4 =
              let uu___5 = FStarC_TypeChecker_NBETerm.t_to_string t in
              FStarC_Format.fmt1 "Not an embedded NBE goal: %s" uu___5 in
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
let e_exn : Prims.exn FStarC_Syntax_Embeddings_Base.embedding=
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
    | FStarC_Errors.Stop ->
        let uu___2 = fstar_tactics_Stop.t in
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
        let uu___2 =
          let uu___3 = FStarC_Errors.issue_of_exn e1 in
          match uu___3 with
          | FStar_Pervasives_Native.Some
              { FStarC_Errors.issue_msg = issue_msg;
                FStarC_Errors.issue_level = uu___4;
                FStarC_Errors.issue_range = issue_range;
                FStarC_Errors.issue_number = uu___5;
                FStarC_Errors.issue_ctx = uu___6;_}
              -> (issue_msg, issue_range)
          | FStar_Pervasives_Native.None ->
              let uu___4 =
                let uu___5 =
                  let uu___6 = FStarC_Util.message_of_exn e1 in
                  FStar_Pprint.arbitrary_string uu___6 in
                [uu___5] in
              (uu___4, FStar_Pervasives_Native.None) in
        (match uu___2 with
         | (msg, range) ->
             let msg1 =
               let uu___3 = FStarC_Errors_Msg.text "Uncaught exception" in
               uu___3 :: msg in
             let uu___3 =
               let uu___4 =
                 let uu___5 =
                   embed
                     (FStarC_Syntax_Embeddings.e_tuple2
                        (FStarC_Syntax_Embeddings.e_list
                           FStarC_Syntax_Embeddings.e_document)
                        (FStarC_Syntax_Embeddings.e_option
                           FStarC_Syntax_Embeddings.e_range)) rng
                     (msg1, range) in
                 FStarC_Syntax_Syntax.as_arg uu___5 in
               [uu___4] in
             FStarC_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure.t
               uu___3 rng) in
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
        FStarC_Option.bind uu___3
          (fun s1 ->
             FStar_Pervasives_Native.Some
               (FStarC_Tactics_Common.TacticFailure s1))
    | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SKIP.lid ->
        FStar_Pervasives_Native.Some FStarC_Tactics_Common.SKIP
    | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Stop.lid ->
        FStar_Pervasives_Native.Some FStarC_Errors.Stop
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
let e_exn_nbe : Prims.exn FStarC_TypeChecker_NBETerm.embedding=
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
          let uu___2 = FStarC_Util.message_of_exn e in
          FStarC_Format.fmt1 "cannot embed exn (NBE) : %s" uu___2 in
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
        FStarC_Option.bind uu___3
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
let e_direction :
  FStarC_Tactics_Types.direction FStarC_Syntax_Embeddings_Base.embedding=
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
let e_direction_nbe :
  FStarC_Tactics_Types.direction FStarC_TypeChecker_NBETerm.embedding=
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
        ((let uu___3 = FStarC_Effect.op_Bang FStarC_Options.debug_embedding in
          if uu___3
          then
            let uu___4 =
              let uu___5 = FStarC_TypeChecker_NBETerm.t_to_string t in
              FStarC_Format.fmt1 "Not an embedded direction: %s" uu___5 in
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
let e_ctrl_flag :
  FStarC_Tactics_Types.ctrl_flag FStarC_Syntax_Embeddings_Base.embedding=
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
let e_ctrl_flag_nbe :
  FStarC_Tactics_Types.ctrl_flag FStarC_TypeChecker_NBETerm.embedding=
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
        ((let uu___3 = FStarC_Effect.op_Bang FStarC_Options.debug_embedding in
          if uu___3
          then
            let uu___4 =
              let uu___5 = FStarC_TypeChecker_NBETerm.t_to_string t in
              FStarC_Format.fmt1 "Not an embedded ctrl_flag: %s" uu___5 in
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
let e_unfold_side :
  FStarC_TypeChecker_Core.side FStarC_Syntax_Embeddings_Base.embedding=
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
let e_unfold_side_nbe :
  FStarC_TypeChecker_Core.side FStarC_TypeChecker_NBETerm.embedding=
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
        ((let uu___3 = FStarC_Effect.op_Bang FStarC_Options.debug_embedding in
          if uu___3
          then
            let uu___4 =
              let uu___5 = FStarC_TypeChecker_NBETerm.t_to_string t in
              FStarC_Format.fmt1 "Not an embedded unfold_side: %s" uu___5 in
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
let e_tot_or_ghost :
  FStarC_TypeChecker_Core.tot_or_ghost
    FStarC_Syntax_Embeddings_Base.embedding=
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
let e_tot_or_ghost_nbe :
  FStarC_TypeChecker_Core.tot_or_ghost FStarC_TypeChecker_NBETerm.embedding=
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
        ((let uu___3 = FStarC_Effect.op_Bang FStarC_Options.debug_embedding in
          if uu___3
          then
            let uu___4 =
              let uu___5 = FStarC_TypeChecker_NBETerm.t_to_string t in
              FStarC_Format.fmt1 "Not an embedded tot_or_ghost: %s" uu___5 in
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
let t_tref : FStarC_Syntax_Syntax.term=
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
  FStarC_Syntax_Syntax.mk_Tm_app uu___ uu___1 FStarC_Range_Type.dummyRange
let e_tref (uu___ : unit) :
  'a FStarC_Tactics_Types.tref FStarC_Syntax_Embeddings_Base.embedding=
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
         let uu___3 = FStarC_Ident.string_of_lid FStarC_Parser_Const.tref_lid in
         (uu___3, [FStarC_Syntax_Syntax.ET_abstract]) in
       FStarC_Syntax_Syntax.ET_app uu___2)
let e_tref_nbe (uu___ : unit) :
  'a FStarC_Tactics_Types.tref FStarC_TypeChecker_NBETerm.embedding=
  let embed_tref _cb r =
    let li =
      let uu___1 = FStarC_Dyn.mkdyn r in
      {
        FStarC_Syntax_Syntax.blob = uu___1;
        FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_tref;
        FStarC_Syntax_Syntax.ltyp = t_tref;
        FStarC_Syntax_Syntax.rng = FStarC_Range_Type.dummyRange
      } in
    let thunk =
      FStarC_Thunk.mk
        (fun uu___1 ->
           FStarC_TypeChecker_NBETerm.mk_t
             (FStarC_TypeChecker_NBETerm.Constant
                (FStarC_TypeChecker_NBETerm.String
                   ("(((tref.nbe)))", FStarC_Range_Type.dummyRange)))) in
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
        ((let uu___4 = FStarC_Effect.op_Bang FStarC_Options.debug_embedding in
          if uu___4
          then
            let uu___5 =
              let uu___6 = FStarC_TypeChecker_NBETerm.t_to_string t in
              FStarC_Format.fmt1 "Not an embedded NBE tref: %s\n" uu___6 in
            FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded
              () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
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
           let uu___4 = FStarC_TypeChecker_NBETerm.as_arg term_t in [uu___4] in
         mkFV uu___2 [FStarC_Syntax_Syntax.U_zero] uu___3);
    FStarC_TypeChecker_NBETerm.e_typ =
      (fun uu___1 ->
         let uu___2 =
           let uu___3 =
             FStarC_Ident.string_of_lid FStarC_Parser_Const.tref_lid in
           (uu___3, [FStarC_Syntax_Syntax.ET_abstract]) in
         FStarC_Syntax_Syntax.ET_app uu___2)
  }
let e_guard_policy :
  FStarC_Tactics_Types.guard_policy FStarC_Syntax_Embeddings_Base.embedding=
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
let e_guard_policy_nbe :
  FStarC_Tactics_Types.guard_policy FStarC_TypeChecker_NBETerm.embedding=
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
