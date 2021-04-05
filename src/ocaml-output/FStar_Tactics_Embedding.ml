open Prims
type name = FStar_Syntax_Syntax.bv
let (fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid) =
  fun s -> FStar_Parser_Const.fstar_tactics_lid' s
let (lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l ->
    let uu___ =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None in
    FStar_All.pipe_right uu___ FStar_Syntax_Syntax.fv_to_tm
let (mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s -> let uu___ = fstar_tactics_lid' ["Effect"; s] in lid_as_tm uu___
type tac_constant =
  {
  lid: FStar_Ident.lid ;
  fv: FStar_Syntax_Syntax.fv ;
  t: FStar_Syntax_Syntax.term }
let (__proj__Mktac_constant__item__lid : tac_constant -> FStar_Ident.lid) =
  fun projectee -> match projectee with | { lid; fv; t;_} -> lid
let (__proj__Mktac_constant__item__fv :
  tac_constant -> FStar_Syntax_Syntax.fv) =
  fun projectee -> match projectee with | { lid; fv; t;_} -> fv
let (__proj__Mktac_constant__item__t :
  tac_constant -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | { lid; fv; t;_} -> t
let (lid_as_data_fv : FStar_Ident.lident -> FStar_Syntax_Syntax.fv) =
  fun l ->
    FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
      (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
let (lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l -> let uu___ = lid_as_data_fv l in FStar_Syntax_Syntax.fv_to_tm uu___
let (fstar_tactics_data : Prims.string Prims.list -> tac_constant) =
  fun ns ->
    let lid = fstar_tactics_lid' ns in
    let uu___ = lid_as_data_fv lid in
    let uu___1 = lid_as_data_tm lid in { lid; fv = uu___; t = uu___1 }
let (fstar_tactics_const : Prims.string Prims.list -> tac_constant) =
  fun ns ->
    let lid = fstar_tactics_lid' ns in
    let uu___ = FStar_Syntax_Syntax.fvconst lid in
    let uu___1 = FStar_Syntax_Syntax.tconst lid in
    { lid; fv = uu___; t = uu___1 }
let (fstar_tactics_proofstate : tac_constant) =
  fstar_tactics_const ["Types"; "proofstate"]
let (fstar_tactics_goal : tac_constant) =
  fstar_tactics_const ["Types"; "goal"]
let (fstar_tactics_TacticFailure : tac_constant) =
  fstar_tactics_data ["Common"; "TacticFailure"]
let (fstar_tactics_result : tac_constant) =
  fstar_tactics_const ["Types"; "result"]
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
let (fstar_tactics_guard_policy : tac_constant) =
  fstar_tactics_const ["Types"; "guard_policy"]
let (fstar_tactics_SMT : tac_constant) = fstar_tactics_data ["Types"; "SMT"]
let (fstar_tactics_Goal : tac_constant) =
  fstar_tactics_data ["Types"; "Goal"]
let (fstar_tactics_Drop : tac_constant) =
  fstar_tactics_data ["Types"; "Drop"]
let (fstar_tactics_Force : tac_constant) =
  fstar_tactics_data ["Types"; "Force"]
let mk_emb :
  'a .
    (FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option)
        -> FStar_Syntax_Syntax.term -> 'a FStar_Syntax_Embeddings.embedding
  =
  fun em ->
    fun un ->
      fun t ->
        let uu___ = FStar_Syntax_Embeddings.term_as_fv t in
        FStar_Syntax_Embeddings.mk_emb
          (fun x -> fun r -> fun _topt -> fun _norm -> em r x)
          (fun x -> fun w -> fun _norm -> un w x) uu___
let embed :
  'uuuuu .
    'uuuuu FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'uuuuu -> FStar_Syntax_Syntax.term
  =
  fun e ->
    fun r ->
      fun x ->
        let uu___ = FStar_Syntax_Embeddings.embed e x in
        uu___ r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
let unembed' :
  'uuuuu .
    Prims.bool ->
      'uuuuu FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term -> 'uuuuu FStar_Pervasives_Native.option
  =
  fun w ->
    fun e ->
      fun x ->
        let uu___ = FStar_Syntax_Embeddings.unembed e x in
        uu___ w FStar_Syntax_Embeddings.id_norm_cb
let (t_result_of :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    let uu___ = let uu___1 = FStar_Syntax_Syntax.as_arg t in [uu___1] in
    FStar_Syntax_Util.mk_app fstar_tactics_result.t uu___
let (hd'_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' * (FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun tm ->
    let tm1 = FStar_Syntax_Util.unascribe tm in
    let uu___ = FStar_Syntax_Util.head_and_args tm1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 = FStar_Syntax_Util.un_uinst hd in
          uu___2.FStar_Syntax_Syntax.n in
        (uu___1, args)
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps fstar_tactics_proofstate.t
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng) in
  let unembed_proofstate w t =
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
          FStar_Syntax_Syntax.ltyp = uu___1;
          FStar_Syntax_Syntax.rng = uu___2;_}
        ->
        let uu___3 = FStar_Dyn.undyn b in
        FStar_All.pipe_left
          (fun uu___4 -> FStar_Pervasives_Native.Some uu___4) uu___3
    | uu___1 ->
        (if w
         then
           (let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded proofstate: %s\n" uu___5 in
              (FStar_Errors.Warning_NotEmbedded, uu___4) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu___3)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_proofstate unembed_proofstate fstar_tactics_proofstate.t
let (unfold_lazy_proofstate :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i -> FStar_Syntax_Util.exp_string "(((proofstate)))"
let (mkFV :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list ->
      (FStar_TypeChecker_NBETerm.t * FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_TypeChecker_NBETerm.t)
  =
  fun fv ->
    fun us ->
      fun ts ->
        FStar_TypeChecker_NBETerm.mkFV fv (FStar_List.rev us)
          (FStar_List.rev ts)
let (mkConstruct :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list ->
      (FStar_TypeChecker_NBETerm.t * FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_TypeChecker_NBETerm.t)
  =
  fun fv ->
    fun us ->
      fun ts ->
        FStar_TypeChecker_NBETerm.mkConstruct fv (FStar_List.rev us)
          (FStar_List.rev ts)
let (fv_as_emb_typ : FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.emb_typ) =
  fun fv ->
    let uu___ =
      let uu___1 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      (uu___1, []) in
    FStar_Syntax_Syntax.ET_app uu___
let (e_proofstate_nbe :
  FStar_Tactics_Types.proofstate FStar_TypeChecker_NBETerm.embedding) =
  let embed_proofstate _cb ps =
    let li =
      let uu___ = FStar_Dyn.mkdyn ps in
      {
        FStar_Syntax_Syntax.blob = uu___;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
        FStar_Syntax_Syntax.ltyp = (fstar_tactics_proofstate.t);
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      } in
    let thunk =
      FStar_Thunk.mk
        (fun uu___ ->
           FStar_All.pipe_left FStar_TypeChecker_NBETerm.mk_t
             (FStar_TypeChecker_NBETerm.Constant
                (FStar_TypeChecker_NBETerm.String
                   ("(((proofstate.nbe)))", FStar_Range.dummyRange)))) in
    FStar_TypeChecker_NBETerm.mk_t
      (FStar_TypeChecker_NBETerm.Lazy ((FStar_Pervasives.Inl li), thunk)) in
  let unembed_proofstate _cb t =
    let uu___ = FStar_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu___ with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
           FStar_Syntax_Syntax.ltyp = uu___1;
           FStar_Syntax_Syntax.rng = uu___2;_},
         uu___3)
        ->
        let uu___4 = FStar_Dyn.undyn b in
        FStar_All.pipe_left
          (fun uu___5 -> FStar_Pervasives_Native.Some uu___5) uu___4
    | uu___1 ->
        ((let uu___3 = FStar_ST.op_Bang FStar_Options.debug_embedding in
          if uu___3
          then
            let uu___4 =
              let uu___5 =
                let uu___6 = FStar_TypeChecker_NBETerm.t_to_string t in
                FStar_Util.format1 "Not an embedded NBE proofstate: %s\n"
                  uu___6 in
              (FStar_Errors.Warning_NotEmbedded, uu___5) in
            FStar_Errors.log_issue FStar_Range.dummyRange uu___4
          else ());
         FStar_Pervasives_Native.None) in
  let uu___ = mkFV fstar_tactics_proofstate.fv [] [] in
  let uu___1 = fv_as_emb_typ fstar_tactics_proofstate.fv in
  {
    FStar_TypeChecker_NBETerm.em = embed_proofstate;
    FStar_TypeChecker_NBETerm.un = unembed_proofstate;
    FStar_TypeChecker_NBETerm.typ = uu___;
    FStar_TypeChecker_NBETerm.emb_typ = uu___1
  }
let (e_goal : FStar_Tactics_Types.goal FStar_Syntax_Embeddings.embedding) =
  let embed_goal rng g =
    FStar_Syntax_Util.mk_lazy g fstar_tactics_goal.t
      FStar_Syntax_Syntax.Lazy_goal (FStar_Pervasives_Native.Some rng) in
  let unembed_goal w t =
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
          FStar_Syntax_Syntax.ltyp = uu___1;
          FStar_Syntax_Syntax.rng = uu___2;_}
        ->
        let uu___3 = FStar_Dyn.undyn b in
        FStar_All.pipe_left
          (fun uu___4 -> FStar_Pervasives_Native.Some uu___4) uu___3
    | uu___1 ->
        (if w
         then
           (let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded goal: %s" uu___5 in
              (FStar_Errors.Warning_NotEmbedded, uu___4) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu___3)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_goal unembed_goal fstar_tactics_goal.t
let (unfold_lazy_goal :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i -> FStar_Syntax_Util.exp_string "(((goal)))"
let (e_goal_nbe :
  FStar_Tactics_Types.goal FStar_TypeChecker_NBETerm.embedding) =
  let embed_goal _cb ps =
    let li =
      let uu___ = FStar_Dyn.mkdyn ps in
      {
        FStar_Syntax_Syntax.blob = uu___;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
        FStar_Syntax_Syntax.ltyp = (fstar_tactics_goal.t);
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      } in
    let thunk =
      FStar_Thunk.mk
        (fun uu___ ->
           FStar_All.pipe_left FStar_TypeChecker_NBETerm.mk_t
             (FStar_TypeChecker_NBETerm.Constant
                (FStar_TypeChecker_NBETerm.String
                   ("(((goal.nbe)))", FStar_Range.dummyRange)))) in
    FStar_All.pipe_left FStar_TypeChecker_NBETerm.mk_t
      (FStar_TypeChecker_NBETerm.Lazy ((FStar_Pervasives.Inl li), thunk)) in
  let unembed_goal _cb t =
    let uu___ = FStar_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu___ with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
           FStar_Syntax_Syntax.ltyp = uu___1;
           FStar_Syntax_Syntax.rng = uu___2;_},
         uu___3)
        ->
        let uu___4 = FStar_Dyn.undyn b in
        FStar_All.pipe_left
          (fun uu___5 -> FStar_Pervasives_Native.Some uu___5) uu___4
    | uu___1 ->
        ((let uu___3 = FStar_ST.op_Bang FStar_Options.debug_embedding in
          if uu___3
          then
            let uu___4 =
              let uu___5 =
                let uu___6 = FStar_TypeChecker_NBETerm.t_to_string t in
                FStar_Util.format1 "Not an embedded NBE goal: %s" uu___6 in
              (FStar_Errors.Warning_NotEmbedded, uu___5) in
            FStar_Errors.log_issue FStar_Range.dummyRange uu___4
          else ());
         FStar_Pervasives_Native.None) in
  let uu___ = mkFV fstar_tactics_goal.fv [] [] in
  let uu___1 = fv_as_emb_typ fstar_tactics_goal.fv in
  {
    FStar_TypeChecker_NBETerm.em = embed_goal;
    FStar_TypeChecker_NBETerm.un = unembed_goal;
    FStar_TypeChecker_NBETerm.typ = uu___;
    FStar_TypeChecker_NBETerm.emb_typ = uu___1
  }
let (e_exn : Prims.exn FStar_Syntax_Embeddings.embedding) =
  let embed_exn e rng uu___ uu___1 =
    match e with
    | FStar_Tactics_Common.TacticFailure s ->
        let uu___2 =
          let uu___3 =
            let uu___4 = embed FStar_Syntax_Embeddings.e_string rng s in
            FStar_Syntax_Syntax.as_arg uu___4 in
          [uu___3] in
        FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure.t uu___2
          rng
    | FStar_Tactics_Common.EExn t ->
        let uu___2 = t in
        {
          FStar_Syntax_Syntax.n = (uu___2.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___2.FStar_Syntax_Syntax.vars)
        }
    | e1 ->
        let s =
          let uu___2 = FStar_Util.message_of_exn e1 in
          Prims.op_Hat "uncaught exception: " uu___2 in
        let uu___2 =
          let uu___3 =
            let uu___4 = embed FStar_Syntax_Embeddings.e_string rng s in
            FStar_Syntax_Syntax.as_arg uu___4 in
          [uu___3] in
        FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure.t uu___2
          rng in
  let unembed_exn t w uu___ =
    let uu___1 = hd'_and_args t in
    match uu___1 with
    | (FStar_Syntax_Syntax.Tm_fvar fv, (s, uu___2)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure.lid ->
        let uu___3 = unembed' w FStar_Syntax_Embeddings.e_string s in
        FStar_Util.bind_opt uu___3
          (fun s1 ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Common.TacticFailure s1))
    | uu___2 -> FStar_Pervasives_Native.Some (FStar_Tactics_Common.EExn t) in
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStar_All.pipe_right FStar_Parser_Const.exn_lid
          FStar_Ident.string_of_lid in
      (uu___2, []) in
    FStar_Syntax_Syntax.ET_app uu___1 in
  FStar_Syntax_Embeddings.mk_emb_full embed_exn unembed_exn
    FStar_Syntax_Syntax.t_exn (fun uu___1 -> "(exn)") uu___
let (e_exn_nbe : Prims.exn FStar_TypeChecker_NBETerm.embedding) =
  let embed_exn cb e =
    match e with
    | FStar_Tactics_Common.TacticFailure s ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct fstar_tactics_TacticFailure.fv [] uu___
    | uu___ ->
        let uu___1 =
          let uu___2 = FStar_Util.message_of_exn e in
          FStar_Util.format1 "cannot embed exn (NBE) : %s" uu___2 in
        failwith uu___1 in
  let unembed_exn cb t =
    let uu___ = FStar_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu___ with
    | FStar_TypeChecker_NBETerm.Construct (fv, uu___1, (s, uu___2)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure.lid ->
        let uu___3 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s in
        FStar_Util.bind_opt uu___3
          (fun s1 ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Common.TacticFailure s1))
    | uu___1 -> FStar_Pervasives_Native.None in
  let fv_exn = FStar_Syntax_Syntax.fvconst FStar_Parser_Const.exn_lid in
  let uu___ = mkFV fv_exn [] [] in
  let uu___1 = fv_as_emb_typ fv_exn in
  {
    FStar_TypeChecker_NBETerm.em = embed_exn;
    FStar_TypeChecker_NBETerm.un = unembed_exn;
    FStar_TypeChecker_NBETerm.typ = uu___;
    FStar_TypeChecker_NBETerm.emb_typ = uu___1
  }
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea ->
    let embed_result res rng uu___ uu___1 =
      match res with
      | FStar_Tactics_Result.Success (a1, ps) ->
          let uu___2 =
            FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success.t
              [FStar_Syntax_Syntax.U_zero] in
          let uu___3 =
            let uu___4 =
              let uu___5 = FStar_Syntax_Embeddings.type_of ea in
              FStar_Syntax_Syntax.iarg uu___5 in
            let uu___5 =
              let uu___6 =
                let uu___7 = embed ea rng a1 in
                FStar_Syntax_Syntax.as_arg uu___7 in
              let uu___7 =
                let uu___8 =
                  let uu___9 = embed e_proofstate rng ps in
                  FStar_Syntax_Syntax.as_arg uu___9 in
                [uu___8] in
              uu___6 :: uu___7 in
            uu___4 :: uu___5 in
          FStar_Syntax_Syntax.mk_Tm_app uu___2 uu___3 rng
      | FStar_Tactics_Result.Failed (e, ps) ->
          let uu___2 =
            FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed.t
              [FStar_Syntax_Syntax.U_zero] in
          let uu___3 =
            let uu___4 =
              let uu___5 = FStar_Syntax_Embeddings.type_of ea in
              FStar_Syntax_Syntax.iarg uu___5 in
            let uu___5 =
              let uu___6 =
                let uu___7 = embed e_exn rng e in
                FStar_Syntax_Syntax.as_arg uu___7 in
              let uu___7 =
                let uu___8 =
                  let uu___9 = embed e_proofstate rng ps in
                  FStar_Syntax_Syntax.as_arg uu___9 in
                [uu___8] in
              uu___6 :: uu___7 in
            uu___4 :: uu___5 in
          FStar_Syntax_Syntax.mk_Tm_app uu___2 uu___3 rng in
    let unembed_result t w uu___ =
      let uu___1 = hd'_and_args t in
      match uu___1 with
      | (FStar_Syntax_Syntax.Tm_fvar fv, _t::(a1, uu___2)::(ps, uu___3)::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success.lid ->
          let uu___4 = unembed' w ea a1 in
          FStar_Util.bind_opt uu___4
            (fun a2 ->
               let uu___5 = unembed' w e_proofstate ps in
               FStar_Util.bind_opt uu___5
                 (fun ps1 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a2, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar fv, _t::(e, uu___2)::(ps, uu___3)::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed.lid ->
          let uu___4 = unembed' w e_exn e in
          FStar_Util.bind_opt uu___4
            (fun e1 ->
               let uu___5 = unembed' w e_proofstate ps in
               FStar_Util.bind_opt uu___5
                 (fun ps1 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu___2 ->
          (if w
           then
             (let uu___4 =
                let uu___5 =
                  let uu___6 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu___6 in
                (FStar_Errors.Warning_NotEmbedded, uu___5) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu___4)
           else ();
           FStar_Pervasives_Native.None) in
    let uu___ =
      let uu___1 = FStar_Syntax_Embeddings.type_of ea in t_result_of uu___1 in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          FStar_All.pipe_right fstar_tactics_result.lid
            FStar_Ident.string_of_lid in
        let uu___4 =
          let uu___5 = FStar_Syntax_Embeddings.emb_typ_of ea in [uu___5] in
        (uu___3, uu___4) in
      FStar_Syntax_Syntax.ET_app uu___2 in
    FStar_Syntax_Embeddings.mk_emb_full embed_result unembed_result uu___
      (fun uu___2 -> "") uu___1
let e_result_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'a FStar_Tactics_Result.__result FStar_TypeChecker_NBETerm.embedding
  =
  fun ea ->
    let embed_result cb res =
      match res with
      | FStar_Tactics_Result.Failed (e, ps) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_TypeChecker_NBETerm.type_of ea in
              FStar_TypeChecker_NBETerm.as_iarg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = FStar_TypeChecker_NBETerm.embed e_exn_nbe cb e in
                FStar_TypeChecker_NBETerm.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps in
                  FStar_TypeChecker_NBETerm.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          mkConstruct fstar_tactics_Failed.fv [FStar_Syntax_Syntax.U_zero]
            uu___
      | FStar_Tactics_Result.Success (a1, ps) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_TypeChecker_NBETerm.type_of ea in
              FStar_TypeChecker_NBETerm.as_iarg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = FStar_TypeChecker_NBETerm.embed ea cb a1 in
                FStar_TypeChecker_NBETerm.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps in
                  FStar_TypeChecker_NBETerm.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          mkConstruct fstar_tactics_Success.fv [FStar_Syntax_Syntax.U_zero]
            uu___ in
    let unembed_result cb t =
      let uu___ = FStar_TypeChecker_NBETerm.nbe_t_of_t t in
      match uu___ with
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu___1, (ps, uu___2)::(a1, uu___3)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success.lid ->
          let uu___4 = FStar_TypeChecker_NBETerm.unembed ea cb a1 in
          FStar_Util.bind_opt uu___4
            (fun a2 ->
               let uu___5 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps in
               FStar_Util.bind_opt uu___5
                 (fun ps1 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a2, ps1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu___1, (ps, uu___2)::(e, uu___3)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed.lid ->
          let uu___4 = FStar_TypeChecker_NBETerm.unembed e_exn_nbe cb e in
          FStar_Util.bind_opt uu___4
            (fun e1 ->
               let uu___5 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps in
               FStar_Util.bind_opt uu___5
                 (fun ps1 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu___1 -> FStar_Pervasives_Native.None in
    let uu___ = mkFV fstar_tactics_result.fv [] [] in
    let uu___1 = fv_as_emb_typ fstar_tactics_result.fv in
    {
      FStar_TypeChecker_NBETerm.em = embed_result;
      FStar_TypeChecker_NBETerm.un = unembed_result;
      FStar_TypeChecker_NBETerm.typ = uu___;
      FStar_TypeChecker_NBETerm.emb_typ = uu___1
    }
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown -> fstar_tactics_topdown.t
    | FStar_Tactics_Types.BottomUp -> fstar_tactics_bottomup.t in
  let unembed_direction w t =
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu___1 ->
        (if w
         then
           (let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded direction: %s" uu___5 in
              (FStar_Errors.Warning_NotEmbedded, uu___4) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu___3)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_direction unembed_direction fstar_tactics_direction.t
let (e_direction_nbe :
  FStar_Tactics_Types.direction FStar_TypeChecker_NBETerm.embedding) =
  let embed_direction cb res =
    match res with
    | FStar_Tactics_Types.TopDown ->
        mkConstruct fstar_tactics_topdown.fv [] []
    | FStar_Tactics_Types.BottomUp ->
        mkConstruct fstar_tactics_bottomup.fv [] [] in
  let unembed_direction cb t =
    let uu___ = FStar_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu___ with
    | FStar_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu___1 ->
        ((let uu___3 = FStar_ST.op_Bang FStar_Options.debug_embedding in
          if uu___3
          then
            let uu___4 =
              let uu___5 =
                let uu___6 = FStar_TypeChecker_NBETerm.t_to_string t in
                FStar_Util.format1 "Not an embedded direction: %s" uu___6 in
              (FStar_Errors.Warning_NotEmbedded, uu___5) in
            FStar_Errors.log_issue FStar_Range.dummyRange uu___4
          else ());
         FStar_Pervasives_Native.None) in
  let uu___ = mkFV fstar_tactics_direction.fv [] [] in
  let uu___1 = fv_as_emb_typ fstar_tactics_direction.fv in
  {
    FStar_TypeChecker_NBETerm.em = embed_direction;
    FStar_TypeChecker_NBETerm.un = unembed_direction;
    FStar_TypeChecker_NBETerm.typ = uu___;
    FStar_TypeChecker_NBETerm.emb_typ = uu___1
  }
let (e_ctrl_flag :
  FStar_Tactics_Types.ctrl_flag FStar_Syntax_Embeddings.embedding) =
  let embed_ctrl_flag rng d =
    match d with
    | FStar_Tactics_Types.Continue -> fstar_tactics_Continue.t
    | FStar_Tactics_Types.Skip -> fstar_tactics_Skip.t
    | FStar_Tactics_Types.Abort -> fstar_tactics_Abort.t in
  let unembed_ctrl_flag w t =
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Continue.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Continue
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Skip.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Skip
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Abort.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Abort
    | uu___1 ->
        (if w
         then
           (let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded ctrl_flag: %s" uu___5 in
              (FStar_Errors.Warning_NotEmbedded, uu___4) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu___3)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_ctrl_flag unembed_ctrl_flag fstar_tactics_ctrl_flag.t
let (e_ctrl_flag_nbe :
  FStar_Tactics_Types.ctrl_flag FStar_TypeChecker_NBETerm.embedding) =
  let embed_ctrl_flag cb res =
    match res with
    | FStar_Tactics_Types.Continue ->
        mkConstruct fstar_tactics_Continue.fv [] []
    | FStar_Tactics_Types.Skip -> mkConstruct fstar_tactics_Skip.fv [] []
    | FStar_Tactics_Types.Abort -> mkConstruct fstar_tactics_Abort.fv [] [] in
  let unembed_ctrl_flag cb t =
    let uu___ = FStar_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu___ with
    | FStar_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Continue.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Continue
    | FStar_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Skip.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Skip
    | FStar_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Abort.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Abort
    | uu___1 ->
        ((let uu___3 = FStar_ST.op_Bang FStar_Options.debug_embedding in
          if uu___3
          then
            let uu___4 =
              let uu___5 =
                let uu___6 = FStar_TypeChecker_NBETerm.t_to_string t in
                FStar_Util.format1 "Not an embedded ctrl_flag: %s" uu___6 in
              (FStar_Errors.Warning_NotEmbedded, uu___5) in
            FStar_Errors.log_issue FStar_Range.dummyRange uu___4
          else ());
         FStar_Pervasives_Native.None) in
  let uu___ = mkFV fstar_tactics_ctrl_flag.fv [] [] in
  let uu___1 = fv_as_emb_typ fstar_tactics_ctrl_flag.fv in
  {
    FStar_TypeChecker_NBETerm.em = embed_ctrl_flag;
    FStar_TypeChecker_NBETerm.un = unembed_ctrl_flag;
    FStar_TypeChecker_NBETerm.typ = uu___;
    FStar_TypeChecker_NBETerm.emb_typ = uu___1
  }
let (e_guard_policy :
  FStar_Tactics_Types.guard_policy FStar_Syntax_Embeddings.embedding) =
  let embed_guard_policy rng p =
    match p with
    | FStar_Tactics_Types.SMT -> fstar_tactics_SMT.t
    | FStar_Tactics_Types.Goal -> fstar_tactics_Goal.t
    | FStar_Tactics_Types.Force -> fstar_tactics_Force.t
    | FStar_Tactics_Types.Drop -> fstar_tactics_Drop.t in
  let unembed_guard_policy w t =
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu___1 ->
        (if w
         then
           (let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded guard_policy: %s" uu___5 in
              (FStar_Errors.Warning_NotEmbedded, uu___4) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu___3)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_guard_policy unembed_guard_policy fstar_tactics_guard_policy.t
let (e_guard_policy_nbe :
  FStar_Tactics_Types.guard_policy FStar_TypeChecker_NBETerm.embedding) =
  let embed_guard_policy cb p =
    match p with
    | FStar_Tactics_Types.SMT -> mkConstruct fstar_tactics_SMT.fv [] []
    | FStar_Tactics_Types.Goal -> mkConstruct fstar_tactics_Goal.fv [] []
    | FStar_Tactics_Types.Force -> mkConstruct fstar_tactics_Force.fv [] []
    | FStar_Tactics_Types.Drop -> mkConstruct fstar_tactics_Drop.fv [] [] in
  let unembed_guard_policy cb t =
    let uu___ = FStar_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu___ with
    | FStar_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_TypeChecker_NBETerm.Construct (fv, uu___1, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu___1 -> FStar_Pervasives_Native.None in
  let uu___ = mkFV fstar_tactics_guard_policy.fv [] [] in
  let uu___1 = fv_as_emb_typ fstar_tactics_guard_policy.fv in
  {
    FStar_TypeChecker_NBETerm.em = embed_guard_policy;
    FStar_TypeChecker_NBETerm.un = unembed_guard_policy;
    FStar_TypeChecker_NBETerm.typ = uu___;
    FStar_TypeChecker_NBETerm.emb_typ = uu___1
  }