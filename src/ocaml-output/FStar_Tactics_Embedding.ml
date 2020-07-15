open Prims
type name = FStar_Syntax_Syntax.bv
let (fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid) =
  fun s -> FStar_Parser_Const.fstar_tactics_lid' s
let (lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l ->
    let uu____17 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None in
    FStar_All.pipe_right uu____17 FStar_Syntax_Syntax.fv_to_tm
let (mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s ->
    let uu____23 = fstar_tactics_lid' ["Effect"; s] in lid_as_tm uu____23
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
  fun l ->
    let uu____73 = lid_as_data_fv l in FStar_Syntax_Syntax.fv_to_tm uu____73
let (fstar_tactics_data : Prims.string Prims.list -> tac_constant) =
  fun ns ->
    let lid = fstar_tactics_lid' ns in
    let uu____84 = lid_as_data_fv lid in
    let uu____85 = lid_as_data_tm lid in { lid; fv = uu____84; t = uu____85 }
let (fstar_tactics_const : Prims.string Prims.list -> tac_constant) =
  fun ns ->
    let lid = fstar_tactics_lid' ns in
    let uu____96 = FStar_Syntax_Syntax.fvconst lid in
    let uu____97 = FStar_Syntax_Syntax.tconst lid in
    { lid; fv = uu____96; t = uu____97 }
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
        let uu____148 = FStar_Syntax_Embeddings.term_as_fv t in
        FStar_Syntax_Embeddings.mk_emb
          (fun x -> fun r -> fun _topt -> fun _norm -> em r x)
          (fun x -> fun w -> fun _norm -> un w x) uu____148
let embed :
  'uuuuuu173 .
    'uuuuuu173 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'uuuuuu173 -> FStar_Syntax_Syntax.term
  =
  fun e ->
    fun r ->
      fun x ->
        let uu____193 = FStar_Syntax_Embeddings.embed e x in
        uu____193 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
let unembed' :
  'uuuuuu210 .
    Prims.bool ->
      'uuuuuu210 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term -> 'uuuuuu210 FStar_Pervasives_Native.option
  =
  fun w ->
    fun e ->
      fun x ->
        let uu____232 = FStar_Syntax_Embeddings.unembed e x in
        uu____232 w FStar_Syntax_Embeddings.id_norm_cb
let (t_result_of :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    let uu____246 =
      let uu____257 = FStar_Syntax_Syntax.as_arg t in [uu____257] in
    FStar_Syntax_Util.mk_app fstar_tactics_result.t uu____246
let (hd'_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' * (FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun tm ->
    let tm1 = FStar_Syntax_Util.unascribe tm in
    let uu____302 = FStar_Syntax_Util.head_and_args tm1 in
    match uu____302 with
    | (hd, args) ->
        let uu____359 =
          let uu____360 = FStar_Syntax_Util.un_uinst hd in
          uu____360.FStar_Syntax_Syntax.n in
        (uu____359, args)
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps fstar_tactics_proofstate.t
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng) in
  let unembed_proofstate w t =
    let uu____401 =
      let uu____402 = FStar_Syntax_Subst.compress t in
      uu____402.FStar_Syntax_Syntax.n in
    match uu____401 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
          FStar_Syntax_Syntax.ltyp = uu____408;
          FStar_Syntax_Syntax.rng = uu____409;_}
        ->
        let uu____412 = FStar_Dyn.undyn b in
        FStar_All.pipe_left
          (fun uu____415 -> FStar_Pervasives_Native.Some uu____415) uu____412
    | uu____416 ->
        (if w
         then
           (let uu____418 =
              let uu____423 =
                let uu____424 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded proofstate: %s\n"
                  uu____424 in
              (FStar_Errors.Warning_NotEmbedded, uu____423) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____418)
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
    let uu____506 =
      let uu____513 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      (uu____513, []) in
    FStar_Syntax_Syntax.ET_app uu____506
let (e_proofstate_nbe :
  FStar_Tactics_Types.proofstate FStar_TypeChecker_NBETerm.embedding) =
  let embed_proofstate _cb ps =
    let li =
      let uu____530 = FStar_Dyn.mkdyn ps in
      {
        FStar_Syntax_Syntax.blob = uu____530;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
        FStar_Syntax_Syntax.ltyp = (fstar_tactics_proofstate.t);
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      } in
    let thunk =
      FStar_Thunk.mk
        (fun uu____535 ->
           FStar_All.pipe_left FStar_TypeChecker_NBETerm.mk_t
             (FStar_TypeChecker_NBETerm.Constant
                (FStar_TypeChecker_NBETerm.String
                   ("(((proofstate.nbe)))", FStar_Range.dummyRange)))) in
    FStar_TypeChecker_NBETerm.mk_t
      (FStar_TypeChecker_NBETerm.Lazy ((FStar_Util.Inl li), thunk)) in
  let unembed_proofstate _cb t =
    let uu____565 = FStar_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu____565 with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
           FStar_Syntax_Syntax.ltyp = uu____569;
           FStar_Syntax_Syntax.rng = uu____570;_},
         uu____571)
        ->
        let uu____590 = FStar_Dyn.undyn b in
        FStar_All.pipe_left
          (fun uu____593 -> FStar_Pervasives_Native.Some uu____593) uu____590
    | uu____594 ->
        ((let uu____596 = FStar_ST.op_Bang FStar_Options.debug_embedding in
          if uu____596
          then
            let uu____603 =
              let uu____608 =
                let uu____609 = FStar_TypeChecker_NBETerm.t_to_string t in
                FStar_Util.format1 "Not an embedded NBE proofstate: %s\n"
                  uu____609 in
              (FStar_Errors.Warning_NotEmbedded, uu____608) in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____603
          else ());
         FStar_Pervasives_Native.None) in
  let uu____611 = mkFV fstar_tactics_proofstate.fv [] [] in
  let uu____616 = fv_as_emb_typ fstar_tactics_proofstate.fv in
  {
    FStar_TypeChecker_NBETerm.em = embed_proofstate;
    FStar_TypeChecker_NBETerm.un = unembed_proofstate;
    FStar_TypeChecker_NBETerm.typ = uu____611;
    FStar_TypeChecker_NBETerm.emb_typ = uu____616
  }
let (e_goal : FStar_Tactics_Types.goal FStar_Syntax_Embeddings.embedding) =
  let embed_goal rng g =
    FStar_Syntax_Util.mk_lazy g fstar_tactics_goal.t
      FStar_Syntax_Syntax.Lazy_goal (FStar_Pervasives_Native.Some rng) in
  let unembed_goal w t =
    let uu____645 =
      let uu____646 = FStar_Syntax_Subst.compress t in
      uu____646.FStar_Syntax_Syntax.n in
    match uu____645 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
          FStar_Syntax_Syntax.ltyp = uu____652;
          FStar_Syntax_Syntax.rng = uu____653;_}
        ->
        let uu____656 = FStar_Dyn.undyn b in
        FStar_All.pipe_left
          (fun uu____659 -> FStar_Pervasives_Native.Some uu____659) uu____656
    | uu____660 ->
        (if w
         then
           (let uu____662 =
              let uu____667 =
                let uu____668 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded goal: %s" uu____668 in
              (FStar_Errors.Warning_NotEmbedded, uu____667) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____662)
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
      let uu____689 = FStar_Dyn.mkdyn ps in
      {
        FStar_Syntax_Syntax.blob = uu____689;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
        FStar_Syntax_Syntax.ltyp = (fstar_tactics_goal.t);
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      } in
    let thunk =
      FStar_Thunk.mk
        (fun uu____694 ->
           FStar_All.pipe_left FStar_TypeChecker_NBETerm.mk_t
             (FStar_TypeChecker_NBETerm.Constant
                (FStar_TypeChecker_NBETerm.String
                   ("(((goal.nbe)))", FStar_Range.dummyRange)))) in
    FStar_All.pipe_left FStar_TypeChecker_NBETerm.mk_t
      (FStar_TypeChecker_NBETerm.Lazy ((FStar_Util.Inl li), thunk)) in
  let unembed_goal _cb t =
    let uu____724 = FStar_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu____724 with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
           FStar_Syntax_Syntax.ltyp = uu____728;
           FStar_Syntax_Syntax.rng = uu____729;_},
         uu____730)
        ->
        let uu____749 = FStar_Dyn.undyn b in
        FStar_All.pipe_left
          (fun uu____752 -> FStar_Pervasives_Native.Some uu____752) uu____749
    | uu____753 ->
        ((let uu____755 = FStar_ST.op_Bang FStar_Options.debug_embedding in
          if uu____755
          then
            let uu____762 =
              let uu____767 =
                let uu____768 = FStar_TypeChecker_NBETerm.t_to_string t in
                FStar_Util.format1 "Not an embedded NBE goal: %s" uu____768 in
              (FStar_Errors.Warning_NotEmbedded, uu____767) in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____762
          else ());
         FStar_Pervasives_Native.None) in
  let uu____770 = mkFV fstar_tactics_goal.fv [] [] in
  let uu____775 = fv_as_emb_typ fstar_tactics_goal.fv in
  {
    FStar_TypeChecker_NBETerm.em = embed_goal;
    FStar_TypeChecker_NBETerm.un = unembed_goal;
    FStar_TypeChecker_NBETerm.typ = uu____770;
    FStar_TypeChecker_NBETerm.emb_typ = uu____775
  }
let (e_exn : Prims.exn FStar_Syntax_Embeddings.embedding) =
  let embed_exn e rng uu____800 uu____801 =
    match e with
    | FStar_Tactics_Common.TacticFailure s ->
        let uu____804 =
          let uu____805 =
            let uu____814 = embed FStar_Syntax_Embeddings.e_string rng s in
            FStar_Syntax_Syntax.as_arg uu____814 in
          [uu____805] in
        FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure.t uu____804
          rng
    | FStar_Tactics_Common.EExn t ->
        let uu___131_832 = t in
        {
          FStar_Syntax_Syntax.n = (uu___131_832.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___131_832.FStar_Syntax_Syntax.vars)
        }
    | e1 ->
        let s =
          let uu____835 = FStar_Util.message_of_exn e1 in
          Prims.op_Hat "uncaught exception: " uu____835 in
        let uu____836 =
          let uu____837 =
            let uu____846 = embed FStar_Syntax_Embeddings.e_string rng s in
            FStar_Syntax_Syntax.as_arg uu____846 in
          [uu____837] in
        FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure.t uu____836
          rng in
  let unembed_exn t w uu____881 =
    let uu____885 = hd'_and_args t in
    match uu____885 with
    | (FStar_Syntax_Syntax.Tm_fvar fv, (s, uu____904)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure.lid ->
        let uu____939 = unembed' w FStar_Syntax_Embeddings.e_string s in
        FStar_Util.bind_opt uu____939
          (fun s1 ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Common.TacticFailure s1))
    | uu____944 -> FStar_Pervasives_Native.Some (FStar_Tactics_Common.EExn t) in
  let uu____959 =
    let uu____960 =
      let uu____967 =
        FStar_All.pipe_right FStar_Parser_Const.exn_lid
          FStar_Ident.string_of_lid in
      (uu____967, []) in
    FStar_Syntax_Syntax.ET_app uu____960 in
  FStar_Syntax_Embeddings.mk_emb_full embed_exn unembed_exn
    FStar_Syntax_Syntax.t_exn (fun uu____971 -> "(exn)") uu____959
let (e_exn_nbe : Prims.exn FStar_TypeChecker_NBETerm.embedding) =
  let embed_exn cb e =
    match e with
    | FStar_Tactics_Common.TacticFailure s ->
        let uu____986 =
          let uu____993 =
            let uu____998 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s in
            FStar_TypeChecker_NBETerm.as_arg uu____998 in
          [uu____993] in
        mkConstruct fstar_tactics_TacticFailure.fv [] uu____986
    | uu____1007 ->
        let uu____1008 =
          let uu____1009 = FStar_Util.message_of_exn e in
          FStar_Util.format1 "cannot embed exn (NBE) : %s" uu____1009 in
        failwith uu____1008 in
  let unembed_exn cb t =
    let uu____1025 = FStar_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu____1025 with
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____1029, (s, uu____1031)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure.lid ->
        let uu____1050 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s in
        FStar_Util.bind_opt uu____1050
          (fun s1 ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Common.TacticFailure s1))
    | uu____1055 -> FStar_Pervasives_Native.None in
  let fv_exn = FStar_Syntax_Syntax.fvconst FStar_Parser_Const.exn_lid in
  let uu____1057 = mkFV fv_exn [] [] in
  let uu____1062 = fv_as_emb_typ fv_exn in
  {
    FStar_TypeChecker_NBETerm.em = embed_exn;
    FStar_TypeChecker_NBETerm.un = unembed_exn;
    FStar_TypeChecker_NBETerm.typ = uu____1057;
    FStar_TypeChecker_NBETerm.emb_typ = uu____1062
  }
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea ->
    let embed_result res rng uu____1103 uu____1104 =
      match res with
      | FStar_Tactics_Result.Success (a1, ps) ->
          let uu____1110 =
            FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success.t
              [FStar_Syntax_Syntax.U_zero] in
          let uu____1111 =
            let uu____1112 =
              let uu____1121 = FStar_Syntax_Embeddings.type_of ea in
              FStar_Syntax_Syntax.iarg uu____1121 in
            let uu____1122 =
              let uu____1133 =
                let uu____1142 = embed ea rng a1 in
                FStar_Syntax_Syntax.as_arg uu____1142 in
              let uu____1143 =
                let uu____1154 =
                  let uu____1163 = embed e_proofstate rng ps in
                  FStar_Syntax_Syntax.as_arg uu____1163 in
                [uu____1154] in
              uu____1133 :: uu____1143 in
            uu____1112 :: uu____1122 in
          FStar_Syntax_Syntax.mk_Tm_app uu____1110 uu____1111 rng
      | FStar_Tactics_Result.Failed (e, ps) ->
          let uu____1198 =
            FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed.t
              [FStar_Syntax_Syntax.U_zero] in
          let uu____1199 =
            let uu____1200 =
              let uu____1209 = FStar_Syntax_Embeddings.type_of ea in
              FStar_Syntax_Syntax.iarg uu____1209 in
            let uu____1210 =
              let uu____1221 =
                let uu____1230 = embed e_exn rng e in
                FStar_Syntax_Syntax.as_arg uu____1230 in
              let uu____1231 =
                let uu____1242 =
                  let uu____1251 = embed e_proofstate rng ps in
                  FStar_Syntax_Syntax.as_arg uu____1251 in
                [uu____1242] in
              uu____1221 :: uu____1231 in
            uu____1200 :: uu____1210 in
          FStar_Syntax_Syntax.mk_Tm_app uu____1198 uu____1199 rng in
    let unembed_result t w uu____1304 =
      let uu____1310 = hd'_and_args t in
      match uu____1310 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,
         _t::(a1, uu____1332)::(ps, uu____1334)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success.lid ->
          let uu____1401 = unembed' w ea a1 in
          FStar_Util.bind_opt uu____1401
            (fun a2 ->
               let uu____1409 = unembed' w e_proofstate ps in
               FStar_Util.bind_opt uu____1409
                 (fun ps1 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a2, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar fv,
         _t::(e, uu____1421)::(ps, uu____1423)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed.lid ->
          let uu____1490 = unembed' w e_exn e in
          FStar_Util.bind_opt uu____1490
            (fun e1 ->
               let uu____1498 = unembed' w e_proofstate ps in
               FStar_Util.bind_opt uu____1498
                 (fun ps1 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____1507 ->
          (if w
           then
             (let uu____1523 =
                let uu____1528 =
                  let uu____1529 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____1529 in
                (FStar_Errors.Warning_NotEmbedded, uu____1528) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1523)
           else ();
           FStar_Pervasives_Native.None) in
    let uu____1533 =
      let uu____1534 = FStar_Syntax_Embeddings.type_of ea in
      t_result_of uu____1534 in
    let uu____1535 =
      let uu____1536 =
        let uu____1543 =
          FStar_All.pipe_right fstar_tactics_result.lid
            FStar_Ident.string_of_lid in
        let uu____1544 =
          let uu____1547 = FStar_Syntax_Embeddings.emb_typ_of ea in
          [uu____1547] in
        (uu____1543, uu____1544) in
      FStar_Syntax_Syntax.ET_app uu____1536 in
    FStar_Syntax_Embeddings.mk_emb_full embed_result unembed_result
      uu____1533 (fun uu____1553 -> "") uu____1535
let e_result_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'a FStar_Tactics_Result.__result FStar_TypeChecker_NBETerm.embedding
  =
  fun ea ->
    let embed_result cb res =
      match res with
      | FStar_Tactics_Result.Failed (e, ps) ->
          let uu____1591 =
            let uu____1598 =
              let uu____1603 = FStar_TypeChecker_NBETerm.type_of ea in
              FStar_TypeChecker_NBETerm.as_iarg uu____1603 in
            let uu____1604 =
              let uu____1611 =
                let uu____1616 =
                  FStar_TypeChecker_NBETerm.embed e_exn_nbe cb e in
                FStar_TypeChecker_NBETerm.as_arg uu____1616 in
              let uu____1617 =
                let uu____1624 =
                  let uu____1629 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps in
                  FStar_TypeChecker_NBETerm.as_arg uu____1629 in
                [uu____1624] in
              uu____1611 :: uu____1617 in
            uu____1598 :: uu____1604 in
          mkConstruct fstar_tactics_Failed.fv [FStar_Syntax_Syntax.U_zero]
            uu____1591
      | FStar_Tactics_Result.Success (a1, ps) ->
          let uu____1648 =
            let uu____1655 =
              let uu____1660 = FStar_TypeChecker_NBETerm.type_of ea in
              FStar_TypeChecker_NBETerm.as_iarg uu____1660 in
            let uu____1661 =
              let uu____1668 =
                let uu____1673 = FStar_TypeChecker_NBETerm.embed ea cb a1 in
                FStar_TypeChecker_NBETerm.as_arg uu____1673 in
              let uu____1674 =
                let uu____1681 =
                  let uu____1686 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps in
                  FStar_TypeChecker_NBETerm.as_arg uu____1686 in
                [uu____1681] in
              uu____1668 :: uu____1674 in
            uu____1655 :: uu____1661 in
          mkConstruct fstar_tactics_Success.fv [FStar_Syntax_Syntax.U_zero]
            uu____1648 in
    let unembed_result cb t =
      let uu____1722 = FStar_TypeChecker_NBETerm.nbe_t_of_t t in
      match uu____1722 with
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____1728, (ps, uu____1730)::(a1, uu____1732)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success.lid ->
          let uu____1764 = FStar_TypeChecker_NBETerm.unembed ea cb a1 in
          FStar_Util.bind_opt uu____1764
            (fun a2 ->
               let uu____1772 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps in
               FStar_Util.bind_opt uu____1772
                 (fun ps1 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a2, ps1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____1782, (ps, uu____1784)::(e, uu____1786)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed.lid ->
          let uu____1818 = FStar_TypeChecker_NBETerm.unembed e_exn_nbe cb e in
          FStar_Util.bind_opt uu____1818
            (fun e1 ->
               let uu____1826 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps in
               FStar_Util.bind_opt uu____1826
                 (fun ps1 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____1835 -> FStar_Pervasives_Native.None in
    let uu____1838 = mkFV fstar_tactics_result.fv [] [] in
    let uu____1843 = fv_as_emb_typ fstar_tactics_result.fv in
    {
      FStar_TypeChecker_NBETerm.em = embed_result;
      FStar_TypeChecker_NBETerm.un = unembed_result;
      FStar_TypeChecker_NBETerm.typ = uu____1838;
      FStar_TypeChecker_NBETerm.emb_typ = uu____1843
    }
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown -> fstar_tactics_topdown.t
    | FStar_Tactics_Types.BottomUp -> fstar_tactics_bottomup.t in
  let unembed_direction w t =
    let uu____1874 =
      let uu____1875 = FStar_Syntax_Subst.compress t in
      uu____1875.FStar_Syntax_Syntax.n in
    match uu____1874 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____1882 ->
        (if w
         then
           (let uu____1884 =
              let uu____1889 =
                let uu____1890 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded direction: %s" uu____1890 in
              (FStar_Errors.Warning_NotEmbedded, uu____1889) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1884)
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
    let uu____1928 = FStar_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu____1928 with
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____1932, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____1948, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____1963 ->
        ((let uu____1965 = FStar_ST.op_Bang FStar_Options.debug_embedding in
          if uu____1965
          then
            let uu____1972 =
              let uu____1977 =
                let uu____1978 = FStar_TypeChecker_NBETerm.t_to_string t in
                FStar_Util.format1 "Not an embedded direction: %s" uu____1978 in
              (FStar_Errors.Warning_NotEmbedded, uu____1977) in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1972
          else ());
         FStar_Pervasives_Native.None) in
  let uu____1980 = mkFV fstar_tactics_direction.fv [] [] in
  let uu____1985 = fv_as_emb_typ fstar_tactics_direction.fv in
  {
    FStar_TypeChecker_NBETerm.em = embed_direction;
    FStar_TypeChecker_NBETerm.un = unembed_direction;
    FStar_TypeChecker_NBETerm.typ = uu____1980;
    FStar_TypeChecker_NBETerm.emb_typ = uu____1985
  }
let (e_ctrl_flag :
  FStar_Tactics_Types.ctrl_flag FStar_Syntax_Embeddings.embedding) =
  let embed_ctrl_flag rng d =
    match d with
    | FStar_Tactics_Types.Continue -> fstar_tactics_Continue.t
    | FStar_Tactics_Types.Skip -> fstar_tactics_Skip.t
    | FStar_Tactics_Types.Abort -> fstar_tactics_Abort.t in
  let unembed_ctrl_flag w t =
    let uu____2014 =
      let uu____2015 = FStar_Syntax_Subst.compress t in
      uu____2015.FStar_Syntax_Syntax.n in
    match uu____2014 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Continue.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Continue
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Skip.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Skip
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Abort.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Abort
    | uu____2023 ->
        (if w
         then
           (let uu____2025 =
              let uu____2030 =
                let uu____2031 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded ctrl_flag: %s" uu____2031 in
              (FStar_Errors.Warning_NotEmbedded, uu____2030) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2025)
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
    let uu____2073 = FStar_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu____2073 with
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____2077, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Continue.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Continue
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____2093, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Skip.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Skip
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____2109, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Abort.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Abort
    | uu____2124 ->
        ((let uu____2126 = FStar_ST.op_Bang FStar_Options.debug_embedding in
          if uu____2126
          then
            let uu____2133 =
              let uu____2138 =
                let uu____2139 = FStar_TypeChecker_NBETerm.t_to_string t in
                FStar_Util.format1 "Not an embedded ctrl_flag: %s" uu____2139 in
              (FStar_Errors.Warning_NotEmbedded, uu____2138) in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____2133
          else ());
         FStar_Pervasives_Native.None) in
  let uu____2141 = mkFV fstar_tactics_ctrl_flag.fv [] [] in
  let uu____2146 = fv_as_emb_typ fstar_tactics_ctrl_flag.fv in
  {
    FStar_TypeChecker_NBETerm.em = embed_ctrl_flag;
    FStar_TypeChecker_NBETerm.un = unembed_ctrl_flag;
    FStar_TypeChecker_NBETerm.typ = uu____2141;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2146
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
    let uu____2175 =
      let uu____2176 = FStar_Syntax_Subst.compress t in
      uu____2176.FStar_Syntax_Syntax.n in
    match uu____2175 with
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
    | uu____2185 ->
        (if w
         then
           (let uu____2187 =
              let uu____2192 =
                let uu____2193 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____2193 in
              (FStar_Errors.Warning_NotEmbedded, uu____2192) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2187)
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
    let uu____2239 = FStar_TypeChecker_NBETerm.nbe_t_of_t t in
    match uu____2239 with
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____2243, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____2259, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____2275, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____2291, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____2306 -> FStar_Pervasives_Native.None in
  let uu____2307 = mkFV fstar_tactics_guard_policy.fv [] [] in
  let uu____2312 = fv_as_emb_typ fstar_tactics_guard_policy.fv in
  {
    FStar_TypeChecker_NBETerm.em = embed_guard_policy;
    FStar_TypeChecker_NBETerm.un = unembed_guard_policy;
    FStar_TypeChecker_NBETerm.typ = uu____2307;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2312
  }