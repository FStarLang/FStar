open Prims
let (term_eq :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term -> Prims.bool)
  = FStar_Reflection_TermEq_Simple.term_eq
let rec (inspect_unascribe :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.term_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Tactics_NamedView.inspect t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Reflection.V2.Formula.fst"
               (Prims.of_int (36)) (Prims.of_int (8)) (Prims.of_int (36))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Reflection.V2.Formula.fst"
               (Prims.of_int (36)) (Prims.of_int (2)) (Prims.of_int (40))
               (Prims.of_int (12))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Tactics_NamedView.Tv_AscribedT
                (t1, uu___2, uu___3, uu___4) ->
                Obj.magic (Obj.repr (inspect_unascribe t1))
            | FStar_Tactics_NamedView.Tv_AscribedC
                (t1, uu___2, uu___3, uu___4) ->
                Obj.magic (Obj.repr (inspect_unascribe t1))
            | tv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> tv))))
           uu___1)
let rec (collect_app' :
  FStarC_Reflection_V2_Data.argv Prims.list ->
    FStar_Tactics_NamedView.term ->
      ((FStar_Tactics_NamedView.term * FStarC_Reflection_V2_Data.argv
         Prims.list),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun args ->
    fun t ->
      let uu___ = inspect_unascribe t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Reflection.V2.Formula.fst"
                 (Prims.of_int (44)) (Prims.of_int (10)) (Prims.of_int (44))
                 (Prims.of_int (29)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Reflection.V2.Formula.fst"
                 (Prims.of_int (44)) (Prims.of_int (4)) (Prims.of_int (47))
                 (Prims.of_int (20))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | FStar_Tactics_NamedView.Tv_App (l, r) ->
                  Obj.magic (Obj.repr (collect_app' (r :: args) l))
              | uu___2 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> (t, args))))) uu___1)
let (collect_app :
  FStar_Tactics_NamedView.term ->
    ((FStar_Tactics_NamedView.term * FStarC_Reflection_V2_Data.argv
       Prims.list),
      unit) FStar_Tactics_Effect.tac_repr)
  = collect_app' []
type comparison =
  | Eq of FStarC_Reflection_Types.typ FStar_Pervasives_Native.option 
  | BoolEq of FStarC_Reflection_Types.typ FStar_Pervasives_Native.option 
  | Lt 
  | Le 
  | Gt 
  | Ge 
let rec __knot_e_comparison _ =
  FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Reflection.V2.Formula.comparison"
    (fun tm_0 ->
       match tm_0 with
       | ("FStar.Reflection.V2.Formula.Eq", _0_2::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                (FStarC_Syntax_Embeddings.e_option
                   FStarC_Reflection_V2_Embeddings.e_term) _0_2)
             (fun _0_2 -> FStar_Pervasives_Native.Some (Eq _0_2))
       | ("FStar.Reflection.V2.Formula.BoolEq", _0_4::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                (FStarC_Syntax_Embeddings.e_option
                   FStarC_Reflection_V2_Embeddings.e_term) _0_4)
             (fun _0_4 -> FStar_Pervasives_Native.Some (BoolEq _0_4))
       | ("FStar.Reflection.V2.Formula.Lt", []) ->
           FStar_Pervasives_Native.Some Lt
       | ("FStar.Reflection.V2.Formula.Le", []) ->
           FStar_Pervasives_Native.Some Le
       | ("FStar.Reflection.V2.Formula.Gt", []) ->
           FStar_Pervasives_Native.Some Gt
       | ("FStar.Reflection.V2.Formula.Ge", []) ->
           FStar_Pervasives_Native.Some Ge
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_9 ->
       match tm_9 with
       | Eq _0_11 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Reflection.V2.Formula.Eq"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  (FStarC_Syntax_Embeddings.e_option
                     FStarC_Reflection_V2_Embeddings.e_term) _0_11),
                FStar_Pervasives_Native.None)]
       | BoolEq _0_13 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Reflection.V2.Formula.BoolEq"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  (FStarC_Syntax_Embeddings.e_option
                     FStarC_Reflection_V2_Embeddings.e_term) _0_13),
                FStar_Pervasives_Native.None)]
       | Lt ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Reflection.V2.Formula.Lt"))
             []
       | Le ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Reflection.V2.Formula.Le"))
             []
       | Gt ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Reflection.V2.Formula.Gt"))
             []
       | Ge ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Reflection.V2.Formula.Ge"))
             [])
let e_comparison = __knot_e_comparison ()
let (uu___is_Eq : comparison -> Prims.bool) =
  fun projectee -> match projectee with | Eq _0 -> true | uu___ -> false
let (__proj__Eq__item___0 :
  comparison -> FStarC_Reflection_Types.typ FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | Eq _0 -> _0
let (uu___is_BoolEq : comparison -> Prims.bool) =
  fun projectee -> match projectee with | BoolEq _0 -> true | uu___ -> false
let (__proj__BoolEq__item___0 :
  comparison -> FStarC_Reflection_Types.typ FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | BoolEq _0 -> _0
let (uu___is_Lt : comparison -> Prims.bool) =
  fun projectee -> match projectee with | Lt -> true | uu___ -> false
let (uu___is_Le : comparison -> Prims.bool) =
  fun projectee -> match projectee with | Le -> true | uu___ -> false
let (uu___is_Gt : comparison -> Prims.bool) =
  fun projectee -> match projectee with | Gt -> true | uu___ -> false
let (uu___is_Ge : comparison -> Prims.bool) =
  fun projectee -> match projectee with | Ge -> true | uu___ -> false
type formula =
  | True_ 
  | False_ 
  | Comp of comparison * FStar_Tactics_NamedView.term *
  FStar_Tactics_NamedView.term 
  | And of FStar_Tactics_NamedView.term * FStar_Tactics_NamedView.term 
  | Or of FStar_Tactics_NamedView.term * FStar_Tactics_NamedView.term 
  | Not of FStar_Tactics_NamedView.term 
  | Implies of FStar_Tactics_NamedView.term * FStar_Tactics_NamedView.term 
  | Iff of FStar_Tactics_NamedView.term * FStar_Tactics_NamedView.term 
  | Forall of FStar_Tactics_NamedView.bv * FStarC_Reflection_Types.typ *
  FStar_Tactics_NamedView.term 
  | Exists of FStar_Tactics_NamedView.bv * FStarC_Reflection_Types.typ *
  FStar_Tactics_NamedView.term 
  | App of FStar_Tactics_NamedView.term * FStar_Tactics_NamedView.term 
  | Name of FStar_Tactics_NamedView.namedv 
  | FV of FStarC_Reflection_Types.fv 
  | IntLit of Prims.int 
  | F_Unknown 
let rec __knot_e_formula _ =
  FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Reflection.V2.Formula.formula"
    (fun tm_18 ->
       match tm_18 with
       | ("FStar.Reflection.V2.Formula.True_", []) ->
           FStar_Pervasives_Native.Some True_
       | ("FStar.Reflection.V2.Formula.False_", []) ->
           FStar_Pervasives_Native.Some False_
       | ("FStar.Reflection.V2.Formula.Comp", _0_22::_1_23::_2_24::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed e_comparison
                _0_22)
             (fun _0_22 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     FStarC_Reflection_V2_Embeddings.e_term _1_23)
                  (fun _1_23 ->
                     FStarC_Compiler_Util.bind_opt
                       (FStarC_Syntax_Embeddings_Base.extracted_unembed
                          FStarC_Reflection_V2_Embeddings.e_term _2_24)
                       (fun _2_24 ->
                          FStar_Pervasives_Native.Some
                            (Comp (_0_22, _1_23, _2_24)))))
       | ("FStar.Reflection.V2.Formula.And", _0_26::_1_27::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_term _0_26)
             (fun _0_26 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     FStarC_Reflection_V2_Embeddings.e_term _1_27)
                  (fun _1_27 ->
                     FStar_Pervasives_Native.Some (And (_0_26, _1_27))))
       | ("FStar.Reflection.V2.Formula.Or", _0_29::_1_30::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_term _0_29)
             (fun _0_29 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     FStarC_Reflection_V2_Embeddings.e_term _1_30)
                  (fun _1_30 ->
                     FStar_Pervasives_Native.Some (Or (_0_29, _1_30))))
       | ("FStar.Reflection.V2.Formula.Not", _0_32::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_term _0_32)
             (fun _0_32 -> FStar_Pervasives_Native.Some (Not _0_32))
       | ("FStar.Reflection.V2.Formula.Implies", _0_34::_1_35::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_term _0_34)
             (fun _0_34 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     FStarC_Reflection_V2_Embeddings.e_term _1_35)
                  (fun _1_35 ->
                     FStar_Pervasives_Native.Some (Implies (_0_34, _1_35))))
       | ("FStar.Reflection.V2.Formula.Iff", _0_37::_1_38::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_term _0_37)
             (fun _0_37 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     FStarC_Reflection_V2_Embeddings.e_term _1_38)
                  (fun _1_38 ->
                     FStar_Pervasives_Native.Some (Iff (_0_37, _1_38))))
       | ("FStar.Reflection.V2.Formula.Forall", _0_40::_1_41::_2_42::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_bv_view _0_40)
             (fun _0_40 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     FStarC_Reflection_V2_Embeddings.e_term _1_41)
                  (fun _1_41 ->
                     FStarC_Compiler_Util.bind_opt
                       (FStarC_Syntax_Embeddings_Base.extracted_unembed
                          FStarC_Reflection_V2_Embeddings.e_term _2_42)
                       (fun _2_42 ->
                          FStar_Pervasives_Native.Some
                            (Forall (_0_40, _1_41, _2_42)))))
       | ("FStar.Reflection.V2.Formula.Exists", _0_44::_1_45::_2_46::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_bv_view _0_44)
             (fun _0_44 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     FStarC_Reflection_V2_Embeddings.e_term _1_45)
                  (fun _1_45 ->
                     FStarC_Compiler_Util.bind_opt
                       (FStarC_Syntax_Embeddings_Base.extracted_unembed
                          FStarC_Reflection_V2_Embeddings.e_term _2_46)
                       (fun _2_46 ->
                          FStar_Pervasives_Native.Some
                            (Exists (_0_44, _1_45, _2_46)))))
       | ("FStar.Reflection.V2.Formula.App", _0_48::_1_49::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_term _0_48)
             (fun _0_48 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     FStarC_Reflection_V2_Embeddings.e_term _1_49)
                  (fun _1_49 ->
                     FStar_Pervasives_Native.Some (App (_0_48, _1_49))))
       | ("FStar.Reflection.V2.Formula.Name", _0_51::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_namedv_view _0_51)
             (fun _0_51 -> FStar_Pervasives_Native.Some (Name _0_51))
       | ("FStar.Reflection.V2.Formula.FV", _0_53::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_fv _0_53)
             (fun _0_53 -> FStar_Pervasives_Native.Some (FV _0_53))
       | ("FStar.Reflection.V2.Formula.IntLit", _0_55::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Syntax_Embeddings.e_int _0_55)
             (fun _0_55 -> FStar_Pervasives_Native.Some (IntLit _0_55))
       | ("FStar.Reflection.V2.Formula.F_Unknown", []) ->
           FStar_Pervasives_Native.Some F_Unknown
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_57 ->
       match tm_57 with
       | True_ ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Reflection.V2.Formula.True_"))
             []
       | False_ ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Reflection.V2.Formula.False_"))
             []
       | Comp (_0_61, _1_62, _2_63) ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Reflection.V2.Formula.Comp"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed e_comparison
                  _0_61), FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term _1_62),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term _2_63),
               FStar_Pervasives_Native.None)]
       | And (_0_65, _1_66) ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Reflection.V2.Formula.And"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_term _0_65),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term _1_66),
               FStar_Pervasives_Native.None)]
       | Or (_0_68, _1_69) ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Reflection.V2.Formula.Or"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_term _0_68),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term _1_69),
               FStar_Pervasives_Native.None)]
       | Not _0_71 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Reflection.V2.Formula.Not"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_term _0_71),
                FStar_Pervasives_Native.None)]
       | Implies (_0_73, _1_74) ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.Implies"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_term _0_73),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term _1_74),
               FStar_Pervasives_Native.None)]
       | Iff (_0_76, _1_77) ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Reflection.V2.Formula.Iff"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_term _0_76),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term _1_77),
               FStar_Pervasives_Native.None)]
       | Forall (_0_79, _1_80, _2_81) ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Reflection.V2.Formula.Forall"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_bv_view _0_79),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term _1_80),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term _2_81),
               FStar_Pervasives_Native.None)]
       | Exists (_0_83, _1_84, _2_85) ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Reflection.V2.Formula.Exists"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_bv_view _0_83),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term _1_84),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term _2_85),
               FStar_Pervasives_Native.None)]
       | App (_0_87, _1_88) ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Reflection.V2.Formula.App"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_term _0_87),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term _1_88),
               FStar_Pervasives_Native.None)]
       | Name _0_90 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Reflection.V2.Formula.Name"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_namedv_view _0_90),
                FStar_Pervasives_Native.None)]
       | FV _0_92 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Reflection.V2.Formula.FV"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_fv _0_92),
                FStar_Pervasives_Native.None)]
       | IntLit _0_94 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Reflection.V2.Formula.IntLit"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Syntax_Embeddings.e_int _0_94),
                FStar_Pervasives_Native.None)]
       | F_Unknown ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.F_Unknown")) [])
let e_formula = __knot_e_formula ()
let (uu___is_True_ : formula -> Prims.bool) =
  fun projectee -> match projectee with | True_ -> true | uu___ -> false
let (uu___is_False_ : formula -> Prims.bool) =
  fun projectee -> match projectee with | False_ -> true | uu___ -> false
let (uu___is_Comp : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Comp (_0, _1, _2) -> true | uu___ -> false
let (__proj__Comp__item___0 : formula -> comparison) =
  fun projectee -> match projectee with | Comp (_0, _1, _2) -> _0
let (__proj__Comp__item___1 : formula -> FStar_Tactics_NamedView.term) =
  fun projectee -> match projectee with | Comp (_0, _1, _2) -> _1
let (__proj__Comp__item___2 : formula -> FStar_Tactics_NamedView.term) =
  fun projectee -> match projectee with | Comp (_0, _1, _2) -> _2
let (uu___is_And : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | And (_0, _1) -> true | uu___ -> false
let (__proj__And__item___0 : formula -> FStar_Tactics_NamedView.term) =
  fun projectee -> match projectee with | And (_0, _1) -> _0
let (__proj__And__item___1 : formula -> FStar_Tactics_NamedView.term) =
  fun projectee -> match projectee with | And (_0, _1) -> _1
let (uu___is_Or : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Or (_0, _1) -> true | uu___ -> false
let (__proj__Or__item___0 : formula -> FStar_Tactics_NamedView.term) =
  fun projectee -> match projectee with | Or (_0, _1) -> _0
let (__proj__Or__item___1 : formula -> FStar_Tactics_NamedView.term) =
  fun projectee -> match projectee with | Or (_0, _1) -> _1
let (uu___is_Not : formula -> Prims.bool) =
  fun projectee -> match projectee with | Not _0 -> true | uu___ -> false
let (__proj__Not__item___0 : formula -> FStar_Tactics_NamedView.term) =
  fun projectee -> match projectee with | Not _0 -> _0
let (uu___is_Implies : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Implies (_0, _1) -> true | uu___ -> false
let (__proj__Implies__item___0 : formula -> FStar_Tactics_NamedView.term) =
  fun projectee -> match projectee with | Implies (_0, _1) -> _0
let (__proj__Implies__item___1 : formula -> FStar_Tactics_NamedView.term) =
  fun projectee -> match projectee with | Implies (_0, _1) -> _1
let (uu___is_Iff : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Iff (_0, _1) -> true | uu___ -> false
let (__proj__Iff__item___0 : formula -> FStar_Tactics_NamedView.term) =
  fun projectee -> match projectee with | Iff (_0, _1) -> _0
let (__proj__Iff__item___1 : formula -> FStar_Tactics_NamedView.term) =
  fun projectee -> match projectee with | Iff (_0, _1) -> _1
let (uu___is_Forall : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Forall (_0, _1, _2) -> true | uu___ -> false
let (__proj__Forall__item___0 : formula -> FStar_Tactics_NamedView.bv) =
  fun projectee -> match projectee with | Forall (_0, _1, _2) -> _0
let (__proj__Forall__item___1 : formula -> FStarC_Reflection_Types.typ) =
  fun projectee -> match projectee with | Forall (_0, _1, _2) -> _1
let (__proj__Forall__item___2 : formula -> FStar_Tactics_NamedView.term) =
  fun projectee -> match projectee with | Forall (_0, _1, _2) -> _2
let (uu___is_Exists : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Exists (_0, _1, _2) -> true | uu___ -> false
let (__proj__Exists__item___0 : formula -> FStar_Tactics_NamedView.bv) =
  fun projectee -> match projectee with | Exists (_0, _1, _2) -> _0
let (__proj__Exists__item___1 : formula -> FStarC_Reflection_Types.typ) =
  fun projectee -> match projectee with | Exists (_0, _1, _2) -> _1
let (__proj__Exists__item___2 : formula -> FStar_Tactics_NamedView.term) =
  fun projectee -> match projectee with | Exists (_0, _1, _2) -> _2
let (uu___is_App : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | App (_0, _1) -> true | uu___ -> false
let (__proj__App__item___0 : formula -> FStar_Tactics_NamedView.term) =
  fun projectee -> match projectee with | App (_0, _1) -> _0
let (__proj__App__item___1 : formula -> FStar_Tactics_NamedView.term) =
  fun projectee -> match projectee with | App (_0, _1) -> _1
let (uu___is_Name : formula -> Prims.bool) =
  fun projectee -> match projectee with | Name _0 -> true | uu___ -> false
let (__proj__Name__item___0 : formula -> FStar_Tactics_NamedView.namedv) =
  fun projectee -> match projectee with | Name _0 -> _0
let (uu___is_FV : formula -> Prims.bool) =
  fun projectee -> match projectee with | FV _0 -> true | uu___ -> false
let (__proj__FV__item___0 : formula -> FStarC_Reflection_Types.fv) =
  fun projectee -> match projectee with | FV _0 -> _0
let (uu___is_IntLit : formula -> Prims.bool) =
  fun projectee -> match projectee with | IntLit _0 -> true | uu___ -> false
let (__proj__IntLit__item___0 : formula -> Prims.int) =
  fun projectee -> match projectee with | IntLit _0 -> _0
let (uu___is_F_Unknown : formula -> Prims.bool) =
  fun projectee -> match projectee with | F_Unknown -> true | uu___ -> false
let (mk_Forall :
  FStar_Tactics_NamedView.term -> FStar_Tactics_NamedView.term -> formula) =
  fun typ ->
    fun pred ->
      let b =
        FStar_Tactics_NamedView.pack_bv
          {
            FStarC_Reflection_V2_Data.index = Prims.int_zero;
            FStarC_Reflection_V2_Data.sort1 = (FStar_Sealed.seal typ);
            FStarC_Reflection_V2_Data.ppname1 =
              (FStarC_Reflection_V2_Data.as_ppname "x")
          } in
      Forall
        (b, typ,
          (FStar_Tactics_NamedView.pack
             (FStar_Tactics_NamedView.Tv_App
                (pred,
                  ((FStar_Tactics_NamedView.pack
                      (FStar_Tactics_NamedView.Tv_BVar b)),
                    FStarC_Reflection_V2_Data.Q_Explicit)))))
let (mk_Exists :
  FStar_Tactics_NamedView.term -> FStar_Tactics_NamedView.term -> formula) =
  fun typ ->
    fun pred ->
      let b =
        FStar_Tactics_NamedView.pack_bv
          {
            FStarC_Reflection_V2_Data.index = Prims.int_zero;
            FStarC_Reflection_V2_Data.sort1 = (FStar_Sealed.seal typ);
            FStarC_Reflection_V2_Data.ppname1 =
              (FStarC_Reflection_V2_Data.as_ppname "x")
          } in
      Exists
        (b, typ,
          (FStar_Tactics_NamedView.pack
             (FStar_Tactics_NamedView.Tv_App
                (pred,
                  ((FStar_Tactics_NamedView.pack
                      (FStar_Tactics_NamedView.Tv_BVar b)),
                    FStarC_Reflection_V2_Data.Q_Explicit)))))
let (term_as_formula' :
  FStar_Tactics_NamedView.term ->
    (formula, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = inspect_unascribe t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Reflection.V2.Formula.fst"
               (Prims.of_int (90)) (Prims.of_int (10)) (Prims.of_int (90))
               (Prims.of_int (29)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Reflection.V2.Formula.fst"
               (Prims.of_int (90)) (Prims.of_int (4)) (Prims.of_int (166))
               (Prims.of_int (76))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Tactics_NamedView.Tv_Var n ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Name n)))
            | FStar_Tactics_NamedView.Tv_FVar fv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           if
                             (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                               FStar_Reflection_Const.true_qn
                           then True_
                           else
                             if
                               (FStarC_Reflection_V2_Builtins.inspect_fv fv)
                                 = FStar_Reflection_Const.false_qn
                             then False_
                             else FV fv)))
            | FStar_Tactics_NamedView.Tv_UInst (fv, uu___2) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 ->
                           if
                             (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                               FStar_Reflection_Const.true_qn
                           then True_
                           else
                             if
                               (FStarC_Reflection_V2_Builtins.inspect_fv fv)
                                 = FStar_Reflection_Const.false_qn
                             then False_
                             else FV fv)))
            | FStar_Tactics_NamedView.Tv_App (h0, t1) ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 = collect_app h0 in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Reflection.V2.Formula.fst"
                                 (Prims.of_int (106)) (Prims.of_int (22))
                                 (Prims.of_int (106)) (Prims.of_int (36)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Reflection.V2.Formula.fst"
                                 (Prims.of_int (105)) (Prims.of_int (26))
                                 (Prims.of_int (144)) (Prims.of_int (26)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun uu___3 ->
                              match uu___3 with
                              | (h, ts) ->
                                  let uu___4 =
                                    Obj.magic
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___5 ->
                                            FStar_Reflection_V2_Derived.un_uinst
                                              h)) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Reflection.V2.Formula.fst"
                                                (Prims.of_int (107))
                                                (Prims.of_int (16))
                                                (Prims.of_int (107))
                                                (Prims.of_int (26)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Reflection.V2.Formula.fst"
                                                (Prims.of_int (108))
                                                (Prims.of_int (8))
                                                (Prims.of_int (144))
                                                (Prims.of_int (26)))))
                                       (Obj.magic uu___4)
                                       (fun uu___5 ->
                                          (fun h1 ->
                                             let uu___5 =
                                               let uu___6 =
                                                 FStar_Tactics_NamedView.inspect
                                                   h1 in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Reflection.V2.Formula.fst"
                                                          (Prims.of_int (108))
                                                          (Prims.of_int (14))
                                                          (Prims.of_int (108))
                                                          (Prims.of_int (23)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Reflection.V2.Formula.fst"
                                                          (Prims.of_int (108))
                                                          (Prims.of_int (14))
                                                          (Prims.of_int (108))
                                                          (Prims.of_int (31)))))
                                                 (Obj.magic uu___6)
                                                 (fun uu___7 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___8 ->
                                                         (uu___7,
                                                           (FStar_List_Tot_Base.op_At
                                                              ts [t1])))) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Reflection.V2.Formula.fst"
                                                           (Prims.of_int (108))
                                                           (Prims.of_int (14))
                                                           (Prims.of_int (108))
                                                           (Prims.of_int (31)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Reflection.V2.Formula.fst"
                                                           (Prims.of_int (108))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (144))
                                                           (Prims.of_int (26)))))
                                                  (Obj.magic uu___5)
                                                  (fun uu___6 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___7 ->
                                                          match uu___6 with
                                                          | (FStar_Tactics_NamedView.Tv_FVar
                                                             fv,
                                                             (a1,
                                                              FStarC_Reflection_V2_Data.Q_Implicit)::
                                                             (a2,
                                                              FStarC_Reflection_V2_Data.Q_Explicit)::
                                                             (a3,
                                                              FStarC_Reflection_V2_Data.Q_Explicit)::[])
                                                              ->
                                                              if
                                                                (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                   fv)
                                                                  =
                                                                  FStar_Reflection_Const.eq2_qn
                                                              then
                                                                Comp
                                                                  ((Eq
                                                                    (FStar_Pervasives_Native.Some
                                                                    a1)), a2,
                                                                    a3)
                                                              else
                                                                if
                                                                  (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.eq1_qn
                                                                then
                                                                  Comp
                                                                    ((BoolEq
                                                                    (FStar_Pervasives_Native.Some
                                                                    a1)), a2,
                                                                    a3)
                                                                else
                                                                  if
                                                                    (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.lt_qn
                                                                  then
                                                                    Comp
                                                                    (Lt, a2,
                                                                    a3)
                                                                  else
                                                                    if
                                                                    (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.lte_qn
                                                                    then
                                                                    Comp
                                                                    (Le, a2,
                                                                    a3)
                                                                    else
                                                                    if
                                                                    (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.gt_qn
                                                                    then
                                                                    Comp
                                                                    (Gt, a2,
                                                                    a3)
                                                                    else
                                                                    if
                                                                    (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.gte_qn
                                                                    then
                                                                    Comp
                                                                    (Ge, a2,
                                                                    a3)
                                                                    else
                                                                    App
                                                                    (h0,
                                                                    (FStar_Pervasives_Native.fst
                                                                    t1))
                                                          | (FStar_Tactics_NamedView.Tv_FVar
                                                             fv,
                                                             (a1,
                                                              FStarC_Reflection_V2_Data.Q_Explicit)::
                                                             (a2,
                                                              FStarC_Reflection_V2_Data.Q_Explicit)::[])
                                                              ->
                                                              if
                                                                (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                   fv)
                                                                  =
                                                                  FStar_Reflection_Const.imp_qn
                                                              then
                                                                Implies
                                                                  (a1, a2)
                                                              else
                                                                if
                                                                  (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.and_qn
                                                                then
                                                                  And
                                                                    (a1, a2)
                                                                else
                                                                  if
                                                                    (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.iff_qn
                                                                  then
                                                                    Iff
                                                                    (a1, a2)
                                                                  else
                                                                    if
                                                                    (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.or_qn
                                                                    then
                                                                    Or
                                                                    (a1, a2)
                                                                    else
                                                                    if
                                                                    (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.eq2_qn
                                                                    then
                                                                    Comp
                                                                    ((Eq
                                                                    FStar_Pervasives_Native.None),
                                                                    a1, a2)
                                                                    else
                                                                    if
                                                                    (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.eq1_qn
                                                                    then
                                                                    Comp
                                                                    ((BoolEq
                                                                    FStar_Pervasives_Native.None),
                                                                    a1, a2)
                                                                    else
                                                                    App
                                                                    (h0,
                                                                    (FStar_Pervasives_Native.fst
                                                                    t1))
                                                          | (FStar_Tactics_NamedView.Tv_FVar
                                                             fv,
                                                             (a1,
                                                              FStarC_Reflection_V2_Data.Q_Implicit)::
                                                             (a2,
                                                              FStarC_Reflection_V2_Data.Q_Explicit)::[])
                                                              ->
                                                              if
                                                                (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                   fv)
                                                                  =
                                                                  FStar_Reflection_Const.forall_qn
                                                              then
                                                                mk_Forall a1
                                                                  a2
                                                              else
                                                                if
                                                                  (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.exists_qn
                                                                then
                                                                  mk_Exists
                                                                    a1 a2
                                                                else
                                                                  App
                                                                    (h0,
                                                                    (FStar_Pervasives_Native.fst
                                                                    t1))
                                                          | (FStar_Tactics_NamedView.Tv_FVar
                                                             fv,
                                                             (a,
                                                              FStarC_Reflection_V2_Data.Q_Explicit)::[])
                                                              ->
                                                              if
                                                                (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                   fv)
                                                                  =
                                                                  FStar_Reflection_Const.not_qn
                                                              then Not a
                                                              else
                                                                if
                                                                  (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.b2t_qn
                                                                then
                                                                  (if
                                                                    term_eq a
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Const
                                                                    FStarC_Reflection_V2_Data.C_False))
                                                                   then
                                                                    False_
                                                                   else
                                                                    if
                                                                    term_eq a
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Const
                                                                    FStarC_Reflection_V2_Data.C_True))
                                                                    then
                                                                    True_
                                                                    else
                                                                    App
                                                                    (h0,
                                                                    (FStar_Pervasives_Native.fst
                                                                    t1)))
                                                                else
                                                                  App
                                                                    (h0,
                                                                    (FStar_Pervasives_Native.fst
                                                                    t1))
                                                          | uu___8 ->
                                                              App
                                                                (h0,
                                                                  (FStar_Pervasives_Native.fst
                                                                    t1))))))
                                            uu___5))) uu___3)))
            | FStar_Tactics_NamedView.Tv_Const
                (FStarC_Reflection_V2_Data.C_Int i) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> IntLit i)))
            | FStar_Tactics_NamedView.Tv_Let
                (uu___2, uu___3, uu___4, uu___5, uu___6) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___7 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_Match (uu___2, uu___3, uu___4) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___5 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_Type uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_Abs (uu___2, uu___3) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___4 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_Arrow (uu___2, uu___3) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___4 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_Uvar (uu___2, uu___3) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___4 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_Unknown ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_Unsupp ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_Refine (uu___2, uu___3) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___4 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_Const uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_BVar uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 -> F_Unknown)))
            | uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.raise
                        (FStarC_Tactics_Common.TacticFailure
                           ([FStarC_Pprint.arbitrary_string
                               "Unexpected: term_as_formula"],
                             FStar_Pervasives_Native.None))))) uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Reflection.V2.Formula.term_as_formula'" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Reflection.V2.Formula.term_as_formula' (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 term_as_formula')
               FStarC_Reflection_V2_Embeddings.e_term e_formula psc ncb us
               args)
let (term_as_formula :
  FStar_Tactics_NamedView.term ->
    (formula, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       match FStar_Reflection_V2_Derived.unsquash_term t with
       | FStar_Pervasives_Native.None ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> F_Unknown)))
       | FStar_Pervasives_Native.Some t1 ->
           Obj.magic (Obj.repr (term_as_formula' t1))) uu___
let (term_as_formula_total :
  FStar_Tactics_NamedView.term ->
    (formula, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    term_as_formula' (FStar_Reflection_V2_Derived.maybe_unsquash_term t)
let (formula_as_term_view : formula -> FStar_Tactics_NamedView.term_view) =
  fun f ->
    let mk_app' tv args =
      FStar_List_Tot_Base.fold_left
        (fun tv1 ->
           fun a ->
             FStar_Tactics_NamedView.Tv_App
               ((FStar_Tactics_NamedView.pack tv1), a)) tv args in
    let e = FStarC_Reflection_V2_Data.Q_Explicit in
    let i = FStarC_Reflection_V2_Data.Q_Implicit in
    match f with
    | True_ ->
        FStar_Tactics_NamedView.Tv_FVar
          (FStarC_Reflection_V2_Builtins.pack_fv
             FStar_Reflection_Const.true_qn)
    | False_ ->
        FStar_Tactics_NamedView.Tv_FVar
          (FStarC_Reflection_V2_Builtins.pack_fv
             FStar_Reflection_Const.false_qn)
    | Comp (Eq (FStar_Pervasives_Native.None), l, r) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.eq2_qn)) [(l, e); (r, e)]
    | Comp (Eq (FStar_Pervasives_Native.Some t), l, r) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.eq2_qn)) [(t, i); (l, e); (r, e)]
    | Comp (BoolEq (FStar_Pervasives_Native.None), l, r) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.eq1_qn)) [(l, e); (r, e)]
    | Comp (BoolEq (FStar_Pervasives_Native.Some t), l, r) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.eq1_qn)) [(t, i); (l, e); (r, e)]
    | Comp (Lt, l, r) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.lt_qn)) [(l, e); (r, e)]
    | Comp (Le, l, r) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.lte_qn)) [(l, e); (r, e)]
    | Comp (Gt, l, r) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.gt_qn)) [(l, e); (r, e)]
    | Comp (Ge, l, r) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.gte_qn)) [(l, e); (r, e)]
    | And (p, q) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.and_qn)) [(p, e); (q, e)]
    | Or (p, q) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.or_qn)) [(p, e); (q, e)]
    | Implies (p, q) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.imp_qn)) [(p, e); (q, e)]
    | Not p ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.not_qn)) [(p, e)]
    | Iff (p, q) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.iff_qn)) [(p, e); (q, e)]
    | Forall (b, sort, t) -> FStar_Tactics_NamedView.Tv_Unknown
    | Exists (b, sort, t) -> FStar_Tactics_NamedView.Tv_Unknown
    | App (p, q) ->
        FStar_Tactics_NamedView.Tv_App
          (p, (q, FStarC_Reflection_V2_Data.Q_Explicit))
    | Name b -> FStar_Tactics_NamedView.Tv_Var b
    | FV fv -> FStar_Tactics_NamedView.Tv_FVar fv
    | IntLit i1 ->
        FStar_Tactics_NamedView.Tv_Const (FStarC_Reflection_V2_Data.C_Int i1)
    | F_Unknown -> FStar_Tactics_NamedView.Tv_Unknown
let (formula_as_term : formula -> FStar_Tactics_NamedView.term) =
  fun f -> FStar_Tactics_NamedView.pack (formula_as_term_view f)
let (namedv_to_string :
  FStar_Tactics_NamedView.namedv ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun namedv ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_Tactics_NamedView.inspect_namedv namedv)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Reflection.V2.Formula.fst"
               (Prims.of_int (222)) (Prims.of_int (18)) (Prims.of_int (222))
               (Prims.of_int (39)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Reflection.V2.Formula.fst"
               (Prims.of_int (223)) (Prims.of_int (4)) (Prims.of_int (223))
               (Prims.of_int (25))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun namedvv ->
            Obj.magic
              (FStarC_Tactics_Unseal.unseal
                 namedvv.FStarC_Reflection_V2_Data.ppname)) uu___1)
let (formula_to_string :
  formula -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    (fun f ->
       match f with
       | True_ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "True_")))
       | False_ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "False_")))
       | Comp (Eq mt, l, r) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 =
                     match mt with
                     | FStar_Pervasives_Native.None ->
                         Obj.magic
                           (Obj.repr
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___2 -> "")))
                     | FStar_Pervasives_Native.Some t ->
                         Obj.magic
                           (Obj.repr
                              (let uu___2 =
                                 let uu___3 =
                                   FStarC_Tactics_V2_Builtins.term_to_string
                                     t in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Reflection.V2.Formula.fst"
                                            (Prims.of_int (232))
                                            (Prims.of_int (44))
                                            (Prims.of_int (232))
                                            (Prims.of_int (60)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "Prims.fst"
                                            (Prims.of_int (611))
                                            (Prims.of_int (19))
                                            (Prims.of_int (611))
                                            (Prims.of_int (31)))))
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___5 ->
                                           Prims.strcat uu___4 ")")) in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Reflection.V2.Formula.fst"
                                          (Prims.of_int (232))
                                          (Prims.of_int (44))
                                          (Prims.of_int (232))
                                          (Prims.of_int (66)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Prims.fst"
                                          (Prims.of_int (611))
                                          (Prims.of_int (19))
                                          (Prims.of_int (611))
                                          (Prims.of_int (31)))))
                                 (Obj.magic uu___2)
                                 (fun uu___3 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___4 -> Prims.strcat " (" uu___3)))) in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (230)) (Prims.of_int (24))
                              (Prims.of_int (232)) (Prims.of_int (67)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (230)) (Prims.of_int (24))
                              (Prims.of_int (233)) (Prims.of_int (80)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             let uu___4 =
                               let uu___5 =
                                 FStarC_Tactics_V2_Builtins.term_to_string l in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Reflection.V2.Formula.fst"
                                          (Prims.of_int (233))
                                          (Prims.of_int (31))
                                          (Prims.of_int (233))
                                          (Prims.of_int (47)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Reflection.V2.Formula.fst"
                                          (Prims.of_int (233))
                                          (Prims.of_int (31))
                                          (Prims.of_int (233))
                                          (Prims.of_int (80)))))
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    (fun uu___6 ->
                                       let uu___7 =
                                         let uu___8 =
                                           let uu___9 =
                                             FStarC_Tactics_V2_Builtins.term_to_string
                                               r in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Reflection.V2.Formula.fst"
                                                      (Prims.of_int (233))
                                                      (Prims.of_int (58))
                                                      (Prims.of_int (233))
                                                      (Prims.of_int (74)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Prims.fst"
                                                      (Prims.of_int (611))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (611))
                                                      (Prims.of_int (31)))))
                                             (Obj.magic uu___9)
                                             (fun uu___10 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___11 ->
                                                     Prims.strcat uu___10 ")")) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Reflection.V2.Formula.fst"
                                                    (Prims.of_int (233))
                                                    (Prims.of_int (58))
                                                    (Prims.of_int (233))
                                                    (Prims.of_int (80)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Prims.fst"
                                                    (Prims.of_int (611))
                                                    (Prims.of_int (19))
                                                    (Prims.of_int (611))
                                                    (Prims.of_int (31)))))
                                           (Obj.magic uu___8)
                                           (fun uu___9 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___10 ->
                                                   Prims.strcat ") (" uu___9)) in
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Reflection.V2.Formula.fst"
                                                     (Prims.of_int (233))
                                                     (Prims.of_int (50))
                                                     (Prims.of_int (233))
                                                     (Prims.of_int (80)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Prims.fst"
                                                     (Prims.of_int (611))
                                                     (Prims.of_int (19))
                                                     (Prims.of_int (611))
                                                     (Prims.of_int (31)))))
                                            (Obj.magic uu___7)
                                            (fun uu___8 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___9 ->
                                                    Prims.strcat uu___6
                                                      uu___8)))) uu___6) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Reflection.V2.Formula.fst"
                                        (Prims.of_int (233))
                                        (Prims.of_int (31))
                                        (Prims.of_int (233))
                                        (Prims.of_int (80)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Prims.fst"
                                        (Prims.of_int (611))
                                        (Prims.of_int (19))
                                        (Prims.of_int (611))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 -> Prims.strcat " (" uu___5)) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Reflection.V2.Formula.fst"
                                         (Prims.of_int (233))
                                         (Prims.of_int (24))
                                         (Prims.of_int (233))
                                         (Prims.of_int (80)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "Prims.fst"
                                         (Prims.of_int (611))
                                         (Prims.of_int (19))
                                         (Prims.of_int (611))
                                         (Prims.of_int (31)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 ->
                                        Prims.strcat uu___2 uu___4)))) uu___2) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (230)) (Prims.of_int (24))
                            (Prims.of_int (233)) (Prims.of_int (80)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Prims.strcat "Eq" uu___1))))
       | Comp (BoolEq mt, l, r) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 =
                     match mt with
                     | FStar_Pervasives_Native.None ->
                         Obj.magic
                           (Obj.repr
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___2 -> "")))
                     | FStar_Pervasives_Native.Some t ->
                         Obj.magic
                           (Obj.repr
                              (let uu___2 =
                                 let uu___3 =
                                   FStarC_Tactics_V2_Builtins.term_to_string
                                     t in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Reflection.V2.Formula.fst"
                                            (Prims.of_int (237))
                                            (Prims.of_int (44))
                                            (Prims.of_int (237))
                                            (Prims.of_int (60)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "Prims.fst"
                                            (Prims.of_int (611))
                                            (Prims.of_int (19))
                                            (Prims.of_int (611))
                                            (Prims.of_int (31)))))
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___5 ->
                                           Prims.strcat uu___4 ")")) in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Reflection.V2.Formula.fst"
                                          (Prims.of_int (237))
                                          (Prims.of_int (44))
                                          (Prims.of_int (237))
                                          (Prims.of_int (66)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Prims.fst"
                                          (Prims.of_int (611))
                                          (Prims.of_int (19))
                                          (Prims.of_int (611))
                                          (Prims.of_int (31)))))
                                 (Obj.magic uu___2)
                                 (fun uu___3 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___4 -> Prims.strcat " (" uu___3)))) in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (235)) (Prims.of_int (24))
                              (Prims.of_int (237)) (Prims.of_int (67)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (235)) (Prims.of_int (24))
                              (Prims.of_int (238)) (Prims.of_int (80)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             let uu___4 =
                               let uu___5 =
                                 FStarC_Tactics_V2_Builtins.term_to_string l in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Reflection.V2.Formula.fst"
                                          (Prims.of_int (238))
                                          (Prims.of_int (31))
                                          (Prims.of_int (238))
                                          (Prims.of_int (47)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Reflection.V2.Formula.fst"
                                          (Prims.of_int (238))
                                          (Prims.of_int (31))
                                          (Prims.of_int (238))
                                          (Prims.of_int (80)))))
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    (fun uu___6 ->
                                       let uu___7 =
                                         let uu___8 =
                                           let uu___9 =
                                             FStarC_Tactics_V2_Builtins.term_to_string
                                               r in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Reflection.V2.Formula.fst"
                                                      (Prims.of_int (238))
                                                      (Prims.of_int (58))
                                                      (Prims.of_int (238))
                                                      (Prims.of_int (74)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Prims.fst"
                                                      (Prims.of_int (611))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (611))
                                                      (Prims.of_int (31)))))
                                             (Obj.magic uu___9)
                                             (fun uu___10 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___11 ->
                                                     Prims.strcat uu___10 ")")) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Reflection.V2.Formula.fst"
                                                    (Prims.of_int (238))
                                                    (Prims.of_int (58))
                                                    (Prims.of_int (238))
                                                    (Prims.of_int (80)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Prims.fst"
                                                    (Prims.of_int (611))
                                                    (Prims.of_int (19))
                                                    (Prims.of_int (611))
                                                    (Prims.of_int (31)))))
                                           (Obj.magic uu___8)
                                           (fun uu___9 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___10 ->
                                                   Prims.strcat ") (" uu___9)) in
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Reflection.V2.Formula.fst"
                                                     (Prims.of_int (238))
                                                     (Prims.of_int (50))
                                                     (Prims.of_int (238))
                                                     (Prims.of_int (80)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Prims.fst"
                                                     (Prims.of_int (611))
                                                     (Prims.of_int (19))
                                                     (Prims.of_int (611))
                                                     (Prims.of_int (31)))))
                                            (Obj.magic uu___7)
                                            (fun uu___8 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___9 ->
                                                    Prims.strcat uu___6
                                                      uu___8)))) uu___6) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Reflection.V2.Formula.fst"
                                        (Prims.of_int (238))
                                        (Prims.of_int (31))
                                        (Prims.of_int (238))
                                        (Prims.of_int (80)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Prims.fst"
                                        (Prims.of_int (611))
                                        (Prims.of_int (19))
                                        (Prims.of_int (611))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 -> Prims.strcat " (" uu___5)) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Reflection.V2.Formula.fst"
                                         (Prims.of_int (238))
                                         (Prims.of_int (24))
                                         (Prims.of_int (238))
                                         (Prims.of_int (80)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "Prims.fst"
                                         (Prims.of_int (611))
                                         (Prims.of_int (19))
                                         (Prims.of_int (611))
                                         (Prims.of_int (31)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 ->
                                        Prims.strcat uu___2 uu___4)))) uu___2) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (235)) (Prims.of_int (24))
                            (Prims.of_int (238)) (Prims.of_int (80)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Prims.strcat "BoolEq" uu___1))))
       | Comp (Lt, l, r) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = FStarC_Tactics_V2_Builtins.term_to_string l in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (239)) (Prims.of_int (30))
                              (Prims.of_int (239)) (Prims.of_int (46)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (239)) (Prims.of_int (30))
                              (Prims.of_int (239)) (Prims.of_int (79)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             let uu___4 =
                               let uu___5 =
                                 FStarC_Tactics_V2_Builtins.term_to_string r in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Reflection.V2.Formula.fst"
                                          (Prims.of_int (239))
                                          (Prims.of_int (57))
                                          (Prims.of_int (239))
                                          (Prims.of_int (73)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Prims.fst"
                                          (Prims.of_int (611))
                                          (Prims.of_int (19))
                                          (Prims.of_int (611))
                                          (Prims.of_int (31)))))
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___7 -> Prims.strcat uu___6 ")")) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Reflection.V2.Formula.fst"
                                        (Prims.of_int (239))
                                        (Prims.of_int (57))
                                        (Prims.of_int (239))
                                        (Prims.of_int (79)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Prims.fst"
                                        (Prims.of_int (611))
                                        (Prims.of_int (19))
                                        (Prims.of_int (611))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 -> Prims.strcat ") (" uu___5)) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Reflection.V2.Formula.fst"
                                         (Prims.of_int (239))
                                         (Prims.of_int (49))
                                         (Prims.of_int (239))
                                         (Prims.of_int (79)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "Prims.fst"
                                         (Prims.of_int (611))
                                         (Prims.of_int (19))
                                         (Prims.of_int (611))
                                         (Prims.of_int (31)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 ->
                                        Prims.strcat uu___2 uu___4)))) uu___2) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (239)) (Prims.of_int (30))
                            (Prims.of_int (239)) (Prims.of_int (79)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Prims.strcat "Lt (" uu___1))))
       | Comp (Le, l, r) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = FStarC_Tactics_V2_Builtins.term_to_string l in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (240)) (Prims.of_int (30))
                              (Prims.of_int (240)) (Prims.of_int (46)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (240)) (Prims.of_int (30))
                              (Prims.of_int (240)) (Prims.of_int (79)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             let uu___4 =
                               let uu___5 =
                                 FStarC_Tactics_V2_Builtins.term_to_string r in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Reflection.V2.Formula.fst"
                                          (Prims.of_int (240))
                                          (Prims.of_int (57))
                                          (Prims.of_int (240))
                                          (Prims.of_int (73)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Prims.fst"
                                          (Prims.of_int (611))
                                          (Prims.of_int (19))
                                          (Prims.of_int (611))
                                          (Prims.of_int (31)))))
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___7 -> Prims.strcat uu___6 ")")) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Reflection.V2.Formula.fst"
                                        (Prims.of_int (240))
                                        (Prims.of_int (57))
                                        (Prims.of_int (240))
                                        (Prims.of_int (79)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Prims.fst"
                                        (Prims.of_int (611))
                                        (Prims.of_int (19))
                                        (Prims.of_int (611))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 -> Prims.strcat ") (" uu___5)) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Reflection.V2.Formula.fst"
                                         (Prims.of_int (240))
                                         (Prims.of_int (49))
                                         (Prims.of_int (240))
                                         (Prims.of_int (79)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "Prims.fst"
                                         (Prims.of_int (611))
                                         (Prims.of_int (19))
                                         (Prims.of_int (611))
                                         (Prims.of_int (31)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 ->
                                        Prims.strcat uu___2 uu___4)))) uu___2) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (240)) (Prims.of_int (30))
                            (Prims.of_int (240)) (Prims.of_int (79)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Prims.strcat "Le (" uu___1))))
       | Comp (Gt, l, r) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = FStarC_Tactics_V2_Builtins.term_to_string l in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (241)) (Prims.of_int (30))
                              (Prims.of_int (241)) (Prims.of_int (46)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (241)) (Prims.of_int (30))
                              (Prims.of_int (241)) (Prims.of_int (79)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             let uu___4 =
                               let uu___5 =
                                 FStarC_Tactics_V2_Builtins.term_to_string r in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Reflection.V2.Formula.fst"
                                          (Prims.of_int (241))
                                          (Prims.of_int (57))
                                          (Prims.of_int (241))
                                          (Prims.of_int (73)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Prims.fst"
                                          (Prims.of_int (611))
                                          (Prims.of_int (19))
                                          (Prims.of_int (611))
                                          (Prims.of_int (31)))))
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___7 -> Prims.strcat uu___6 ")")) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Reflection.V2.Formula.fst"
                                        (Prims.of_int (241))
                                        (Prims.of_int (57))
                                        (Prims.of_int (241))
                                        (Prims.of_int (79)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Prims.fst"
                                        (Prims.of_int (611))
                                        (Prims.of_int (19))
                                        (Prims.of_int (611))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 -> Prims.strcat ") (" uu___5)) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Reflection.V2.Formula.fst"
                                         (Prims.of_int (241))
                                         (Prims.of_int (49))
                                         (Prims.of_int (241))
                                         (Prims.of_int (79)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "Prims.fst"
                                         (Prims.of_int (611))
                                         (Prims.of_int (19))
                                         (Prims.of_int (611))
                                         (Prims.of_int (31)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 ->
                                        Prims.strcat uu___2 uu___4)))) uu___2) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (241)) (Prims.of_int (30))
                            (Prims.of_int (241)) (Prims.of_int (79)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Prims.strcat "Gt (" uu___1))))
       | Comp (Ge, l, r) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = FStarC_Tactics_V2_Builtins.term_to_string l in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (242)) (Prims.of_int (30))
                              (Prims.of_int (242)) (Prims.of_int (46)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (242)) (Prims.of_int (30))
                              (Prims.of_int (242)) (Prims.of_int (79)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             let uu___4 =
                               let uu___5 =
                                 FStarC_Tactics_V2_Builtins.term_to_string r in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Reflection.V2.Formula.fst"
                                          (Prims.of_int (242))
                                          (Prims.of_int (57))
                                          (Prims.of_int (242))
                                          (Prims.of_int (73)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Prims.fst"
                                          (Prims.of_int (611))
                                          (Prims.of_int (19))
                                          (Prims.of_int (611))
                                          (Prims.of_int (31)))))
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___7 -> Prims.strcat uu___6 ")")) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Reflection.V2.Formula.fst"
                                        (Prims.of_int (242))
                                        (Prims.of_int (57))
                                        (Prims.of_int (242))
                                        (Prims.of_int (79)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Prims.fst"
                                        (Prims.of_int (611))
                                        (Prims.of_int (19))
                                        (Prims.of_int (611))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 -> Prims.strcat ") (" uu___5)) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Reflection.V2.Formula.fst"
                                         (Prims.of_int (242))
                                         (Prims.of_int (49))
                                         (Prims.of_int (242))
                                         (Prims.of_int (79)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "Prims.fst"
                                         (Prims.of_int (611))
                                         (Prims.of_int (19))
                                         (Prims.of_int (611))
                                         (Prims.of_int (31)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 ->
                                        Prims.strcat uu___2 uu___4)))) uu___2) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (242)) (Prims.of_int (30))
                            (Prims.of_int (242)) (Prims.of_int (79)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Prims.strcat "Ge (" uu___1))))
       | And (p, q) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = FStarC_Tactics_V2_Builtins.term_to_string p in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (243)) (Prims.of_int (27))
                              (Prims.of_int (243)) (Prims.of_int (43)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (243)) (Prims.of_int (27))
                              (Prims.of_int (243)) (Prims.of_int (76)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             let uu___4 =
                               let uu___5 =
                                 FStarC_Tactics_V2_Builtins.term_to_string q in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Reflection.V2.Formula.fst"
                                          (Prims.of_int (243))
                                          (Prims.of_int (54))
                                          (Prims.of_int (243))
                                          (Prims.of_int (70)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Prims.fst"
                                          (Prims.of_int (611))
                                          (Prims.of_int (19))
                                          (Prims.of_int (611))
                                          (Prims.of_int (31)))))
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___7 -> Prims.strcat uu___6 ")")) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Reflection.V2.Formula.fst"
                                        (Prims.of_int (243))
                                        (Prims.of_int (54))
                                        (Prims.of_int (243))
                                        (Prims.of_int (76)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Prims.fst"
                                        (Prims.of_int (611))
                                        (Prims.of_int (19))
                                        (Prims.of_int (611))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 -> Prims.strcat ") (" uu___5)) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Reflection.V2.Formula.fst"
                                         (Prims.of_int (243))
                                         (Prims.of_int (46))
                                         (Prims.of_int (243))
                                         (Prims.of_int (76)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "Prims.fst"
                                         (Prims.of_int (611))
                                         (Prims.of_int (19))
                                         (Prims.of_int (611))
                                         (Prims.of_int (31)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 ->
                                        Prims.strcat uu___2 uu___4)))) uu___2) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (243)) (Prims.of_int (27))
                            (Prims.of_int (243)) (Prims.of_int (76)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Prims.strcat "And (" uu___1))))
       | Or (p, q) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = FStarC_Tactics_V2_Builtins.term_to_string p in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (244)) (Prims.of_int (27))
                              (Prims.of_int (244)) (Prims.of_int (43)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (244)) (Prims.of_int (27))
                              (Prims.of_int (244)) (Prims.of_int (76)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             let uu___4 =
                               let uu___5 =
                                 FStarC_Tactics_V2_Builtins.term_to_string q in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Reflection.V2.Formula.fst"
                                          (Prims.of_int (244))
                                          (Prims.of_int (54))
                                          (Prims.of_int (244))
                                          (Prims.of_int (70)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Prims.fst"
                                          (Prims.of_int (611))
                                          (Prims.of_int (19))
                                          (Prims.of_int (611))
                                          (Prims.of_int (31)))))
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___7 -> Prims.strcat uu___6 ")")) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Reflection.V2.Formula.fst"
                                        (Prims.of_int (244))
                                        (Prims.of_int (54))
                                        (Prims.of_int (244))
                                        (Prims.of_int (76)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Prims.fst"
                                        (Prims.of_int (611))
                                        (Prims.of_int (19))
                                        (Prims.of_int (611))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 -> Prims.strcat ") (" uu___5)) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Reflection.V2.Formula.fst"
                                         (Prims.of_int (244))
                                         (Prims.of_int (46))
                                         (Prims.of_int (244))
                                         (Prims.of_int (76)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "Prims.fst"
                                         (Prims.of_int (611))
                                         (Prims.of_int (19))
                                         (Prims.of_int (611))
                                         (Prims.of_int (31)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 ->
                                        Prims.strcat uu___2 uu___4)))) uu___2) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (244)) (Prims.of_int (27))
                            (Prims.of_int (244)) (Prims.of_int (76)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Prims.strcat "Or (" uu___1))))
       | Implies (p, q) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = FStarC_Tactics_V2_Builtins.term_to_string p in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (245)) (Prims.of_int (36))
                              (Prims.of_int (245)) (Prims.of_int (52)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (245)) (Prims.of_int (36))
                              (Prims.of_int (245)) (Prims.of_int (85)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             let uu___4 =
                               let uu___5 =
                                 FStarC_Tactics_V2_Builtins.term_to_string q in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Reflection.V2.Formula.fst"
                                          (Prims.of_int (245))
                                          (Prims.of_int (63))
                                          (Prims.of_int (245))
                                          (Prims.of_int (79)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Prims.fst"
                                          (Prims.of_int (611))
                                          (Prims.of_int (19))
                                          (Prims.of_int (611))
                                          (Prims.of_int (31)))))
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___7 -> Prims.strcat uu___6 ")")) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Reflection.V2.Formula.fst"
                                        (Prims.of_int (245))
                                        (Prims.of_int (63))
                                        (Prims.of_int (245))
                                        (Prims.of_int (85)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Prims.fst"
                                        (Prims.of_int (611))
                                        (Prims.of_int (19))
                                        (Prims.of_int (611))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 -> Prims.strcat ") (" uu___5)) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Reflection.V2.Formula.fst"
                                         (Prims.of_int (245))
                                         (Prims.of_int (55))
                                         (Prims.of_int (245))
                                         (Prims.of_int (85)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "Prims.fst"
                                         (Prims.of_int (611))
                                         (Prims.of_int (19))
                                         (Prims.of_int (611))
                                         (Prims.of_int (31)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 ->
                                        Prims.strcat uu___2 uu___4)))) uu___2) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (245)) (Prims.of_int (36))
                            (Prims.of_int (245)) (Prims.of_int (85)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Prims.strcat "Implies (" uu___1))))
       | Not p ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = FStarC_Tactics_V2_Builtins.term_to_string p in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (246)) (Prims.of_int (26))
                              (Prims.of_int (246)) (Prims.of_int (42)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Prims.fst"
                              (Prims.of_int (611)) (Prims.of_int (19))
                              (Prims.of_int (611)) (Prims.of_int (31)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> Prims.strcat uu___2 ")")) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (246)) (Prims.of_int (26))
                            (Prims.of_int (246)) (Prims.of_int (48)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Prims.strcat "Not (" uu___1))))
       | Iff (p, q) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = FStarC_Tactics_V2_Builtins.term_to_string p in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (247)) (Prims.of_int (28))
                              (Prims.of_int (247)) (Prims.of_int (44)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (247)) (Prims.of_int (28))
                              (Prims.of_int (247)) (Prims.of_int (77)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             let uu___4 =
                               let uu___5 =
                                 FStarC_Tactics_V2_Builtins.term_to_string q in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Reflection.V2.Formula.fst"
                                          (Prims.of_int (247))
                                          (Prims.of_int (55))
                                          (Prims.of_int (247))
                                          (Prims.of_int (71)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Prims.fst"
                                          (Prims.of_int (611))
                                          (Prims.of_int (19))
                                          (Prims.of_int (611))
                                          (Prims.of_int (31)))))
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___7 -> Prims.strcat uu___6 ")")) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Reflection.V2.Formula.fst"
                                        (Prims.of_int (247))
                                        (Prims.of_int (55))
                                        (Prims.of_int (247))
                                        (Prims.of_int (77)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Prims.fst"
                                        (Prims.of_int (611))
                                        (Prims.of_int (19))
                                        (Prims.of_int (611))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 -> Prims.strcat ") (" uu___5)) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Reflection.V2.Formula.fst"
                                         (Prims.of_int (247))
                                         (Prims.of_int (47))
                                         (Prims.of_int (247))
                                         (Prims.of_int (77)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "Prims.fst"
                                         (Prims.of_int (611))
                                         (Prims.of_int (19))
                                         (Prims.of_int (611))
                                         (Prims.of_int (31)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 ->
                                        Prims.strcat uu___2 uu___4)))) uu___2) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (247)) (Prims.of_int (28))
                            (Prims.of_int (247)) (Prims.of_int (77)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Prims.strcat "Iff (" uu___1))))
       | Forall (bs, _sort, t) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = FStarC_Tactics_V2_Builtins.term_to_string t in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (248)) (Prims.of_int (45))
                              (Prims.of_int (248)) (Prims.of_int (61)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Prims.fst"
                              (Prims.of_int (611)) (Prims.of_int (19))
                              (Prims.of_int (611)) (Prims.of_int (31)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> Prims.strcat uu___2 ")")) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (248)) (Prims.of_int (45))
                            (Prims.of_int (248)) (Prims.of_int (67)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Prims.strcat "Forall <bs> (" uu___1))))
       | Exists (bs, _sort, t) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = FStarC_Tactics_V2_Builtins.term_to_string t in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (249)) (Prims.of_int (45))
                              (Prims.of_int (249)) (Prims.of_int (61)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Prims.fst"
                              (Prims.of_int (611)) (Prims.of_int (19))
                              (Prims.of_int (611)) (Prims.of_int (31)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> Prims.strcat uu___2 ")")) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (249)) (Prims.of_int (45))
                            (Prims.of_int (249)) (Prims.of_int (67)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Prims.strcat "Exists <bs> (" uu___1))))
       | App (p, q) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = FStarC_Tactics_V2_Builtins.term_to_string p in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (250)) (Prims.of_int (28))
                              (Prims.of_int (250)) (Prims.of_int (44)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (250)) (Prims.of_int (28))
                              (Prims.of_int (250)) (Prims.of_int (77)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             let uu___4 =
                               let uu___5 =
                                 FStarC_Tactics_V2_Builtins.term_to_string q in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Reflection.V2.Formula.fst"
                                          (Prims.of_int (250))
                                          (Prims.of_int (55))
                                          (Prims.of_int (250))
                                          (Prims.of_int (71)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Prims.fst"
                                          (Prims.of_int (611))
                                          (Prims.of_int (19))
                                          (Prims.of_int (611))
                                          (Prims.of_int (31)))))
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___7 -> Prims.strcat uu___6 ")")) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Reflection.V2.Formula.fst"
                                        (Prims.of_int (250))
                                        (Prims.of_int (55))
                                        (Prims.of_int (250))
                                        (Prims.of_int (77)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Prims.fst"
                                        (Prims.of_int (611))
                                        (Prims.of_int (19))
                                        (Prims.of_int (611))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 -> Prims.strcat ") (" uu___5)) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Reflection.V2.Formula.fst"
                                         (Prims.of_int (250))
                                         (Prims.of_int (47))
                                         (Prims.of_int (250))
                                         (Prims.of_int (77)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "Prims.fst"
                                         (Prims.of_int (611))
                                         (Prims.of_int (19))
                                         (Prims.of_int (611))
                                         (Prims.of_int (31)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 ->
                                        Prims.strcat uu___2 uu___4)))) uu___2) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (250)) (Prims.of_int (28))
                            (Prims.of_int (250)) (Prims.of_int (77)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Prims.strcat "App (" uu___1))))
       | Name bv ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = namedv_to_string bv in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Reflection.V2.Formula.fst"
                              (Prims.of_int (251)) (Prims.of_int (29))
                              (Prims.of_int (251)) (Prims.of_int (48)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Prims.fst"
                              (Prims.of_int (611)) (Prims.of_int (19))
                              (Prims.of_int (611)) (Prims.of_int (31)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> Prims.strcat uu___2 ")")) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (251)) (Prims.of_int (29))
                            (Prims.of_int (251)) (Prims.of_int (54)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Prims.strcat "Name (" uu___1))))
       | FV fv ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Prims.strcat "FV ("
                        (Prims.strcat
                           (FStar_Reflection_V2_Derived.flatten_name
                              (FStarC_Reflection_V2_Builtins.inspect_fv fv))
                           ")"))))
       | IntLit i ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> Prims.strcat "Int " (Prims.string_of_int i))))
       | F_Unknown ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "?"))))
      uu___