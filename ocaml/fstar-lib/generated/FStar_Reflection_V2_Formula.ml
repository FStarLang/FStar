open Prims
let rec (inspect_unascribe :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.term_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Reflection.V2.Formula.fst"
               (Prims.of_int (33)) (Prims.of_int (8)) (Prims.of_int (33))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Reflection.V2.Formula.fst"
               (Prims.of_int (33)) (Prims.of_int (2)) (Prims.of_int (37))
               (Prims.of_int (12)))))
      (Obj.magic (FStar_Tactics_NamedView.inspect t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Tactics_NamedView.Tv_AscribedT
                (t1, uu___1, uu___2, uu___3) ->
                Obj.magic (Obj.repr (inspect_unascribe t1))
            | FStar_Tactics_NamedView.Tv_AscribedC
                (t1, uu___1, uu___2, uu___3) ->
                Obj.magic (Obj.repr (inspect_unascribe t1))
            | tv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> tv))))
           uu___)
let rec (collect_app' :
  FStar_Reflection_V2_Data.argv Prims.list ->
    FStar_Tactics_NamedView.term ->
      ((FStar_Tactics_NamedView.term * FStar_Reflection_V2_Data.argv
         Prims.list),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun args ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Reflection.V2.Formula.fst"
                 (Prims.of_int (41)) (Prims.of_int (10)) (Prims.of_int (41))
                 (Prims.of_int (29)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Reflection.V2.Formula.fst"
                 (Prims.of_int (41)) (Prims.of_int (4)) (Prims.of_int (44))
                 (Prims.of_int (20))))) (Obj.magic (inspect_unascribe t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Tactics_NamedView.Tv_App (l, r) ->
                  Obj.magic (Obj.repr (collect_app' (r :: args) l))
              | uu___1 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> (t, args))))) uu___)
let (collect_app :
  FStar_Tactics_NamedView.term ->
    ((FStar_Tactics_NamedView.term * FStar_Reflection_V2_Data.argv
       Prims.list),
      unit) FStar_Tactics_Effect.tac_repr)
  = collect_app' []
type comparison =
  | Eq of FStar_Reflection_Types.typ FStar_Pervasives_Native.option 
  | BoolEq of FStar_Reflection_Types.typ FStar_Pervasives_Native.option 
  | Lt 
  | Le 
  | Gt 
  | Ge 
let rec __knot_e_comparison _ =
  FStar_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Reflection.V2.Formula.comparison"
    (fun tm_0 ->
       match tm_0 with
       | ("FStar.Reflection.V2.Formula.Eq", _0_2::[]) ->
           FStar_Compiler_Util.bind_opt
             (FStar_Syntax_Embeddings_Base.extracted_unembed
                (FStar_Syntax_Embeddings.e_option
                   FStar_Reflection_V2_Embeddings.e_term) _0_2)
             (fun _0_2 -> FStar_Pervasives_Native.Some (Eq _0_2))
       | ("FStar.Reflection.V2.Formula.BoolEq", _0_4::[]) ->
           FStar_Compiler_Util.bind_opt
             (FStar_Syntax_Embeddings_Base.extracted_unembed
                (FStar_Syntax_Embeddings.e_option
                   FStar_Reflection_V2_Embeddings.e_term) _0_4)
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
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.Eq"))
             [((FStar_Syntax_Embeddings_Base.extracted_embed
                  (FStar_Syntax_Embeddings.e_option
                     FStar_Reflection_V2_Embeddings.e_term) _0_11),
                FStar_Pervasives_Native.None)]
       | BoolEq _0_13 ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.BoolEq"))
             [((FStar_Syntax_Embeddings_Base.extracted_embed
                  (FStar_Syntax_Embeddings.e_option
                     FStar_Reflection_V2_Embeddings.e_term) _0_13),
                FStar_Pervasives_Native.None)]
       | Lt ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.Lt")) []
       | Le ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.Le")) []
       | Gt ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.Gt")) []
       | Ge ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.Ge")) [])
let e_comparison = __knot_e_comparison ()
let (uu___is_Eq : comparison -> Prims.bool) =
  fun projectee -> match projectee with | Eq _0 -> true | uu___ -> false
let (__proj__Eq__item___0 :
  comparison -> FStar_Reflection_Types.typ FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | Eq _0 -> _0
let (uu___is_BoolEq : comparison -> Prims.bool) =
  fun projectee -> match projectee with | BoolEq _0 -> true | uu___ -> false
let (__proj__BoolEq__item___0 :
  comparison -> FStar_Reflection_Types.typ FStar_Pervasives_Native.option) =
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
  | Forall of FStar_Tactics_NamedView.bv * FStar_Reflection_Types.typ *
  FStar_Tactics_NamedView.term 
  | Exists of FStar_Tactics_NamedView.bv * FStar_Reflection_Types.typ *
  FStar_Tactics_NamedView.term 
  | App of FStar_Tactics_NamedView.term * FStar_Tactics_NamedView.term 
  | Name of FStar_Tactics_NamedView.namedv 
  | FV of FStar_Reflection_Types.fv 
  | IntLit of Prims.int 
  | F_Unknown 
let rec __knot_e_formula _ =
  FStar_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Reflection.V2.Formula.formula"
    (fun tm_18 ->
       match tm_18 with
       | ("FStar.Reflection.V2.Formula.True_", []) ->
           FStar_Pervasives_Native.Some True_
       | ("FStar.Reflection.V2.Formula.False_", []) ->
           FStar_Pervasives_Native.Some False_
       | ("FStar.Reflection.V2.Formula.Comp", _0_22::_1_23::_2_24::[]) ->
           FStar_Compiler_Util.bind_opt
             (FStar_Syntax_Embeddings_Base.extracted_unembed e_comparison
                _0_22)
             (fun _0_22 ->
                FStar_Compiler_Util.bind_opt
                  (FStar_Syntax_Embeddings_Base.extracted_unembed
                     FStar_Reflection_V2_Embeddings.e_term _1_23)
                  (fun _1_23 ->
                     FStar_Compiler_Util.bind_opt
                       (FStar_Syntax_Embeddings_Base.extracted_unembed
                          FStar_Reflection_V2_Embeddings.e_term _2_24)
                       (fun _2_24 ->
                          FStar_Pervasives_Native.Some
                            (Comp (_0_22, _1_23, _2_24)))))
       | ("FStar.Reflection.V2.Formula.And", _0_26::_1_27::[]) ->
           FStar_Compiler_Util.bind_opt
             (FStar_Syntax_Embeddings_Base.extracted_unembed
                FStar_Reflection_V2_Embeddings.e_term _0_26)
             (fun _0_26 ->
                FStar_Compiler_Util.bind_opt
                  (FStar_Syntax_Embeddings_Base.extracted_unembed
                     FStar_Reflection_V2_Embeddings.e_term _1_27)
                  (fun _1_27 ->
                     FStar_Pervasives_Native.Some (And (_0_26, _1_27))))
       | ("FStar.Reflection.V2.Formula.Or", _0_29::_1_30::[]) ->
           FStar_Compiler_Util.bind_opt
             (FStar_Syntax_Embeddings_Base.extracted_unembed
                FStar_Reflection_V2_Embeddings.e_term _0_29)
             (fun _0_29 ->
                FStar_Compiler_Util.bind_opt
                  (FStar_Syntax_Embeddings_Base.extracted_unembed
                     FStar_Reflection_V2_Embeddings.e_term _1_30)
                  (fun _1_30 ->
                     FStar_Pervasives_Native.Some (Or (_0_29, _1_30))))
       | ("FStar.Reflection.V2.Formula.Not", _0_32::[]) ->
           FStar_Compiler_Util.bind_opt
             (FStar_Syntax_Embeddings_Base.extracted_unembed
                FStar_Reflection_V2_Embeddings.e_term _0_32)
             (fun _0_32 -> FStar_Pervasives_Native.Some (Not _0_32))
       | ("FStar.Reflection.V2.Formula.Implies", _0_34::_1_35::[]) ->
           FStar_Compiler_Util.bind_opt
             (FStar_Syntax_Embeddings_Base.extracted_unembed
                FStar_Reflection_V2_Embeddings.e_term _0_34)
             (fun _0_34 ->
                FStar_Compiler_Util.bind_opt
                  (FStar_Syntax_Embeddings_Base.extracted_unembed
                     FStar_Reflection_V2_Embeddings.e_term _1_35)
                  (fun _1_35 ->
                     FStar_Pervasives_Native.Some (Implies (_0_34, _1_35))))
       | ("FStar.Reflection.V2.Formula.Iff", _0_37::_1_38::[]) ->
           FStar_Compiler_Util.bind_opt
             (FStar_Syntax_Embeddings_Base.extracted_unembed
                FStar_Reflection_V2_Embeddings.e_term _0_37)
             (fun _0_37 ->
                FStar_Compiler_Util.bind_opt
                  (FStar_Syntax_Embeddings_Base.extracted_unembed
                     FStar_Reflection_V2_Embeddings.e_term _1_38)
                  (fun _1_38 ->
                     FStar_Pervasives_Native.Some (Iff (_0_37, _1_38))))
       | ("FStar.Reflection.V2.Formula.Forall", _0_40::_1_41::_2_42::[]) ->
           FStar_Compiler_Util.bind_opt
             (FStar_Syntax_Embeddings_Base.extracted_unembed
                FStar_Reflection_V2_Embeddings.e_bv_view _0_40)
             (fun _0_40 ->
                FStar_Compiler_Util.bind_opt
                  (FStar_Syntax_Embeddings_Base.extracted_unembed
                     FStar_Reflection_V2_Embeddings.e_term _1_41)
                  (fun _1_41 ->
                     FStar_Compiler_Util.bind_opt
                       (FStar_Syntax_Embeddings_Base.extracted_unembed
                          FStar_Reflection_V2_Embeddings.e_term _2_42)
                       (fun _2_42 ->
                          FStar_Pervasives_Native.Some
                            (Forall (_0_40, _1_41, _2_42)))))
       | ("FStar.Reflection.V2.Formula.Exists", _0_44::_1_45::_2_46::[]) ->
           FStar_Compiler_Util.bind_opt
             (FStar_Syntax_Embeddings_Base.extracted_unembed
                FStar_Reflection_V2_Embeddings.e_bv_view _0_44)
             (fun _0_44 ->
                FStar_Compiler_Util.bind_opt
                  (FStar_Syntax_Embeddings_Base.extracted_unembed
                     FStar_Reflection_V2_Embeddings.e_term _1_45)
                  (fun _1_45 ->
                     FStar_Compiler_Util.bind_opt
                       (FStar_Syntax_Embeddings_Base.extracted_unembed
                          FStar_Reflection_V2_Embeddings.e_term _2_46)
                       (fun _2_46 ->
                          FStar_Pervasives_Native.Some
                            (Exists (_0_44, _1_45, _2_46)))))
       | ("FStar.Reflection.V2.Formula.App", _0_48::_1_49::[]) ->
           FStar_Compiler_Util.bind_opt
             (FStar_Syntax_Embeddings_Base.extracted_unembed
                FStar_Reflection_V2_Embeddings.e_term _0_48)
             (fun _0_48 ->
                FStar_Compiler_Util.bind_opt
                  (FStar_Syntax_Embeddings_Base.extracted_unembed
                     FStar_Reflection_V2_Embeddings.e_term _1_49)
                  (fun _1_49 ->
                     FStar_Pervasives_Native.Some (App (_0_48, _1_49))))
       | ("FStar.Reflection.V2.Formula.Name", _0_51::[]) ->
           FStar_Compiler_Util.bind_opt
             (FStar_Syntax_Embeddings_Base.extracted_unembed
                FStar_Reflection_V2_Embeddings.e_namedv_view _0_51)
             (fun _0_51 -> FStar_Pervasives_Native.Some (Name _0_51))
       | ("FStar.Reflection.V2.Formula.FV", _0_53::[]) ->
           FStar_Compiler_Util.bind_opt
             (FStar_Syntax_Embeddings_Base.extracted_unembed
                FStar_Reflection_V2_Embeddings.e_fv _0_53)
             (fun _0_53 -> FStar_Pervasives_Native.Some (FV _0_53))
       | ("FStar.Reflection.V2.Formula.IntLit", _0_55::[]) ->
           FStar_Compiler_Util.bind_opt
             (FStar_Syntax_Embeddings_Base.extracted_unembed
                FStar_Syntax_Embeddings.e_int _0_55)
             (fun _0_55 -> FStar_Pervasives_Native.Some (IntLit _0_55))
       | ("FStar.Reflection.V2.Formula.F_Unknown", []) ->
           FStar_Pervasives_Native.Some F_Unknown
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_57 ->
       match tm_57 with
       | True_ ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.True_"))
             []
       | False_ ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.False_"))
             []
       | Comp (_0_61, _1_62, _2_63) ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.Comp"))
             [((FStar_Syntax_Embeddings_Base.extracted_embed e_comparison
                  _0_61), FStar_Pervasives_Native.None);
             ((FStar_Syntax_Embeddings_Base.extracted_embed
                 FStar_Reflection_V2_Embeddings.e_term _1_62),
               FStar_Pervasives_Native.None);
             ((FStar_Syntax_Embeddings_Base.extracted_embed
                 FStar_Reflection_V2_Embeddings.e_term _2_63),
               FStar_Pervasives_Native.None)]
       | And (_0_65, _1_66) ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.And"))
             [((FStar_Syntax_Embeddings_Base.extracted_embed
                  FStar_Reflection_V2_Embeddings.e_term _0_65),
                FStar_Pervasives_Native.None);
             ((FStar_Syntax_Embeddings_Base.extracted_embed
                 FStar_Reflection_V2_Embeddings.e_term _1_66),
               FStar_Pervasives_Native.None)]
       | Or (_0_68, _1_69) ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.Or"))
             [((FStar_Syntax_Embeddings_Base.extracted_embed
                  FStar_Reflection_V2_Embeddings.e_term _0_68),
                FStar_Pervasives_Native.None);
             ((FStar_Syntax_Embeddings_Base.extracted_embed
                 FStar_Reflection_V2_Embeddings.e_term _1_69),
               FStar_Pervasives_Native.None)]
       | Not _0_71 ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.Not"))
             [((FStar_Syntax_Embeddings_Base.extracted_embed
                  FStar_Reflection_V2_Embeddings.e_term _0_71),
                FStar_Pervasives_Native.None)]
       | Implies (_0_73, _1_74) ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.Implies"))
             [((FStar_Syntax_Embeddings_Base.extracted_embed
                  FStar_Reflection_V2_Embeddings.e_term _0_73),
                FStar_Pervasives_Native.None);
             ((FStar_Syntax_Embeddings_Base.extracted_embed
                 FStar_Reflection_V2_Embeddings.e_term _1_74),
               FStar_Pervasives_Native.None)]
       | Iff (_0_76, _1_77) ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.Iff"))
             [((FStar_Syntax_Embeddings_Base.extracted_embed
                  FStar_Reflection_V2_Embeddings.e_term _0_76),
                FStar_Pervasives_Native.None);
             ((FStar_Syntax_Embeddings_Base.extracted_embed
                 FStar_Reflection_V2_Embeddings.e_term _1_77),
               FStar_Pervasives_Native.None)]
       | Forall (_0_79, _1_80, _2_81) ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.Forall"))
             [((FStar_Syntax_Embeddings_Base.extracted_embed
                  FStar_Reflection_V2_Embeddings.e_bv_view _0_79),
                FStar_Pervasives_Native.None);
             ((FStar_Syntax_Embeddings_Base.extracted_embed
                 FStar_Reflection_V2_Embeddings.e_term _1_80),
               FStar_Pervasives_Native.None);
             ((FStar_Syntax_Embeddings_Base.extracted_embed
                 FStar_Reflection_V2_Embeddings.e_term _2_81),
               FStar_Pervasives_Native.None)]
       | Exists (_0_83, _1_84, _2_85) ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.Exists"))
             [((FStar_Syntax_Embeddings_Base.extracted_embed
                  FStar_Reflection_V2_Embeddings.e_bv_view _0_83),
                FStar_Pervasives_Native.None);
             ((FStar_Syntax_Embeddings_Base.extracted_embed
                 FStar_Reflection_V2_Embeddings.e_term _1_84),
               FStar_Pervasives_Native.None);
             ((FStar_Syntax_Embeddings_Base.extracted_embed
                 FStar_Reflection_V2_Embeddings.e_term _2_85),
               FStar_Pervasives_Native.None)]
       | App (_0_87, _1_88) ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.App"))
             [((FStar_Syntax_Embeddings_Base.extracted_embed
                  FStar_Reflection_V2_Embeddings.e_term _0_87),
                FStar_Pervasives_Native.None);
             ((FStar_Syntax_Embeddings_Base.extracted_embed
                 FStar_Reflection_V2_Embeddings.e_term _1_88),
               FStar_Pervasives_Native.None)]
       | Name _0_90 ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.Name"))
             [((FStar_Syntax_Embeddings_Base.extracted_embed
                  FStar_Reflection_V2_Embeddings.e_namedv_view _0_90),
                FStar_Pervasives_Native.None)]
       | FV _0_92 ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.FV"))
             [((FStar_Syntax_Embeddings_Base.extracted_embed
                  FStar_Reflection_V2_Embeddings.e_fv _0_92),
                FStar_Pervasives_Native.None)]
       | IntLit _0_94 ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str "FStar.Reflection.V2.Formula.IntLit"))
             [((FStar_Syntax_Embeddings_Base.extracted_embed
                  FStar_Syntax_Embeddings.e_int _0_94),
                FStar_Pervasives_Native.None)]
       | F_Unknown ->
           FStar_Syntax_Util.mk_app
             (FStar_Syntax_Syntax.tdataconstr
                (FStar_Ident.lid_of_str
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
let (__proj__Forall__item___1 : formula -> FStar_Reflection_Types.typ) =
  fun projectee -> match projectee with | Forall (_0, _1, _2) -> _1
let (__proj__Forall__item___2 : formula -> FStar_Tactics_NamedView.term) =
  fun projectee -> match projectee with | Forall (_0, _1, _2) -> _2
let (uu___is_Exists : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Exists (_0, _1, _2) -> true | uu___ -> false
let (__proj__Exists__item___0 : formula -> FStar_Tactics_NamedView.bv) =
  fun projectee -> match projectee with | Exists (_0, _1, _2) -> _0
let (__proj__Exists__item___1 : formula -> FStar_Reflection_Types.typ) =
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
let (__proj__FV__item___0 : formula -> FStar_Reflection_Types.fv) =
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
            FStar_Reflection_V2_Data.index = Prims.int_zero;
            FStar_Reflection_V2_Data.sort1 = (FStar_Sealed.seal typ);
            FStar_Reflection_V2_Data.ppname1 =
              (FStar_Reflection_V2_Data.as_ppname "x")
          } in
      Forall
        (b, typ,
          (FStar_Tactics_NamedView.pack
             (FStar_Tactics_NamedView.Tv_App
                (pred,
                  ((FStar_Tactics_NamedView.pack
                      (FStar_Tactics_NamedView.Tv_BVar b)),
                    FStar_Reflection_V2_Data.Q_Explicit)))))
let (mk_Exists :
  FStar_Tactics_NamedView.term -> FStar_Tactics_NamedView.term -> formula) =
  fun typ ->
    fun pred ->
      let b =
        FStar_Tactics_NamedView.pack_bv
          {
            FStar_Reflection_V2_Data.index = Prims.int_zero;
            FStar_Reflection_V2_Data.sort1 = (FStar_Sealed.seal typ);
            FStar_Reflection_V2_Data.ppname1 =
              (FStar_Reflection_V2_Data.as_ppname "x")
          } in
      Exists
        (b, typ,
          (FStar_Tactics_NamedView.pack
             (FStar_Tactics_NamedView.Tv_App
                (pred,
                  ((FStar_Tactics_NamedView.pack
                      (FStar_Tactics_NamedView.Tv_BVar b)),
                    FStar_Reflection_V2_Data.Q_Explicit)))))
let (term_as_formula' :
  FStar_Tactics_NamedView.term ->
    (formula, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Reflection.V2.Formula.fst"
               (Prims.of_int (87)) (Prims.of_int (10)) (Prims.of_int (87))
               (Prims.of_int (29)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Reflection.V2.Formula.fst"
               (Prims.of_int (87)) (Prims.of_int (4)) (Prims.of_int (163))
               (Prims.of_int (38))))) (Obj.magic (inspect_unascribe t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Tactics_NamedView.Tv_Var n ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Name n)))
            | FStar_Tactics_NamedView.Tv_FVar fv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           if
                             (FStar_Reflection_V2_Builtins.inspect_fv fv) =
                               FStar_Reflection_Const.true_qn
                           then True_
                           else
                             if
                               (FStar_Reflection_V2_Builtins.inspect_fv fv) =
                                 FStar_Reflection_Const.false_qn
                             then False_
                             else FV fv)))
            | FStar_Tactics_NamedView.Tv_UInst (fv, uu___1) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           if
                             (FStar_Reflection_V2_Builtins.inspect_fv fv) =
                               FStar_Reflection_Const.true_qn
                           then True_
                           else
                             if
                               (FStar_Reflection_V2_Builtins.inspect_fv fv) =
                                 FStar_Reflection_Const.false_qn
                             then False_
                             else FV fv)))
            | FStar_Tactics_NamedView.Tv_App (h0, t1) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Reflection.V2.Formula.fst"
                                 (Prims.of_int (103)) (Prims.of_int (22))
                                 (Prims.of_int (103)) (Prims.of_int (36)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Reflection.V2.Formula.fst"
                                 (Prims.of_int (102)) (Prims.of_int (26))
                                 (Prims.of_int (141)) (Prims.of_int (26)))))
                        (Obj.magic (collect_app h0))
                        (fun uu___1 ->
                           (fun uu___1 ->
                              match uu___1 with
                              | (h, ts) ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Reflection.V2.Formula.fst"
                                                (Prims.of_int (104))
                                                (Prims.of_int (16))
                                                (Prims.of_int (104))
                                                (Prims.of_int (26)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Reflection.V2.Formula.fst"
                                                (Prims.of_int (105))
                                                (Prims.of_int (8))
                                                (Prims.of_int (141))
                                                (Prims.of_int (26)))))
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___2 ->
                                             FStar_Reflection_V2_Derived.un_uinst
                                               h))
                                       (fun uu___2 ->
                                          (fun h1 ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Reflection.V2.Formula.fst"
                                                           (Prims.of_int (105))
                                                           (Prims.of_int (14))
                                                           (Prims.of_int (105))
                                                           (Prims.of_int (31)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Reflection.V2.Formula.fst"
                                                           (Prims.of_int (105))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (141))
                                                           (Prims.of_int (26)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Reflection.V2.Formula.fst"
                                                                 (Prims.of_int (105))
                                                                 (Prims.of_int (14))
                                                                 (Prims.of_int (105))
                                                                 (Prims.of_int (23)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Reflection.V2.Formula.fst"
                                                                 (Prims.of_int (105))
                                                                 (Prims.of_int (14))
                                                                 (Prims.of_int (105))
                                                                 (Prims.of_int (31)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_NamedView.inspect
                                                              h1))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                (uu___2,
                                                                  (FStar_List_Tot_Base.op_At
                                                                    ts 
                                                                    [t1]))))))
                                                  (fun uu___2 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___3 ->
                                                          match uu___2 with
                                                          | (FStar_Tactics_NamedView.Tv_FVar
                                                             fv,
                                                             (a1,
                                                              FStar_Reflection_V2_Data.Q_Implicit)::
                                                             (a2,
                                                              FStar_Reflection_V2_Data.Q_Explicit)::
                                                             (a3,
                                                              FStar_Reflection_V2_Data.Q_Explicit)::[])
                                                              ->
                                                              if
                                                                (FStar_Reflection_V2_Builtins.inspect_fv
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
                                                                  (FStar_Reflection_V2_Builtins.inspect_fv
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
                                                                    (FStar_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.lt_qn
                                                                  then
                                                                    Comp
                                                                    (Lt, a2,
                                                                    a3)
                                                                  else
                                                                    if
                                                                    (FStar_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.lte_qn
                                                                    then
                                                                    Comp
                                                                    (Le, a2,
                                                                    a3)
                                                                    else
                                                                    if
                                                                    (FStar_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.gt_qn
                                                                    then
                                                                    Comp
                                                                    (Gt, a2,
                                                                    a3)
                                                                    else
                                                                    if
                                                                    (FStar_Reflection_V2_Builtins.inspect_fv
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
                                                              FStar_Reflection_V2_Data.Q_Explicit)::
                                                             (a2,
                                                              FStar_Reflection_V2_Data.Q_Explicit)::[])
                                                              ->
                                                              if
                                                                (FStar_Reflection_V2_Builtins.inspect_fv
                                                                   fv)
                                                                  =
                                                                  FStar_Reflection_Const.imp_qn
                                                              then
                                                                Implies
                                                                  (a1, a2)
                                                              else
                                                                if
                                                                  (FStar_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.and_qn
                                                                then
                                                                  And
                                                                    (a1, a2)
                                                                else
                                                                  if
                                                                    (FStar_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.iff_qn
                                                                  then
                                                                    Iff
                                                                    (a1, a2)
                                                                  else
                                                                    if
                                                                    (FStar_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.or_qn
                                                                    then
                                                                    Or
                                                                    (a1, a2)
                                                                    else
                                                                    if
                                                                    (FStar_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.eq2_qn
                                                                    then
                                                                    Comp
                                                                    ((Eq
                                                                    FStar_Pervasives_Native.None),
                                                                    a1, a2)
                                                                    else
                                                                    if
                                                                    (FStar_Reflection_V2_Builtins.inspect_fv
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
                                                              FStar_Reflection_V2_Data.Q_Implicit)::
                                                             (a2,
                                                              FStar_Reflection_V2_Data.Q_Explicit)::[])
                                                              ->
                                                              if
                                                                (FStar_Reflection_V2_Builtins.inspect_fv
                                                                   fv)
                                                                  =
                                                                  FStar_Reflection_Const.forall_qn
                                                              then
                                                                mk_Forall a1
                                                                  a2
                                                              else
                                                                if
                                                                  (FStar_Reflection_V2_Builtins.inspect_fv
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
                                                              FStar_Reflection_V2_Data.Q_Explicit)::[])
                                                              ->
                                                              if
                                                                (FStar_Reflection_V2_Builtins.inspect_fv
                                                                   fv)
                                                                  =
                                                                  FStar_Reflection_Const.not_qn
                                                              then Not a
                                                              else
                                                                if
                                                                  (FStar_Reflection_V2_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.b2t_qn
                                                                then
                                                                  (if
                                                                    FStar_Reflection_V2_Builtins.term_eq
                                                                    a
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    FStar_Reflection_V2_Data.C_False))
                                                                   then
                                                                    False_
                                                                   else
                                                                    if
                                                                    FStar_Reflection_V2_Builtins.term_eq
                                                                    a
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    FStar_Reflection_V2_Data.C_True))
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
                                                          | uu___4 ->
                                                              App
                                                                (h0,
                                                                  (FStar_Pervasives_Native.fst
                                                                    t1))))))
                                            uu___2))) uu___1)))
            | FStar_Tactics_NamedView.Tv_Const
                (FStar_Reflection_V2_Data.C_Int i) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> IntLit i)))
            | FStar_Tactics_NamedView.Tv_Let
                (uu___1, uu___2, uu___3, uu___4, uu___5) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___6 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_Match (uu___1, uu___2, uu___3) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___4 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_Type uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_Abs (uu___1, uu___2) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_Arrow (uu___1, uu___2) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_Uvar (uu___1, uu___2) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_Unknown ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_Unsupp ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_Refine (uu___1, uu___2) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_Const uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> F_Unknown)))
            | FStar_Tactics_NamedView.Tv_BVar uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> F_Unknown)))
            | uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.raise
                        (FStar_Tactics_Common.TacticFailure "???")))) uu___)
let _ =
  FStar_Tactics_Native.register_tactic
    "FStar.Reflection.V2.Formula.term_as_formula'" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_V2_InterpFuns.mk_tactic_interpretation_1
             (FStar_Tactics_Native.from_tactic_1 term_as_formula')
             FStar_Reflection_V2_Embeddings.e_term e_formula psc ncb args)
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
    let e = FStar_Reflection_V2_Data.Q_Explicit in
    let i = FStar_Reflection_V2_Data.Q_Implicit in
    match f with
    | True_ ->
        FStar_Tactics_NamedView.Tv_FVar
          (FStar_Reflection_V2_Builtins.pack_fv
             FStar_Reflection_Const.true_qn)
    | False_ ->
        FStar_Tactics_NamedView.Tv_FVar
          (FStar_Reflection_V2_Builtins.pack_fv
             FStar_Reflection_Const.false_qn)
    | Comp (Eq (FStar_Pervasives_Native.None), l, r) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.eq2_qn)) [(l, e); (r, e)]
    | Comp (Eq (FStar_Pervasives_Native.Some t), l, r) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.eq2_qn)) [(t, i); (l, e); (r, e)]
    | Comp (BoolEq (FStar_Pervasives_Native.None), l, r) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.eq1_qn)) [(l, e); (r, e)]
    | Comp (BoolEq (FStar_Pervasives_Native.Some t), l, r) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.eq1_qn)) [(t, i); (l, e); (r, e)]
    | Comp (Lt, l, r) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.lt_qn)) [(l, e); (r, e)]
    | Comp (Le, l, r) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.lte_qn)) [(l, e); (r, e)]
    | Comp (Gt, l, r) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.gt_qn)) [(l, e); (r, e)]
    | Comp (Ge, l, r) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.gte_qn)) [(l, e); (r, e)]
    | And (p, q) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.and_qn)) [(p, e); (q, e)]
    | Or (p, q) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.or_qn)) [(p, e); (q, e)]
    | Implies (p, q) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.imp_qn)) [(p, e); (q, e)]
    | Not p ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.not_qn)) [(p, e)]
    | Iff (p, q) ->
        mk_app'
          (FStar_Tactics_NamedView.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.iff_qn)) [(p, e); (q, e)]
    | Forall (b, sort, t) -> FStar_Tactics_NamedView.Tv_Unknown
    | Exists (b, sort, t) -> FStar_Tactics_NamedView.Tv_Unknown
    | App (p, q) ->
        FStar_Tactics_NamedView.Tv_App
          (p, (q, FStar_Reflection_V2_Data.Q_Explicit))
    | Name b -> FStar_Tactics_NamedView.Tv_Var b
    | FV fv -> FStar_Tactics_NamedView.Tv_FVar fv
    | IntLit i1 ->
        FStar_Tactics_NamedView.Tv_Const (FStar_Reflection_V2_Data.C_Int i1)
    | F_Unknown -> FStar_Tactics_NamedView.Tv_Unknown
let (formula_as_term : formula -> FStar_Tactics_NamedView.term) =
  fun f -> FStar_Tactics_NamedView.pack (formula_as_term_view f)
let (namedv_to_string :
  FStar_Tactics_NamedView.namedv ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun namedv ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Reflection.V2.Formula.fst"
               (Prims.of_int (219)) (Prims.of_int (18)) (Prims.of_int (219))
               (Prims.of_int (39)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Reflection.V2.Formula.fst"
               (Prims.of_int (220)) (Prims.of_int (4)) (Prims.of_int (220))
               (Prims.of_int (25)))))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ -> FStar_Tactics_NamedView.inspect_namedv namedv))
      (fun uu___ ->
         (fun namedvv ->
            Obj.magic
              (FStar_Tactics_Unseal.unseal
                 namedvv.FStar_Reflection_V2_Data.ppname)) uu___)
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
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (227)) (Prims.of_int (24))
                            (Prims.of_int (230)) (Prims.of_int (80)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (227)) (Prims.of_int (24))
                                  (Prims.of_int (229)) (Prims.of_int (67)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (227)) (Prims.of_int (24))
                                  (Prims.of_int (230)) (Prims.of_int (80)))))
                         (match mt with
                          | FStar_Pervasives_Native.None ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___ -> "")))
                          | FStar_Pervasives_Native.Some t ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Reflection.V2.Formula.fst"
                                               (Prims.of_int (229))
                                               (Prims.of_int (44))
                                               (Prims.of_int (229))
                                               (Prims.of_int (66)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range "prims.fst"
                                               (Prims.of_int (590))
                                               (Prims.of_int (19))
                                               (Prims.of_int (590))
                                               (Prims.of_int (31)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Reflection.V2.Formula.fst"
                                                     (Prims.of_int (229))
                                                     (Prims.of_int (44))
                                                     (Prims.of_int (229))
                                                     (Prims.of_int (60)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "prims.fst"
                                                     (Prims.of_int (590))
                                                     (Prims.of_int (19))
                                                     (Prims.of_int (590))
                                                     (Prims.of_int (31)))))
                                            (Obj.magic
                                               (FStar_Tactics_V2_Builtins.term_to_string
                                                  t))
                                            (fun uu___ ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___1 ->
                                                    Prims.strcat uu___ ")"))))
                                      (fun uu___ ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              Prims.strcat " (" uu___)))))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Reflection.V2.Formula.fst"
                                             (Prims.of_int (230))
                                             (Prims.of_int (24))
                                             (Prims.of_int (230))
                                             (Prims.of_int (80)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Reflection.V2.Formula.fst"
                                                   (Prims.of_int (230))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (230))
                                                   (Prims.of_int (80)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "prims.fst"
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (31)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Reflection.V2.Formula.fst"
                                                         (Prims.of_int (230))
                                                         (Prims.of_int (31))
                                                         (Prims.of_int (230))
                                                         (Prims.of_int (47)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Reflection.V2.Formula.fst"
                                                         (Prims.of_int (230))
                                                         (Prims.of_int (31))
                                                         (Prims.of_int (230))
                                                         (Prims.of_int (80)))))
                                                (Obj.magic
                                                   (FStar_Tactics_V2_Builtins.term_to_string
                                                      l))
                                                (fun uu___1 ->
                                                   (fun uu___1 ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Reflection.V2.Formula.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (80)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                           (Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Reflection.V2.Formula.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (80)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Reflection.V2.Formula.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    r))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    uu___2
                                                                    ")"))))
                                                                 (fun uu___2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    ") ("
                                                                    uu___2))))
                                                           (fun uu___2 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___3
                                                                   ->
                                                                   Prims.strcat
                                                                    uu___1
                                                                    uu___2))))
                                                     uu___1)))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat " (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Eq" uu___))))
       | Comp (BoolEq mt, l, r) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (232)) (Prims.of_int (24))
                            (Prims.of_int (235)) (Prims.of_int (80)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (232)) (Prims.of_int (24))
                                  (Prims.of_int (234)) (Prims.of_int (67)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (232)) (Prims.of_int (24))
                                  (Prims.of_int (235)) (Prims.of_int (80)))))
                         (match mt with
                          | FStar_Pervasives_Native.None ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___ -> "")))
                          | FStar_Pervasives_Native.Some t ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Reflection.V2.Formula.fst"
                                               (Prims.of_int (234))
                                               (Prims.of_int (44))
                                               (Prims.of_int (234))
                                               (Prims.of_int (66)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range "prims.fst"
                                               (Prims.of_int (590))
                                               (Prims.of_int (19))
                                               (Prims.of_int (590))
                                               (Prims.of_int (31)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Reflection.V2.Formula.fst"
                                                     (Prims.of_int (234))
                                                     (Prims.of_int (44))
                                                     (Prims.of_int (234))
                                                     (Prims.of_int (60)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "prims.fst"
                                                     (Prims.of_int (590))
                                                     (Prims.of_int (19))
                                                     (Prims.of_int (590))
                                                     (Prims.of_int (31)))))
                                            (Obj.magic
                                               (FStar_Tactics_V2_Builtins.term_to_string
                                                  t))
                                            (fun uu___ ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___1 ->
                                                    Prims.strcat uu___ ")"))))
                                      (fun uu___ ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              Prims.strcat " (" uu___)))))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Reflection.V2.Formula.fst"
                                             (Prims.of_int (235))
                                             (Prims.of_int (24))
                                             (Prims.of_int (235))
                                             (Prims.of_int (80)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Reflection.V2.Formula.fst"
                                                   (Prims.of_int (235))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (235))
                                                   (Prims.of_int (80)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "prims.fst"
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (31)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Reflection.V2.Formula.fst"
                                                         (Prims.of_int (235))
                                                         (Prims.of_int (31))
                                                         (Prims.of_int (235))
                                                         (Prims.of_int (47)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Reflection.V2.Formula.fst"
                                                         (Prims.of_int (235))
                                                         (Prims.of_int (31))
                                                         (Prims.of_int (235))
                                                         (Prims.of_int (80)))))
                                                (Obj.magic
                                                   (FStar_Tactics_V2_Builtins.term_to_string
                                                      l))
                                                (fun uu___1 ->
                                                   (fun uu___1 ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Reflection.V2.Formula.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (80)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                           (Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Reflection.V2.Formula.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (80)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Reflection.V2.Formula.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    r))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    uu___2
                                                                    ")"))))
                                                                 (fun uu___2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    ") ("
                                                                    uu___2))))
                                                           (fun uu___2 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___3
                                                                   ->
                                                                   Prims.strcat
                                                                    uu___1
                                                                    uu___2))))
                                                     uu___1)))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat " (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "BoolEq" uu___))))
       | Comp (Lt, l, r) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (236)) (Prims.of_int (30))
                            (Prims.of_int (236)) (Prims.of_int (79)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (236)) (Prims.of_int (30))
                                  (Prims.of_int (236)) (Prims.of_int (46)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (236)) (Prims.of_int (30))
                                  (Prims.of_int (236)) (Prims.of_int (79)))))
                         (Obj.magic
                            (FStar_Tactics_V2_Builtins.term_to_string l))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Reflection.V2.Formula.fst"
                                             (Prims.of_int (236))
                                             (Prims.of_int (49))
                                             (Prims.of_int (236))
                                             (Prims.of_int (79)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Reflection.V2.Formula.fst"
                                                   (Prims.of_int (236))
                                                   (Prims.of_int (57))
                                                   (Prims.of_int (236))
                                                   (Prims.of_int (79)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "prims.fst"
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (31)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Reflection.V2.Formula.fst"
                                                         (Prims.of_int (236))
                                                         (Prims.of_int (57))
                                                         (Prims.of_int (236))
                                                         (Prims.of_int (73)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "prims.fst"
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (31)))))
                                                (Obj.magic
                                                   (FStar_Tactics_V2_Builtins.term_to_string
                                                      r))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat uu___1
                                                          ")"))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat ") (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Lt (" uu___))))
       | Comp (Le, l, r) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (237)) (Prims.of_int (30))
                            (Prims.of_int (237)) (Prims.of_int (79)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (237)) (Prims.of_int (30))
                                  (Prims.of_int (237)) (Prims.of_int (46)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (237)) (Prims.of_int (30))
                                  (Prims.of_int (237)) (Prims.of_int (79)))))
                         (Obj.magic
                            (FStar_Tactics_V2_Builtins.term_to_string l))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Reflection.V2.Formula.fst"
                                             (Prims.of_int (237))
                                             (Prims.of_int (49))
                                             (Prims.of_int (237))
                                             (Prims.of_int (79)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Reflection.V2.Formula.fst"
                                                   (Prims.of_int (237))
                                                   (Prims.of_int (57))
                                                   (Prims.of_int (237))
                                                   (Prims.of_int (79)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "prims.fst"
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (31)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Reflection.V2.Formula.fst"
                                                         (Prims.of_int (237))
                                                         (Prims.of_int (57))
                                                         (Prims.of_int (237))
                                                         (Prims.of_int (73)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "prims.fst"
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (31)))))
                                                (Obj.magic
                                                   (FStar_Tactics_V2_Builtins.term_to_string
                                                      r))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat uu___1
                                                          ")"))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat ") (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Le (" uu___))))
       | Comp (Gt, l, r) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (238)) (Prims.of_int (30))
                            (Prims.of_int (238)) (Prims.of_int (79)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (238)) (Prims.of_int (30))
                                  (Prims.of_int (238)) (Prims.of_int (46)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (238)) (Prims.of_int (30))
                                  (Prims.of_int (238)) (Prims.of_int (79)))))
                         (Obj.magic
                            (FStar_Tactics_V2_Builtins.term_to_string l))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Reflection.V2.Formula.fst"
                                             (Prims.of_int (238))
                                             (Prims.of_int (49))
                                             (Prims.of_int (238))
                                             (Prims.of_int (79)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Reflection.V2.Formula.fst"
                                                   (Prims.of_int (238))
                                                   (Prims.of_int (57))
                                                   (Prims.of_int (238))
                                                   (Prims.of_int (79)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "prims.fst"
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (31)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Reflection.V2.Formula.fst"
                                                         (Prims.of_int (238))
                                                         (Prims.of_int (57))
                                                         (Prims.of_int (238))
                                                         (Prims.of_int (73)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "prims.fst"
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (31)))))
                                                (Obj.magic
                                                   (FStar_Tactics_V2_Builtins.term_to_string
                                                      r))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat uu___1
                                                          ")"))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat ") (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Gt (" uu___))))
       | Comp (Ge, l, r) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (239)) (Prims.of_int (30))
                            (Prims.of_int (239)) (Prims.of_int (79)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
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
                         (Obj.magic
                            (FStar_Tactics_V2_Builtins.term_to_string l))
                         (fun uu___ ->
                            (fun uu___ ->
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
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
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
                                                (FStar_Range.mk_range
                                                   "prims.fst"
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (31)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
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
                                                      (FStar_Range.mk_range
                                                         "prims.fst"
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (31)))))
                                                (Obj.magic
                                                   (FStar_Tactics_V2_Builtins.term_to_string
                                                      r))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat uu___1
                                                          ")"))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat ") (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Ge (" uu___))))
       | And (p, q) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (240)) (Prims.of_int (27))
                            (Prims.of_int (240)) (Prims.of_int (76)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (240)) (Prims.of_int (27))
                                  (Prims.of_int (240)) (Prims.of_int (43)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (240)) (Prims.of_int (27))
                                  (Prims.of_int (240)) (Prims.of_int (76)))))
                         (Obj.magic
                            (FStar_Tactics_V2_Builtins.term_to_string p))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Reflection.V2.Formula.fst"
                                             (Prims.of_int (240))
                                             (Prims.of_int (46))
                                             (Prims.of_int (240))
                                             (Prims.of_int (76)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Reflection.V2.Formula.fst"
                                                   (Prims.of_int (240))
                                                   (Prims.of_int (54))
                                                   (Prims.of_int (240))
                                                   (Prims.of_int (76)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "prims.fst"
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (31)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Reflection.V2.Formula.fst"
                                                         (Prims.of_int (240))
                                                         (Prims.of_int (54))
                                                         (Prims.of_int (240))
                                                         (Prims.of_int (70)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "prims.fst"
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (31)))))
                                                (Obj.magic
                                                   (FStar_Tactics_V2_Builtins.term_to_string
                                                      q))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat uu___1
                                                          ")"))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat ") (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "And (" uu___))))
       | Or (p, q) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (241)) (Prims.of_int (27))
                            (Prims.of_int (241)) (Prims.of_int (76)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (241)) (Prims.of_int (27))
                                  (Prims.of_int (241)) (Prims.of_int (43)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (241)) (Prims.of_int (27))
                                  (Prims.of_int (241)) (Prims.of_int (76)))))
                         (Obj.magic
                            (FStar_Tactics_V2_Builtins.term_to_string p))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Reflection.V2.Formula.fst"
                                             (Prims.of_int (241))
                                             (Prims.of_int (46))
                                             (Prims.of_int (241))
                                             (Prims.of_int (76)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Reflection.V2.Formula.fst"
                                                   (Prims.of_int (241))
                                                   (Prims.of_int (54))
                                                   (Prims.of_int (241))
                                                   (Prims.of_int (76)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "prims.fst"
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (31)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Reflection.V2.Formula.fst"
                                                         (Prims.of_int (241))
                                                         (Prims.of_int (54))
                                                         (Prims.of_int (241))
                                                         (Prims.of_int (70)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "prims.fst"
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (31)))))
                                                (Obj.magic
                                                   (FStar_Tactics_V2_Builtins.term_to_string
                                                      q))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat uu___1
                                                          ")"))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat ") (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Or (" uu___))))
       | Implies (p, q) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (242)) (Prims.of_int (36))
                            (Prims.of_int (242)) (Prims.of_int (85)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (242)) (Prims.of_int (36))
                                  (Prims.of_int (242)) (Prims.of_int (52)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (242)) (Prims.of_int (36))
                                  (Prims.of_int (242)) (Prims.of_int (85)))))
                         (Obj.magic
                            (FStar_Tactics_V2_Builtins.term_to_string p))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Reflection.V2.Formula.fst"
                                             (Prims.of_int (242))
                                             (Prims.of_int (55))
                                             (Prims.of_int (242))
                                             (Prims.of_int (85)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Reflection.V2.Formula.fst"
                                                   (Prims.of_int (242))
                                                   (Prims.of_int (63))
                                                   (Prims.of_int (242))
                                                   (Prims.of_int (85)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "prims.fst"
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (31)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Reflection.V2.Formula.fst"
                                                         (Prims.of_int (242))
                                                         (Prims.of_int (63))
                                                         (Prims.of_int (242))
                                                         (Prims.of_int (79)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "prims.fst"
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (31)))))
                                                (Obj.magic
                                                   (FStar_Tactics_V2_Builtins.term_to_string
                                                      q))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat uu___1
                                                          ")"))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat ") (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Implies (" uu___))))
       | Not p ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (243)) (Prims.of_int (26))
                            (Prims.of_int (243)) (Prims.of_int (48)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (243)) (Prims.of_int (26))
                                  (Prims.of_int (243)) (Prims.of_int (42)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "prims.fst"
                                  (Prims.of_int (590)) (Prims.of_int (19))
                                  (Prims.of_int (590)) (Prims.of_int (31)))))
                         (Obj.magic
                            (FStar_Tactics_V2_Builtins.term_to_string p))
                         (fun uu___ ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> Prims.strcat uu___ ")"))))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Not (" uu___))))
       | Iff (p, q) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (244)) (Prims.of_int (28))
                            (Prims.of_int (244)) (Prims.of_int (77)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (244)) (Prims.of_int (28))
                                  (Prims.of_int (244)) (Prims.of_int (44)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (244)) (Prims.of_int (28))
                                  (Prims.of_int (244)) (Prims.of_int (77)))))
                         (Obj.magic
                            (FStar_Tactics_V2_Builtins.term_to_string p))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Reflection.V2.Formula.fst"
                                             (Prims.of_int (244))
                                             (Prims.of_int (47))
                                             (Prims.of_int (244))
                                             (Prims.of_int (77)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Reflection.V2.Formula.fst"
                                                   (Prims.of_int (244))
                                                   (Prims.of_int (55))
                                                   (Prims.of_int (244))
                                                   (Prims.of_int (77)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "prims.fst"
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (31)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Reflection.V2.Formula.fst"
                                                         (Prims.of_int (244))
                                                         (Prims.of_int (55))
                                                         (Prims.of_int (244))
                                                         (Prims.of_int (71)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "prims.fst"
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (31)))))
                                                (Obj.magic
                                                   (FStar_Tactics_V2_Builtins.term_to_string
                                                      q))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat uu___1
                                                          ")"))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat ") (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Iff (" uu___))))
       | Forall (bs, _sort, t) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (245)) (Prims.of_int (45))
                            (Prims.of_int (245)) (Prims.of_int (67)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (245)) (Prims.of_int (45))
                                  (Prims.of_int (245)) (Prims.of_int (61)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "prims.fst"
                                  (Prims.of_int (590)) (Prims.of_int (19))
                                  (Prims.of_int (590)) (Prims.of_int (31)))))
                         (Obj.magic
                            (FStar_Tactics_V2_Builtins.term_to_string t))
                         (fun uu___ ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> Prims.strcat uu___ ")"))))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Forall <bs> (" uu___))))
       | Exists (bs, _sort, t) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (246)) (Prims.of_int (45))
                            (Prims.of_int (246)) (Prims.of_int (67)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (246)) (Prims.of_int (45))
                                  (Prims.of_int (246)) (Prims.of_int (61)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "prims.fst"
                                  (Prims.of_int (590)) (Prims.of_int (19))
                                  (Prims.of_int (590)) (Prims.of_int (31)))))
                         (Obj.magic
                            (FStar_Tactics_V2_Builtins.term_to_string t))
                         (fun uu___ ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> Prims.strcat uu___ ")"))))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Exists <bs> (" uu___))))
       | App (p, q) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (247)) (Prims.of_int (28))
                            (Prims.of_int (247)) (Prims.of_int (77)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
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
                         (Obj.magic
                            (FStar_Tactics_V2_Builtins.term_to_string p))
                         (fun uu___ ->
                            (fun uu___ ->
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
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
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
                                                (FStar_Range.mk_range
                                                   "prims.fst"
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (31)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
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
                                                      (FStar_Range.mk_range
                                                         "prims.fst"
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (31)))))
                                                (Obj.magic
                                                   (FStar_Tactics_V2_Builtins.term_to_string
                                                      q))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat uu___1
                                                          ")"))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat ") (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "App (" uu___))))
       | Name bv ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Reflection.V2.Formula.fst"
                            (Prims.of_int (248)) (Prims.of_int (29))
                            (Prims.of_int (248)) (Prims.of_int (54)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Reflection.V2.Formula.fst"
                                  (Prims.of_int (248)) (Prims.of_int (29))
                                  (Prims.of_int (248)) (Prims.of_int (48)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "prims.fst"
                                  (Prims.of_int (590)) (Prims.of_int (19))
                                  (Prims.of_int (590)) (Prims.of_int (31)))))
                         (Obj.magic (namedv_to_string bv))
                         (fun uu___ ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> Prims.strcat uu___ ")"))))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Name (" uu___))))
       | FV fv ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Prims.strcat "FV ("
                        (Prims.strcat
                           (FStar_Reflection_V2_Derived.flatten_name
                              (FStar_Reflection_V2_Builtins.inspect_fv fv))
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