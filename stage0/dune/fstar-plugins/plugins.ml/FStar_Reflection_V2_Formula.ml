open Fstarcompiler
open Prims
let term_eq :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term -> Prims.bool=
  FStar_Reflection_TermEq_Simple.term_eq
let rec inspect_unascribe (t : FStar_Tactics_NamedView.term) :
  (FStar_Tactics_NamedView.term_view, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_NamedView.inspect t ps in
    match x with
    | FStar_Tactics_NamedView.Tv_AscribedT (t1, uu___, uu___1, uu___2) ->
        inspect_unascribe t1 ps
    | FStar_Tactics_NamedView.Tv_AscribedC (t1, uu___, uu___1, uu___2) ->
        inspect_unascribe t1 ps
    | tv -> tv
let rec collect_app' (args : FStarC_Reflection_V2_Data.argv Prims.list)
  (t : FStar_Tactics_NamedView.term) :
  ((FStar_Tactics_NamedView.term * FStarC_Reflection_V2_Data.argv Prims.list),
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = inspect_unascribe t ps in
    match x with
    | FStar_Tactics_NamedView.Tv_App (l, r) -> collect_app' (r :: args) l ps
    | uu___ -> (t, args)
let collect_app :
  FStar_Tactics_NamedView.term ->
    ((FStar_Tactics_NamedView.term * FStarC_Reflection_V2_Data.argv
       Prims.list),
      unit) FStar_Tactics_Effect.tac_repr=
  collect_app' []
type comparison =
  | Eq of FStarC_Reflection_Types.typ FStar_Pervasives_Native.option 
  | BoolEq of FStarC_Reflection_Types.typ FStar_Pervasives_Native.option 
  | Lt 
  | Le 
  | Gt 
  | Ge 
let rec __knot_e_comparison _ =
  Fstarcompiler.FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Reflection.V2.Formula.comparison"
    (fun tm_0 ->
       match tm_0 with
       | ("FStar.Reflection.V2.Formula.Eq", _0_2::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                (Fstarcompiler.FStarC_Syntax_Embeddings.e_option
                   Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term) _0_2)
             (fun _0_2 -> FStar_Pervasives_Native.Some (Eq _0_2))
       | ("FStar.Reflection.V2.Formula.BoolEq", _0_4::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                (Fstarcompiler.FStarC_Syntax_Embeddings.e_option
                   Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term) _0_4)
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
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.Eq"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  (Fstarcompiler.FStarC_Syntax_Embeddings.e_option
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
                  _0_11), FStar_Pervasives_Native.None)]
       | BoolEq _0_13 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.BoolEq"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  (Fstarcompiler.FStarC_Syntax_Embeddings.e_option
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
                  _0_13), FStar_Pervasives_Native.None)]
       | Lt ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.Lt")) []
       | Le ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.Le")) []
       | Gt ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.Gt")) []
       | Ge ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.Ge")) [])
let e_comparison = __knot_e_comparison ()
let uu___is_Eq (projectee : comparison) : Prims.bool=
  match projectee with | Eq _0 -> true | uu___ -> false
let __proj__Eq__item___0 (projectee : comparison) :
  FStarC_Reflection_Types.typ FStar_Pervasives_Native.option=
  match projectee with | Eq _0 -> _0
let uu___is_BoolEq (projectee : comparison) : Prims.bool=
  match projectee with | BoolEq _0 -> true | uu___ -> false
let __proj__BoolEq__item___0 (projectee : comparison) :
  FStarC_Reflection_Types.typ FStar_Pervasives_Native.option=
  match projectee with | BoolEq _0 -> _0
let uu___is_Lt (projectee : comparison) : Prims.bool=
  match projectee with | Lt -> true | uu___ -> false
let uu___is_Le (projectee : comparison) : Prims.bool=
  match projectee with | Le -> true | uu___ -> false
let uu___is_Gt (projectee : comparison) : Prims.bool=
  match projectee with | Gt -> true | uu___ -> false
let uu___is_Ge (projectee : comparison) : Prims.bool=
  match projectee with | Ge -> true | uu___ -> false
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
  Fstarcompiler.FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Reflection.V2.Formula.formula"
    (fun tm_18 ->
       match tm_18 with
       | ("FStar.Reflection.V2.Formula.True_", []) ->
           FStar_Pervasives_Native.Some True_
       | ("FStar.Reflection.V2.Formula.False_", []) ->
           FStar_Pervasives_Native.Some False_
       | ("FStar.Reflection.V2.Formula.Comp", _0_22::_1_23::_2_24::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                e_comparison _0_22)
             (fun _0_22 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                     _1_23)
                  (fun _1_23 ->
                     Fstarcompiler.FStarC_Option.bind
                       (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                          Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                          _2_24)
                       (fun _2_24 ->
                          FStar_Pervasives_Native.Some
                            (Comp (_0_22, _1_23, _2_24)))))
       | ("FStar.Reflection.V2.Formula.And", _0_26::_1_27::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _0_26)
             (fun _0_26 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                     _1_27)
                  (fun _1_27 ->
                     FStar_Pervasives_Native.Some (And (_0_26, _1_27))))
       | ("FStar.Reflection.V2.Formula.Or", _0_29::_1_30::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _0_29)
             (fun _0_29 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                     _1_30)
                  (fun _1_30 ->
                     FStar_Pervasives_Native.Some (Or (_0_29, _1_30))))
       | ("FStar.Reflection.V2.Formula.Not", _0_32::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _0_32)
             (fun _0_32 -> FStar_Pervasives_Native.Some (Not _0_32))
       | ("FStar.Reflection.V2.Formula.Implies", _0_34::_1_35::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _0_34)
             (fun _0_34 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                     _1_35)
                  (fun _1_35 ->
                     FStar_Pervasives_Native.Some (Implies (_0_34, _1_35))))
       | ("FStar.Reflection.V2.Formula.Iff", _0_37::_1_38::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _0_37)
             (fun _0_37 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                     _1_38)
                  (fun _1_38 ->
                     FStar_Pervasives_Native.Some (Iff (_0_37, _1_38))))
       | ("FStar.Reflection.V2.Formula.Forall", _0_40::_1_41::_2_42::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_bv_view _0_40)
             (fun _0_40 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                     _1_41)
                  (fun _1_41 ->
                     Fstarcompiler.FStarC_Option.bind
                       (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                          Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                          _2_42)
                       (fun _2_42 ->
                          FStar_Pervasives_Native.Some
                            (Forall (_0_40, _1_41, _2_42)))))
       | ("FStar.Reflection.V2.Formula.Exists", _0_44::_1_45::_2_46::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_bv_view _0_44)
             (fun _0_44 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                     _1_45)
                  (fun _1_45 ->
                     Fstarcompiler.FStarC_Option.bind
                       (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                          Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                          _2_46)
                       (fun _2_46 ->
                          FStar_Pervasives_Native.Some
                            (Exists (_0_44, _1_45, _2_46)))))
       | ("FStar.Reflection.V2.Formula.App", _0_48::_1_49::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _0_48)
             (fun _0_48 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                     _1_49)
                  (fun _1_49 ->
                     FStar_Pervasives_Native.Some (App (_0_48, _1_49))))
       | ("FStar.Reflection.V2.Formula.Name", _0_51::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_namedv_view
                _0_51)
             (fun _0_51 -> FStar_Pervasives_Native.Some (Name _0_51))
       | ("FStar.Reflection.V2.Formula.FV", _0_53::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_fv _0_53)
             (fun _0_53 -> FStar_Pervasives_Native.Some (FV _0_53))
       | ("FStar.Reflection.V2.Formula.IntLit", _0_55::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Syntax_Embeddings.e_int _0_55)
             (fun _0_55 -> FStar_Pervasives_Native.Some (IntLit _0_55))
       | ("FStar.Reflection.V2.Formula.F_Unknown", []) ->
           FStar_Pervasives_Native.Some F_Unknown
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_57 ->
       match tm_57 with
       | True_ ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.True_")) []
       | False_ ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.False_")) []
       | Comp (_0_61, _1_62, _2_63) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.Comp"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  e_comparison _0_61), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _1_62),
               FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _2_63),
               FStar_Pervasives_Native.None)]
       | And (_0_65, _1_66) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.And"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _0_65),
                FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _1_66),
               FStar_Pervasives_Native.None)]
       | Or (_0_68, _1_69) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.Or"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _0_68),
                FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _1_69),
               FStar_Pervasives_Native.None)]
       | Not _0_71 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.Not"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _0_71),
                FStar_Pervasives_Native.None)]
       | Implies (_0_73, _1_74) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.Implies"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _0_73),
                FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _1_74),
               FStar_Pervasives_Native.None)]
       | Iff (_0_76, _1_77) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.Iff"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _0_76),
                FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _1_77),
               FStar_Pervasives_Native.None)]
       | Forall (_0_79, _1_80, _2_81) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.Forall"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_bv_view
                  _0_79), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _1_80),
               FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _2_81),
               FStar_Pervasives_Native.None)]
       | Exists (_0_83, _1_84, _2_85) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.Exists"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_bv_view
                  _0_83), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _1_84),
               FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _2_85),
               FStar_Pervasives_Native.None)]
       | App (_0_87, _1_88) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.App"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _0_87),
                FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _1_88),
               FStar_Pervasives_Native.None)]
       | Name _0_90 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.Name"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_namedv_view
                  _0_90), FStar_Pervasives_Native.None)]
       | FV _0_92 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.FV"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_fv _0_92),
                FStar_Pervasives_Native.None)]
       | IntLit _0_94 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.IntLit"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Syntax_Embeddings.e_int _0_94),
                FStar_Pervasives_Native.None)]
       | F_Unknown ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Reflection.V2.Formula.F_Unknown")) [])
let e_formula = __knot_e_formula ()
let uu___is_True_ (projectee : formula) : Prims.bool=
  match projectee with | True_ -> true | uu___ -> false
let uu___is_False_ (projectee : formula) : Prims.bool=
  match projectee with | False_ -> true | uu___ -> false
let uu___is_Comp (projectee : formula) : Prims.bool=
  match projectee with | Comp (_0, _1, _2) -> true | uu___ -> false
let __proj__Comp__item___0 (projectee : formula) : comparison=
  match projectee with | Comp (_0, _1, _2) -> _0
let __proj__Comp__item___1 (projectee : formula) :
  FStar_Tactics_NamedView.term=
  match projectee with | Comp (_0, _1, _2) -> _1
let __proj__Comp__item___2 (projectee : formula) :
  FStar_Tactics_NamedView.term=
  match projectee with | Comp (_0, _1, _2) -> _2
let uu___is_And (projectee : formula) : Prims.bool=
  match projectee with | And (_0, _1) -> true | uu___ -> false
let __proj__And__item___0 (projectee : formula) :
  FStar_Tactics_NamedView.term= match projectee with | And (_0, _1) -> _0
let __proj__And__item___1 (projectee : formula) :
  FStar_Tactics_NamedView.term= match projectee with | And (_0, _1) -> _1
let uu___is_Or (projectee : formula) : Prims.bool=
  match projectee with | Or (_0, _1) -> true | uu___ -> false
let __proj__Or__item___0 (projectee : formula) :
  FStar_Tactics_NamedView.term= match projectee with | Or (_0, _1) -> _0
let __proj__Or__item___1 (projectee : formula) :
  FStar_Tactics_NamedView.term= match projectee with | Or (_0, _1) -> _1
let uu___is_Not (projectee : formula) : Prims.bool=
  match projectee with | Not _0 -> true | uu___ -> false
let __proj__Not__item___0 (projectee : formula) :
  FStar_Tactics_NamedView.term= match projectee with | Not _0 -> _0
let uu___is_Implies (projectee : formula) : Prims.bool=
  match projectee with | Implies (_0, _1) -> true | uu___ -> false
let __proj__Implies__item___0 (projectee : formula) :
  FStar_Tactics_NamedView.term= match projectee with | Implies (_0, _1) -> _0
let __proj__Implies__item___1 (projectee : formula) :
  FStar_Tactics_NamedView.term= match projectee with | Implies (_0, _1) -> _1
let uu___is_Iff (projectee : formula) : Prims.bool=
  match projectee with | Iff (_0, _1) -> true | uu___ -> false
let __proj__Iff__item___0 (projectee : formula) :
  FStar_Tactics_NamedView.term= match projectee with | Iff (_0, _1) -> _0
let __proj__Iff__item___1 (projectee : formula) :
  FStar_Tactics_NamedView.term= match projectee with | Iff (_0, _1) -> _1
let uu___is_Forall (projectee : formula) : Prims.bool=
  match projectee with | Forall (_0, _1, _2) -> true | uu___ -> false
let __proj__Forall__item___0 (projectee : formula) :
  FStar_Tactics_NamedView.bv=
  match projectee with | Forall (_0, _1, _2) -> _0
let __proj__Forall__item___1 (projectee : formula) :
  FStarC_Reflection_Types.typ=
  match projectee with | Forall (_0, _1, _2) -> _1
let __proj__Forall__item___2 (projectee : formula) :
  FStar_Tactics_NamedView.term=
  match projectee with | Forall (_0, _1, _2) -> _2
let uu___is_Exists (projectee : formula) : Prims.bool=
  match projectee with | Exists (_0, _1, _2) -> true | uu___ -> false
let __proj__Exists__item___0 (projectee : formula) :
  FStar_Tactics_NamedView.bv=
  match projectee with | Exists (_0, _1, _2) -> _0
let __proj__Exists__item___1 (projectee : formula) :
  FStarC_Reflection_Types.typ=
  match projectee with | Exists (_0, _1, _2) -> _1
let __proj__Exists__item___2 (projectee : formula) :
  FStar_Tactics_NamedView.term=
  match projectee with | Exists (_0, _1, _2) -> _2
let uu___is_App (projectee : formula) : Prims.bool=
  match projectee with | App (_0, _1) -> true | uu___ -> false
let __proj__App__item___0 (projectee : formula) :
  FStar_Tactics_NamedView.term= match projectee with | App (_0, _1) -> _0
let __proj__App__item___1 (projectee : formula) :
  FStar_Tactics_NamedView.term= match projectee with | App (_0, _1) -> _1
let uu___is_Name (projectee : formula) : Prims.bool=
  match projectee with | Name _0 -> true | uu___ -> false
let __proj__Name__item___0 (projectee : formula) :
  FStar_Tactics_NamedView.namedv= match projectee with | Name _0 -> _0
let uu___is_FV (projectee : formula) : Prims.bool=
  match projectee with | FV _0 -> true | uu___ -> false
let __proj__FV__item___0 (projectee : formula) : FStarC_Reflection_Types.fv=
  match projectee with | FV _0 -> _0
let uu___is_IntLit (projectee : formula) : Prims.bool=
  match projectee with | IntLit _0 -> true | uu___ -> false
let __proj__IntLit__item___0 (projectee : formula) : Prims.int=
  match projectee with | IntLit _0 -> _0
let uu___is_F_Unknown (projectee : formula) : Prims.bool=
  match projectee with | F_Unknown -> true | uu___ -> false
let mk_Forall (typ : FStar_Tactics_NamedView.term)
  (pred : FStar_Tactics_NamedView.term) : formula=
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
let mk_Exists (typ : FStar_Tactics_NamedView.term)
  (pred : FStar_Tactics_NamedView.term) : formula=
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
let term_as_formula' (t : FStar_Tactics_NamedView.term) :
  (formula, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = inspect_unascribe t ps in
    match x with
    | FStar_Tactics_NamedView.Tv_Var n -> Obj.magic (Obj.repr (Name n))
    | FStar_Tactics_NamedView.Tv_FVar fv ->
        Obj.magic
          (Obj.repr
             (if
                (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                  FStar_Reflection_Const.true_qn
              then True_
              else
                if
                  (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                    FStar_Reflection_Const.false_qn
                then False_
                else FV fv))
    | FStar_Tactics_NamedView.Tv_UInst (fv, uu___) ->
        Obj.magic
          (Obj.repr
             (if
                (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                  FStar_Reflection_Const.true_qn
              then True_
              else
                if
                  (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                    FStar_Reflection_Const.false_qn
                then False_
                else FV fv))
    | FStar_Tactics_NamedView.Tv_App (h0, t1) ->
        Obj.magic
          (Obj.repr
             (let x1 = collect_app h0 ps in
              match x1 with
              | (h, ts) ->
                  let x2 = FStar_Reflection_V2_Derived.un_uinst h in
                  let x3 =
                    let x4 = FStar_Tactics_NamedView.inspect x2 ps in
                    (x4, (FStar_List_Tot_Base.op_At ts [t1])) in
                  (match x3 with
                   | (FStar_Tactics_NamedView.Tv_FVar fv,
                      (a1, FStarC_Reflection_V2_Data.Q_Implicit)::(a2,
                                                                   FStarC_Reflection_V2_Data.Q_Explicit)::
                      (a3, FStarC_Reflection_V2_Data.Q_Explicit)::[]) ->
                       if
                         (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                           FStar_Reflection_Const.eq2_qn
                       then
                         Comp
                           ((Eq (FStar_Pervasives_Native.Some a1)), a2, a3)
                       else
                         if
                           (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                             FStar_Reflection_Const.eq1_qn
                         then
                           Comp
                             ((BoolEq (FStar_Pervasives_Native.Some a1)), a2,
                               a3)
                         else
                           if
                             (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                               FStar_Reflection_Const.lt_qn
                           then Comp (Lt, a2, a3)
                           else
                             if
                               (FStarC_Reflection_V2_Builtins.inspect_fv fv)
                                 = FStar_Reflection_Const.lte_qn
                             then Comp (Le, a2, a3)
                             else
                               if
                                 (FStarC_Reflection_V2_Builtins.inspect_fv fv)
                                   = FStar_Reflection_Const.gt_qn
                               then Comp (Gt, a2, a3)
                               else
                                 if
                                   (FStarC_Reflection_V2_Builtins.inspect_fv
                                      fv)
                                     = FStar_Reflection_Const.gte_qn
                                 then Comp (Ge, a2, a3)
                                 else
                                   App (h0, (FStar_Pervasives_Native.fst t1))
                   | (FStar_Tactics_NamedView.Tv_FVar fv,
                      (a1, FStarC_Reflection_V2_Data.Q_Explicit)::(a2,
                                                                   FStarC_Reflection_V2_Data.Q_Explicit)::[])
                       ->
                       if
                         (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                           FStar_Reflection_Const.imp_qn
                       then Implies (a1, a2)
                       else
                         if
                           (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                             FStar_Reflection_Const.and_qn
                         then And (a1, a2)
                         else
                           if
                             (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                               FStar_Reflection_Const.iff_qn
                           then Iff (a1, a2)
                           else
                             if
                               (FStarC_Reflection_V2_Builtins.inspect_fv fv)
                                 = FStar_Reflection_Const.or_qn
                             then Or (a1, a2)
                             else
                               if
                                 (FStarC_Reflection_V2_Builtins.inspect_fv fv)
                                   = FStar_Reflection_Const.eq2_qn
                               then
                                 Comp
                                   ((Eq FStar_Pervasives_Native.None), a1,
                                     a2)
                               else
                                 if
                                   (FStarC_Reflection_V2_Builtins.inspect_fv
                                      fv)
                                     = FStar_Reflection_Const.eq1_qn
                                 then
                                   Comp
                                     ((BoolEq FStar_Pervasives_Native.None),
                                       a1, a2)
                                 else
                                   App (h0, (FStar_Pervasives_Native.fst t1))
                   | (FStar_Tactics_NamedView.Tv_FVar fv,
                      (a1, FStarC_Reflection_V2_Data.Q_Implicit)::(a2,
                                                                   FStarC_Reflection_V2_Data.Q_Explicit)::[])
                       ->
                       if
                         (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                           FStar_Reflection_Const.forall_qn
                       then mk_Forall a1 a2
                       else
                         if
                           (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                             FStar_Reflection_Const.exists_qn
                         then mk_Exists a1 a2
                         else App (h0, (FStar_Pervasives_Native.fst t1))
                   | (FStar_Tactics_NamedView.Tv_FVar fv,
                      (a, FStarC_Reflection_V2_Data.Q_Explicit)::[]) ->
                       if
                         (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                           FStar_Reflection_Const.not_qn
                       then Not a
                       else
                         if
                           (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                             FStar_Reflection_Const.b2t_qn
                         then
                           (if
                              term_eq a
                                (FStarC_Reflection_V2_Builtins.pack_ln
                                   (FStarC_Reflection_V2_Data.Tv_Const
                                      FStarC_Reflection_V2_Data.C_False))
                            then False_
                            else
                              if
                                term_eq a
                                  (FStarC_Reflection_V2_Builtins.pack_ln
                                     (FStarC_Reflection_V2_Data.Tv_Const
                                        FStarC_Reflection_V2_Data.C_True))
                              then True_
                              else App (h0, (FStar_Pervasives_Native.fst t1)))
                         else App (h0, (FStar_Pervasives_Native.fst t1))
                   | uu___ -> App (h0, (FStar_Pervasives_Native.fst t1)))))
    | FStar_Tactics_NamedView.Tv_Const (FStarC_Reflection_V2_Data.C_Int i) ->
        Obj.magic (Obj.repr (IntLit i))
    | FStar_Tactics_NamedView.Tv_Let (uu___, uu___1, uu___2, uu___3, uu___4)
        -> Obj.magic (Obj.repr F_Unknown)
    | FStar_Tactics_NamedView.Tv_Match (uu___, uu___1, uu___2) ->
        Obj.magic (Obj.repr F_Unknown)
    | FStar_Tactics_NamedView.Tv_Type uu___ -> Obj.magic (Obj.repr F_Unknown)
    | FStar_Tactics_NamedView.Tv_Abs (uu___, uu___1) ->
        Obj.magic (Obj.repr F_Unknown)
    | FStar_Tactics_NamedView.Tv_Arrow (uu___, uu___1) ->
        Obj.magic (Obj.repr F_Unknown)
    | FStar_Tactics_NamedView.Tv_Uvar (uu___, uu___1) ->
        Obj.magic (Obj.repr F_Unknown)
    | FStar_Tactics_NamedView.Tv_Unknown -> Obj.magic (Obj.repr F_Unknown)
    | FStar_Tactics_NamedView.Tv_Unsupp -> Obj.magic (Obj.repr F_Unknown)
    | FStar_Tactics_NamedView.Tv_Refine (uu___, uu___1) ->
        Obj.magic (Obj.repr F_Unknown)
    | FStar_Tactics_NamedView.Tv_Const uu___ ->
        Obj.magic (Obj.repr F_Unknown)
    | FStar_Tactics_NamedView.Tv_BVar uu___ -> Obj.magic (Obj.repr F_Unknown)
    | uu___ ->
        Obj.magic
          (Obj.repr
             (FStarC_Tactics_V2_Builtins.raise_core
                (FStarC_Tactics_Common.TacticFailure
                   ([FStar_Pprint.arbitrary_string
                       "Unexpected: term_as_formula"],
                     FStar_Pervasives_Native.None)) ps))
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Reflection.V2.Formula.term_as_formula'" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Reflection.V2.Formula.term_as_formula' (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  term_as_formula')
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term e_formula
               psc ncb us args)
let term_as_formula (uu___ : FStar_Tactics_NamedView.term) :
  (formula, unit) FStar_Tactics_Effect.tac_repr=
  (fun t ->
     match FStar_Reflection_V2_Derived.unsquash_term t with
     | FStar_Pervasives_Native.None ->
         Obj.magic (Obj.repr (fun uu___ -> F_Unknown))
     | FStar_Pervasives_Native.Some t1 ->
         Obj.magic (Obj.repr (term_as_formula' t1))) uu___
let term_as_formula_total (t : FStar_Tactics_NamedView.term) :
  (formula, unit) FStar_Tactics_Effect.tac_repr=
  term_as_formula' (FStar_Reflection_V2_Derived.maybe_unsquash_term t)
let formula_as_term_view (f : formula) : FStar_Tactics_NamedView.term_view=
  let mk_app' tv args =
    FStar_List_Tot_Base.fold_left
      (fun tv1 a ->
         FStar_Tactics_NamedView.Tv_App
           ((FStar_Tactics_NamedView.pack tv1), a)) tv args in
  let e = FStarC_Reflection_V2_Data.Q_Explicit in
  let i = FStarC_Reflection_V2_Data.Q_Implicit in
  match f with
  | True_ ->
      FStar_Tactics_NamedView.Tv_FVar
        (FStarC_Reflection_V2_Builtins.pack_fv FStar_Reflection_Const.true_qn)
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
let formula_as_term (f : formula) : FStar_Tactics_NamedView.term=
  FStar_Tactics_NamedView.pack (formula_as_term_view f)
let namedv_to_string (namedv : FStar_Tactics_NamedView.namedv) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_NamedView.inspect_namedv namedv in
    FStarC_Tactics_Unseal.unseal x.FStarC_Reflection_V2_Data.ppname ps
let formula_to_string (uu___ : formula) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  (fun f ->
     match f with
     | True_ -> Obj.magic (Obj.repr (fun uu___ -> "True_"))
     | False_ -> Obj.magic (Obj.repr (fun uu___ -> "False_"))
     | Comp (Eq mt, l, r) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
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
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (Obj.magic
                                             (FStarC_Tactics_V2_Builtins.term_to_string
                                                t))
                                          (fun uu___ uu___1 ->
                                             Prims.strcat uu___ ")")))
                                    (fun uu___ uu___1 ->
                                       Prims.strcat " (" uu___))))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V2_Builtins.term_to_string
                                          l ps in
                                      let x3 =
                                        let x4 =
                                          let x5 =
                                            FStarC_Tactics_V2_Builtins.term_to_string
                                              r ps in
                                          Prims.strcat x5 ")" in
                                        Prims.strcat ") (" x4 in
                                      Prims.strcat x2 x3 in
                                    Prims.strcat " (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "Eq" uu___)))
     | Comp (BoolEq mt, l, r) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
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
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (Obj.magic
                                             (FStarC_Tactics_V2_Builtins.term_to_string
                                                t))
                                          (fun uu___ uu___1 ->
                                             Prims.strcat uu___ ")")))
                                    (fun uu___ uu___1 ->
                                       Prims.strcat " (" uu___))))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V2_Builtins.term_to_string
                                          l ps in
                                      let x3 =
                                        let x4 =
                                          let x5 =
                                            FStarC_Tactics_V2_Builtins.term_to_string
                                              r ps in
                                          Prims.strcat x5 ")" in
                                        Prims.strcat ") (" x4 in
                                      Prims.strcat x2 x3 in
                                    Prims.strcat " (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "BoolEq" uu___)))
     | Comp (Lt, l, r) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V2_Builtins.term_to_string l))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V2_Builtins.term_to_string
                                          r ps in
                                      Prims.strcat x2 ")" in
                                    Prims.strcat ") (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "Lt (" uu___)))
     | Comp (Le, l, r) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V2_Builtins.term_to_string l))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V2_Builtins.term_to_string
                                          r ps in
                                      Prims.strcat x2 ")" in
                                    Prims.strcat ") (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "Le (" uu___)))
     | Comp (Gt, l, r) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V2_Builtins.term_to_string l))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V2_Builtins.term_to_string
                                          r ps in
                                      Prims.strcat x2 ")" in
                                    Prims.strcat ") (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "Gt (" uu___)))
     | Comp (Ge, l, r) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V2_Builtins.term_to_string l))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V2_Builtins.term_to_string
                                          r ps in
                                      Prims.strcat x2 ")" in
                                    Prims.strcat ") (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "Ge (" uu___)))
     | And (p, q) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V2_Builtins.term_to_string p))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V2_Builtins.term_to_string
                                          q ps in
                                      Prims.strcat x2 ")" in
                                    Prims.strcat ") (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "And (" uu___)))
     | Or (p, q) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V2_Builtins.term_to_string p))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V2_Builtins.term_to_string
                                          q ps in
                                      Prims.strcat x2 ")" in
                                    Prims.strcat ") (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "Or (" uu___)))
     | Implies (p, q) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V2_Builtins.term_to_string p))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V2_Builtins.term_to_string
                                          q ps in
                                      Prims.strcat x2 ")" in
                                    Prims.strcat ") (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "Implies (" uu___)))
     | Not p ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V2_Builtins.term_to_string p))
                       (fun uu___ uu___1 -> Prims.strcat uu___ ")")))
                 (fun uu___ uu___1 -> Prims.strcat "Not (" uu___)))
     | Iff (p, q) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V2_Builtins.term_to_string p))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V2_Builtins.term_to_string
                                          q ps in
                                      Prims.strcat x2 ")" in
                                    Prims.strcat ") (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "Iff (" uu___)))
     | Forall (bs, _sort, t) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V2_Builtins.term_to_string t))
                       (fun uu___ uu___1 -> Prims.strcat uu___ ")")))
                 (fun uu___ uu___1 -> Prims.strcat "Forall <bs> (" uu___)))
     | Exists (bs, _sort, t) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V2_Builtins.term_to_string t))
                       (fun uu___ uu___1 -> Prims.strcat uu___ ")")))
                 (fun uu___ uu___1 -> Prims.strcat "Exists <bs> (" uu___)))
     | App (p, q) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V2_Builtins.term_to_string p))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V2_Builtins.term_to_string
                                          q ps in
                                      Prims.strcat x2 ")" in
                                    Prims.strcat ") (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "App (" uu___)))
     | Name bv ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic (namedv_to_string bv))
                       (fun uu___ uu___1 -> Prims.strcat uu___ ")")))
                 (fun uu___ uu___1 -> Prims.strcat "Name (" uu___)))
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
     | F_Unknown -> Obj.magic (Obj.repr (fun uu___ -> "?"))) uu___
