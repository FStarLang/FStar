open Prims
type namedv = FStarC_Reflection_V2_Data.namedv_view
type bv = FStarC_Reflection_V2_Data.bv_view
type comp = FStarC_Reflection_V2_Data.comp_view
type binding = FStarC_Reflection_V2_Data.binding
type term = FStarC_Reflection_Types.term
type universe = FStarC_Reflection_Types.universe
type binder =
  {
  uniq: Prims.nat ;
  ppname: FStarC_Reflection_V2_Data.ppname_t ;
  sort: FStarC_Reflection_Types.typ ;
  qual: FStarC_Reflection_V2_Data.aqualv ;
  attrs: term Prims.list }
let rec __knot_e_binder _ =
  FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.binder"
    (fun tm_0 ->
       match tm_0 with
       | ("FStar.Tactics.NamedView.Mkbinder",
          uniq_2::ppname_3::sort_4::qual_5::attrs_6::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Syntax_Embeddings.e_int uniq_2)
             (fun uniq_2 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (FStarC_Syntax_Embeddings.e_sealed
                        FStarC_Syntax_Embeddings.e_string) ppname_3)
                  (fun ppname_3 ->
                     FStarC_Compiler_Util.bind_opt
                       (FStarC_Syntax_Embeddings_Base.extracted_unembed
                          FStarC_Reflection_V2_Embeddings.e_term sort_4)
                       (fun sort_4 ->
                          FStarC_Compiler_Util.bind_opt
                            (FStarC_Syntax_Embeddings_Base.extracted_unembed
                               FStarC_Reflection_V2_Embeddings.e_aqualv
                               qual_5)
                            (fun qual_5 ->
                               FStarC_Compiler_Util.bind_opt
                                 (FStarC_Syntax_Embeddings_Base.extracted_unembed
                                    (FStarC_Syntax_Embeddings.e_list
                                       FStarC_Reflection_V2_Embeddings.e_term)
                                    attrs_6)
                                 (fun attrs_6 ->
                                    FStar_Pervasives_Native.Some
                                      {
                                        uniq = uniq_2;
                                        ppname = ppname_3;
                                        sort = sort_4;
                                        qual = qual_5;
                                        attrs = attrs_6
                                      })))))
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_7 ->
       match tm_7 with
       | { uniq = uniq_9; ppname = ppname_10; sort = sort_11; qual = qual_12;
           attrs = attrs_13;_} ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Mkbinder"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Syntax_Embeddings.e_int uniq_9),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 (FStarC_Syntax_Embeddings.e_sealed
                    FStarC_Syntax_Embeddings.e_string) ppname_10),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term sort_11),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_aqualv qual_12),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 (FStarC_Syntax_Embeddings.e_list
                    FStarC_Reflection_V2_Embeddings.e_term) attrs_13),
               FStar_Pervasives_Native.None)])
let e_binder = __knot_e_binder ()
let (__proj__Mkbinder__item__uniq : binder -> Prims.nat) =
  fun projectee ->
    match projectee with | { uniq; ppname; sort; qual; attrs;_} -> uniq
let (__proj__Mkbinder__item__ppname :
  binder -> FStarC_Reflection_V2_Data.ppname_t) =
  fun projectee ->
    match projectee with | { uniq; ppname; sort; qual; attrs;_} -> ppname
let (__proj__Mkbinder__item__sort : binder -> FStarC_Reflection_Types.typ) =
  fun projectee ->
    match projectee with | { uniq; ppname; sort; qual; attrs;_} -> sort
let (__proj__Mkbinder__item__qual :
  binder -> FStarC_Reflection_V2_Data.aqualv) =
  fun projectee ->
    match projectee with | { uniq; ppname; sort; qual; attrs;_} -> qual
let (__proj__Mkbinder__item__attrs : binder -> term Prims.list) =
  fun projectee ->
    match projectee with | { uniq; ppname; sort; qual; attrs;_} -> attrs
type binders = binder Prims.list
type 'b is_simple_binder = unit
type simple_binder = binder
type univ_name = (Prims.string * FStar_Range.range)
type named_universe_view =
  | Uv_Zero 
  | Uv_Succ of universe 
  | Uv_Max of FStarC_Reflection_V2_Data.universes 
  | Uv_BVar of Prims.nat 
  | Uv_Name of univ_name 
  | Uv_Unif of FStarC_Reflection_Types.universe_uvar 
  | Uv_Unk 
let rec __knot_e_named_universe_view _ =
  FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.named_universe_view"
    (fun tm_14 ->
       match tm_14 with
       | ("FStar.Tactics.NamedView.Uv_Zero", []) ->
           FStar_Pervasives_Native.Some Uv_Zero
       | ("FStar.Tactics.NamedView.Uv_Succ", _0_17::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_universe _0_17)
             (fun _0_17 -> FStar_Pervasives_Native.Some (Uv_Succ _0_17))
       | ("FStar.Tactics.NamedView.Uv_Max", _0_19::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                (FStarC_Syntax_Embeddings.e_list
                   FStarC_Reflection_V2_Embeddings.e_universe) _0_19)
             (fun _0_19 -> FStar_Pervasives_Native.Some (Uv_Max _0_19))
       | ("FStar.Tactics.NamedView.Uv_BVar", _0_21::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Syntax_Embeddings.e_int _0_21)
             (fun _0_21 -> FStar_Pervasives_Native.Some (Uv_BVar _0_21))
       | ("FStar.Tactics.NamedView.Uv_Name", _0_23::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                (FStarC_Syntax_Embeddings.e_tuple2
                   FStarC_Syntax_Embeddings.e_string
                   (FStarC_Syntax_Embeddings.e_sealed
                      FStarC_Syntax_Embeddings.e___range)) _0_23)
             (fun _0_23 -> FStar_Pervasives_Native.Some (Uv_Name _0_23))
       | ("FStar.Tactics.NamedView.Uv_Unif", _0_25::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_universe_uvar _0_25)
             (fun _0_25 -> FStar_Pervasives_Native.Some (Uv_Unif _0_25))
       | ("FStar.Tactics.NamedView.Uv_Unk", []) ->
           FStar_Pervasives_Native.Some Uv_Unk
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_27 ->
       match tm_27 with
       | Uv_Zero ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Uv_Zero"))
             []
       | Uv_Succ _0_30 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Uv_Succ"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_universe _0_30),
                FStar_Pervasives_Native.None)]
       | Uv_Max _0_32 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Uv_Max"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  (FStarC_Syntax_Embeddings.e_list
                     FStarC_Reflection_V2_Embeddings.e_universe) _0_32),
                FStar_Pervasives_Native.None)]
       | Uv_BVar _0_34 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Uv_BVar"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Syntax_Embeddings.e_int _0_34),
                FStar_Pervasives_Native.None)]
       | Uv_Name _0_36 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Uv_Name"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  (FStarC_Syntax_Embeddings.e_tuple2
                     FStarC_Syntax_Embeddings.e_string
                     (FStarC_Syntax_Embeddings.e_sealed
                        FStarC_Syntax_Embeddings.e___range)) _0_36),
                FStar_Pervasives_Native.None)]
       | Uv_Unif _0_38 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Uv_Unif"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_universe_uvar _0_38),
                FStar_Pervasives_Native.None)]
       | Uv_Unk ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Uv_Unk"))
             [])
let e_named_universe_view = __knot_e_named_universe_view ()
let (uu___is_Uv_Zero : named_universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_Zero -> true | uu___ -> false
let (uu___is_Uv_Succ : named_universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_Succ _0 -> true | uu___ -> false
let (__proj__Uv_Succ__item___0 : named_universe_view -> universe) =
  fun projectee -> match projectee with | Uv_Succ _0 -> _0
let (uu___is_Uv_Max : named_universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_Max _0 -> true | uu___ -> false
let (__proj__Uv_Max__item___0 :
  named_universe_view -> FStarC_Reflection_V2_Data.universes) =
  fun projectee -> match projectee with | Uv_Max _0 -> _0
let (uu___is_Uv_BVar : named_universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_BVar _0 -> true | uu___ -> false
let (__proj__Uv_BVar__item___0 : named_universe_view -> Prims.nat) =
  fun projectee -> match projectee with | Uv_BVar _0 -> _0
let (uu___is_Uv_Name : named_universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_Name _0 -> true | uu___ -> false
let (__proj__Uv_Name__item___0 : named_universe_view -> univ_name) =
  fun projectee -> match projectee with | Uv_Name _0 -> _0
let (uu___is_Uv_Unif : named_universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_Unif _0 -> true | uu___ -> false
let (__proj__Uv_Unif__item___0 :
  named_universe_view -> FStarC_Reflection_Types.universe_uvar) =
  fun projectee -> match projectee with | Uv_Unif _0 -> _0
let (uu___is_Uv_Unk : named_universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_Unk -> true | uu___ -> false
type pattern__Pat_Constant__payload = {
  c: FStarC_Reflection_V2_Data.vconst }
and pattern__Pat_Cons__payload =
  {
  head: FStarC_Reflection_Types.fv ;
  univs: FStarC_Reflection_V2_Data.universes FStar_Pervasives_Native.option ;
  subpats: (pattern * Prims.bool) Prims.list }
and pattern__Pat_Var__payload =
  {
  v: namedv ;
  sort1: FStarC_Reflection_Types.typ FStar_Sealed.sealed }
and pattern__Pat_Dot_Term__payload =
  {
  t: term FStar_Pervasives_Native.option }
and pattern =
  | Pat_Constant of pattern__Pat_Constant__payload 
  | Pat_Cons of pattern__Pat_Cons__payload 
  | Pat_Var of pattern__Pat_Var__payload 
  | Pat_Dot_Term of pattern__Pat_Dot_Term__payload 
let rec __knot_e_pattern__Pat_Constant__payload _ =
  FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.pattern__Pat_Constant__payload"
    (fun tm_40 ->
       match tm_40 with
       | ("FStar.Tactics.NamedView.Mkpattern__Pat_Constant__payload",
          c_42::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_vconst c_42)
             (fun c_42 -> FStar_Pervasives_Native.Some { c = c_42 })
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_43 ->
       match tm_43 with
       | { c = c_45;_} ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Mkpattern__Pat_Constant__payload"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_vconst c_45),
                FStar_Pervasives_Native.None)])
and __knot_e_pattern__Pat_Cons__payload _ =
  FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.pattern__Pat_Cons__payload"
    (fun tm_46 ->
       match tm_46 with
       | ("FStar.Tactics.NamedView.Mkpattern__Pat_Cons__payload",
          head_48::univs_49::subpats_50::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_fv head_48)
             (fun head_48 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (FStarC_Syntax_Embeddings.e_option
                        (FStarC_Syntax_Embeddings.e_list
                           FStarC_Reflection_V2_Embeddings.e_universe))
                     univs_49)
                  (fun univs_49 ->
                     FStarC_Compiler_Util.bind_opt
                       (FStarC_Syntax_Embeddings_Base.extracted_unembed
                          (FStarC_Syntax_Embeddings.e_list
                             (FStarC_Syntax_Embeddings.e_tuple2
                                (__knot_e_pattern ())
                                FStarC_Syntax_Embeddings.e_bool)) subpats_50)
                       (fun subpats_50 ->
                          FStar_Pervasives_Native.Some
                            {
                              head = head_48;
                              univs = univs_49;
                              subpats = subpats_50
                            })))
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_51 ->
       match tm_51 with
       | { head = head_53; univs = univs_54; subpats = subpats_55;_} ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Mkpattern__Pat_Cons__payload"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_fv head_53),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 (FStarC_Syntax_Embeddings.e_option
                    (FStarC_Syntax_Embeddings.e_list
                       FStarC_Reflection_V2_Embeddings.e_universe)) univs_54),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 (FStarC_Syntax_Embeddings.e_list
                    (FStarC_Syntax_Embeddings.e_tuple2 (__knot_e_pattern ())
                       FStarC_Syntax_Embeddings.e_bool)) subpats_55),
               FStar_Pervasives_Native.None)])
and __knot_e_pattern__Pat_Var__payload _ =
  FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.pattern__Pat_Var__payload"
    (fun tm_56 ->
       match tm_56 with
       | ("FStar.Tactics.NamedView.Mkpattern__Pat_Var__payload",
          v_58::sort_59::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_namedv_view v_58)
             (fun v_58 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (FStarC_Syntax_Embeddings.e_sealed
                        FStarC_Reflection_V2_Embeddings.e_term) sort_59)
                  (fun sort_59 ->
                     FStar_Pervasives_Native.Some
                       { v = v_58; sort1 = sort_59 }))
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_60 ->
       match tm_60 with
       | { v = v_62; sort1 = sort_63;_} ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Mkpattern__Pat_Var__payload"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_namedv_view v_62),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 (FStarC_Syntax_Embeddings.e_sealed
                    FStarC_Reflection_V2_Embeddings.e_term) sort_63),
               FStar_Pervasives_Native.None)])
and __knot_e_pattern__Pat_Dot_Term__payload _ =
  FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.pattern__Pat_Dot_Term__payload"
    (fun tm_64 ->
       match tm_64 with
       | ("FStar.Tactics.NamedView.Mkpattern__Pat_Dot_Term__payload",
          t_66::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                (FStarC_Syntax_Embeddings.e_option
                   FStarC_Reflection_V2_Embeddings.e_term) t_66)
             (fun t_66 -> FStar_Pervasives_Native.Some { t = t_66 })
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_67 ->
       match tm_67 with
       | { t = t_69;_} ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Mkpattern__Pat_Dot_Term__payload"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  (FStarC_Syntax_Embeddings.e_option
                     FStarC_Reflection_V2_Embeddings.e_term) t_69),
                FStar_Pervasives_Native.None)])
and __knot_e_pattern _ =
  FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.pattern"
    (fun tm_70 ->
       match tm_70 with
       | ("FStar.Tactics.NamedView.Pat_Constant", _0_72::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                (__knot_e_pattern__Pat_Constant__payload ()) _0_72)
             (fun _0_72 -> FStar_Pervasives_Native.Some (Pat_Constant _0_72))
       | ("FStar.Tactics.NamedView.Pat_Cons", _0_74::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                (__knot_e_pattern__Pat_Cons__payload ()) _0_74)
             (fun _0_74 -> FStar_Pervasives_Native.Some (Pat_Cons _0_74))
       | ("FStar.Tactics.NamedView.Pat_Var", _0_76::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                (__knot_e_pattern__Pat_Var__payload ()) _0_76)
             (fun _0_76 -> FStar_Pervasives_Native.Some (Pat_Var _0_76))
       | ("FStar.Tactics.NamedView.Pat_Dot_Term", _0_78::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                (__knot_e_pattern__Pat_Dot_Term__payload ()) _0_78)
             (fun _0_78 -> FStar_Pervasives_Native.Some (Pat_Dot_Term _0_78))
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_79 ->
       match tm_79 with
       | Pat_Constant _0_81 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Pat_Constant"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  (__knot_e_pattern__Pat_Constant__payload ()) _0_81),
                FStar_Pervasives_Native.None)]
       | Pat_Cons _0_83 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Pat_Cons"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  (__knot_e_pattern__Pat_Cons__payload ()) _0_83),
                FStar_Pervasives_Native.None)]
       | Pat_Var _0_85 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Pat_Var"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  (__knot_e_pattern__Pat_Var__payload ()) _0_85),
                FStar_Pervasives_Native.None)]
       | Pat_Dot_Term _0_87 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Pat_Dot_Term"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  (__knot_e_pattern__Pat_Dot_Term__payload ()) _0_87),
                FStar_Pervasives_Native.None)])
let e_pattern__Pat_Constant__payload =
  __knot_e_pattern__Pat_Constant__payload ()
let e_pattern__Pat_Cons__payload = __knot_e_pattern__Pat_Cons__payload ()
let e_pattern__Pat_Var__payload = __knot_e_pattern__Pat_Var__payload ()
let e_pattern__Pat_Dot_Term__payload =
  __knot_e_pattern__Pat_Dot_Term__payload ()
let e_pattern = __knot_e_pattern ()
let (__proj__Mkpattern__Pat_Constant__payload__item__c :
  pattern__Pat_Constant__payload -> FStarC_Reflection_V2_Data.vconst) =
  fun projectee -> match projectee with | { c;_} -> c
let (__proj__Mkpattern__Pat_Cons__payload__item__head :
  pattern__Pat_Cons__payload -> FStarC_Reflection_Types.fv) =
  fun projectee -> match projectee with | { head; univs; subpats;_} -> head
let (__proj__Mkpattern__Pat_Cons__payload__item__univs :
  pattern__Pat_Cons__payload ->
    FStarC_Reflection_V2_Data.universes FStar_Pervasives_Native.option)
  =
  fun projectee -> match projectee with | { head; univs; subpats;_} -> univs
let (__proj__Mkpattern__Pat_Cons__payload__item__subpats :
  pattern__Pat_Cons__payload -> (pattern * Prims.bool) Prims.list) =
  fun projectee ->
    match projectee with | { head; univs; subpats;_} -> subpats
let (__proj__Mkpattern__Pat_Var__payload__item__v :
  pattern__Pat_Var__payload -> namedv) =
  fun projectee -> match projectee with | { v; sort1 = sort;_} -> v
let (__proj__Mkpattern__Pat_Var__payload__item__sort :
  pattern__Pat_Var__payload ->
    FStarC_Reflection_Types.typ FStar_Sealed.sealed)
  = fun projectee -> match projectee with | { v; sort1 = sort;_} -> sort
let (__proj__Mkpattern__Pat_Dot_Term__payload__item__t :
  pattern__Pat_Dot_Term__payload -> term FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | { t;_} -> t
let (uu___is_Pat_Constant : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_Constant _0 -> true | uu___ -> false
let (__proj__Pat_Constant__item___0 :
  pattern -> pattern__Pat_Constant__payload) =
  fun projectee -> match projectee with | Pat_Constant _0 -> _0
let (uu___is_Pat_Cons : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_Cons _0 -> true | uu___ -> false
let (__proj__Pat_Cons__item___0 : pattern -> pattern__Pat_Cons__payload) =
  fun projectee -> match projectee with | Pat_Cons _0 -> _0
let (uu___is_Pat_Var : pattern -> Prims.bool) =
  fun projectee -> match projectee with | Pat_Var _0 -> true | uu___ -> false
let (__proj__Pat_Var__item___0 : pattern -> pattern__Pat_Var__payload) =
  fun projectee -> match projectee with | Pat_Var _0 -> _0
let (uu___is_Pat_Dot_Term : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_Dot_Term _0 -> true | uu___ -> false
let (__proj__Pat_Dot_Term__item___0 :
  pattern -> pattern__Pat_Dot_Term__payload) =
  fun projectee -> match projectee with | Pat_Dot_Term _0 -> _0
type branch = (pattern * term)
type match_returns_ascription =
  (binder * ((term, comp) FStar_Pervasives.either * term
    FStar_Pervasives_Native.option * Prims.bool))
type named_term_view =
  | Tv_Var of namedv 
  | Tv_BVar of bv 
  | Tv_FVar of FStarC_Reflection_Types.fv 
  | Tv_UInst of FStarC_Reflection_Types.fv *
  FStarC_Reflection_V2_Data.universes 
  | Tv_App of term * FStarC_Reflection_V2_Data.argv 
  | Tv_Abs of binder * term 
  | Tv_Arrow of binder * comp 
  | Tv_Type of universe 
  | Tv_Refine of simple_binder * term 
  | Tv_Const of FStarC_Reflection_V2_Data.vconst 
  | Tv_Uvar of Prims.nat * FStarC_Reflection_Types.ctx_uvar_and_subst 
  | Tv_Let of Prims.bool * term Prims.list * simple_binder * term * term 
  | Tv_Match of term * match_returns_ascription
  FStar_Pervasives_Native.option * branch Prims.list 
  | Tv_AscribedT of term * term * term FStar_Pervasives_Native.option *
  Prims.bool 
  | Tv_AscribedC of term * comp * term FStar_Pervasives_Native.option *
  Prims.bool 
  | Tv_Unknown 
  | Tv_Unsupp 
let rec __knot_e_named_term_view _ =
  FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.named_term_view"
    (fun tm_88 ->
       match tm_88 with
       | ("FStar.Tactics.NamedView.Tv_Var", v_90::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_namedv_view v_90)
             (fun v_90 -> FStar_Pervasives_Native.Some (Tv_Var v_90))
       | ("FStar.Tactics.NamedView.Tv_BVar", v_92::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_bv_view v_92)
             (fun v_92 -> FStar_Pervasives_Native.Some (Tv_BVar v_92))
       | ("FStar.Tactics.NamedView.Tv_FVar", v_94::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_fv v_94)
             (fun v_94 -> FStar_Pervasives_Native.Some (Tv_FVar v_94))
       | ("FStar.Tactics.NamedView.Tv_UInst", v_96::us_97::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_fv v_96)
             (fun v_96 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (FStarC_Syntax_Embeddings.e_list
                        FStarC_Reflection_V2_Embeddings.e_universe) us_97)
                  (fun us_97 ->
                     FStar_Pervasives_Native.Some (Tv_UInst (v_96, us_97))))
       | ("FStar.Tactics.NamedView.Tv_App", hd_99::a_100::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_term hd_99)
             (fun hd_99 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (FStarC_Syntax_Embeddings.e_tuple2
                        FStarC_Reflection_V2_Embeddings.e_term
                        FStarC_Reflection_V2_Embeddings.e_aqualv) a_100)
                  (fun a_100 ->
                     FStar_Pervasives_Native.Some (Tv_App (hd_99, a_100))))
       | ("FStar.Tactics.NamedView.Tv_Abs", b_102::body_103::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed e_binder b_102)
             (fun b_102 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     FStarC_Reflection_V2_Embeddings.e_term body_103)
                  (fun body_103 ->
                     FStar_Pervasives_Native.Some (Tv_Abs (b_102, body_103))))
       | ("FStar.Tactics.NamedView.Tv_Arrow", b_105::c_106::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed e_binder b_105)
             (fun b_105 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     FStarC_Reflection_V2_Embeddings.e_comp_view c_106)
                  (fun c_106 ->
                     FStar_Pervasives_Native.Some (Tv_Arrow (b_105, c_106))))
       | ("FStar.Tactics.NamedView.Tv_Type", _0_108::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_universe _0_108)
             (fun _0_108 -> FStar_Pervasives_Native.Some (Tv_Type _0_108))
       | ("FStar.Tactics.NamedView.Tv_Refine", b_110::ref_111::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed e_binder b_110)
             (fun b_110 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     FStarC_Reflection_V2_Embeddings.e_term ref_111)
                  (fun ref_111 ->
                     FStar_Pervasives_Native.Some
                       (Tv_Refine (b_110, ref_111))))
       | ("FStar.Tactics.NamedView.Tv_Const", _0_113::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_vconst _0_113)
             (fun _0_113 -> FStar_Pervasives_Native.Some (Tv_Const _0_113))
       | ("FStar.Tactics.NamedView.Tv_Uvar", _0_115::_1_116::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Syntax_Embeddings.e_int _0_115)
             (fun _0_115 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     FStarC_Reflection_V2_Embeddings.e_ctx_uvar_and_subst
                     _1_116)
                  (fun _1_116 ->
                     FStar_Pervasives_Native.Some (Tv_Uvar (_0_115, _1_116))))
       | ("FStar.Tactics.NamedView.Tv_Let",
          recf_118::attrs_119::b_120::def_121::body_122::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Syntax_Embeddings.e_bool recf_118)
             (fun recf_118 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (FStarC_Syntax_Embeddings.e_list
                        FStarC_Reflection_V2_Embeddings.e_term) attrs_119)
                  (fun attrs_119 ->
                     FStarC_Compiler_Util.bind_opt
                       (FStarC_Syntax_Embeddings_Base.extracted_unembed
                          e_binder b_120)
                       (fun b_120 ->
                          FStarC_Compiler_Util.bind_opt
                            (FStarC_Syntax_Embeddings_Base.extracted_unembed
                               FStarC_Reflection_V2_Embeddings.e_term def_121)
                            (fun def_121 ->
                               FStarC_Compiler_Util.bind_opt
                                 (FStarC_Syntax_Embeddings_Base.extracted_unembed
                                    FStarC_Reflection_V2_Embeddings.e_term
                                    body_122)
                                 (fun body_122 ->
                                    FStar_Pervasives_Native.Some
                                      (Tv_Let
                                         (recf_118, attrs_119, b_120,
                                           def_121, body_122)))))))
       | ("FStar.Tactics.NamedView.Tv_Match",
          scrutinee_124::ret_125::brs_126::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_term scrutinee_124)
             (fun scrutinee_124 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (FStarC_Syntax_Embeddings.e_option
                        (FStarC_Syntax_Embeddings.e_tuple2 e_binder
                           (FStarC_Syntax_Embeddings.e_tuple3
                              (FStarC_Syntax_Embeddings.e_either
                                 FStarC_Reflection_V2_Embeddings.e_term
                                 FStarC_Reflection_V2_Embeddings.e_comp_view)
                              (FStarC_Syntax_Embeddings.e_option
                                 FStarC_Reflection_V2_Embeddings.e_term)
                              FStarC_Syntax_Embeddings.e_bool))) ret_125)
                  (fun ret_125 ->
                     FStarC_Compiler_Util.bind_opt
                       (FStarC_Syntax_Embeddings_Base.extracted_unembed
                          (FStarC_Syntax_Embeddings.e_list
                             (FStarC_Syntax_Embeddings.e_tuple2 e_pattern
                                FStarC_Reflection_V2_Embeddings.e_term))
                          brs_126)
                       (fun brs_126 ->
                          FStar_Pervasives_Native.Some
                            (Tv_Match (scrutinee_124, ret_125, brs_126)))))
       | ("FStar.Tactics.NamedView.Tv_AscribedT",
          e_128::t_129::tac_130::use_eq_131::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_term e_128)
             (fun e_128 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     FStarC_Reflection_V2_Embeddings.e_term t_129)
                  (fun t_129 ->
                     FStarC_Compiler_Util.bind_opt
                       (FStarC_Syntax_Embeddings_Base.extracted_unembed
                          (FStarC_Syntax_Embeddings.e_option
                             FStarC_Reflection_V2_Embeddings.e_term) tac_130)
                       (fun tac_130 ->
                          FStarC_Compiler_Util.bind_opt
                            (FStarC_Syntax_Embeddings_Base.extracted_unembed
                               FStarC_Syntax_Embeddings.e_bool use_eq_131)
                            (fun use_eq_131 ->
                               FStar_Pervasives_Native.Some
                                 (Tv_AscribedT
                                    (e_128, t_129, tac_130, use_eq_131))))))
       | ("FStar.Tactics.NamedView.Tv_AscribedC",
          e_133::c_134::tac_135::use_eq_136::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_term e_133)
             (fun e_133 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     FStarC_Reflection_V2_Embeddings.e_comp_view c_134)
                  (fun c_134 ->
                     FStarC_Compiler_Util.bind_opt
                       (FStarC_Syntax_Embeddings_Base.extracted_unembed
                          (FStarC_Syntax_Embeddings.e_option
                             FStarC_Reflection_V2_Embeddings.e_term) tac_135)
                       (fun tac_135 ->
                          FStarC_Compiler_Util.bind_opt
                            (FStarC_Syntax_Embeddings_Base.extracted_unembed
                               FStarC_Syntax_Embeddings.e_bool use_eq_136)
                            (fun use_eq_136 ->
                               FStar_Pervasives_Native.Some
                                 (Tv_AscribedC
                                    (e_133, c_134, tac_135, use_eq_136))))))
       | ("FStar.Tactics.NamedView.Tv_Unknown", []) ->
           FStar_Pervasives_Native.Some Tv_Unknown
       | ("FStar.Tactics.NamedView.Tv_Unsupp", []) ->
           FStar_Pervasives_Native.Some Tv_Unsupp
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_139 ->
       match tm_139 with
       | Tv_Var v_141 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Tv_Var"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_namedv_view v_141),
                FStar_Pervasives_Native.None)]
       | Tv_BVar v_143 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Tv_BVar"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_bv_view v_143),
                FStar_Pervasives_Native.None)]
       | Tv_FVar v_145 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Tv_FVar"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_fv v_145),
                FStar_Pervasives_Native.None)]
       | Tv_UInst (v_147, us_148) ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Tv_UInst"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_fv v_147),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 (FStarC_Syntax_Embeddings.e_list
                    FStarC_Reflection_V2_Embeddings.e_universe) us_148),
               FStar_Pervasives_Native.None)]
       | Tv_App (hd_150, a_151) ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Tv_App"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_term hd_150),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 (FStarC_Syntax_Embeddings.e_tuple2
                    FStarC_Reflection_V2_Embeddings.e_term
                    FStarC_Reflection_V2_Embeddings.e_aqualv) a_151),
               FStar_Pervasives_Native.None)]
       | Tv_Abs (b_153, body_154) ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Tv_Abs"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed e_binder b_153),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term body_154),
               FStar_Pervasives_Native.None)]
       | Tv_Arrow (b_156, c_157) ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Tv_Arrow"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed e_binder b_156),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_comp_view c_157),
               FStar_Pervasives_Native.None)]
       | Tv_Type _0_159 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Tv_Type"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_universe _0_159),
                FStar_Pervasives_Native.None)]
       | Tv_Refine (b_161, ref_162) ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Tv_Refine"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed e_binder b_161),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term ref_162),
               FStar_Pervasives_Native.None)]
       | Tv_Const _0_164 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Tv_Const"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_vconst _0_164),
                FStar_Pervasives_Native.None)]
       | Tv_Uvar (_0_166, _1_167) ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Tv_Uvar"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Syntax_Embeddings.e_int _0_166),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_ctx_uvar_and_subst _1_167),
               FStar_Pervasives_Native.None)]
       | Tv_Let (recf_169, attrs_170, b_171, def_172, body_173) ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Tv_Let"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Syntax_Embeddings.e_bool recf_169),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 (FStarC_Syntax_Embeddings.e_list
                    FStarC_Reflection_V2_Embeddings.e_term) attrs_170),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed e_binder b_171),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term def_172),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term body_173),
               FStar_Pervasives_Native.None)]
       | Tv_Match (scrutinee_175, ret_176, brs_177) ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Tv_Match"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_term scrutinee_175),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 (FStarC_Syntax_Embeddings.e_option
                    (FStarC_Syntax_Embeddings.e_tuple2 e_binder
                       (FStarC_Syntax_Embeddings.e_tuple3
                          (FStarC_Syntax_Embeddings.e_either
                             FStarC_Reflection_V2_Embeddings.e_term
                             FStarC_Reflection_V2_Embeddings.e_comp_view)
                          (FStarC_Syntax_Embeddings.e_option
                             FStarC_Reflection_V2_Embeddings.e_term)
                          FStarC_Syntax_Embeddings.e_bool))) ret_176),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 (FStarC_Syntax_Embeddings.e_list
                    (FStarC_Syntax_Embeddings.e_tuple2 e_pattern
                       FStarC_Reflection_V2_Embeddings.e_term)) brs_177),
               FStar_Pervasives_Native.None)]
       | Tv_AscribedT (e_179, t_180, tac_181, use_eq_182) ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Tv_AscribedT"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_term e_179),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term t_180),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 (FStarC_Syntax_Embeddings.e_option
                    FStarC_Reflection_V2_Embeddings.e_term) tac_181),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Syntax_Embeddings.e_bool use_eq_182),
               FStar_Pervasives_Native.None)]
       | Tv_AscribedC (e_184, c_185, tac_186, use_eq_187) ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Tv_AscribedC"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_term e_184),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_comp_view c_185),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 (FStarC_Syntax_Embeddings.e_option
                    FStarC_Reflection_V2_Embeddings.e_term) tac_186),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Syntax_Embeddings.e_bool use_eq_187),
               FStar_Pervasives_Native.None)]
       | Tv_Unknown ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Tv_Unknown"))
             []
       | Tv_Unsupp ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Tv_Unsupp"))
             [])
let e_named_term_view = __knot_e_named_term_view ()
let (uu___is_Tv_Var : named_term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Var v -> true | uu___ -> false
let (__proj__Tv_Var__item__v : named_term_view -> namedv) =
  fun projectee -> match projectee with | Tv_Var v -> v
let (uu___is_Tv_BVar : named_term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_BVar v -> true | uu___ -> false
let (__proj__Tv_BVar__item__v : named_term_view -> bv) =
  fun projectee -> match projectee with | Tv_BVar v -> v
let (uu___is_Tv_FVar : named_term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_FVar v -> true | uu___ -> false
let (__proj__Tv_FVar__item__v :
  named_term_view -> FStarC_Reflection_Types.fv) =
  fun projectee -> match projectee with | Tv_FVar v -> v
let (uu___is_Tv_UInst : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_UInst (v, us) -> true | uu___ -> false
let (__proj__Tv_UInst__item__v :
  named_term_view -> FStarC_Reflection_Types.fv) =
  fun projectee -> match projectee with | Tv_UInst (v, us) -> v
let (__proj__Tv_UInst__item__us :
  named_term_view -> FStarC_Reflection_V2_Data.universes) =
  fun projectee -> match projectee with | Tv_UInst (v, us) -> us
let (uu___is_Tv_App : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_App (hd, a) -> true | uu___ -> false
let (__proj__Tv_App__item__hd : named_term_view -> term) =
  fun projectee -> match projectee with | Tv_App (hd, a) -> hd
let (__proj__Tv_App__item__a :
  named_term_view -> FStarC_Reflection_V2_Data.argv) =
  fun projectee -> match projectee with | Tv_App (hd, a) -> a
let (uu___is_Tv_Abs : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Abs (b, body) -> true | uu___ -> false
let (__proj__Tv_Abs__item__b : named_term_view -> binder) =
  fun projectee -> match projectee with | Tv_Abs (b, body) -> b
let (__proj__Tv_Abs__item__body : named_term_view -> term) =
  fun projectee -> match projectee with | Tv_Abs (b, body) -> body
let (uu___is_Tv_Arrow : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Arrow (b, c) -> true | uu___ -> false
let (__proj__Tv_Arrow__item__b : named_term_view -> binder) =
  fun projectee -> match projectee with | Tv_Arrow (b, c) -> b
let (__proj__Tv_Arrow__item__c : named_term_view -> comp) =
  fun projectee -> match projectee with | Tv_Arrow (b, c) -> c
let (uu___is_Tv_Type : named_term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Type _0 -> true | uu___ -> false
let (__proj__Tv_Type__item___0 : named_term_view -> universe) =
  fun projectee -> match projectee with | Tv_Type _0 -> _0
let (uu___is_Tv_Refine : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Refine (b, ref) -> true | uu___ -> false
let (__proj__Tv_Refine__item__b : named_term_view -> simple_binder) =
  fun projectee -> match projectee with | Tv_Refine (b, ref) -> b
let (__proj__Tv_Refine__item__ref : named_term_view -> term) =
  fun projectee -> match projectee with | Tv_Refine (b, ref) -> ref
let (uu___is_Tv_Const : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Const _0 -> true | uu___ -> false
let (__proj__Tv_Const__item___0 :
  named_term_view -> FStarC_Reflection_V2_Data.vconst) =
  fun projectee -> match projectee with | Tv_Const _0 -> _0
let (uu___is_Tv_Uvar : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Uvar (_0, _1) -> true | uu___ -> false
let (__proj__Tv_Uvar__item___0 : named_term_view -> Prims.nat) =
  fun projectee -> match projectee with | Tv_Uvar (_0, _1) -> _0
let (__proj__Tv_Uvar__item___1 :
  named_term_view -> FStarC_Reflection_Types.ctx_uvar_and_subst) =
  fun projectee -> match projectee with | Tv_Uvar (_0, _1) -> _1
let (uu___is_Tv_Let : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Tv_Let (recf, attrs, b, def, body) -> true
    | uu___ -> false
let (__proj__Tv_Let__item__recf : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Let (recf, attrs, b, def, body) -> recf
let (__proj__Tv_Let__item__attrs : named_term_view -> term Prims.list) =
  fun projectee ->
    match projectee with | Tv_Let (recf, attrs, b, def, body) -> attrs
let (__proj__Tv_Let__item__b : named_term_view -> simple_binder) =
  fun projectee ->
    match projectee with | Tv_Let (recf, attrs, b, def, body) -> b
let (__proj__Tv_Let__item__def : named_term_view -> term) =
  fun projectee ->
    match projectee with | Tv_Let (recf, attrs, b, def, body) -> def
let (__proj__Tv_Let__item__body : named_term_view -> term) =
  fun projectee ->
    match projectee with | Tv_Let (recf, attrs, b, def, body) -> body
let (uu___is_Tv_Match : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Tv_Match (scrutinee, ret, brs) -> true
    | uu___ -> false
let (__proj__Tv_Match__item__scrutinee : named_term_view -> term) =
  fun projectee ->
    match projectee with | Tv_Match (scrutinee, ret, brs) -> scrutinee
let (__proj__Tv_Match__item__ret :
  named_term_view -> match_returns_ascription FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with | Tv_Match (scrutinee, ret, brs) -> ret
let (__proj__Tv_Match__item__brs : named_term_view -> branch Prims.list) =
  fun projectee ->
    match projectee with | Tv_Match (scrutinee, ret, brs) -> brs
let (uu___is_Tv_AscribedT : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Tv_AscribedT (e, t, tac, use_eq) -> true
    | uu___ -> false
let (__proj__Tv_AscribedT__item__e : named_term_view -> term) =
  fun projectee ->
    match projectee with | Tv_AscribedT (e, t, tac, use_eq) -> e
let (__proj__Tv_AscribedT__item__t : named_term_view -> term) =
  fun projectee ->
    match projectee with | Tv_AscribedT (e, t, tac, use_eq) -> t
let (__proj__Tv_AscribedT__item__tac :
  named_term_view -> term FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | Tv_AscribedT (e, t, tac, use_eq) -> tac
let (__proj__Tv_AscribedT__item__use_eq : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_AscribedT (e, t, tac, use_eq) -> use_eq
let (uu___is_Tv_AscribedC : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Tv_AscribedC (e, c, tac, use_eq) -> true
    | uu___ -> false
let (__proj__Tv_AscribedC__item__e : named_term_view -> term) =
  fun projectee ->
    match projectee with | Tv_AscribedC (e, c, tac, use_eq) -> e
let (__proj__Tv_AscribedC__item__c : named_term_view -> comp) =
  fun projectee ->
    match projectee with | Tv_AscribedC (e, c, tac, use_eq) -> c
let (__proj__Tv_AscribedC__item__tac :
  named_term_view -> term FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | Tv_AscribedC (e, c, tac, use_eq) -> tac
let (__proj__Tv_AscribedC__item__use_eq : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_AscribedC (e, c, tac, use_eq) -> use_eq
let (uu___is_Tv_Unknown : named_term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Unknown -> true | uu___ -> false
let (uu___is_Tv_Unsupp : named_term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Unsupp -> true | uu___ -> false
let (notAscription : named_term_view -> Prims.bool) =
  fun tv ->
    (Prims.op_Negation (uu___is_Tv_AscribedT tv)) &&
      (Prims.op_Negation (uu___is_Tv_AscribedC tv))
type letbinding =
  {
  lb_fv: FStarC_Reflection_Types.fv ;
  lb_us: univ_name Prims.list ;
  lb_typ: FStarC_Reflection_Types.typ ;
  lb_def: term }
let rec __knot_e_letbinding _ =
  FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.letbinding"
    (fun tm_190 ->
       match tm_190 with
       | ("FStar.Tactics.NamedView.Mkletbinding",
          lb_fv_192::lb_us_193::lb_typ_194::lb_def_195::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Reflection_V2_Embeddings.e_fv lb_fv_192)
             (fun lb_fv_192 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (FStarC_Syntax_Embeddings.e_list
                        (FStarC_Syntax_Embeddings.e_tuple2
                           FStarC_Syntax_Embeddings.e_string
                           (FStarC_Syntax_Embeddings.e_sealed
                              FStarC_Syntax_Embeddings.e___range))) lb_us_193)
                  (fun lb_us_193 ->
                     FStarC_Compiler_Util.bind_opt
                       (FStarC_Syntax_Embeddings_Base.extracted_unembed
                          FStarC_Reflection_V2_Embeddings.e_term lb_typ_194)
                       (fun lb_typ_194 ->
                          FStarC_Compiler_Util.bind_opt
                            (FStarC_Syntax_Embeddings_Base.extracted_unembed
                               FStarC_Reflection_V2_Embeddings.e_term
                               lb_def_195)
                            (fun lb_def_195 ->
                               FStar_Pervasives_Native.Some
                                 {
                                   lb_fv = lb_fv_192;
                                   lb_us = lb_us_193;
                                   lb_typ = lb_typ_194;
                                   lb_def = lb_def_195
                                 }))))
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_196 ->
       match tm_196 with
       | { lb_fv = lb_fv_198; lb_us = lb_us_199; lb_typ = lb_typ_200;
           lb_def = lb_def_201;_} ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Mkletbinding"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Reflection_V2_Embeddings.e_fv lb_fv_198),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 (FStarC_Syntax_Embeddings.e_list
                    (FStarC_Syntax_Embeddings.e_tuple2
                       FStarC_Syntax_Embeddings.e_string
                       (FStarC_Syntax_Embeddings.e_sealed
                          FStarC_Syntax_Embeddings.e___range))) lb_us_199),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term lb_typ_200),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term lb_def_201),
               FStar_Pervasives_Native.None)])
let e_letbinding = __knot_e_letbinding ()
let (__proj__Mkletbinding__item__lb_fv :
  letbinding -> FStarC_Reflection_Types.fv) =
  fun projectee ->
    match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_fv
let (__proj__Mkletbinding__item__lb_us : letbinding -> univ_name Prims.list)
  =
  fun projectee ->
    match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_us
let (__proj__Mkletbinding__item__lb_typ :
  letbinding -> FStarC_Reflection_Types.typ) =
  fun projectee ->
    match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_typ
let (__proj__Mkletbinding__item__lb_def : letbinding -> term) =
  fun projectee ->
    match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_def
type named_sigelt_view__Sg_Let__payload =
  {
  isrec: Prims.bool ;
  lbs: letbinding Prims.list }
and named_sigelt_view__Sg_Inductive__payload =
  {
  nm: FStarC_Reflection_Types.name ;
  univs1: univ_name Prims.list ;
  params: binders ;
  typ: FStarC_Reflection_Types.typ ;
  ctors: FStarC_Reflection_V2_Data.ctor Prims.list }
and named_sigelt_view__Sg_Val__payload =
  {
  nm1: FStarC_Reflection_Types.name ;
  univs2: univ_name Prims.list ;
  typ1: FStarC_Reflection_Types.typ }
and named_sigelt_view =
  | Sg_Let of named_sigelt_view__Sg_Let__payload 
  | Sg_Inductive of named_sigelt_view__Sg_Inductive__payload 
  | Sg_Val of named_sigelt_view__Sg_Val__payload 
  | Unk 
let rec __knot_e_named_sigelt_view__Sg_Let__payload _ =
  FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.named_sigelt_view__Sg_Let__payload"
    (fun tm_202 ->
       match tm_202 with
       | ("FStar.Tactics.NamedView.Mknamed_sigelt_view__Sg_Let__payload",
          isrec_204::lbs_205::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                FStarC_Syntax_Embeddings.e_bool isrec_204)
             (fun isrec_204 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (FStarC_Syntax_Embeddings.e_list e_letbinding) lbs_205)
                  (fun lbs_205 ->
                     FStar_Pervasives_Native.Some
                       { isrec = isrec_204; lbs = lbs_205 }))
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_206 ->
       match tm_206 with
       | { isrec = isrec_208; lbs = lbs_209;_} ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Mknamed_sigelt_view__Sg_Let__payload"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  FStarC_Syntax_Embeddings.e_bool isrec_208),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 (FStarC_Syntax_Embeddings.e_list e_letbinding) lbs_209),
               FStar_Pervasives_Native.None)])
and __knot_e_named_sigelt_view__Sg_Inductive__payload _ =
  FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.named_sigelt_view__Sg_Inductive__payload"
    (fun tm_210 ->
       match tm_210 with
       | ("FStar.Tactics.NamedView.Mknamed_sigelt_view__Sg_Inductive__payload",
          nm_212::univs_213::params_214::typ_215::ctors_216::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                (FStarC_Syntax_Embeddings.e_list
                   FStarC_Syntax_Embeddings.e_string) nm_212)
             (fun nm_212 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (FStarC_Syntax_Embeddings.e_list
                        (FStarC_Syntax_Embeddings.e_tuple2
                           FStarC_Syntax_Embeddings.e_string
                           (FStarC_Syntax_Embeddings.e_sealed
                              FStarC_Syntax_Embeddings.e___range))) univs_213)
                  (fun univs_213 ->
                     FStarC_Compiler_Util.bind_opt
                       (FStarC_Syntax_Embeddings_Base.extracted_unembed
                          (FStarC_Syntax_Embeddings.e_list e_binder)
                          params_214)
                       (fun params_214 ->
                          FStarC_Compiler_Util.bind_opt
                            (FStarC_Syntax_Embeddings_Base.extracted_unembed
                               FStarC_Reflection_V2_Embeddings.e_term typ_215)
                            (fun typ_215 ->
                               FStarC_Compiler_Util.bind_opt
                                 (FStarC_Syntax_Embeddings_Base.extracted_unembed
                                    (FStarC_Syntax_Embeddings.e_list
                                       (FStarC_Syntax_Embeddings.e_tuple2
                                          (FStarC_Syntax_Embeddings.e_list
                                             FStarC_Syntax_Embeddings.e_string)
                                          FStarC_Reflection_V2_Embeddings.e_term))
                                    ctors_216)
                                 (fun ctors_216 ->
                                    FStar_Pervasives_Native.Some
                                      {
                                        nm = nm_212;
                                        univs1 = univs_213;
                                        params = params_214;
                                        typ = typ_215;
                                        ctors = ctors_216
                                      })))))
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_217 ->
       match tm_217 with
       | { nm = nm_219; univs1 = univs_220; params = params_221;
           typ = typ_222; ctors = ctors_223;_} ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Mknamed_sigelt_view__Sg_Inductive__payload"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  (FStarC_Syntax_Embeddings.e_list
                     FStarC_Syntax_Embeddings.e_string) nm_219),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 (FStarC_Syntax_Embeddings.e_list
                    (FStarC_Syntax_Embeddings.e_tuple2
                       FStarC_Syntax_Embeddings.e_string
                       (FStarC_Syntax_Embeddings.e_sealed
                          FStarC_Syntax_Embeddings.e___range))) univs_220),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 (FStarC_Syntax_Embeddings.e_list e_binder) params_221),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term typ_222),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 (FStarC_Syntax_Embeddings.e_list
                    (FStarC_Syntax_Embeddings.e_tuple2
                       (FStarC_Syntax_Embeddings.e_list
                          FStarC_Syntax_Embeddings.e_string)
                       FStarC_Reflection_V2_Embeddings.e_term)) ctors_223),
               FStar_Pervasives_Native.None)])
and __knot_e_named_sigelt_view__Sg_Val__payload _ =
  FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.named_sigelt_view__Sg_Val__payload"
    (fun tm_224 ->
       match tm_224 with
       | ("FStar.Tactics.NamedView.Mknamed_sigelt_view__Sg_Val__payload",
          nm_226::univs_227::typ_228::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                (FStarC_Syntax_Embeddings.e_list
                   FStarC_Syntax_Embeddings.e_string) nm_226)
             (fun nm_226 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (FStarC_Syntax_Embeddings.e_list
                        (FStarC_Syntax_Embeddings.e_tuple2
                           FStarC_Syntax_Embeddings.e_string
                           (FStarC_Syntax_Embeddings.e_sealed
                              FStarC_Syntax_Embeddings.e___range))) univs_227)
                  (fun univs_227 ->
                     FStarC_Compiler_Util.bind_opt
                       (FStarC_Syntax_Embeddings_Base.extracted_unembed
                          FStarC_Reflection_V2_Embeddings.e_term typ_228)
                       (fun typ_228 ->
                          FStar_Pervasives_Native.Some
                            {
                              nm1 = nm_226;
                              univs2 = univs_227;
                              typ1 = typ_228
                            })))
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_229 ->
       match tm_229 with
       | { nm1 = nm_231; univs2 = univs_232; typ1 = typ_233;_} ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Mknamed_sigelt_view__Sg_Val__payload"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  (FStarC_Syntax_Embeddings.e_list
                     FStarC_Syntax_Embeddings.e_string) nm_231),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 (FStarC_Syntax_Embeddings.e_list
                    (FStarC_Syntax_Embeddings.e_tuple2
                       FStarC_Syntax_Embeddings.e_string
                       (FStarC_Syntax_Embeddings.e_sealed
                          FStarC_Syntax_Embeddings.e___range))) univs_232),
               FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 FStarC_Reflection_V2_Embeddings.e_term typ_233),
               FStar_Pervasives_Native.None)])
and __knot_e_named_sigelt_view _ =
  FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.named_sigelt_view"
    (fun tm_234 ->
       match tm_234 with
       | ("FStar.Tactics.NamedView.Sg_Let", _0_236::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                (__knot_e_named_sigelt_view__Sg_Let__payload ()) _0_236)
             (fun _0_236 -> FStar_Pervasives_Native.Some (Sg_Let _0_236))
       | ("FStar.Tactics.NamedView.Sg_Inductive", _0_238::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                (__knot_e_named_sigelt_view__Sg_Inductive__payload ()) _0_238)
             (fun _0_238 ->
                FStar_Pervasives_Native.Some (Sg_Inductive _0_238))
       | ("FStar.Tactics.NamedView.Sg_Val", _0_240::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                (__knot_e_named_sigelt_view__Sg_Val__payload ()) _0_240)
             (fun _0_240 -> FStar_Pervasives_Native.Some (Sg_Val _0_240))
       | ("FStar.Tactics.NamedView.Unk", []) ->
           FStar_Pervasives_Native.Some Unk
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_242 ->
       match tm_242 with
       | Sg_Let _0_244 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Sg_Let"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  (__knot_e_named_sigelt_view__Sg_Let__payload ()) _0_244),
                FStar_Pervasives_Native.None)]
       | Sg_Inductive _0_246 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Sg_Inductive"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  (__knot_e_named_sigelt_view__Sg_Inductive__payload ())
                  _0_246), FStar_Pervasives_Native.None)]
       | Sg_Val _0_248 ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Sg_Val"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  (__knot_e_named_sigelt_view__Sg_Val__payload ()) _0_248),
                FStar_Pervasives_Native.None)]
       | Unk ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.Unk")) [])
let e_named_sigelt_view__Sg_Let__payload =
  __knot_e_named_sigelt_view__Sg_Let__payload ()
let e_named_sigelt_view__Sg_Inductive__payload =
  __knot_e_named_sigelt_view__Sg_Inductive__payload ()
let e_named_sigelt_view__Sg_Val__payload =
  __knot_e_named_sigelt_view__Sg_Val__payload ()
let e_named_sigelt_view = __knot_e_named_sigelt_view ()
let (__proj__Mknamed_sigelt_view__Sg_Let__payload__item__isrec :
  named_sigelt_view__Sg_Let__payload -> Prims.bool) =
  fun projectee -> match projectee with | { isrec; lbs;_} -> isrec
let (__proj__Mknamed_sigelt_view__Sg_Let__payload__item__lbs :
  named_sigelt_view__Sg_Let__payload -> letbinding Prims.list) =
  fun projectee -> match projectee with | { isrec; lbs;_} -> lbs
let (__proj__Mknamed_sigelt_view__Sg_Inductive__payload__item__nm :
  named_sigelt_view__Sg_Inductive__payload -> FStarC_Reflection_Types.name) =
  fun projectee ->
    match projectee with | { nm; univs1 = univs; params; typ; ctors;_} -> nm
let (__proj__Mknamed_sigelt_view__Sg_Inductive__payload__item__univs :
  named_sigelt_view__Sg_Inductive__payload -> univ_name Prims.list) =
  fun projectee ->
    match projectee with
    | { nm; univs1 = univs; params; typ; ctors;_} -> univs
let (__proj__Mknamed_sigelt_view__Sg_Inductive__payload__item__params :
  named_sigelt_view__Sg_Inductive__payload -> binders) =
  fun projectee ->
    match projectee with
    | { nm; univs1 = univs; params; typ; ctors;_} -> params
let (__proj__Mknamed_sigelt_view__Sg_Inductive__payload__item__typ :
  named_sigelt_view__Sg_Inductive__payload -> FStarC_Reflection_Types.typ) =
  fun projectee ->
    match projectee with | { nm; univs1 = univs; params; typ; ctors;_} -> typ
let (__proj__Mknamed_sigelt_view__Sg_Inductive__payload__item__ctors :
  named_sigelt_view__Sg_Inductive__payload ->
    FStarC_Reflection_V2_Data.ctor Prims.list)
  =
  fun projectee ->
    match projectee with
    | { nm; univs1 = univs; params; typ; ctors;_} -> ctors
let (__proj__Mknamed_sigelt_view__Sg_Val__payload__item__nm :
  named_sigelt_view__Sg_Val__payload -> FStarC_Reflection_Types.name) =
  fun projectee ->
    match projectee with | { nm1 = nm; univs2 = univs; typ1 = typ;_} -> nm
let (__proj__Mknamed_sigelt_view__Sg_Val__payload__item__univs :
  named_sigelt_view__Sg_Val__payload -> univ_name Prims.list) =
  fun projectee ->
    match projectee with | { nm1 = nm; univs2 = univs; typ1 = typ;_} -> univs
let (__proj__Mknamed_sigelt_view__Sg_Val__payload__item__typ :
  named_sigelt_view__Sg_Val__payload -> FStarC_Reflection_Types.typ) =
  fun projectee ->
    match projectee with | { nm1 = nm; univs2 = univs; typ1 = typ;_} -> typ
let (uu___is_Sg_Let : named_sigelt_view -> Prims.bool) =
  fun projectee -> match projectee with | Sg_Let _0 -> true | uu___ -> false
let (__proj__Sg_Let__item___0 :
  named_sigelt_view -> named_sigelt_view__Sg_Let__payload) =
  fun projectee -> match projectee with | Sg_Let _0 -> _0
let (uu___is_Sg_Inductive : named_sigelt_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Sg_Inductive _0 -> true | uu___ -> false
let (__proj__Sg_Inductive__item___0 :
  named_sigelt_view -> named_sigelt_view__Sg_Inductive__payload) =
  fun projectee -> match projectee with | Sg_Inductive _0 -> _0
let (uu___is_Sg_Val : named_sigelt_view -> Prims.bool) =
  fun projectee -> match projectee with | Sg_Val _0 -> true | uu___ -> false
let (__proj__Sg_Val__item___0 :
  named_sigelt_view -> named_sigelt_view__Sg_Val__payload) =
  fun projectee -> match projectee with | Sg_Val _0 -> _0
let (uu___is_Unk : named_sigelt_view -> Prims.bool) =
  fun projectee -> match projectee with | Unk -> true | uu___ -> false
let (binder_to_binding : binder -> binding) =
  fun b ->
    {
      FStarC_Reflection_V2_Data.uniq1 = (b.uniq);
      FStarC_Reflection_V2_Data.sort3 = (b.sort);
      FStarC_Reflection_V2_Data.ppname3 = (b.ppname)
    }
let (binding_to_binder : binding -> binder) =
  fun bnd ->
    {
      uniq = (bnd.FStarC_Reflection_V2_Data.uniq1);
      ppname = (bnd.FStarC_Reflection_V2_Data.ppname3);
      sort = (bnd.FStarC_Reflection_V2_Data.sort3);
      qual = FStarC_Reflection_V2_Data.Q_Explicit;
      attrs = []
    }
let (namedv_to_binder : namedv -> term -> binder) =
  fun v ->
    fun sort ->
      {
        uniq = (v.FStarC_Reflection_V2_Data.uniq);
        ppname = (v.FStarC_Reflection_V2_Data.ppname);
        sort;
        qual = FStarC_Reflection_V2_Data.Q_Explicit;
        attrs = []
      }
exception LengthMismatch 
let (uu___is_LengthMismatch : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | LengthMismatch -> true | uu___ -> false
exception NotEnoughBinders 
let (uu___is_NotEnoughBinders : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | NotEnoughBinders -> true | uu___ -> false
let (open_universe_view :
  FStarC_Reflection_V2_Data.universe_view -> named_universe_view) =
  fun v ->
    match v with
    | FStarC_Reflection_V2_Data.Uv_Zero -> Uv_Zero
    | FStarC_Reflection_V2_Data.Uv_Succ u -> Uv_Succ u
    | FStarC_Reflection_V2_Data.Uv_Max us -> Uv_Max us
    | FStarC_Reflection_V2_Data.Uv_BVar n -> Uv_BVar n
    | FStarC_Reflection_V2_Data.Uv_Name i ->
        Uv_Name (FStarC_Reflection_V2_Builtins.inspect_ident i)
    | FStarC_Reflection_V2_Data.Uv_Unif uvar -> Uv_Unif uvar
    | FStarC_Reflection_V2_Data.Uv_Unk -> Uv_Unk
let (inspect_universe : universe -> named_universe_view) =
  fun u ->
    let v = FStarC_Reflection_V2_Builtins.inspect_universe u in
    open_universe_view v
let _ =
  FStarC_Tactics_Native.register_plugin
    "FStar.Tactics.NamedView.inspect_universe" Prims.int_one
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Tactics.NamedView.inspect_universe"
               (fun _ ->
                  (FStarC_Syntax_Embeddings.arrow_as_prim_step_1
                     FStarC_Reflection_V2_Embeddings.e_universe
                     e_named_universe_view inspect_universe
                     (FStarC_Ident.lid_of_str
                        "FStar.Tactics.NamedView.inspect_universe") cb us)
                    args))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Tactics.NamedView.inspect_universe"
             (fun _ ->
                (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_1
                   FStarC_Reflection_V2_NBEEmbeddings.e_universe
                   (FStarC_TypeChecker_NBETerm.e_unsupported ())
                   inspect_universe
                   (FStarC_Ident.lid_of_str
                      "FStar.Tactics.NamedView.inspect_universe") cb us) args))
let (close_universe_view :
  named_universe_view -> FStarC_Reflection_V2_Data.universe_view) =
  fun v ->
    match v with
    | Uv_Zero -> FStarC_Reflection_V2_Data.Uv_Zero
    | Uv_Succ u -> FStarC_Reflection_V2_Data.Uv_Succ u
    | Uv_Max us -> FStarC_Reflection_V2_Data.Uv_Max us
    | Uv_BVar n -> FStarC_Reflection_V2_Data.Uv_BVar n
    | Uv_Name i ->
        FStarC_Reflection_V2_Data.Uv_Name
          (FStarC_Reflection_V2_Builtins.pack_ident i)
    | Uv_Unif uvar -> FStarC_Reflection_V2_Data.Uv_Unif uvar
    | Uv_Unk -> FStarC_Reflection_V2_Data.Uv_Unk
let (pack_universe : named_universe_view -> universe) =
  fun uv ->
    let uv1 = close_universe_view uv in
    FStarC_Reflection_V2_Builtins.pack_universe uv1
let _ =
  FStarC_Tactics_Native.register_plugin
    "FStar.Tactics.NamedView.pack_universe" Prims.int_one
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Tactics.NamedView.pack_universe"
               (fun _ ->
                  (FStarC_Syntax_Embeddings.arrow_as_prim_step_1
                     e_named_universe_view
                     FStarC_Reflection_V2_Embeddings.e_universe pack_universe
                     (FStarC_Ident.lid_of_str
                        "FStar.Tactics.NamedView.pack_universe") cb us) args))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Tactics.NamedView.pack_universe"
             (fun _ ->
                (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_1
                   (FStarC_TypeChecker_NBETerm.e_unsupported ())
                   FStarC_Reflection_V2_NBEEmbeddings.e_universe
                   pack_universe
                   (FStarC_Ident.lid_of_str
                      "FStar.Tactics.NamedView.pack_universe") cb us) args))
let (__binding_to_binder :
  binding -> FStarC_Reflection_Types.binder -> binder) =
  fun bnd ->
    fun b ->
      {
        uniq = (bnd.FStarC_Reflection_V2_Data.uniq1);
        ppname = (bnd.FStarC_Reflection_V2_Data.ppname3);
        sort = (bnd.FStarC_Reflection_V2_Data.sort3);
        qual =
          ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.qual);
        attrs =
          ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.attrs)
      }
let (r_binder_to_namedv : binder -> FStarC_Reflection_Types.namedv) =
  fun b ->
    FStarC_Reflection_V2_Builtins.pack_namedv
      {
        FStarC_Reflection_V2_Data.uniq = (b.uniq);
        FStarC_Reflection_V2_Data.sort = (FStar_Sealed.seal b.sort);
        FStarC_Reflection_V2_Data.ppname = (b.ppname)
      }
let (open_binder :
  FStarC_Reflection_Types.binder ->
    (binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    let uu___ = FStarC_Tactics_V2_Builtins.fresh () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
               (Prims.of_int (81)) (Prims.of_int (10)) (Prims.of_int (81))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
               (Prims.of_int (81)) (Prims.of_int (21)) (Prims.of_int (89))
               (Prims.of_int (3))))) (Obj.magic uu___)
      (fun n ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              {
                uniq = n;
                ppname =
                  ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.ppname2);
                sort =
                  ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.sort2);
                qual =
                  ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.qual);
                attrs =
                  ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.attrs)
              }))
let (close_binder : binder -> FStarC_Reflection_Types.binder) =
  fun b ->
    FStarC_Reflection_V2_Builtins.pack_binder
      {
        FStarC_Reflection_V2_Data.sort2 = (b.sort);
        FStarC_Reflection_V2_Data.qual = (b.qual);
        FStarC_Reflection_V2_Data.attrs = (b.attrs);
        FStarC_Reflection_V2_Data.ppname2 = (b.ppname)
      }
let (open_term_with :
  FStarC_Reflection_Types.binder ->
    binder -> term -> (term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun b ->
           fun nb ->
             fun t ->
               Obj.magic
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       FStarC_Reflection_V2_Builtins.subst_term
                         [FStarC_Syntax_Syntax.DB
                            (Prims.int_zero,
                              (FStarC_Reflection_V2_Builtins.pack_namedv
                                 {
                                   FStarC_Reflection_V2_Data.uniq = (nb.uniq);
                                   FStarC_Reflection_V2_Data.sort =
                                     (FStar_Sealed.seal nb.sort);
                                   FStarC_Reflection_V2_Data.ppname =
                                     (nb.ppname)
                                 }))] t))) uu___2 uu___1 uu___
let (open_term :
  FStarC_Reflection_Types.binder ->
    term -> ((binder * term), unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun t ->
      let uu___ = open_binder b in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                 (Prims.of_int (113)) (Prims.of_int (22))
                 (Prims.of_int (113)) (Prims.of_int (35)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                 (Prims.of_int (114)) (Prims.of_int (2)) (Prims.of_int (114))
                 (Prims.of_int (33))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun bndr ->
              let uu___1 = open_term_with b bndr t in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (114)) (Prims.of_int (9))
                            (Prims.of_int (114)) (Prims.of_int (32)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (114)) (Prims.of_int (2))
                            (Prims.of_int (114)) (Prims.of_int (33)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 -> (bndr, uu___2))))) uu___1)
let (subst_comp : FStarC_Syntax_Syntax.subst_t -> comp -> comp) =
  fun s ->
    fun c ->
      FStarC_Reflection_V2_Builtins.inspect_comp
        (FStarC_Reflection_V2_Builtins.subst_comp s
           (FStarC_Reflection_V2_Builtins.pack_comp c))
let (open_comp :
  FStarC_Reflection_Types.binder ->
    comp -> ((binder * comp), unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun t ->
      let uu___ = FStarC_Tactics_V2_Builtins.fresh () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                 (Prims.of_int (121)) (Prims.of_int (10))
                 (Prims.of_int (121)) (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                 (Prims.of_int (121)) (Prims.of_int (21))
                 (Prims.of_int (138)) (Prims.of_int (12)))))
        (Obj.magic uu___)
        (fun n ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                ({
                   uniq = n;
                   ppname =
                     ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.ppname2);
                   sort =
                     ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.sort2);
                   qual =
                     ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.qual);
                   attrs =
                     ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.attrs)
                 },
                  (subst_comp
                     [FStarC_Syntax_Syntax.DB
                        (Prims.int_zero,
                          (FStarC_Reflection_V2_Builtins.pack_namedv
                             {
                               FStarC_Reflection_V2_Data.uniq = n;
                               FStarC_Reflection_V2_Data.sort =
                                 (FStar_Sealed.seal
                                    (FStarC_Reflection_V2_Builtins.inspect_binder
                                       b).FStarC_Reflection_V2_Data.sort2);
                               FStarC_Reflection_V2_Data.ppname =
                                 ((FStarC_Reflection_V2_Builtins.inspect_binder
                                     b).FStarC_Reflection_V2_Data.ppname2)
                             }))] t))))
let (open_comp_with :
  FStarC_Reflection_Types.binder ->
    binder -> comp -> (comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun b ->
           fun nb ->
             fun c ->
               Obj.magic
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       subst_comp
                         [FStarC_Syntax_Syntax.DB
                            (Prims.int_zero,
                              (FStarC_Reflection_V2_Builtins.pack_namedv
                                 {
                                   FStarC_Reflection_V2_Data.uniq = (nb.uniq);
                                   FStarC_Reflection_V2_Data.sort =
                                     (FStar_Sealed.seal nb.sort);
                                   FStarC_Reflection_V2_Data.ppname =
                                     (nb.ppname)
                                 }))] c))) uu___2 uu___1 uu___
let (open_term_simple :
  FStarC_Reflection_V2_Data.simple_binder ->
    term -> ((simple_binder * term), unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun t ->
      let uu___ = FStarC_Tactics_V2_Builtins.fresh () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                 (Prims.of_int (155)) (Prims.of_int (10))
                 (Prims.of_int (155)) (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                 (Prims.of_int (155)) (Prims.of_int (21))
                 (Prims.of_int (172)) (Prims.of_int (12)))))
        (Obj.magic uu___)
        (fun n ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                ({
                   uniq = n;
                   ppname =
                     ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.ppname2);
                   sort =
                     ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.sort2);
                   qual =
                     ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.qual);
                   attrs =
                     ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.attrs)
                 },
                  (FStarC_Reflection_V2_Builtins.subst_term
                     [FStarC_Syntax_Syntax.DB
                        (Prims.int_zero,
                          (FStarC_Reflection_V2_Builtins.pack_namedv
                             {
                               FStarC_Reflection_V2_Data.uniq = n;
                               FStarC_Reflection_V2_Data.sort =
                                 (FStar_Sealed.seal
                                    (FStarC_Reflection_V2_Builtins.inspect_binder
                                       b).FStarC_Reflection_V2_Data.sort2);
                               FStarC_Reflection_V2_Data.ppname =
                                 ((FStarC_Reflection_V2_Builtins.inspect_binder
                                     b).FStarC_Reflection_V2_Data.ppname2)
                             }))] t))))
let (open_comp_simple :
  FStarC_Reflection_V2_Data.simple_binder ->
    comp -> ((simple_binder * comp), unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun t ->
      let uu___ = FStarC_Tactics_V2_Builtins.fresh () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                 (Prims.of_int (176)) (Prims.of_int (10))
                 (Prims.of_int (176)) (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                 (Prims.of_int (176)) (Prims.of_int (21))
                 (Prims.of_int (193)) (Prims.of_int (12)))))
        (Obj.magic uu___)
        (fun n ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                ({
                   uniq = n;
                   ppname =
                     ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.ppname2);
                   sort =
                     ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.sort2);
                   qual =
                     ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.qual);
                   attrs =
                     ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.attrs)
                 },
                  (subst_comp
                     [FStarC_Syntax_Syntax.DB
                        (Prims.int_zero,
                          (FStarC_Reflection_V2_Builtins.pack_namedv
                             {
                               FStarC_Reflection_V2_Data.uniq = n;
                               FStarC_Reflection_V2_Data.sort =
                                 (FStar_Sealed.seal
                                    (FStarC_Reflection_V2_Builtins.inspect_binder
                                       b).FStarC_Reflection_V2_Data.sort2);
                               FStarC_Reflection_V2_Data.ppname =
                                 ((FStarC_Reflection_V2_Builtins.inspect_binder
                                     b).FStarC_Reflection_V2_Data.ppname2)
                             }))] t))))
let (close_term : binder -> term -> (FStarC_Reflection_Types.binder * term))
  =
  fun b ->
    fun t ->
      let nv = r_binder_to_namedv b in
      let t' =
        FStarC_Reflection_V2_Builtins.subst_term
          [FStarC_Syntax_Syntax.NM (nv, Prims.int_zero)] t in
      let b1 =
        FStarC_Reflection_V2_Builtins.pack_binder
          {
            FStarC_Reflection_V2_Data.sort2 = (b.sort);
            FStarC_Reflection_V2_Data.qual = (b.qual);
            FStarC_Reflection_V2_Data.attrs = (b.attrs);
            FStarC_Reflection_V2_Data.ppname2 = (b.ppname)
          } in
      (b1, t')
let _ =
  FStarC_Tactics_Native.register_plugin "FStar.Tactics.NamedView.close_term"
    (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Tactics.NamedView.close_term"
               (fun _ ->
                  (FStarC_Syntax_Embeddings.arrow_as_prim_step_2 e_binder
                     FStarC_Reflection_V2_Embeddings.e_term
                     (FStarC_Syntax_Embeddings.e_tuple2
                        FStarC_Reflection_V2_Embeddings.e_binder
                        FStarC_Reflection_V2_Embeddings.e_term) close_term
                     (FStarC_Ident.lid_of_str
                        "FStar.Tactics.NamedView.close_term") cb us) args))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Tactics.NamedView.close_term"
             (fun _ ->
                (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_2
                   (FStarC_TypeChecker_NBETerm.e_unsupported ())
                   FStarC_Reflection_V2_NBEEmbeddings.e_term
                   (FStarC_TypeChecker_NBETerm.e_tuple2
                      FStarC_Reflection_V2_NBEEmbeddings.e_binder
                      FStarC_Reflection_V2_NBEEmbeddings.e_term) close_term
                   (FStarC_Ident.lid_of_str
                      "FStar.Tactics.NamedView.close_term") cb us) args))
let (close_comp : binder -> comp -> (FStarC_Reflection_Types.binder * comp))
  =
  fun b ->
    fun t ->
      let nv = r_binder_to_namedv b in
      let t' = subst_comp [FStarC_Syntax_Syntax.NM (nv, Prims.int_zero)] t in
      let b1 =
        FStarC_Reflection_V2_Builtins.pack_binder
          {
            FStarC_Reflection_V2_Data.sort2 = (b.sort);
            FStarC_Reflection_V2_Data.qual = (b.qual);
            FStarC_Reflection_V2_Data.attrs = (b.attrs);
            FStarC_Reflection_V2_Data.ppname2 = (b.ppname)
          } in
      (b1, t')
let (close_term_simple :
  simple_binder -> term -> (FStarC_Reflection_V2_Data.simple_binder * term))
  =
  fun b ->
    fun t ->
      let nv = r_binder_to_namedv b in
      let t' =
        FStarC_Reflection_V2_Builtins.subst_term
          [FStarC_Syntax_Syntax.NM (nv, Prims.int_zero)] t in
      let bv1 =
        {
          FStarC_Reflection_V2_Data.sort2 = (b.sort);
          FStarC_Reflection_V2_Data.qual = (b.qual);
          FStarC_Reflection_V2_Data.attrs = (b.attrs);
          FStarC_Reflection_V2_Data.ppname2 = (b.ppname)
        } in
      let b1 = FStarC_Reflection_V2_Builtins.pack_binder bv1 in (b1, t')
let (close_comp_simple :
  simple_binder -> comp -> (FStarC_Reflection_V2_Data.simple_binder * comp))
  =
  fun b ->
    fun t ->
      let nv = r_binder_to_namedv b in
      let t' = subst_comp [FStarC_Syntax_Syntax.NM (nv, Prims.int_zero)] t in
      let bv1 =
        {
          FStarC_Reflection_V2_Data.sort2 = (b.sort);
          FStarC_Reflection_V2_Data.qual = (b.qual);
          FStarC_Reflection_V2_Data.attrs = (b.attrs);
          FStarC_Reflection_V2_Data.ppname2 = (b.ppname)
        } in
      let b1 = FStarC_Reflection_V2_Builtins.pack_binder bv1 in (b1, t')
let (r_subst_binder_sort :
  FStarC_Syntax_Syntax.subst_t ->
    FStarC_Reflection_Types.binder -> FStarC_Reflection_Types.binder)
  =
  fun s ->
    fun b ->
      let v = FStarC_Reflection_V2_Builtins.inspect_binder b in
      let v1 =
        {
          FStarC_Reflection_V2_Data.sort2 =
            (FStarC_Reflection_V2_Builtins.subst_term s
               v.FStarC_Reflection_V2_Data.sort2);
          FStarC_Reflection_V2_Data.qual = (v.FStarC_Reflection_V2_Data.qual);
          FStarC_Reflection_V2_Data.attrs =
            (v.FStarC_Reflection_V2_Data.attrs);
          FStarC_Reflection_V2_Data.ppname2 =
            (v.FStarC_Reflection_V2_Data.ppname2)
        } in
      FStarC_Reflection_V2_Builtins.pack_binder v1
let (subst_binder_sort : FStarC_Syntax_Syntax.subst_t -> binder -> binder) =
  fun s ->
    fun b ->
      {
        uniq = (b.uniq);
        ppname = (b.ppname);
        sort = (FStarC_Reflection_V2_Builtins.subst_term s b.sort);
        qual = (b.qual);
        attrs = (b.attrs)
      }
let rec (__open_term_n_aux :
  FStarC_Reflection_Types.binder Prims.list ->
    binder Prims.list ->
      FStarC_Syntax_Syntax.subst_t ->
        ((binder Prims.list * FStarC_Syntax_Syntax.subst_t), unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun bs ->
           fun nbs ->
             fun s ->
               match bs with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> (nbs, s))))
               | b::bs1 ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ =
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 -> r_subst_binder_sort s b)) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.NamedView.fst"
                                    (Prims.of_int (240)) (Prims.of_int (12))
                                    (Prims.of_int (240)) (Prims.of_int (35)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.NamedView.fst"
                                    (Prims.of_int (240)) (Prims.of_int (38))
                                    (Prims.of_int (243)) (Prims.of_int (62)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun b1 ->
                                 let uu___1 = open_binder b1 in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.NamedView.fst"
                                               (Prims.of_int (241))
                                               (Prims.of_int (12))
                                               (Prims.of_int (241))
                                               (Prims.of_int (25)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.NamedView.fst"
                                               (Prims.of_int (241))
                                               (Prims.of_int (28))
                                               (Prims.of_int (243))
                                               (Prims.of_int (62)))))
                                      (Obj.magic uu___1)
                                      (fun uu___2 ->
                                         (fun b2 ->
                                            let uu___2 =
                                              Obj.magic
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___3 ->
                                                      r_binder_to_namedv b2)) in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.NamedView.fst"
                                                          (Prims.of_int (242))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (242))
                                                          (Prims.of_int (33)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.NamedView.fst"
                                                          (Prims.of_int (243))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (243))
                                                          (Prims.of_int (62)))))
                                                 (Obj.magic uu___2)
                                                 (fun uu___3 ->
                                                    (fun nv ->
                                                       Obj.magic
                                                         (__open_term_n_aux
                                                            bs1 (b2 :: nbs)
                                                            ((FStarC_Syntax_Syntax.DB
                                                                (Prims.int_zero,
                                                                  nv)) ::
                                                            (FStar_Reflection_V2_Derived.shift_subst
                                                               Prims.int_one
                                                               s)))) uu___3)))
                                           uu___2))) uu___1)))) uu___2 uu___1
          uu___
let (open_term_n :
  FStarC_Reflection_Types.binder Prims.list ->
    term -> ((binder Prims.list * term), unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bs ->
    fun t ->
      let uu___ = __open_term_n_aux bs [] [] in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                 (Prims.of_int (247)) (Prims.of_int (15))
                 (Prims.of_int (247)) (Prims.of_int (41)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                 (Prims.of_int (246)) (Prims.of_int (76))
                 (Prims.of_int (248)) (Prims.of_int (34)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___2 ->
                match uu___1 with
                | (nbs, s) ->
                    ((FStar_List_Tot_Base.rev nbs),
                      (FStarC_Reflection_V2_Builtins.subst_term s t))))
let rec (open_term_n_with :
  FStarC_Reflection_Types.binder Prims.list ->
    binder Prims.list -> term -> (term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun bs ->
           fun nbs ->
             fun t ->
               match (bs, nbs) with
               | ([], []) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t)))
               | (b::bs1, nb::nbs1) ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ = open_term_n_with bs1 nbs1 t in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.NamedView.fst"
                                    (Prims.of_int (255)) (Prims.of_int (13))
                                    (Prims.of_int (255)) (Prims.of_int (38)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.NamedView.fst"
                                    (Prims.of_int (255)) (Prims.of_int (41))
                                    (Prims.of_int (257)) (Prims.of_int (7)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun t' ->
                                 let uu___1 = open_term_with b nb t' in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.NamedView.fst"
                                               (Prims.of_int (256))
                                               (Prims.of_int (14))
                                               (Prims.of_int (256))
                                               (Prims.of_int (36)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.NamedView.fst"
                                               (Prims.of_int (256))
                                               (Prims.of_int (8))
                                               (Prims.of_int (256))
                                               (Prims.of_int (11)))))
                                      (Obj.magic uu___1)
                                      (fun t'' ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 -> t'')))) uu___1)))
               | uu___ ->
                   Obj.magic
                     (Obj.repr (FStar_Tactics_Effect.raise LengthMismatch)))
          uu___2 uu___1 uu___
let (close_term_n :
  binder Prims.list ->
    term -> (FStarC_Reflection_Types.binder Prims.list * term))
  =
  fun bs ->
    fun t ->
      let rec aux bs1 cbs s =
        match bs1 with
        | [] -> (cbs, s)
        | b::bs2 ->
            let b1 = subst_binder_sort s b in
            let nv = r_binder_to_namedv b1 in
            let b2 = close_binder b1 in
            aux bs2 (b2 :: cbs)
              ((FStarC_Syntax_Syntax.NM (nv, Prims.int_zero)) ::
              (FStar_Reflection_V2_Derived.shift_subst Prims.int_one s)) in
      let uu___ = aux bs [] [] in
      match uu___ with
      | (cbs, s) ->
          ((FStar_List_Tot_Base.rev cbs),
            (FStarC_Reflection_V2_Builtins.subst_term s t))
let rec (open_term_n_simple :
  FStarC_Reflection_V2_Data.simple_binder Prims.list ->
    term ->
      ((simple_binder Prims.list * term), unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun bs ->
         fun t ->
           match bs with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ([], t))))
           | b::bs1 ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = open_term_n_simple bs1 t in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.NamedView.fst"
                                (Prims.of_int (279)) (Prims.of_int (18))
                                (Prims.of_int (279)) (Prims.of_int (41)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.NamedView.fst"
                                (Prims.of_int (278)) (Prims.of_int (12))
                                (Prims.of_int (281)) (Prims.of_int (18)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             match uu___1 with
                             | (bs', t') ->
                                 let uu___2 = open_term_simple b t' in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.NamedView.fst"
                                               (Prims.of_int (280))
                                               (Prims.of_int (18))
                                               (Prims.of_int (280))
                                               (Prims.of_int (39)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.NamedView.fst"
                                               (Prims.of_int (279))
                                               (Prims.of_int (44))
                                               (Prims.of_int (281))
                                               (Prims.of_int (18)))))
                                      (Obj.magic uu___2)
                                      (fun uu___3 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 ->
                                              match uu___3 with
                                              | (b', t'') ->
                                                  ((b' :: bs'), t'')))))
                            uu___1)))) uu___1 uu___
let rec (close_term_n_simple :
  simple_binder Prims.list ->
    term -> (FStarC_Reflection_V2_Data.simple_binder Prims.list * term))
  =
  fun bs ->
    fun t ->
      match bs with
      | [] -> ([], t)
      | b::bs1 ->
          let uu___ = close_term_n_simple bs1 t in
          (match uu___ with
           | (bs', t') ->
               let uu___1 = close_term_simple b t' in
               (match uu___1 with | (b', t'') -> ((b' :: bs'), t'')))
let rec (open_pat :
  FStarC_Reflection_V2_Data.pattern ->
    FStarC_Syntax_Syntax.subst_t ->
      ((pattern * FStarC_Syntax_Syntax.subst_t), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun p ->
         fun s ->
           match p with
           | FStarC_Reflection_V2_Data.Pat_Constant c ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> ((Pat_Constant { c }), s))))
           | FStarC_Reflection_V2_Data.Pat_Var (ssort, n) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = FStarC_Tactics_Unseal.unseal ssort in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.NamedView.fst"
                                (Prims.of_int (299)) (Prims.of_int (15))
                                (Prims.of_int (299)) (Prims.of_int (27)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.NamedView.fst"
                                (Prims.of_int (299)) (Prims.of_int (30))
                                (Prims.of_int (308)) (Prims.of_int (65)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun sort ->
                             let uu___1 =
                               Obj.magic
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       FStarC_Reflection_V2_Builtins.subst_term
                                         s sort)) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.NamedView.fst"
                                           (Prims.of_int (300))
                                           (Prims.of_int (15))
                                           (Prims.of_int (300))
                                           (Prims.of_int (32)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.NamedView.fst"
                                           (Prims.of_int (300))
                                           (Prims.of_int (35))
                                           (Prims.of_int (308))
                                           (Prims.of_int (65)))))
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun sort1 ->
                                        let uu___2 =
                                          let uu___3 =
                                            FStarC_Tactics_V2_Builtins.fresh
                                              () in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.NamedView.fst"
                                                     (Prims.of_int (302))
                                                     (Prims.of_int (13))
                                                     (Prims.of_int (302))
                                                     (Prims.of_int (20)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.NamedView.fst"
                                                     (Prims.of_int (302))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (304))
                                                     (Prims.of_int (17)))))
                                            (Obj.magic uu___3)
                                            (fun uu___4 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___5 ->
                                                    {
                                                      FStarC_Reflection_V2_Data.uniq
                                                        = uu___4;
                                                      FStarC_Reflection_V2_Data.sort
                                                        =
                                                        (FStar_Sealed.seal
                                                           sort1);
                                                      FStarC_Reflection_V2_Data.ppname
                                                        = n
                                                    })) in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.NamedView.fst"
                                                      (Prims.of_int (302))
                                                      (Prims.of_int (6))
                                                      (Prims.of_int (304))
                                                      (Prims.of_int (17)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.NamedView.fst"
                                                      (Prims.of_int (308))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (308))
                                                      (Prims.of_int (65)))))
                                             (Obj.magic uu___2)
                                             (fun nvv ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___3 ->
                                                     ((Pat_Var
                                                         {
                                                           v = nvv;
                                                           sort1 =
                                                             (FStar_Sealed.seal
                                                                sort1)
                                                         }),
                                                       ((FStarC_Syntax_Syntax.DB
                                                           (Prims.int_zero,
                                                             (FStarC_Reflection_V2_Builtins.pack_namedv
                                                                nvv))) ::
                                                       (FStar_Reflection_V2_Derived.shift_subst
                                                          Prims.int_one s)))))))
                                       uu___2))) uu___1)))
           | FStarC_Reflection_V2_Data.Pat_Cons (head, univs, subpats) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       FStar_Tactics_Util.fold_left
                         (fun uu___1 ->
                            fun uu___2 ->
                              match (uu___1, uu___2) with
                              | ((pats, s1), (pat, b)) ->
                                  let uu___3 = open_pat pat s1 in
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.NamedView.fst"
                                             (Prims.of_int (312))
                                             (Prims.of_int (38))
                                             (Prims.of_int (312))
                                             (Prims.of_int (52)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.NamedView.fst"
                                             (Prims.of_int (311))
                                             (Prims.of_int (55))
                                             (Prims.of_int (313))
                                             (Prims.of_int (43)))))
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___5 ->
                                            match uu___4 with
                                            | (pat1, s') ->
                                                (((pat1, b) :: pats), s'))))
                         ([], s) subpats in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.NamedView.fst"
                                (Prims.of_int (311)) (Prims.of_int (21))
                                (Prims.of_int (314)) (Prims.of_int (38)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.NamedView.fst"
                                (Prims.of_int (310)) (Prims.of_int (36))
                                (Prims.of_int (317)) (Prims.of_int (57)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               match uu___1 with
                               | (subpats1, s1) ->
                                   ((Pat_Cons
                                       {
                                         head;
                                         univs;
                                         subpats =
                                           (FStar_List_Tot_Base.rev subpats1)
                                       }), s1)))))
           | FStarC_Reflection_V2_Data.Pat_Dot_Term
               (FStar_Pervasives_Native.None) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          ((Pat_Dot_Term { t = FStar_Pervasives_Native.None }),
                            s))))
           | FStarC_Reflection_V2_Data.Pat_Dot_Term
               (FStar_Pervasives_Native.Some t) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          ((Pat_Dot_Term
                              {
                                t =
                                  (FStar_Pervasives_Native.Some
                                     (FStarC_Reflection_V2_Builtins.subst_term
                                        s t))
                              }), s))))) uu___1 uu___
let (open_branch :
  FStarC_Reflection_V2_Data.branch ->
    (branch, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    let uu___ =
      Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> b)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
               (Prims.of_int (328)) (Prims.of_int (17)) (Prims.of_int (328))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
               (Prims.of_int (327)) (Prims.of_int (45)) (Prims.of_int (331))
               (Prims.of_int (11))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | (pat, t) ->
                let uu___2 = open_pat pat [] in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.NamedView.fst"
                              (Prims.of_int (329)) (Prims.of_int (15))
                              (Prims.of_int (329)) (Prims.of_int (30)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.NamedView.fst"
                              (Prims.of_int (328)) (Prims.of_int (21))
                              (Prims.of_int (331)) (Prims.of_int (11)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___4 ->
                             match uu___3 with
                             | (pat1, s) ->
                                 (pat1,
                                   (FStarC_Reflection_V2_Builtins.subst_term
                                      s t)))))) uu___1)
let rec (close_pat :
  pattern ->
    FStarC_Syntax_Syntax.subst_t ->
      (FStarC_Reflection_V2_Data.pattern * FStarC_Syntax_Syntax.subst_t))
  =
  fun p ->
    fun s ->
      match p with
      | Pat_Constant { c;_} ->
          ((FStarC_Reflection_V2_Data.Pat_Constant c), s)
      | Pat_Var { v; sort1 = sort;_} ->
          let nv = FStarC_Reflection_V2_Builtins.pack_namedv v in
          let s1 = (FStarC_Syntax_Syntax.NM (nv, Prims.int_zero)) ::
            (FStar_Reflection_V2_Derived.shift_subst Prims.int_one s) in
          ((FStarC_Reflection_V2_Data.Pat_Var
              (sort, (v.FStarC_Reflection_V2_Data.ppname))), s1)
      | Pat_Cons { head; univs; subpats;_} ->
          let uu___ =
            FStar_List_Tot_Base.fold_left
              (fun uu___1 ->
                 fun uu___2 ->
                   match (uu___1, uu___2) with
                   | ((pats, s1), (pat, b)) ->
                       let uu___3 = close_pat pat s1 in
                       (match uu___3 with
                        | (pat1, s') -> (((pat1, b) :: pats), s'))) ([], s)
              subpats in
          (match uu___ with
           | (subpats1, s1) ->
               let subpats2 = FStar_List_Tot_Base.rev subpats1 in
               ((FStarC_Reflection_V2_Data.Pat_Cons (head, univs, subpats2)),
                 s1))
      | Pat_Dot_Term { t = FStar_Pervasives_Native.None;_} ->
          ((FStarC_Reflection_V2_Data.Pat_Dot_Term
              FStar_Pervasives_Native.None), s)
      | Pat_Dot_Term { t = FStar_Pervasives_Native.Some t;_} ->
          let t1 = FStarC_Reflection_V2_Builtins.subst_term s t in
          ((FStarC_Reflection_V2_Data.Pat_Dot_Term
              (FStar_Pervasives_Native.Some t1)), s)
let (close_branch : branch -> FStarC_Reflection_V2_Data.branch) =
  fun b ->
    let uu___ = b in
    match uu___ with
    | (pat, t) ->
        let uu___1 = close_pat pat [] in
        (match uu___1 with
         | (pat1, s) ->
             let t' = FStarC_Reflection_V2_Builtins.subst_term s t in
             (pat1, t'))
let (open_match_returns_ascription :
  FStarC_Syntax_Syntax.match_returns_ascription ->
    (match_returns_ascription, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun mra ->
    let uu___ =
      Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> mra)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
               (Prims.of_int (375)) (Prims.of_int (32)) (Prims.of_int (375))
               (Prims.of_int (35)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
               (Prims.of_int (374)) (Prims.of_int (101)) (Prims.of_int (389))
               (Prims.of_int (26))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | (b, (ct, topt, use_eq)) ->
                let uu___2 = open_binder b in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.NamedView.fst"
                              (Prims.of_int (376)) (Prims.of_int (11))
                              (Prims.of_int (376)) (Prims.of_int (24)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.NamedView.fst"
                              (Prims.of_int (376)) (Prims.of_int (27))
                              (Prims.of_int (389)) (Prims.of_int (26)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun nb ->
                           let uu___3 =
                             match ct with
                             | FStar_Pervasives.Inl t ->
                                 let uu___4 = open_term_with b nb t in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.NamedView.fst"
                                            (Prims.of_int (378))
                                            (Prims.of_int (19))
                                            (Prims.of_int (378))
                                            (Prims.of_int (42)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.NamedView.fst"
                                            (Prims.of_int (378))
                                            (Prims.of_int (15))
                                            (Prims.of_int (378))
                                            (Prims.of_int (42)))))
                                   (Obj.magic uu___4)
                                   (fun uu___5 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___6 ->
                                           FStar_Pervasives.Inl uu___5))
                             | FStar_Pervasives.Inr c ->
                                 let uu___4 =
                                   Obj.magic
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___5 ->
                                           FStarC_Reflection_V2_Builtins.inspect_comp
                                             c)) in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.NamedView.fst"
                                            (Prims.of_int (380))
                                            (Prims.of_int (14))
                                            (Prims.of_int (380))
                                            (Prims.of_int (28)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.NamedView.fst"
                                            (Prims.of_int (380))
                                            (Prims.of_int (31))
                                            (Prims.of_int (382))
                                            (Prims.of_int (11)))))
                                   (Obj.magic uu___4)
                                   (fun uu___5 ->
                                      (fun c1 ->
                                         let uu___5 = open_comp_with b nb c1 in
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.NamedView.fst"
                                                       (Prims.of_int (381))
                                                       (Prims.of_int (14))
                                                       (Prims.of_int (381))
                                                       (Prims.of_int (35)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.NamedView.fst"
                                                       (Prims.of_int (382))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (382))
                                                       (Prims.of_int (11)))))
                                              (Obj.magic uu___5)
                                              (fun c2 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___6 ->
                                                      FStar_Pervasives.Inr c2))))
                                        uu___5) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.NamedView.fst"
                                         (Prims.of_int (377))
                                         (Prims.of_int (11))
                                         (Prims.of_int (382))
                                         (Prims.of_int (11)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.NamedView.fst"
                                         (Prims.of_int (383))
                                         (Prims.of_int (4))
                                         (Prims.of_int (389))
                                         (Prims.of_int (26)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   (fun ct1 ->
                                      let uu___4 =
                                        match topt with
                                        | FStar_Pervasives_Native.None ->
                                            Obj.magic
                                              (Obj.repr
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___5 ->
                                                       FStar_Pervasives_Native.None)))
                                        | FStar_Pervasives_Native.Some t ->
                                            Obj.magic
                                              (Obj.repr
                                                 (let uu___5 =
                                                    open_term_with b nb t in
                                                  FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.NamedView.fst"
                                                             (Prims.of_int (387))
                                                             (Prims.of_int (21))
                                                             (Prims.of_int (387))
                                                             (Prims.of_int (44)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.NamedView.fst"
                                                             (Prims.of_int (387))
                                                             (Prims.of_int (16))
                                                             (Prims.of_int (387))
                                                             (Prims.of_int (44)))))
                                                    (Obj.magic uu___5)
                                                    (fun uu___6 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___7 ->
                                                            FStar_Pervasives_Native.Some
                                                              uu___6)))) in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.NamedView.fst"
                                                    (Prims.of_int (385))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (387))
                                                    (Prims.of_int (44)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.NamedView.fst"
                                                    (Prims.of_int (389))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (389))
                                                    (Prims.of_int (26)))))
                                           (Obj.magic uu___4)
                                           (fun topt1 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___5 ->
                                                   (nb, (ct1, topt1, use_eq))))))
                                     uu___4))) uu___3))) uu___1)
let (close_match_returns_ascription :
  match_returns_ascription -> FStarC_Syntax_Syntax.match_returns_ascription)
  =
  fun mra ->
    let uu___ = mra in
    match uu___ with
    | (nb, (ct, topt, use_eq)) ->
        let b = close_binder nb in
        let ct1 =
          match ct with
          | FStar_Pervasives.Inl t ->
              FStar_Pervasives.Inl
                (FStar_Pervasives_Native.snd (close_term nb t))
          | FStar_Pervasives.Inr c ->
              let uu___1 = close_comp nb c in
              (match uu___1 with
               | (uu___2, c1) ->
                   let c2 = FStarC_Reflection_V2_Builtins.pack_comp c1 in
                   FStar_Pervasives.Inr c2) in
        let topt1 =
          match topt with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some t ->
              FStar_Pervasives_Native.Some
                (FStar_Pervasives_Native.snd (close_term nb t)) in
        (b, (ct1, topt1, use_eq))
let (open_view :
  FStarC_Reflection_V2_Data.term_view ->
    (named_term_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun tv ->
       match tv with
       | FStarC_Reflection_V2_Data.Tv_Var v ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Tv_Var (FStarC_Reflection_V2_Builtins.inspect_namedv v))))
       | FStarC_Reflection_V2_Data.Tv_BVar v ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Tv_BVar (FStarC_Reflection_V2_Builtins.inspect_bv v))))
       | FStarC_Reflection_V2_Data.Tv_FVar v ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> Tv_FVar v)))
       | FStarC_Reflection_V2_Data.Tv_UInst (v, us) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> Tv_UInst (v, us))))
       | FStarC_Reflection_V2_Data.Tv_App (hd, a) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> Tv_App (hd, a))))
       | FStarC_Reflection_V2_Data.Tv_Type u ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> Tv_Type u)))
       | FStarC_Reflection_V2_Data.Tv_Const c ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> Tv_Const c)))
       | FStarC_Reflection_V2_Data.Tv_Uvar (n, ctx_uvar_and_subst) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> Tv_Uvar (n, ctx_uvar_and_subst))))
       | FStarC_Reflection_V2_Data.Tv_AscribedT (e, t, tac, use_eq) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> Tv_AscribedT (e, t, tac, use_eq))))
       | FStarC_Reflection_V2_Data.Tv_AscribedC (e, c, tac, use_eq) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Tv_AscribedC
                        (e, (FStarC_Reflection_V2_Builtins.inspect_comp c),
                          tac, use_eq))))
       | FStarC_Reflection_V2_Data.Tv_Unknown ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> Tv_Unknown)))
       | FStarC_Reflection_V2_Data.Tv_Unsupp ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> Tv_Unsupp)))
       | FStarC_Reflection_V2_Data.Tv_Abs (b, body) ->
           Obj.magic
             (Obj.repr
                (let uu___ = open_term b body in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (431)) (Prims.of_int (19))
                            (Prims.of_int (431)) (Prims.of_int (35)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (430)) (Prims.of_int (23))
                            (Prims.of_int (432)) (Prims.of_int (18)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           match uu___1 with
                           | (nb, body1) -> Tv_Abs (nb, body1)))))
       | FStarC_Reflection_V2_Data.Tv_Arrow (b, c) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   open_comp b (FStarC_Reflection_V2_Builtins.inspect_comp c) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (435)) (Prims.of_int (16))
                            (Prims.of_int (435)) (Prims.of_int (44)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (434)) (Prims.of_int (22))
                            (Prims.of_int (436)) (Prims.of_int (17)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           match uu___1 with | (nb, c1) -> Tv_Arrow (nb, c1)))))
       | FStarC_Reflection_V2_Data.Tv_Refine (b, ref) ->
           Obj.magic
             (Obj.repr
                (let uu___ = open_term_simple b ref in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (439)) (Prims.of_int (18))
                            (Prims.of_int (439)) (Prims.of_int (40)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (438)) (Prims.of_int (25))
                            (Prims.of_int (440)) (Prims.of_int (20)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           match uu___1 with
                           | (nb, ref1) -> Tv_Refine (nb, ref1)))))
       | FStarC_Reflection_V2_Data.Tv_Let (recf, attrs, b, def, body) ->
           Obj.magic
             (Obj.repr
                (let uu___ = open_term_simple b body in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (443)) (Prims.of_int (19))
                            (Prims.of_int (443)) (Prims.of_int (42)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (442)) (Prims.of_int (38))
                            (Prims.of_int (449)) (Prims.of_int (33)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           match uu___1 with
                           | (nb, body1) ->
                               Tv_Let
                                 (recf, attrs, nb,
                                   (if recf
                                    then
                                      FStarC_Reflection_V2_Builtins.subst_term
                                        [FStarC_Syntax_Syntax.DB
                                           (Prims.int_zero,
                                             (r_binder_to_namedv nb))] def
                                    else def), body1)))))
       | FStarC_Reflection_V2_Data.Tv_Match (scrutinee, ret, brs) ->
           Obj.magic
             (Obj.repr
                (let uu___ = FStar_Tactics_Util.map open_branch brs in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (452)) (Prims.of_int (14))
                            (Prims.of_int (452)) (Prims.of_int (33)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (452)) (Prims.of_int (36))
                            (Prims.of_int (454)) (Prims.of_int (30)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      (fun brs1 ->
                         let uu___1 =
                           FStar_Tactics_Util.map_opt
                             open_match_returns_ascription ret in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.NamedView.fst"
                                       (Prims.of_int (453))
                                       (Prims.of_int (14))
                                       (Prims.of_int (453))
                                       (Prims.of_int (55)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.NamedView.fst"
                                       (Prims.of_int (454))
                                       (Prims.of_int (4))
                                       (Prims.of_int (454))
                                       (Prims.of_int (30)))))
                              (Obj.magic uu___1)
                              (fun ret1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 ->
                                      Tv_Match (scrutinee, ret1, brs1)))))
                        uu___1)))) uu___
let (close_view : named_term_view -> FStarC_Reflection_V2_Data.term_view) =
  fun tv ->
    match tv with
    | Tv_Var v ->
        FStarC_Reflection_V2_Data.Tv_Var
          (FStarC_Reflection_V2_Builtins.pack_namedv v)
    | Tv_BVar v ->
        FStarC_Reflection_V2_Data.Tv_BVar
          (FStarC_Reflection_V2_Builtins.pack_bv v)
    | Tv_FVar v -> FStarC_Reflection_V2_Data.Tv_FVar v
    | Tv_UInst (v, us) -> FStarC_Reflection_V2_Data.Tv_UInst (v, us)
    | Tv_App (hd, a) -> FStarC_Reflection_V2_Data.Tv_App (hd, a)
    | Tv_Type u -> FStarC_Reflection_V2_Data.Tv_Type u
    | Tv_Const c -> FStarC_Reflection_V2_Data.Tv_Const c
    | Tv_Uvar (n, ctx_uvar_and_subst) ->
        FStarC_Reflection_V2_Data.Tv_Uvar (n, ctx_uvar_and_subst)
    | Tv_AscribedT (e, t, tac, use_eq) ->
        FStarC_Reflection_V2_Data.Tv_AscribedT (e, t, tac, use_eq)
    | Tv_AscribedC (e, c, tac, use_eq) ->
        FStarC_Reflection_V2_Data.Tv_AscribedC
          (e, (FStarC_Reflection_V2_Builtins.pack_comp c), tac, use_eq)
    | Tv_Unknown -> FStarC_Reflection_V2_Data.Tv_Unknown
    | Tv_Unsupp -> FStarC_Reflection_V2_Data.Tv_Unsupp
    | Tv_Abs (nb, body) ->
        let uu___ = close_term nb body in
        (match uu___ with
         | (b, body1) -> FStarC_Reflection_V2_Data.Tv_Abs (b, body1))
    | Tv_Arrow (nb, c) ->
        let uu___ = close_comp nb c in
        (match uu___ with
         | (b, c1) ->
             let c2 = FStarC_Reflection_V2_Builtins.pack_comp c1 in
             FStarC_Reflection_V2_Data.Tv_Arrow (b, c2))
    | Tv_Refine (nb, ref) ->
        let uu___ = close_term_simple nb ref in
        (match uu___ with
         | (b, ref1) -> FStarC_Reflection_V2_Data.Tv_Refine (b, ref1))
    | Tv_Let (recf, attrs, nb, def, body) ->
        let def1 =
          if recf
          then
            FStarC_Reflection_V2_Builtins.subst_term
              [FStarC_Syntax_Syntax.NM
                 ((r_binder_to_namedv nb), Prims.int_zero)] def
          else def in
        let uu___ = close_term_simple nb body in
        (match uu___ with
         | (b, body1) ->
             FStarC_Reflection_V2_Data.Tv_Let (recf, attrs, b, def1, body1))
    | Tv_Match (scrutinee, ret, brs) ->
        let brs1 = FStar_List_Tot_Base.map close_branch brs in
        let ret1 =
          match ret with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some asc ->
              FStar_Pervasives_Native.Some
                (close_match_returns_ascription asc) in
        FStarC_Reflection_V2_Data.Tv_Match (scrutinee, ret1, brs1)
let (inspect : term -> (named_term_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStarC_Tactics_V2_Builtins.compress t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
               (Prims.of_int (511)) (Prims.of_int (10)) (Prims.of_int (511))
               (Prims.of_int (20)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
               (Prims.of_int (511)) (Prims.of_int (23)) (Prims.of_int (513))
               (Prims.of_int (14))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun t1 ->
            let uu___1 =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 -> FStarC_Reflection_V2_Builtins.inspect_ln t1)) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                          (Prims.of_int (512)) (Prims.of_int (11))
                          (Prims.of_int (512)) (Prims.of_int (23)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                          (Prims.of_int (513)) (Prims.of_int (2))
                          (Prims.of_int (513)) (Prims.of_int (14)))))
                 (Obj.magic uu___1)
                 (fun uu___2 -> (fun tv -> Obj.magic (open_view tv)) uu___2)))
           uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.NamedView.inspect"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.NamedView.inspect (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 inspect)
               FStarC_Reflection_V2_Embeddings.e_term e_named_term_view psc
               ncb us args)
let (pack : named_term_view -> term) =
  fun tv ->
    let tv1 = close_view tv in FStarC_Reflection_V2_Builtins.pack_ln tv1
let _ =
  FStarC_Tactics_Native.register_plugin "FStar.Tactics.NamedView.pack"
    Prims.int_one
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Tactics.NamedView.pack"
               (fun _ ->
                  (FStarC_Syntax_Embeddings.arrow_as_prim_step_1
                     e_named_term_view FStarC_Reflection_V2_Embeddings.e_term
                     pack
                     (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.pack")
                     cb us) args))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap "FStar.Tactics.NamedView.pack"
             (fun _ ->
                (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_1
                   (FStarC_TypeChecker_NBETerm.e_unsupported ())
                   FStarC_Reflection_V2_NBEEmbeddings.e_term pack
                   (FStarC_Ident.lid_of_str "FStar.Tactics.NamedView.pack")
                   cb us) args))
let (open_univ_s :
  FStarC_Reflection_Types.univ_name Prims.list ->
    ((univ_name Prims.list * FStarC_Syntax_Syntax.subst_t), unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun us ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_List_Tot_Base.length us)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
               (Prims.of_int (522)) (Prims.of_int (10)) (Prims.of_int (522))
               (Prims.of_int (28)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
               (Prims.of_int (522)) (Prims.of_int (31)) (Prims.of_int (524))
               (Prims.of_int (43))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun n ->
            let uu___1 =
              FStar_Tactics_Util.mapi
                (fun uu___3 ->
                   fun uu___2 ->
                     (fun i ->
                        fun u ->
                          Obj.magic
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 ->
                                  FStarC_Syntax_Syntax.UN
                                    (((n - Prims.int_one) - i),
                                      (FStarC_Reflection_V2_Builtins.pack_universe
                                         (FStarC_Reflection_V2_Data.Uv_Name u))))))
                       uu___3 uu___2) us in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                          (Prims.of_int (523)) (Prims.of_int (10))
                          (Prims.of_int (523)) (Prims.of_int (73)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                          (Prims.of_int (524)) (Prims.of_int (2))
                          (Prims.of_int (524)) (Prims.of_int (43)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun s ->
                       let uu___2 =
                         FStar_Tactics_Util.map
                           (fun uu___3 ->
                              (fun i ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___3 ->
                                         FStarC_Reflection_V2_Builtins.inspect_ident
                                           i))) uu___3) us in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.NamedView.fst"
                                     (Prims.of_int (524)) (Prims.of_int (2))
                                     (Prims.of_int (524)) (Prims.of_int (40)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.NamedView.fst"
                                     (Prims.of_int (524)) (Prims.of_int (2))
                                     (Prims.of_int (524)) (Prims.of_int (43)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___4 -> (uu___3, s))))) uu___2)))
           uu___1)
let (close_univ_s :
  univ_name Prims.list ->
    (FStarC_Reflection_Types.univ_name Prims.list *
      FStarC_Syntax_Syntax.subst_t))
  =
  fun us ->
    let n = FStar_List_Tot_Base.length us in
    let us1 =
      FStar_List_Tot_Base.map
        (fun i -> FStarC_Reflection_V2_Builtins.pack_ident i) us in
    let s =
      FStar_List_Tot_Base.mapi
        (fun i ->
           fun u -> FStarC_Syntax_Syntax.UD (u, ((n - i) - Prims.int_one)))
        us1 in
    (us1, s)
let (open_lb :
  FStarC_Reflection_Types.letbinding ->
    (letbinding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun lb ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStarC_Reflection_V2_Builtins.inspect_lb lb)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
               (Prims.of_int (535)) (Prims.of_int (39)) (Prims.of_int (535))
               (Prims.of_int (52)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
               (Prims.of_int (534)) (Prims.of_int (50)) (Prims.of_int (539))
               (Prims.of_int (34))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | { FStarC_Reflection_V2_Data.lb_fv = lb_fv;
                FStarC_Reflection_V2_Data.lb_us = lb_us;
                FStarC_Reflection_V2_Data.lb_typ = lb_typ;
                FStarC_Reflection_V2_Data.lb_def = lb_def;_} ->
                let uu___2 = open_univ_s lb_us in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.NamedView.fst"
                              (Prims.of_int (536)) (Prims.of_int (17))
                              (Prims.of_int (536)) (Prims.of_int (34)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.NamedView.fst"
                              (Prims.of_int (535)) (Prims.of_int (55))
                              (Prims.of_int (539)) (Prims.of_int (34)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___4 ->
                             match uu___3 with
                             | (lb_us1, s) ->
                                 {
                                   lb_fv;
                                   lb_us = lb_us1;
                                   lb_typ =
                                     (FStarC_Reflection_V2_Builtins.subst_term
                                        s lb_typ);
                                   lb_def =
                                     (FStarC_Reflection_V2_Builtins.subst_term
                                        s lb_def)
                                 })))) uu___1)
let (close_lb : letbinding -> FStarC_Reflection_Types.letbinding) =
  fun lb ->
    let uu___ = lb in
    match uu___ with
    | { lb_fv; lb_us; lb_typ; lb_def;_} ->
        let uu___1 = close_univ_s lb_us in
        (match uu___1 with
         | (lb_us1, s) ->
             let lb_typ1 = FStarC_Reflection_V2_Builtins.subst_term s lb_typ in
             let lb_def1 = FStarC_Reflection_V2_Builtins.subst_term s lb_def in
             FStarC_Reflection_V2_Builtins.pack_lb
               {
                 FStarC_Reflection_V2_Data.lb_fv = lb_fv;
                 FStarC_Reflection_V2_Data.lb_us = lb_us1;
                 FStarC_Reflection_V2_Data.lb_typ = lb_typ1;
                 FStarC_Reflection_V2_Data.lb_def = lb_def1
               })
let (subst_r_binders :
  FStarC_Syntax_Syntax.subst_t ->
    FStarC_Reflection_Types.binder Prims.list ->
      FStarC_Reflection_Types.binder Prims.list)
  =
  fun s ->
    fun bs ->
      FStar_List_Tot_Base.mapi
        (fun i ->
           fun b ->
             r_subst_binder_sort
               (FStar_Reflection_V2_Derived.shift_subst i s) b) bs
let rec (open_n_binders_from_arrow :
  binders -> term -> (term, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___1 ->
    fun uu___ ->
      (fun bs ->
         fun t ->
           match bs with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t)))
           | b::bs1 ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = inspect t in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.NamedView.fst"
                                (Prims.of_int (558)) (Prims.of_int (10))
                                (Prims.of_int (558)) (Prims.of_int (19)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.NamedView.fst"
                                (Prims.of_int (558)) (Prims.of_int (4))
                                (Prims.of_int (562)) (Prims.of_int (33)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             match uu___1 with
                             | Tv_Arrow
                                 (b', FStarC_Reflection_V2_Data.C_Total t')
                                 ->
                                 Obj.magic
                                   (Obj.repr
                                      (let uu___2 =
                                         Obj.magic
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___3 ->
                                                 FStarC_Reflection_V2_Builtins.subst_term
                                                   [FStarC_Syntax_Syntax.NT
                                                      ((r_binder_to_namedv b'),
                                                        (pack
                                                           (Tv_Var
                                                              (FStarC_Reflection_V2_Builtins.inspect_namedv
                                                                 (r_binder_to_namedv
                                                                    b)))))]
                                                   t')) in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.NamedView.fst"
                                                  (Prims.of_int (560))
                                                  (Prims.of_int (15))
                                                  (Prims.of_int (560))
                                                  (Prims.of_int (113)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.NamedView.fst"
                                                  (Prims.of_int (561))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (561))
                                                  (Prims.of_int (37)))))
                                         (Obj.magic uu___2)
                                         (fun uu___3 ->
                                            (fun t'1 ->
                                               Obj.magic
                                                 (open_n_binders_from_arrow
                                                    bs1 t'1)) uu___3)))
                             | uu___2 ->
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.raise
                                         NotEnoughBinders))) uu___1))))
        uu___1 uu___
let (open_sigelt_view :
  FStarC_Reflection_V2_Data.sigelt_view ->
    (named_sigelt_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun sv ->
       match sv with
       | FStarC_Reflection_V2_Data.Sg_Let (isrec, lbs) ->
           Obj.magic
             (Obj.repr
                (let uu___ = FStar_Tactics_Util.map open_lb lbs in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (568)) (Prims.of_int (14))
                            (Prims.of_int (568)) (Prims.of_int (29)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (570)) (Prims.of_int (4))
                            (Prims.of_int (570)) (Prims.of_int (25)))))
                   (Obj.magic uu___)
                   (fun lbs1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Sg_Let { isrec; lbs = lbs1 }))))
       | FStarC_Reflection_V2_Data.Sg_Inductive
           (nm, univs, params, typ, ctors) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   Obj.magic
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> FStar_List_Tot_Base.length params)) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (573)) (Prims.of_int (18))
                            (Prims.of_int (573)) (Prims.of_int (40)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (573)) (Prims.of_int (43))
                            (Prims.of_int (596)) (Prims.of_int (48)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      (fun nparams ->
                         let uu___1 = open_univ_s univs in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.NamedView.fst"
                                       (Prims.of_int (576))
                                       (Prims.of_int (19))
                                       (Prims.of_int (576))
                                       (Prims.of_int (36)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.NamedView.fst"
                                       (Prims.of_int (573))
                                       (Prims.of_int (43))
                                       (Prims.of_int (596))
                                       (Prims.of_int (48)))))
                              (Obj.magic uu___1)
                              (fun uu___2 ->
                                 (fun uu___2 ->
                                    match uu___2 with
                                    | (univs1, s) ->
                                        let uu___3 =
                                          Obj.magic
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___4 ->
                                                  subst_r_binders s params)) in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.NamedView.fst"
                                                      (Prims.of_int (577))
                                                      (Prims.of_int (17))
                                                      (Prims.of_int (577))
                                                      (Prims.of_int (41)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.NamedView.fst"
                                                      (Prims.of_int (577))
                                                      (Prims.of_int (44))
                                                      (Prims.of_int (596))
                                                      (Prims.of_int (48)))))
                                             (Obj.magic uu___3)
                                             (fun uu___4 ->
                                                (fun params1 ->
                                                   let uu___4 =
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___5 ->
                                                             FStarC_Reflection_V2_Builtins.subst_term
                                                               (FStar_Reflection_V2_Derived.shift_subst
                                                                  nparams s)
                                                               typ)) in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.NamedView.fst"
                                                                 (Prims.of_int (578))
                                                                 (Prims.of_int (14))
                                                                 (Prims.of_int (578))
                                                                 (Prims.of_int (52)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.NamedView.fst"
                                                                 (Prims.of_int (578))
                                                                 (Prims.of_int (55))
                                                                 (Prims.of_int (596))
                                                                 (Prims.of_int (48)))))
                                                        (Obj.magic uu___4)
                                                        (fun uu___5 ->
                                                           (fun typ1 ->
                                                              let uu___5 =
                                                                FStar_Tactics_Util.map
                                                                  (fun uu___6
                                                                    ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (nm1, ty)
                                                                    ->
                                                                    (nm1,
                                                                    (FStarC_Reflection_V2_Builtins.subst_term
                                                                    s ty)))))
                                                                    uu___6)
                                                                  ctors in
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (63)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (596))
                                                                    (Prims.of_int (48)))))
                                                                   (Obj.magic
                                                                    uu___5)
                                                                   (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    ctors1 ->
                                                                    let uu___6
                                                                    =
                                                                    open_term_n
                                                                    params1
                                                                    typ1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (596))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (params2,
                                                                    typ2) ->
                                                                    let uu___8
                                                                    =
                                                                    FStar_Tactics_Util.map
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (nm1, ty)
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    open_n_binders_from_arrow
                                                                    params2
                                                                    ty in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (591))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (591))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (592))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (592))
                                                                    (Prims.of_int (17)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun ty'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (nm1,
                                                                    ty'))))
                                                                    ctors1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (13)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (596))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (596))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    ctors2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Sg_Inductive
                                                                    {
                                                                    nm;
                                                                    univs1;
                                                                    params =
                                                                    params2;
                                                                    typ =
                                                                    typ2;
                                                                    ctors =
                                                                    ctors2
                                                                    }))))
                                                                    uu___7)))
                                                                    uu___6)))
                                                             uu___5))) uu___4)))
                                   uu___2))) uu___1)))
       | FStarC_Reflection_V2_Data.Sg_Val (nm, univs, typ) ->
           Obj.magic
             (Obj.repr
                (let uu___ = open_univ_s univs in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (599)) (Prims.of_int (19))
                            (Prims.of_int (599)) (Prims.of_int (36)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (598)) (Prims.of_int (29))
                            (Prims.of_int (601)) (Prims.of_int (27)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           match uu___1 with
                           | (univs1, s) ->
                               Sg_Val
                                 {
                                   nm1 = nm;
                                   univs2 = univs1;
                                   typ1 =
                                     (FStarC_Reflection_V2_Builtins.subst_term
                                        s typ)
                                 }))))
       | FStarC_Reflection_V2_Data.Unk ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> Unk))))
      uu___
let rec (mk_arr :
  binder Prims.list -> term -> (term, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___1 ->
    fun uu___ ->
      (fun args ->
         fun t ->
           match args with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t)))
           | a::args' ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       let uu___1 = mk_arr args' t in
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.NamedView.fst"
                                  (Prims.of_int (610)) (Prims.of_int (21))
                                  (Prims.of_int (610)) (Prims.of_int (37)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.NamedView.fst"
                                  (Prims.of_int (610)) (Prims.of_int (13))
                                  (Prims.of_int (610)) (Prims.of_int (37)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___3 ->
                                 FStarC_Reflection_V2_Data.C_Total uu___2)) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.NamedView.fst"
                                (Prims.of_int (610)) (Prims.of_int (13))
                                (Prims.of_int (610)) (Prims.of_int (37)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "dummy" Prims.int_zero
                                Prims.int_zero Prims.int_zero Prims.int_zero)))
                       (Obj.magic uu___)
                       (fun t' ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> pack (Tv_Arrow (a, t')))))))
        uu___1 uu___
let (close_sigelt_view :
  named_sigelt_view ->
    (FStarC_Reflection_V2_Data.sigelt_view, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun sv ->
       match sv with
       | Sg_Let { isrec; lbs;_} ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      FStarC_Reflection_V2_Data.Sg_Let
                        (isrec, (FStar_List_Tot_Base.map close_lb lbs)))))
       | Sg_Inductive { nm; univs1 = univs; params; typ; ctors;_} ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   Obj.magic
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> FStar_List_Tot_Base.length params)) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (621)) (Prims.of_int (18))
                            (Prims.of_int (621)) (Prims.of_int (40)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                            (Prims.of_int (621)) (Prims.of_int (43))
                            (Prims.of_int (640)) (Prims.of_int (45)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      (fun nparams ->
                         let uu___1 =
                           FStar_Tactics_Util.map
                             (fun uu___2 ->
                                match uu___2 with
                                | (nm1, ty) ->
                                    let uu___3 = mk_arr params ty in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.NamedView.fst"
                                               (Prims.of_int (626))
                                               (Prims.of_int (22))
                                               (Prims.of_int (626))
                                               (Prims.of_int (38)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.NamedView.fst"
                                               (Prims.of_int (627))
                                               (Prims.of_int (12))
                                               (Prims.of_int (627))
                                               (Prims.of_int (19)))))
                                      (Obj.magic uu___3)
                                      (fun ty' ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 -> (nm1, ty')))) ctors in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.NamedView.fst"
                                       (Prims.of_int (625))
                                       (Prims.of_int (8))
                                       (Prims.of_int (628))
                                       (Prims.of_int (13)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.NamedView.fst"
                                       (Prims.of_int (629))
                                       (Prims.of_int (6))
                                       (Prims.of_int (640))
                                       (Prims.of_int (45)))))
                              (Obj.magic uu___1)
                              (fun uu___2 ->
                                 (fun ctors1 ->
                                    let uu___2 =
                                      Obj.magic
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 ->
                                              close_term_n params typ)) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.NamedView.fst"
                                                  (Prims.of_int (632))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (632))
                                                  (Prims.of_int (45)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.NamedView.fst"
                                                  (Prims.of_int (629))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (640))
                                                  (Prims.of_int (45)))))
                                         (Obj.magic uu___2)
                                         (fun uu___3 ->
                                            (fun uu___3 ->
                                               match uu___3 with
                                               | (params1, typ1) ->
                                                   let uu___4 =
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___5 ->
                                                             close_univ_s
                                                               univs)) in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.NamedView.fst"
                                                                 (Prims.of_int (635))
                                                                 (Prims.of_int (19))
                                                                 (Prims.of_int (635))
                                                                 (Prims.of_int (37)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.NamedView.fst"
                                                                 (Prims.of_int (632))
                                                                 (Prims.of_int (48))
                                                                 (Prims.of_int (640))
                                                                 (Prims.of_int (45)))))
                                                        (Obj.magic uu___4)
                                                        (fun uu___5 ->
                                                           (fun uu___5 ->
                                                              match uu___5
                                                              with
                                                              | (univs1, s)
                                                                  ->
                                                                  let uu___6
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    subst_r_binders
                                                                    s params1)) in
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (636))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (636))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (636))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    params2
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStarC_Reflection_V2_Builtins.subst_term
                                                                    (FStar_Reflection_V2_Derived.shift_subst
                                                                    nparams s)
                                                                    typ1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun typ2
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    FStar_Tactics_Util.map
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (nm1, ty)
                                                                    ->
                                                                    (nm1,
                                                                    (FStarC_Reflection_V2_Builtins.subst_term
                                                                    s ty)))))
                                                                    uu___9)
                                                                    ctors1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (638))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (638))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    ctors2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStarC_Reflection_V2_Data.Sg_Inductive
                                                                    (nm,
                                                                    univs1,
                                                                    params2,
                                                                    typ2,
                                                                    ctors2)))))
                                                                    uu___8)))
                                                                    uu___7)))
                                                             uu___5))) uu___3)))
                                   uu___2))) uu___1)))
       | Sg_Val { nm1 = nm; univs2 = univs; typ1 = typ;_} ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      match close_univ_s univs with
                      | (univs1, s) ->
                          FStarC_Reflection_V2_Data.Sg_Val
                            (nm, univs1,
                              (FStarC_Reflection_V2_Builtins.subst_term s typ))))))
      uu___
let (inspect_sigelt :
  FStarC_Reflection_Types.sigelt ->
    (named_sigelt_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStarC_Reflection_V2_Builtins.inspect_sigelt s)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
               (Prims.of_int (649)) (Prims.of_int (11)) (Prims.of_int (649))
               (Prims.of_int (29)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
               (Prims.of_int (651)) (Prims.of_int (2)) (Prims.of_int (651))
               (Prims.of_int (21))))) (Obj.magic uu___)
      (fun uu___1 -> (fun sv -> Obj.magic (open_sigelt_view sv)) uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.NamedView.inspect_sigelt" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.NamedView.inspect_sigelt (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 inspect_sigelt)
               FStarC_Reflection_V2_Embeddings.e_sigelt e_named_sigelt_view
               psc ncb us args)
let (pack_sigelt :
  named_sigelt_view ->
    (FStarC_Reflection_Types.sigelt, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun sv ->
    let uu___ = close_sigelt_view sv in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
               (Prims.of_int (655)) (Prims.of_int (11)) (Prims.of_int (655))
               (Prims.of_int (31)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
               (Prims.of_int (656)) (Prims.of_int (2)) (Prims.of_int (656))
               (Prims.of_int (18))))) (Obj.magic uu___)
      (fun sv1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStarC_Reflection_V2_Builtins.pack_sigelt sv1))
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.NamedView.pack_sigelt"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.NamedView.pack_sigelt (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 pack_sigelt)
               e_named_sigelt_view FStarC_Reflection_V2_Embeddings.e_sigelt
               psc ncb us args)
let (tcc :
  FStarC_Reflection_Types.env ->
    term -> (comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun t ->
      let uu___ = FStarC_Tactics_V2_Builtins.tcc e t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                 (Prims.of_int (659)) (Prims.of_int (19))
                 (Prims.of_int (659)) (Prims.of_int (52)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                 (Prims.of_int (660)) (Prims.of_int (2)) (Prims.of_int (660))
                 (Prims.of_int (18))))) (Obj.magic uu___)
        (fun c ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> FStarC_Reflection_V2_Builtins.inspect_comp c))
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.NamedView.tcc"
    (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.NamedView.tcc (plugin)"
               (FStarC_Tactics_Native.from_tactic_2 tcc)
               FStarC_Reflection_V2_Embeddings.e_env
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Reflection_V2_Embeddings.e_comp_view psc ncb us args)
let (comp_to_string :
  comp -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun c ->
    FStarC_Tactics_V2_Builtins.comp_to_string
      (FStarC_Reflection_V2_Builtins.pack_comp c)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.NamedView.comp_to_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.NamedView.comp_to_string (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 comp_to_string)
               FStarC_Reflection_V2_Embeddings.e_comp_view
               FStarC_Syntax_Embeddings.e_string psc ncb us args)
type universe_view = named_universe_view
type term_view = named_term_view
type sigelt_view = named_sigelt_view
let (inspect_namedv : namedv -> namedv) = fun x -> x
let (pack_namedv : namedv -> namedv) = fun x -> x
let (inspect_bv : bv -> bv) = fun x -> x
let (pack_bv : bv -> bv) = fun x -> x
let (inspect_comp : comp -> comp) = fun x -> x
let (pack_comp : comp -> comp) = fun x -> x
let (tag_of : term -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun t ->
    let uu___ = inspect t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.NamedView.fsti"
               (Prims.of_int (220)) (Prims.of_int (8)) (Prims.of_int (220))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.NamedView.fsti"
               (Prims.of_int (220)) (Prims.of_int (2)) (Prims.of_int (237))
               (Prims.of_int (28))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 ->
              match uu___1 with
              | Tv_Var bv1 -> "Tv_Var"
              | Tv_BVar fv -> "Tv_BVar"
              | Tv_FVar fv -> "Tv_FVar"
              | Tv_UInst (uu___3, uu___4) -> "Tv_UInst"
              | Tv_App (f, x) -> "Tv_App"
              | Tv_Abs (x, t1) -> "Tv_Abs"
              | Tv_Arrow (x, t1) -> "Tv_Arrow"
              | Tv_Type uu___3 -> "Tv_Type"
              | Tv_Refine (x, t1) -> "Tv_Refine"
              | Tv_Const cst -> "Tv_Const"
              | Tv_Uvar (i, t1) -> "Tv_Uvar"
              | Tv_Let (r, attrs, b, t1, t2) -> "Tv_Let"
              | Tv_Match (t1, uu___3, branches) -> "Tv_Match"
              | Tv_AscribedT (uu___3, uu___4, uu___5, uu___6) ->
                  "Tv_AscribedT"
              | Tv_AscribedC (uu___3, uu___4, uu___5, uu___6) ->
                  "Tv_AscribedC"
              | Tv_Unknown -> "Tv_Unknown"
              | Tv_Unsupp -> "Tv_Unsupp"))