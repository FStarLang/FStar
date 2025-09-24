open Fstarcompiler
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
  Fstarcompiler.FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.binder"
    (fun tm_0 ->
       match tm_0 with
       | ("FStar.Tactics.NamedView.Mkbinder",
          uniq_2::ppname_3::sort_4::qual_5::attrs_6::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Syntax_Embeddings.e_int uniq_2)
             (fun uniq_2 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (Fstarcompiler.FStarC_Syntax_Embeddings.e_sealed
                        Fstarcompiler.FStarC_Syntax_Embeddings.e_string)
                     ppname_3)
                  (fun ppname_3 ->
                     Fstarcompiler.FStarC_Option.bind
                       (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                          Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                          sort_4)
                       (fun sort_4 ->
                          Fstarcompiler.FStarC_Option.bind
                            (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_aqualv
                               qual_5)
                            (fun qual_5 ->
                               Fstarcompiler.FStarC_Option.bind
                                 (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                                    (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                                       Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
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
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Mkbinder"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Syntax_Embeddings.e_int uniq_9),
                FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (Fstarcompiler.FStarC_Syntax_Embeddings.e_sealed
                    Fstarcompiler.FStarC_Syntax_Embeddings.e_string)
                 ppname_10), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term sort_11),
               FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_aqualv
                 qual_12), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                    Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
                 attrs_13), FStar_Pervasives_Native.None)])
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
  Fstarcompiler.FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.named_universe_view"
    (fun tm_14 ->
       match tm_14 with
       | ("FStar.Tactics.NamedView.Uv_Zero", []) ->
           FStar_Pervasives_Native.Some Uv_Zero
       | ("FStar.Tactics.NamedView.Uv_Succ", _0_17::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe
                _0_17)
             (fun _0_17 -> FStar_Pervasives_Native.Some (Uv_Succ _0_17))
       | ("FStar.Tactics.NamedView.Uv_Max", _0_19::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                   Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe)
                _0_19)
             (fun _0_19 -> FStar_Pervasives_Native.Some (Uv_Max _0_19))
       | ("FStar.Tactics.NamedView.Uv_BVar", _0_21::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Syntax_Embeddings.e_int _0_21)
             (fun _0_21 -> FStar_Pervasives_Native.Some (Uv_BVar _0_21))
       | ("FStar.Tactics.NamedView.Uv_Name", _0_23::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                   Fstarcompiler.FStarC_Syntax_Embeddings.e_string
                   (Fstarcompiler.FStarC_Syntax_Embeddings.e_sealed
                      Fstarcompiler.FStarC_Syntax_Embeddings.e___range))
                _0_23)
             (fun _0_23 -> FStar_Pervasives_Native.Some (Uv_Name _0_23))
       | ("FStar.Tactics.NamedView.Uv_Unif", _0_25::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe_uvar
                _0_25)
             (fun _0_25 -> FStar_Pervasives_Native.Some (Uv_Unif _0_25))
       | ("FStar.Tactics.NamedView.Uv_Unk", []) ->
           FStar_Pervasives_Native.Some Uv_Unk
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_27 ->
       match tm_27 with
       | Uv_Zero ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Uv_Zero")) []
       | Uv_Succ _0_30 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Uv_Succ"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe
                  _0_30), FStar_Pervasives_Native.None)]
       | Uv_Max _0_32 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Uv_Max"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe)
                  _0_32), FStar_Pervasives_Native.None)]
       | Uv_BVar _0_34 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Uv_BVar"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Syntax_Embeddings.e_int _0_34),
                FStar_Pervasives_Native.None)]
       | Uv_Name _0_36 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Uv_Name"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                     Fstarcompiler.FStarC_Syntax_Embeddings.e_string
                     (Fstarcompiler.FStarC_Syntax_Embeddings.e_sealed
                        Fstarcompiler.FStarC_Syntax_Embeddings.e___range))
                  _0_36), FStar_Pervasives_Native.None)]
       | Uv_Unif _0_38 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Uv_Unif"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe_uvar
                  _0_38), FStar_Pervasives_Native.None)]
       | Uv_Unk ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Uv_Unk")) [])
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
  Fstarcompiler.FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.pattern__Pat_Constant__payload"
    (fun tm_40 ->
       match tm_40 with
       | ("FStar.Tactics.NamedView.Mkpattern__Pat_Constant__payload",
          c_42::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_vconst c_42)
             (fun c_42 -> FStar_Pervasives_Native.Some { c = c_42 })
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_43 ->
       match tm_43 with
       | { c = c_45;_} ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Mkpattern__Pat_Constant__payload"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_vconst c_45),
                FStar_Pervasives_Native.None)])
and __knot_e_pattern__Pat_Cons__payload _ =
  Fstarcompiler.FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.pattern__Pat_Cons__payload"
    (fun tm_46 ->
       match tm_46 with
       | ("FStar.Tactics.NamedView.Mkpattern__Pat_Cons__payload",
          head_48::univs_49::subpats_50::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_fv head_48)
             (fun head_48 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (Fstarcompiler.FStarC_Syntax_Embeddings.e_option
                        (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                           Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe))
                     univs_49)
                  (fun univs_49 ->
                     Fstarcompiler.FStarC_Option.bind
                       (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                          (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                             (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                                (__knot_e_pattern ())
                                Fstarcompiler.FStarC_Syntax_Embeddings.e_bool))
                          subpats_50)
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
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Mkpattern__Pat_Cons__payload"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_fv head_53),
                FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (Fstarcompiler.FStarC_Syntax_Embeddings.e_option
                    (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                       Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe))
                 univs_54), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                    (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                       (__knot_e_pattern ())
                       Fstarcompiler.FStarC_Syntax_Embeddings.e_bool))
                 subpats_55), FStar_Pervasives_Native.None)])
and __knot_e_pattern__Pat_Var__payload _ =
  Fstarcompiler.FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.pattern__Pat_Var__payload"
    (fun tm_56 ->
       match tm_56 with
       | ("FStar.Tactics.NamedView.Mkpattern__Pat_Var__payload",
          v_58::sort_59::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_namedv_view
                v_58)
             (fun v_58 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (Fstarcompiler.FStarC_Syntax_Embeddings.e_sealed
                        Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
                     sort_59)
                  (fun sort_59 ->
                     FStar_Pervasives_Native.Some
                       { v = v_58; sort1 = sort_59 }))
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_60 ->
       match tm_60 with
       | { v = v_62; sort1 = sort_63;_} ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Mkpattern__Pat_Var__payload"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_namedv_view
                  v_62), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (Fstarcompiler.FStarC_Syntax_Embeddings.e_sealed
                    Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
                 sort_63), FStar_Pervasives_Native.None)])
and __knot_e_pattern__Pat_Dot_Term__payload _ =
  Fstarcompiler.FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.pattern__Pat_Dot_Term__payload"
    (fun tm_64 ->
       match tm_64 with
       | ("FStar.Tactics.NamedView.Mkpattern__Pat_Dot_Term__payload",
          t_66::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                (Fstarcompiler.FStarC_Syntax_Embeddings.e_option
                   Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term) t_66)
             (fun t_66 -> FStar_Pervasives_Native.Some { t = t_66 })
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_67 ->
       match tm_67 with
       | { t = t_69;_} ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Mkpattern__Pat_Dot_Term__payload"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  (Fstarcompiler.FStarC_Syntax_Embeddings.e_option
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
                  t_69), FStar_Pervasives_Native.None)])
and __knot_e_pattern _ =
  Fstarcompiler.FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.pattern"
    (fun tm_70 ->
       match tm_70 with
       | ("FStar.Tactics.NamedView.Pat_Constant", _0_72::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                (__knot_e_pattern__Pat_Constant__payload ()) _0_72)
             (fun _0_72 -> FStar_Pervasives_Native.Some (Pat_Constant _0_72))
       | ("FStar.Tactics.NamedView.Pat_Cons", _0_74::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                (__knot_e_pattern__Pat_Cons__payload ()) _0_74)
             (fun _0_74 -> FStar_Pervasives_Native.Some (Pat_Cons _0_74))
       | ("FStar.Tactics.NamedView.Pat_Var", _0_76::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                (__knot_e_pattern__Pat_Var__payload ()) _0_76)
             (fun _0_76 -> FStar_Pervasives_Native.Some (Pat_Var _0_76))
       | ("FStar.Tactics.NamedView.Pat_Dot_Term", _0_78::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                (__knot_e_pattern__Pat_Dot_Term__payload ()) _0_78)
             (fun _0_78 -> FStar_Pervasives_Native.Some (Pat_Dot_Term _0_78))
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_79 ->
       match tm_79 with
       | Pat_Constant _0_81 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Pat_Constant"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  (__knot_e_pattern__Pat_Constant__payload ()) _0_81),
                FStar_Pervasives_Native.None)]
       | Pat_Cons _0_83 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Pat_Cons"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  (__knot_e_pattern__Pat_Cons__payload ()) _0_83),
                FStar_Pervasives_Native.None)]
       | Pat_Var _0_85 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Pat_Var"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  (__knot_e_pattern__Pat_Var__payload ()) _0_85),
                FStar_Pervasives_Native.None)]
       | Pat_Dot_Term _0_87 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Pat_Dot_Term"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
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
  (binder * ((term, comp) Fstarcompiler.FStar_Pervasives.either * term
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
  Fstarcompiler.FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.named_term_view"
    (fun tm_88 ->
       match tm_88 with
       | ("FStar.Tactics.NamedView.Tv_Var", v_90::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_namedv_view
                v_90)
             (fun v_90 -> FStar_Pervasives_Native.Some (Tv_Var v_90))
       | ("FStar.Tactics.NamedView.Tv_BVar", v_92::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_bv_view v_92)
             (fun v_92 -> FStar_Pervasives_Native.Some (Tv_BVar v_92))
       | ("FStar.Tactics.NamedView.Tv_FVar", v_94::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_fv v_94)
             (fun v_94 -> FStar_Pervasives_Native.Some (Tv_FVar v_94))
       | ("FStar.Tactics.NamedView.Tv_UInst", v_96::us_97::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_fv v_96)
             (fun v_96 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                        Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe)
                     us_97)
                  (fun us_97 ->
                     FStar_Pervasives_Native.Some (Tv_UInst (v_96, us_97))))
       | ("FStar.Tactics.NamedView.Tv_App", hd_99::a_100::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term hd_99)
             (fun hd_99 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                        Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                        Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_aqualv)
                     a_100)
                  (fun a_100 ->
                     FStar_Pervasives_Native.Some (Tv_App (hd_99, a_100))))
       | ("FStar.Tactics.NamedView.Tv_Abs", b_102::body_103::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                e_binder b_102)
             (fun b_102 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                     body_103)
                  (fun body_103 ->
                     FStar_Pervasives_Native.Some (Tv_Abs (b_102, body_103))))
       | ("FStar.Tactics.NamedView.Tv_Arrow", b_105::c_106::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                e_binder b_105)
             (fun b_105 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_comp_view
                     c_106)
                  (fun c_106 ->
                     FStar_Pervasives_Native.Some (Tv_Arrow (b_105, c_106))))
       | ("FStar.Tactics.NamedView.Tv_Type", _0_108::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe
                _0_108)
             (fun _0_108 -> FStar_Pervasives_Native.Some (Tv_Type _0_108))
       | ("FStar.Tactics.NamedView.Tv_Refine", b_110::ref_111::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                e_binder b_110)
             (fun b_110 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                     ref_111)
                  (fun ref_111 ->
                     FStar_Pervasives_Native.Some
                       (Tv_Refine (b_110, ref_111))))
       | ("FStar.Tactics.NamedView.Tv_Const", _0_113::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_vconst _0_113)
             (fun _0_113 -> FStar_Pervasives_Native.Some (Tv_Const _0_113))
       | ("FStar.Tactics.NamedView.Tv_Uvar", _0_115::_1_116::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Syntax_Embeddings.e_int _0_115)
             (fun _0_115 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_ctx_uvar_and_subst
                     _1_116)
                  (fun _1_116 ->
                     FStar_Pervasives_Native.Some (Tv_Uvar (_0_115, _1_116))))
       | ("FStar.Tactics.NamedView.Tv_Let",
          recf_118::attrs_119::b_120::def_121::body_122::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Syntax_Embeddings.e_bool recf_118)
             (fun recf_118 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                        Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
                     attrs_119)
                  (fun attrs_119 ->
                     Fstarcompiler.FStarC_Option.bind
                       (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                          e_binder b_120)
                       (fun b_120 ->
                          Fstarcompiler.FStarC_Option.bind
                            (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                               def_121)
                            (fun def_121 ->
                               Fstarcompiler.FStarC_Option.bind
                                 (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                                    Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                                    body_122)
                                 (fun body_122 ->
                                    FStar_Pervasives_Native.Some
                                      (Tv_Let
                                         (recf_118, attrs_119, b_120,
                                           def_121, body_122)))))))
       | ("FStar.Tactics.NamedView.Tv_Match",
          scrutinee_124::ret_125::brs_126::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                scrutinee_124)
             (fun scrutinee_124 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (Fstarcompiler.FStarC_Syntax_Embeddings.e_option
                        (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                           e_binder
                           (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple3
                              (Fstarcompiler.FStarC_Syntax_Embeddings.e_either
                                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_comp_view)
                              (Fstarcompiler.FStarC_Syntax_Embeddings.e_option
                                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
                              Fstarcompiler.FStarC_Syntax_Embeddings.e_bool)))
                     ret_125)
                  (fun ret_125 ->
                     Fstarcompiler.FStarC_Option.bind
                       (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                          (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                             (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                                e_pattern
                                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term))
                          brs_126)
                       (fun brs_126 ->
                          FStar_Pervasives_Native.Some
                            (Tv_Match (scrutinee_124, ret_125, brs_126)))))
       | ("FStar.Tactics.NamedView.Tv_AscribedT",
          e_128::t_129::tac_130::use_eq_131::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term e_128)
             (fun e_128 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                     t_129)
                  (fun t_129 ->
                     Fstarcompiler.FStarC_Option.bind
                       (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                          (Fstarcompiler.FStarC_Syntax_Embeddings.e_option
                             Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
                          tac_130)
                       (fun tac_130 ->
                          Fstarcompiler.FStarC_Option.bind
                            (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                               Fstarcompiler.FStarC_Syntax_Embeddings.e_bool
                               use_eq_131)
                            (fun use_eq_131 ->
                               FStar_Pervasives_Native.Some
                                 (Tv_AscribedT
                                    (e_128, t_129, tac_130, use_eq_131))))))
       | ("FStar.Tactics.NamedView.Tv_AscribedC",
          e_133::c_134::tac_135::use_eq_136::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term e_133)
             (fun e_133 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_comp_view
                     c_134)
                  (fun c_134 ->
                     Fstarcompiler.FStarC_Option.bind
                       (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                          (Fstarcompiler.FStarC_Syntax_Embeddings.e_option
                             Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
                          tac_135)
                       (fun tac_135 ->
                          Fstarcompiler.FStarC_Option.bind
                            (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                               Fstarcompiler.FStarC_Syntax_Embeddings.e_bool
                               use_eq_136)
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
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Tv_Var"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_namedv_view
                  v_141), FStar_Pervasives_Native.None)]
       | Tv_BVar v_143 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Tv_BVar"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_bv_view
                  v_143), FStar_Pervasives_Native.None)]
       | Tv_FVar v_145 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Tv_FVar"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_fv v_145),
                FStar_Pervasives_Native.None)]
       | Tv_UInst (v_147, us_148) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Tv_UInst"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_fv v_147),
                FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                    Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe)
                 us_148), FStar_Pervasives_Native.None)]
       | Tv_App (hd_150, a_151) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Tv_App"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term hd_150),
                FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                    Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                    Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_aqualv)
                 a_151), FStar_Pervasives_Native.None)]
       | Tv_Abs (b_153, body_154) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Tv_Abs"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  e_binder b_153), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                 body_154), FStar_Pervasives_Native.None)]
       | Tv_Arrow (b_156, c_157) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Tv_Arrow"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  e_binder b_156), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_comp_view
                 c_157), FStar_Pervasives_Native.None)]
       | Tv_Type _0_159 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Tv_Type"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe
                  _0_159), FStar_Pervasives_Native.None)]
       | Tv_Refine (b_161, ref_162) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Tv_Refine"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  e_binder b_161), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term ref_162),
               FStar_Pervasives_Native.None)]
       | Tv_Const _0_164 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Tv_Const"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_vconst
                  _0_164), FStar_Pervasives_Native.None)]
       | Tv_Uvar (_0_166, _1_167) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Tv_Uvar"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Syntax_Embeddings.e_int _0_166),
                FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_ctx_uvar_and_subst
                 _1_167), FStar_Pervasives_Native.None)]
       | Tv_Let (recf_169, attrs_170, b_171, def_172, body_173) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Tv_Let"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Syntax_Embeddings.e_bool recf_169),
                FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                    Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
                 attrs_170), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 e_binder b_171), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term def_172),
               FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                 body_173), FStar_Pervasives_Native.None)]
       | Tv_Match (scrutinee_175, ret_176, brs_177) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Tv_Match"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                  scrutinee_175), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (Fstarcompiler.FStarC_Syntax_Embeddings.e_option
                    (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2 e_binder
                       (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple3
                          (Fstarcompiler.FStarC_Syntax_Embeddings.e_either
                             Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                             Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_comp_view)
                          (Fstarcompiler.FStarC_Syntax_Embeddings.e_option
                             Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
                          Fstarcompiler.FStarC_Syntax_Embeddings.e_bool)))
                 ret_176), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                    (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                       e_pattern
                       Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term))
                 brs_177), FStar_Pervasives_Native.None)]
       | Tv_AscribedT (e_179, t_180, tac_181, use_eq_182) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Tv_AscribedT"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term e_179),
                FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term t_180),
               FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (Fstarcompiler.FStarC_Syntax_Embeddings.e_option
                    Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
                 tac_181), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Syntax_Embeddings.e_bool use_eq_182),
               FStar_Pervasives_Native.None)]
       | Tv_AscribedC (e_184, c_185, tac_186, use_eq_187) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Tv_AscribedC"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term e_184),
                FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_comp_view
                 c_185), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (Fstarcompiler.FStarC_Syntax_Embeddings.e_option
                    Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
                 tac_186), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Syntax_Embeddings.e_bool use_eq_187),
               FStar_Pervasives_Native.None)]
       | Tv_Unknown ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Tv_Unknown")) []
       | Tv_Unsupp ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Tv_Unsupp")) [])
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
type ('v1, 'v2) ctor_matches = Obj.t
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
  Fstarcompiler.FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.letbinding"
    (fun tm_190 ->
       match tm_190 with
       | ("FStar.Tactics.NamedView.Mkletbinding",
          lb_fv_192::lb_us_193::lb_typ_194::lb_def_195::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_fv lb_fv_192)
             (fun lb_fv_192 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                        (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                           Fstarcompiler.FStarC_Syntax_Embeddings.e_string
                           (Fstarcompiler.FStarC_Syntax_Embeddings.e_sealed
                              Fstarcompiler.FStarC_Syntax_Embeddings.e___range)))
                     lb_us_193)
                  (fun lb_us_193 ->
                     Fstarcompiler.FStarC_Option.bind
                       (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                          Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                          lb_typ_194)
                       (fun lb_typ_194 ->
                          Fstarcompiler.FStarC_Option.bind
                            (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
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
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Mkletbinding"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_fv
                  lb_fv_198), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                    (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                       Fstarcompiler.FStarC_Syntax_Embeddings.e_string
                       (Fstarcompiler.FStarC_Syntax_Embeddings.e_sealed
                          Fstarcompiler.FStarC_Syntax_Embeddings.e___range)))
                 lb_us_199), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                 lb_typ_200), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                 lb_def_201), FStar_Pervasives_Native.None)])
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
  Fstarcompiler.FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.named_sigelt_view__Sg_Let__payload"
    (fun tm_202 ->
       match tm_202 with
       | ("FStar.Tactics.NamedView.Mknamed_sigelt_view__Sg_Let__payload",
          isrec_204::lbs_205::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Syntax_Embeddings.e_bool isrec_204)
             (fun isrec_204 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                        e_letbinding) lbs_205)
                  (fun lbs_205 ->
                     FStar_Pervasives_Native.Some
                       { isrec = isrec_204; lbs = lbs_205 }))
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_206 ->
       match tm_206 with
       | { isrec = isrec_208; lbs = lbs_209;_} ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Mknamed_sigelt_view__Sg_Let__payload"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Syntax_Embeddings.e_bool isrec_208),
                FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (Fstarcompiler.FStarC_Syntax_Embeddings.e_list e_letbinding)
                 lbs_209), FStar_Pervasives_Native.None)])
and __knot_e_named_sigelt_view__Sg_Inductive__payload _ =
  Fstarcompiler.FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.named_sigelt_view__Sg_Inductive__payload"
    (fun tm_210 ->
       match tm_210 with
       | ("FStar.Tactics.NamedView.Mknamed_sigelt_view__Sg_Inductive__payload",
          nm_212::univs_213::params_214::typ_215::ctors_216::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                   Fstarcompiler.FStarC_Syntax_Embeddings.e_string) nm_212)
             (fun nm_212 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                        (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                           Fstarcompiler.FStarC_Syntax_Embeddings.e_string
                           (Fstarcompiler.FStarC_Syntax_Embeddings.e_sealed
                              Fstarcompiler.FStarC_Syntax_Embeddings.e___range)))
                     univs_213)
                  (fun univs_213 ->
                     Fstarcompiler.FStarC_Option.bind
                       (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                          (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                             e_binder) params_214)
                       (fun params_214 ->
                          Fstarcompiler.FStarC_Option.bind
                            (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                               typ_215)
                            (fun typ_215 ->
                               Fstarcompiler.FStarC_Option.bind
                                 (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                                    (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                                       (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                                          (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                                             Fstarcompiler.FStarC_Syntax_Embeddings.e_string)
                                          Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term))
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
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Mknamed_sigelt_view__Sg_Inductive__payload"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                     Fstarcompiler.FStarC_Syntax_Embeddings.e_string) nm_219),
                FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                    (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                       Fstarcompiler.FStarC_Syntax_Embeddings.e_string
                       (Fstarcompiler.FStarC_Syntax_Embeddings.e_sealed
                          Fstarcompiler.FStarC_Syntax_Embeddings.e___range)))
                 univs_220), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (Fstarcompiler.FStarC_Syntax_Embeddings.e_list e_binder)
                 params_221), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term typ_222),
               FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                    (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                       (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                          Fstarcompiler.FStarC_Syntax_Embeddings.e_string)
                       Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term))
                 ctors_223), FStar_Pervasives_Native.None)])
and __knot_e_named_sigelt_view__Sg_Val__payload _ =
  Fstarcompiler.FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.named_sigelt_view__Sg_Val__payload"
    (fun tm_224 ->
       match tm_224 with
       | ("FStar.Tactics.NamedView.Mknamed_sigelt_view__Sg_Val__payload",
          nm_226::univs_227::typ_228::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                   Fstarcompiler.FStarC_Syntax_Embeddings.e_string) nm_226)
             (fun nm_226 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                        (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                           Fstarcompiler.FStarC_Syntax_Embeddings.e_string
                           (Fstarcompiler.FStarC_Syntax_Embeddings.e_sealed
                              Fstarcompiler.FStarC_Syntax_Embeddings.e___range)))
                     univs_227)
                  (fun univs_227 ->
                     Fstarcompiler.FStarC_Option.bind
                       (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                          Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                          typ_228)
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
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Mknamed_sigelt_view__Sg_Val__payload"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                     Fstarcompiler.FStarC_Syntax_Embeddings.e_string) nm_231),
                FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                    (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                       Fstarcompiler.FStarC_Syntax_Embeddings.e_string
                       (Fstarcompiler.FStarC_Syntax_Embeddings.e_sealed
                          Fstarcompiler.FStarC_Syntax_Embeddings.e___range)))
                 univs_232), FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term typ_233),
               FStar_Pervasives_Native.None)])
and __knot_e_named_sigelt_view _ =
  Fstarcompiler.FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.NamedView.named_sigelt_view"
    (fun tm_234 ->
       match tm_234 with
       | ("FStar.Tactics.NamedView.Sg_Let", _0_236::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                (__knot_e_named_sigelt_view__Sg_Let__payload ()) _0_236)
             (fun _0_236 -> FStar_Pervasives_Native.Some (Sg_Let _0_236))
       | ("FStar.Tactics.NamedView.Sg_Inductive", _0_238::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                (__knot_e_named_sigelt_view__Sg_Inductive__payload ()) _0_238)
             (fun _0_238 ->
                FStar_Pervasives_Native.Some (Sg_Inductive _0_238))
       | ("FStar.Tactics.NamedView.Sg_Val", _0_240::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                (__knot_e_named_sigelt_view__Sg_Val__payload ()) _0_240)
             (fun _0_240 -> FStar_Pervasives_Native.Some (Sg_Val _0_240))
       | ("FStar.Tactics.NamedView.Unk", []) ->
           FStar_Pervasives_Native.Some Unk
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_242 ->
       match tm_242 with
       | Sg_Let _0_244 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Sg_Let"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  (__knot_e_named_sigelt_view__Sg_Let__payload ()) _0_244),
                FStar_Pervasives_Native.None)]
       | Sg_Inductive _0_246 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Sg_Inductive"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  (__knot_e_named_sigelt_view__Sg_Inductive__payload ())
                  _0_246), FStar_Pervasives_Native.None)]
       | Sg_Val _0_248 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Sg_Val"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  (__knot_e_named_sigelt_view__Sg_Val__payload ()) _0_248),
                FStar_Pervasives_Native.None)]
       | Unk ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.NamedView.Unk")) [])
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
let (inspect_universe :
  universe -> (named_universe_view, unit) FStar_Tactics_Effect.tac_repr) =
  fun u ->
    fun ps ->
      let x = FStarC_Tactics_V2_Builtins.compress_univ u ps in
      open_universe_view (FStarC_Reflection_V2_Builtins.inspect_universe x)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.NamedView.inspect_universe" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.NamedView.inspect_universe (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  inspect_universe)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe
               e_named_universe_view psc ncb us args)
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
  Fstarcompiler.FStarC_Tactics_Native.register_plugin
    "FStar.Tactics.NamedView.pack_universe" Prims.int_one
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Tactics.NamedView.pack_universe"
               (fun _ ->
                  (Fstarcompiler.FStarC_Syntax_Embeddings.arrow_as_prim_step_1
                     e_named_universe_view
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe
                     pack_universe
                     (Fstarcompiler.FStarC_Ident.lid_of_str
                        "FStar.Tactics.NamedView.pack_universe") cb us) args))
    (fun cb ->
       fun us ->
         fun args ->
           Fstarcompiler.FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Tactics.NamedView.pack_universe"
             (fun _ ->
                (Fstarcompiler.FStarC_TypeChecker_NBETerm.arrow_as_prim_step_1
                   (Fstarcompiler.FStarC_TypeChecker_NBETerm.e_unsupported ())
                   Fstarcompiler.FStarC_Reflection_V2_NBEEmbeddings.e_universe
                   pack_universe
                   (Fstarcompiler.FStarC_Ident.lid_of_str
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
    fun ps ->
      let x = FStarC_Tactics_V2_Builtins.fresh () ps in
      {
        uniq = x;
        ppname =
          ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.ppname2);
        sort =
          ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.sort2);
        qual =
          ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.qual);
        attrs =
          ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.attrs)
      }
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
                              }))] t)) uu___2 uu___1 uu___
let (open_term :
  FStarC_Reflection_Types.binder ->
    term -> ((binder * term), unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun t ->
      fun ps ->
        let x = open_binder b ps in
        let x1 = open_term_with b x t ps in (x, x1)
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
      fun ps ->
        let x = FStarC_Tactics_V2_Builtins.fresh () ps in
        ({
           uniq = x;
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
                       FStarC_Reflection_V2_Data.uniq = x;
                       FStarC_Reflection_V2_Data.sort =
                         (FStar_Sealed.seal
                            (FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.sort2);
                       FStarC_Reflection_V2_Data.ppname =
                         ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.ppname2)
                     }))] t))
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
                              }))] c)) uu___2 uu___1 uu___
let (open_term_simple :
  FStarC_Reflection_V2_Data.simple_binder ->
    term -> ((simple_binder * term), unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun t ->
      fun ps ->
        let x = FStarC_Tactics_V2_Builtins.fresh () ps in
        ({
           uniq = x;
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
                       FStarC_Reflection_V2_Data.uniq = x;
                       FStarC_Reflection_V2_Data.sort =
                         (FStar_Sealed.seal
                            (FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.sort2);
                       FStarC_Reflection_V2_Data.ppname =
                         ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.ppname2)
                     }))] t))
let (open_comp_simple :
  FStarC_Reflection_V2_Data.simple_binder ->
    comp -> ((simple_binder * comp), unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun t ->
      fun ps ->
        let x = FStarC_Tactics_V2_Builtins.fresh () ps in
        ({
           uniq = x;
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
                       FStarC_Reflection_V2_Data.uniq = x;
                       FStarC_Reflection_V2_Data.sort =
                         (FStar_Sealed.seal
                            (FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.sort2);
                       FStarC_Reflection_V2_Data.ppname =
                         ((FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.ppname2)
                     }))] t))
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
  Fstarcompiler.FStarC_Tactics_Native.register_plugin
    "FStar.Tactics.NamedView.close_term" (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Tactics.NamedView.close_term"
               (fun _ ->
                  (Fstarcompiler.FStarC_Syntax_Embeddings.arrow_as_prim_step_2
                     e_binder
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                     (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                        Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder
                        Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
                     close_term
                     (Fstarcompiler.FStarC_Ident.lid_of_str
                        "FStar.Tactics.NamedView.close_term") cb us) args))
    (fun cb ->
       fun us ->
         fun args ->
           Fstarcompiler.FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Tactics.NamedView.close_term"
             (fun _ ->
                (Fstarcompiler.FStarC_TypeChecker_NBETerm.arrow_as_prim_step_2
                   (Fstarcompiler.FStarC_TypeChecker_NBETerm.e_unsupported ())
                   Fstarcompiler.FStarC_Reflection_V2_NBEEmbeddings.e_term
                   (Fstarcompiler.FStarC_TypeChecker_NBETerm.e_tuple2
                      Fstarcompiler.FStarC_Reflection_V2_NBEEmbeddings.e_binder
                      Fstarcompiler.FStarC_Reflection_V2_NBEEmbeddings.e_term)
                   close_term
                   (Fstarcompiler.FStarC_Ident.lid_of_str
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
               | [] -> Obj.magic (Obj.repr (fun uu___ -> (nbs, s)))
               | b::bs1 ->
                   Obj.magic
                     (Obj.repr
                        (fun ps ->
                           let x = r_subst_binder_sort s b in
                           let x1 = open_binder x ps in
                           let x2 = r_binder_to_namedv x1 in
                           __open_term_n_aux bs1 (x1 :: nbs)
                             ((FStarC_Syntax_Syntax.DB (Prims.int_zero, x2))
                             ::
                             (FStar_Reflection_V2_Derived.shift_subst
                                Prims.int_one s)) ps))) uu___2 uu___1 uu___
let (open_term_n :
  FStarC_Reflection_Types.binder Prims.list ->
    term -> ((binder Prims.list * term), unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bs ->
    fun t ->
      fun ps ->
        let x = __open_term_n_aux bs [] [] ps in
        match x with
        | (nbs, s) ->
            ((FStar_List_Tot_Base.rev nbs),
              (FStarC_Reflection_V2_Builtins.subst_term s t))
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
               | ([], []) -> Obj.magic (Obj.repr (fun uu___ -> t))
               | (b::bs1, nb::nbs1) ->
                   Obj.magic
                     (Obj.repr
                        (fun ps ->
                           let x = open_term_n_with bs1 nbs1 t ps in
                           let x1 = open_term_with b nb x ps in x1))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (fun ps ->
                           Obj.magic
                             (FStarC_Tactics_V2_Builtins.raise_core
                                LengthMismatch ps)))) uu___2 uu___1 uu___
let (close_term_n :
  binder Prims.list ->
    term -> (FStarC_Reflection_Types.binder Prims.list * term))
  =
  fun bs ->
    fun t ->
      let rec aux bs1 =
        fun cbs ->
          fun s ->
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
           | [] -> Obj.magic (Obj.repr (fun uu___ -> ([], t)))
           | b::bs1 ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x = open_term_n_simple bs1 t ps in
                       match x with
                       | (bs', t') ->
                           let x1 = open_term_simple b t' ps in
                           (match x1 with | (b', t'') -> ((b' :: bs'), t'')))))
        uu___1 uu___
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
               Obj.magic (Obj.repr (fun uu___ -> ((Pat_Constant { c }), s)))
           | FStarC_Reflection_V2_Data.Pat_Var (ssort, n) ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x = FStarC_Tactics_Unseal.unseal ssort ps in
                       let x1 = FStarC_Reflection_V2_Builtins.subst_term s x in
                       let x2 =
                         let x3 = FStarC_Tactics_V2_Builtins.fresh () ps in
                         {
                           FStarC_Reflection_V2_Data.uniq = x3;
                           FStarC_Reflection_V2_Data.sort =
                             (FStar_Sealed.seal x1);
                           FStarC_Reflection_V2_Data.ppname = n
                         } in
                       ((Pat_Var { v = x2; sort1 = (FStar_Sealed.seal x1) }),
                         ((FStarC_Syntax_Syntax.DB
                             (Prims.int_zero,
                               (FStarC_Reflection_V2_Builtins.pack_namedv x2)))
                         ::
                         (FStar_Reflection_V2_Derived.shift_subst
                            Prims.int_one s)))))
           | FStarC_Reflection_V2_Data.Pat_Cons (head, univs, subpats) ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x =
                         FStar_Tactics_Util.fold_left
                           (fun uu___ ->
                              fun uu___1 ->
                                match (uu___, uu___1) with
                                | ((pats, s1), (pat, b)) ->
                                    (fun ps1 ->
                                       let x1 = open_pat pat s1 ps1 in
                                       match x1 with
                                       | (pat1, s') ->
                                           (((pat1, b) :: pats), s')))
                           ([], s) subpats ps in
                       match x with
                       | (subpats1, s1) ->
                           ((Pat_Cons
                               {
                                 head;
                                 univs;
                                 subpats = (FStar_List_Tot_Base.rev subpats1)
                               }), s1)))
           | FStarC_Reflection_V2_Data.Pat_Dot_Term
               (FStar_Pervasives_Native.None) ->
               Obj.magic
                 (Obj.repr
                    (fun uu___ ->
                       ((Pat_Dot_Term { t = FStar_Pervasives_Native.None }),
                         s)))
           | FStarC_Reflection_V2_Data.Pat_Dot_Term
               (FStar_Pervasives_Native.Some t) ->
               Obj.magic
                 (Obj.repr
                    (fun uu___ ->
                       ((Pat_Dot_Term
                           {
                             t =
                               (FStar_Pervasives_Native.Some
                                  (FStarC_Reflection_V2_Builtins.subst_term s
                                     t))
                           }), s)))) uu___1 uu___
let (open_branch :
  FStarC_Reflection_V2_Data.branch ->
    (branch, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun ps ->
      let x = b in
      match x with
      | (pat, t) ->
          let x1 = open_pat pat [] ps in
          (match x1 with
           | (pat1, s) ->
               (pat1, (FStarC_Reflection_V2_Builtins.subst_term s t)))
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
    fun ps ->
      let x = mra in
      match x with
      | (b, (ct, topt, use_eq)) ->
          let x1 = open_binder b ps in
          let x2 =
            match ct with
            | Fstarcompiler.FStar_Pervasives.Inl t ->
                let x3 = open_term_with b x1 t ps in
                Fstarcompiler.FStar_Pervasives.Inl x3
            | Fstarcompiler.FStar_Pervasives.Inr c ->
                let x3 = FStarC_Reflection_V2_Builtins.inspect_comp c in
                let x4 = open_comp_with b x1 x3 ps in
                Fstarcompiler.FStar_Pervasives.Inr x4 in
          let x3 =
            match topt with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some t ->
                let x4 = open_term_with b x1 t ps in
                FStar_Pervasives_Native.Some x4 in
          (x1, (x2, x3, use_eq))
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
          | Fstarcompiler.FStar_Pervasives.Inl t ->
              Fstarcompiler.FStar_Pervasives.Inl
                (FStar_Pervasives_Native.snd (close_term nb t))
          | Fstarcompiler.FStar_Pervasives.Inr c ->
              let uu___1 = close_comp nb c in
              (match uu___1 with
               | (uu___2, c1) ->
                   let c2 = FStarC_Reflection_V2_Builtins.pack_comp c1 in
                   Fstarcompiler.FStar_Pervasives.Inr c2) in
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
                (fun uu___ ->
                   Tv_Var (FStarC_Reflection_V2_Builtins.inspect_namedv v)))
       | FStarC_Reflection_V2_Data.Tv_BVar v ->
           Obj.magic
             (Obj.repr
                (fun uu___ ->
                   Tv_BVar (FStarC_Reflection_V2_Builtins.inspect_bv v)))
       | FStarC_Reflection_V2_Data.Tv_FVar v ->
           Obj.magic (Obj.repr (fun uu___ -> Tv_FVar v))
       | FStarC_Reflection_V2_Data.Tv_UInst (v, us) ->
           Obj.magic (Obj.repr (fun uu___ -> Tv_UInst (v, us)))
       | FStarC_Reflection_V2_Data.Tv_App (hd, a) ->
           Obj.magic (Obj.repr (fun uu___ -> Tv_App (hd, a)))
       | FStarC_Reflection_V2_Data.Tv_Type u ->
           Obj.magic (Obj.repr (fun uu___ -> Tv_Type u))
       | FStarC_Reflection_V2_Data.Tv_Const c ->
           Obj.magic (Obj.repr (fun uu___ -> Tv_Const c))
       | FStarC_Reflection_V2_Data.Tv_Uvar (n, ctx_uvar_and_subst) ->
           Obj.magic
             (Obj.repr (fun uu___ -> Tv_Uvar (n, ctx_uvar_and_subst)))
       | FStarC_Reflection_V2_Data.Tv_AscribedT (e, t, tac, use_eq) ->
           Obj.magic
             (Obj.repr (fun uu___ -> Tv_AscribedT (e, t, tac, use_eq)))
       | FStarC_Reflection_V2_Data.Tv_AscribedC (e, c, tac, use_eq) ->
           Obj.magic
             (Obj.repr
                (fun uu___ ->
                   Tv_AscribedC
                     (e, (FStarC_Reflection_V2_Builtins.inspect_comp c), tac,
                       use_eq)))
       | FStarC_Reflection_V2_Data.Tv_Unknown ->
           Obj.magic (Obj.repr (fun uu___ -> Tv_Unknown))
       | FStarC_Reflection_V2_Data.Tv_Unsupp ->
           Obj.magic (Obj.repr (fun uu___ -> Tv_Unsupp))
       | FStarC_Reflection_V2_Data.Tv_Abs (b, body) ->
           Obj.magic
             (Obj.repr
                (fun ps ->
                   let x = open_term b body ps in
                   match x with | (nb, body1) -> Tv_Abs (nb, body1)))
       | FStarC_Reflection_V2_Data.Tv_Arrow (b, c) ->
           Obj.magic
             (Obj.repr
                (fun ps ->
                   let x =
                     open_comp b
                       (FStarC_Reflection_V2_Builtins.inspect_comp c) ps in
                   match x with | (nb, c1) -> Tv_Arrow (nb, c1)))
       | FStarC_Reflection_V2_Data.Tv_Refine (b, ref) ->
           Obj.magic
             (Obj.repr
                (fun ps ->
                   let x = open_term_simple b ref ps in
                   match x with | (nb, ref1) -> Tv_Refine (nb, ref1)))
       | FStarC_Reflection_V2_Data.Tv_Let (recf, attrs, b, def, body) ->
           Obj.magic
             (Obj.repr
                (fun ps ->
                   let x = open_term_simple b body ps in
                   match x with
                   | (nb, body1) ->
                       Tv_Let
                         (recf, attrs, nb,
                           (if recf
                            then
                              FStarC_Reflection_V2_Builtins.subst_term
                                [FStarC_Syntax_Syntax.DB
                                   (Prims.int_zero, (r_binder_to_namedv nb))]
                                def
                            else def), body1)))
       | FStarC_Reflection_V2_Data.Tv_Match (scrutinee, ret, brs) ->
           Obj.magic
             (Obj.repr
                (fun ps ->
                   let x = FStar_Tactics_Util.map open_branch brs ps in
                   let x1 =
                     FStar_Tactics_Util.map_opt open_match_returns_ascription
                       ret ps in
                   Tv_Match (scrutinee, x1, x)))) uu___
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
    fun ps ->
      let x = FStarC_Tactics_V2_Builtins.compress t ps in
      let x1 = FStarC_Reflection_V2_Builtins.inspect_ln x in open_view x1 ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.NamedView.inspect" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.NamedView.inspect (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 inspect)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               e_named_term_view psc ncb us args)
let (pack : named_term_view -> term) =
  fun tv ->
    let tv1 = close_view tv in FStarC_Reflection_V2_Builtins.pack_ln tv1
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_plugin
    "FStar.Tactics.NamedView.pack" Prims.int_one
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Tactics.NamedView.pack"
               (fun _ ->
                  (Fstarcompiler.FStarC_Syntax_Embeddings.arrow_as_prim_step_1
                     e_named_term_view
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                     pack
                     (Fstarcompiler.FStarC_Ident.lid_of_str
                        "FStar.Tactics.NamedView.pack") cb us) args))
    (fun cb ->
       fun us ->
         fun args ->
           Fstarcompiler.FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Tactics.NamedView.pack"
             (fun _ ->
                (Fstarcompiler.FStarC_TypeChecker_NBETerm.arrow_as_prim_step_1
                   (Fstarcompiler.FStarC_TypeChecker_NBETerm.e_unsupported ())
                   Fstarcompiler.FStarC_Reflection_V2_NBEEmbeddings.e_term
                   pack
                   (Fstarcompiler.FStarC_Ident.lid_of_str
                      "FStar.Tactics.NamedView.pack") cb us) args))
let (open_univ_s :
  FStarC_Reflection_Types.univ_name Prims.list ->
    ((univ_name Prims.list * FStarC_Syntax_Syntax.subst_t), unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun us ->
    fun ps ->
      let x = FStar_List_Tot_Base.length us in
      let x1 =
        FStar_Tactics_Util.mapi
          (fun uu___1 ->
             fun uu___ ->
               (fun i ->
                  fun u ->
                    Obj.magic
                      (fun uu___ ->
                         FStarC_Syntax_Syntax.UN
                           (((x - Prims.int_one) - i),
                             (FStarC_Reflection_V2_Builtins.pack_universe
                                (FStarC_Reflection_V2_Data.Uv_Name u)))))
                 uu___1 uu___) us ps in
      let x2 =
        FStar_Tactics_Util.map
          (fun uu___ ->
             (fun i ->
                Obj.magic
                  (fun uu___ -> FStarC_Reflection_V2_Builtins.inspect_ident i))
               uu___) us ps in
      (x2, x1)
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
    fun ps ->
      let x = FStarC_Reflection_V2_Builtins.inspect_lb lb in
      match x with
      | { FStarC_Reflection_V2_Data.lb_fv = lb_fv;
          FStarC_Reflection_V2_Data.lb_us = lb_us;
          FStarC_Reflection_V2_Data.lb_typ = lb_typ;
          FStarC_Reflection_V2_Data.lb_def = lb_def;_} ->
          let x1 = open_univ_s lb_us ps in
          (match x1 with
           | (lb_us1, s) ->
               {
                 lb_fv;
                 lb_us = lb_us1;
                 lb_typ = (FStarC_Reflection_V2_Builtins.subst_term s lb_typ);
                 lb_def = (FStarC_Reflection_V2_Builtins.subst_term s lb_def)
               })
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
           | [] -> Obj.magic (Obj.repr (fun uu___ -> t))
           | b::bs1 ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x = inspect t ps in
                       match x with
                       | Tv_Arrow (b', FStarC_Reflection_V2_Data.C_Total t')
                           ->
                           Obj.magic
                             (Obj.repr
                                (let x1 =
                                   FStarC_Reflection_V2_Builtins.subst_term
                                     [FStarC_Syntax_Syntax.NT
                                        ((r_binder_to_namedv b'),
                                          (pack
                                             (Tv_Var
                                                (FStarC_Reflection_V2_Builtins.inspect_namedv
                                                   (r_binder_to_namedv b)))))]
                                     t' in
                                 open_n_binders_from_arrow bs1 x1 ps))
                       | uu___ ->
                           Obj.magic
                             (Obj.repr
                                (FStarC_Tactics_V2_Builtins.raise_core
                                   NotEnoughBinders ps))))) uu___1 uu___
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
                (fun ps ->
                   let x = FStar_Tactics_Util.map open_lb lbs ps in
                   Sg_Let { isrec; lbs = x }))
       | FStarC_Reflection_V2_Data.Sg_Inductive
           (nm, univs, params, typ, ctors) ->
           Obj.magic
             (Obj.repr
                (fun ps ->
                   let x = FStar_List_Tot_Base.length params in
                   let x1 = open_univ_s univs ps in
                   match x1 with
                   | (univs1, s) ->
                       let x2 = subst_r_binders s params in
                       let x3 =
                         FStarC_Reflection_V2_Builtins.subst_term
                           (FStar_Reflection_V2_Derived.shift_subst x s) typ in
                       let x4 =
                         FStar_Tactics_Util.map
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (fun uu___1 ->
                                      match uu___ with
                                      | (nm1, ty) ->
                                          (nm1,
                                            (FStarC_Reflection_V2_Builtins.subst_term
                                               s ty)))) uu___) ctors ps in
                       let x5 = open_term_n x2 x3 ps in
                       (match x5 with
                        | (params1, typ1) ->
                            let x6 =
                              FStar_Tactics_Util.map
                                (fun uu___ ->
                                   match uu___ with
                                   | (nm1, ty) ->
                                       (fun ps1 ->
                                          let x7 =
                                            open_n_binders_from_arrow params1
                                              ty ps1 in
                                          (nm1, x7))) x4 ps in
                            Sg_Inductive
                              {
                                nm;
                                univs1;
                                params = params1;
                                typ = typ1;
                                ctors = x6
                              })))
       | FStarC_Reflection_V2_Data.Sg_Val (nm, univs, typ) ->
           Obj.magic
             (Obj.repr
                (fun ps ->
                   let x = open_univ_s univs ps in
                   match x with
                   | (univs1, s) ->
                       Sg_Val
                         {
                           nm1 = nm;
                           univs2 = univs1;
                           typ1 =
                             (FStarC_Reflection_V2_Builtins.subst_term s typ)
                         }))
       | FStarC_Reflection_V2_Data.Unk ->
           Obj.magic (Obj.repr (fun uu___ -> Unk))) uu___
let rec (mk_arr :
  binder Prims.list -> term -> (term, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___1 ->
    fun uu___ ->
      (fun args ->
         fun t ->
           match args with
           | [] -> Obj.magic (Obj.repr (fun uu___ -> t))
           | a::args' ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x =
                         let x1 = mk_arr args' t ps in
                         FStarC_Reflection_V2_Data.C_Total x1 in
                       pack (Tv_Arrow (a, x))))) uu___1 uu___
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
                (fun uu___ ->
                   FStarC_Reflection_V2_Data.Sg_Let
                     (isrec, (FStar_List_Tot_Base.map close_lb lbs))))
       | Sg_Inductive { nm; univs1 = univs; params; typ; ctors;_} ->
           Obj.magic
             (Obj.repr
                (fun ps ->
                   let x = FStar_List_Tot_Base.length params in
                   let x1 =
                     FStar_Tactics_Util.map
                       (fun uu___ ->
                          match uu___ with
                          | (nm1, ty) ->
                              (fun ps1 ->
                                 let x2 = mk_arr params ty ps1 in (nm1, x2)))
                       ctors ps in
                   let x2 = close_term_n params typ in
                   match x2 with
                   | (params1, typ1) ->
                       let x3 = close_univ_s univs in
                       (match x3 with
                        | (univs1, s) ->
                            let x4 = subst_r_binders s params1 in
                            let x5 =
                              FStarC_Reflection_V2_Builtins.subst_term
                                (FStar_Reflection_V2_Derived.shift_subst x s)
                                typ1 in
                            let x6 =
                              FStar_Tactics_Util.map
                                (fun uu___ ->
                                   (fun uu___ ->
                                      Obj.magic
                                        (fun uu___1 ->
                                           match uu___ with
                                           | (nm1, ty) ->
                                               (nm1,
                                                 (FStarC_Reflection_V2_Builtins.subst_term
                                                    s ty)))) uu___) x1 ps in
                            FStarC_Reflection_V2_Data.Sg_Inductive
                              (nm, univs1, x4, x5, x6))))
       | Sg_Val { nm1 = nm; univs2 = univs; typ1 = typ;_} ->
           Obj.magic
             (Obj.repr
                (fun uu___ ->
                   match close_univ_s univs with
                   | (univs1, s) ->
                       FStarC_Reflection_V2_Data.Sg_Val
                         (nm, univs1,
                           (FStarC_Reflection_V2_Builtins.subst_term s typ)))))
      uu___
let (inspect_sigelt :
  FStarC_Reflection_Types.sigelt ->
    (named_sigelt_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    fun ps ->
      let x = FStarC_Reflection_V2_Builtins.inspect_sigelt s in
      open_sigelt_view x ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.NamedView.inspect_sigelt" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.NamedView.inspect_sigelt (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  inspect_sigelt)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_sigelt
               e_named_sigelt_view psc ncb us args)
let (pack_sigelt :
  named_sigelt_view ->
    (FStarC_Reflection_Types.sigelt, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun sv ->
    fun ps ->
      let x = close_sigelt_view sv ps in
      FStarC_Reflection_V2_Builtins.pack_sigelt x
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.NamedView.pack_sigelt" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.NamedView.pack_sigelt (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 pack_sigelt)
               e_named_sigelt_view
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_sigelt psc ncb
               us args)
let (tcc :
  FStarC_Reflection_Types.env ->
    term -> (comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun t ->
      fun ps ->
        let x = FStarC_Tactics_V2_Builtins.tcc e t ps in
        FStarC_Reflection_V2_Builtins.inspect_comp x
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.NamedView.tcc" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.NamedView.tcc (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_2 tcc)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_env
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_comp_view psc
               ncb us args)
let (comp_to_string :
  comp -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun c ->
    FStarC_Tactics_V2_Builtins.comp_to_string
      (FStarC_Reflection_V2_Builtins.pack_comp c)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.NamedView.comp_to_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.NamedView.comp_to_string (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  comp_to_string)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_comp_view
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string psc ncb us
               args)
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
    fun ps ->
      let x = inspect t ps in
      match x with
      | Tv_Var bv1 -> "Tv_Var"
      | Tv_BVar fv -> "Tv_BVar"
      | Tv_FVar fv -> "Tv_FVar"
      | Tv_UInst (uu___, uu___1) -> "Tv_UInst"
      | Tv_App (f, x1) -> "Tv_App"
      | Tv_Abs (x1, t1) -> "Tv_Abs"
      | Tv_Arrow (x1, t1) -> "Tv_Arrow"
      | Tv_Type uu___ -> "Tv_Type"
      | Tv_Refine (x1, t1) -> "Tv_Refine"
      | Tv_Const cst -> "Tv_Const"
      | Tv_Uvar (i, t1) -> "Tv_Uvar"
      | Tv_Let (r, attrs, b, t1, t2) -> "Tv_Let"
      | Tv_Match (t1, uu___, branches) -> "Tv_Match"
      | Tv_AscribedT (uu___, uu___1, uu___2, uu___3) -> "Tv_AscribedT"
      | Tv_AscribedC (uu___, uu___1, uu___2, uu___3) -> "Tv_AscribedC"
      | Tv_Unknown -> "Tv_Unknown"
      | Tv_Unsupp -> "Tv_Unsupp"
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.NamedView.tag_of" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.NamedView.tag_of (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 tag_of)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string psc ncb us
               args)
