open Fstarcompiler
open Prims
type ('s, 'a) named = 'a
let (fakeunit : FStarC_Reflection_Types.term) =
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_FVar
       (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "unit"]))
type ('a, 'b, 'f, 'g, 'x) f_inverses = unit
type atom = FStar_Tactics_NamedView.term
type parsed_type =
  | Atom of atom 
  | Tuple2 of parsed_type * parsed_type 
  | Either of parsed_type * parsed_type 
  | Named of Prims.string * parsed_type 
let rec __knot_e_parsed_type _ =
  Fstarcompiler.FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Tactics.PrettifyType.parsed_type"
    (fun tm_0 ->
       match tm_0 with
       | ("FStar.Tactics.PrettifyType.Atom", _0_2::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _0_2)
             (fun _0_2 -> FStar_Pervasives_Native.Some (Atom _0_2))
       | ("FStar.Tactics.PrettifyType.Tuple2", _0_4::_1_5::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                (__knot_e_parsed_type ()) _0_4)
             (fun _0_4 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (__knot_e_parsed_type ()) _1_5)
                  (fun _1_5 ->
                     FStar_Pervasives_Native.Some (Tuple2 (_0_4, _1_5))))
       | ("FStar.Tactics.PrettifyType.Either", _0_7::_1_8::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                (__knot_e_parsed_type ()) _0_7)
             (fun _0_7 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (__knot_e_parsed_type ()) _1_8)
                  (fun _1_8 ->
                     FStar_Pervasives_Native.Some (Either (_0_7, _1_8))))
       | ("FStar.Tactics.PrettifyType.Named", _0_10::_1_11::[]) ->
           Fstarcompiler.FStarC_Option.bind
             (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                Fstarcompiler.FStarC_Syntax_Embeddings.e_string _0_10)
             (fun _0_10 ->
                Fstarcompiler.FStarC_Option.bind
                  (Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (__knot_e_parsed_type ()) _1_11)
                  (fun _1_11 ->
                     FStar_Pervasives_Native.Some (Named (_0_10, _1_11))))
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_12 ->
       match tm_12 with
       | Atom _0_14 ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.PrettifyType.Atom"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term _0_14),
                FStar_Pervasives_Native.None)]
       | Tuple2 (_0_16, _1_17) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.PrettifyType.Tuple2"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  (__knot_e_parsed_type ()) _0_16),
                FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (__knot_e_parsed_type ()) _1_17),
               FStar_Pervasives_Native.None)]
       | Either (_0_19, _1_20) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.PrettifyType.Either"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  (__knot_e_parsed_type ()) _0_19),
                FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (__knot_e_parsed_type ()) _1_20),
               FStar_Pervasives_Native.None)]
       | Named (_0_22, _1_23) ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str
                   "FStar.Tactics.PrettifyType.Named"))
             [((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                  Fstarcompiler.FStarC_Syntax_Embeddings.e_string _0_22),
                FStar_Pervasives_Native.None);
             ((Fstarcompiler.FStarC_Syntax_Embeddings_Base.extracted_embed
                 (__knot_e_parsed_type ()) _1_23),
               FStar_Pervasives_Native.None)])
let e_parsed_type = __knot_e_parsed_type ()
let (uu___is_Atom : parsed_type -> Prims.bool) =
  fun projectee -> match projectee with | Atom _0 -> true | uu___ -> false
let (__proj__Atom__item___0 : parsed_type -> atom) =
  fun projectee -> match projectee with | Atom _0 -> _0
let (uu___is_Tuple2 : parsed_type -> Prims.bool) =
  fun projectee ->
    match projectee with | Tuple2 (_0, _1) -> true | uu___ -> false
let (__proj__Tuple2__item___0 : parsed_type -> parsed_type) =
  fun projectee -> match projectee with | Tuple2 (_0, _1) -> _0
let (__proj__Tuple2__item___1 : parsed_type -> parsed_type) =
  fun projectee -> match projectee with | Tuple2 (_0, _1) -> _1
let (uu___is_Either : parsed_type -> Prims.bool) =
  fun projectee ->
    match projectee with | Either (_0, _1) -> true | uu___ -> false
let (__proj__Either__item___0 : parsed_type -> parsed_type) =
  fun projectee -> match projectee with | Either (_0, _1) -> _0
let (__proj__Either__item___1 : parsed_type -> parsed_type) =
  fun projectee -> match projectee with | Either (_0, _1) -> _1
let (uu___is_Named : parsed_type -> Prims.bool) =
  fun projectee ->
    match projectee with | Named (_0, _1) -> true | uu___ -> false
let (__proj__Named__item___0 : parsed_type -> Prims.string) =
  fun projectee -> match projectee with | Named (_0, _1) -> _0
let (__proj__Named__item___1 : parsed_type -> parsed_type) =
  fun projectee -> match projectee with | Named (_0, _1) -> _1
let (add_suffix :
  Prims.string ->
    FStarC_Reflection_Types.name -> FStarC_Reflection_Types.name)
  =
  fun s ->
    fun nm ->
      FStarC_Reflection_V2_Builtins.explode_qn
        (Prims.strcat (FStarC_Reflection_V2_Builtins.implode_qn nm) s)
let (add_prefix :
  Prims.string ->
    FStarC_Reflection_Types.name -> FStarC_Reflection_Types.name)
  =
  fun s ->
    fun nm ->
      let uu___ = FStar_List_Tot_Base.unsnoc nm in
      match uu___ with
      | (first, last) ->
          FStar_List_Tot_Base.op_At first [Prims.strcat s last]
type prod_type =
  | Prod of (Prims.string * atom) Prims.list 
let (uu___is_Prod : prod_type -> Prims.bool) = fun projectee -> true
let (__proj__Prod__item___0 : prod_type -> (Prims.string * atom) Prims.list)
  = fun projectee -> match projectee with | Prod _0 -> _0
type flat_type =
  | Sum of (Prims.string * prod_type) Prims.list 
let (uu___is_Sum : flat_type -> Prims.bool) = fun projectee -> true
let (__proj__Sum__item___0 :
  flat_type -> (Prims.string * prod_type) Prims.list) =
  fun projectee -> match projectee with | Sum _0 -> _0
type cfg_t =
  {
  at: parsed_type ;
  fat: flat_type ;
  orig_tynm: FStarC_Reflection_Types.name ;
  pretty_tynm: FStarC_Reflection_Types.name ;
  ctors: FStarC_Reflection_V2_Data.ctor Prims.list }
let (__proj__Mkcfg_t__item__at : cfg_t -> parsed_type) =
  fun projectee ->
    match projectee with | { at; fat; orig_tynm; pretty_tynm; ctors;_} -> at
let (__proj__Mkcfg_t__item__fat : cfg_t -> flat_type) =
  fun projectee ->
    match projectee with | { at; fat; orig_tynm; pretty_tynm; ctors;_} -> fat
let (__proj__Mkcfg_t__item__orig_tynm :
  cfg_t -> FStarC_Reflection_Types.name) =
  fun projectee ->
    match projectee with
    | { at; fat; orig_tynm; pretty_tynm; ctors;_} -> orig_tynm
let (__proj__Mkcfg_t__item__pretty_tynm :
  cfg_t -> FStarC_Reflection_Types.name) =
  fun projectee ->
    match projectee with
    | { at; fat; orig_tynm; pretty_tynm; ctors;_} -> pretty_tynm
let (__proj__Mkcfg_t__item__ctors :
  cfg_t -> FStarC_Reflection_V2_Data.ctor Prims.list) =
  fun projectee ->
    match projectee with
    | { at; fat; orig_tynm; pretty_tynm; ctors;_} -> ctors
let rec (parsed_type_to_string :
  parsed_type -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun t ->
    match t with
    | Atom t1 -> FStarC_Tactics_V2_Builtins.term_to_string t1
    | Tuple2 (a, b) ->
        let uu___ =
          let uu___1 = parsed_type_to_string a in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                     (Prims.of_int (41)) (Prims.of_int (10))
                     (Prims.of_int (41)) (Prims.of_int (33)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                     (Prims.of_int (41)) (Prims.of_int (10))
                     (Prims.of_int (41)) (Prims.of_int (72)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               (fun uu___2 ->
                  let uu___3 =
                    let uu___4 =
                      let uu___5 = parsed_type_to_string b in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PrettifyType.fst"
                                 (Prims.of_int (41)) (Prims.of_int (43))
                                 (Prims.of_int (41)) (Prims.of_int (66)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (613)) (Prims.of_int (19))
                                 (Prims.of_int (613)) (Prims.of_int (31)))))
                        (Obj.magic uu___5)
                        (fun uu___6 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___7 -> Prims.strcat uu___6 ")")) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.PrettifyType.fst"
                               (Prims.of_int (41)) (Prims.of_int (43))
                               (Prims.of_int (41)) (Prims.of_int (72)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Prims.fst"
                               (Prims.of_int (613)) (Prims.of_int (19))
                               (Prims.of_int (613)) (Prims.of_int (31)))))
                      (Obj.magic uu___4)
                      (fun uu___5 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___6 -> Prims.strcat ", " uu___5)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.PrettifyType.fst"
                                (Prims.of_int (41)) (Prims.of_int (36))
                                (Prims.of_int (41)) (Prims.of_int (72)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Prims.fst"
                                (Prims.of_int (613)) (Prims.of_int (19))
                                (Prims.of_int (613)) (Prims.of_int (31)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___5 -> Prims.strcat uu___2 uu___4))))
                 uu___2) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                   (Prims.of_int (41)) (Prims.of_int (10))
                   (Prims.of_int (41)) (Prims.of_int (72)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (613))
                   (Prims.of_int (19)) (Prims.of_int (613))
                   (Prims.of_int (31))))) (Obj.magic uu___)
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 -> Prims.strcat "(" uu___1))
    | Either (a, b) ->
        let uu___ =
          let uu___1 = parsed_type_to_string a in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                     (Prims.of_int (43)) (Prims.of_int (10))
                     (Prims.of_int (43)) (Prims.of_int (33)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                     (Prims.of_int (43)) (Prims.of_int (10))
                     (Prims.of_int (43)) (Prims.of_int (73)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               (fun uu___2 ->
                  let uu___3 =
                    let uu___4 =
                      let uu___5 = parsed_type_to_string b in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PrettifyType.fst"
                                 (Prims.of_int (43)) (Prims.of_int (44))
                                 (Prims.of_int (43)) (Prims.of_int (67)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (613)) (Prims.of_int (19))
                                 (Prims.of_int (613)) (Prims.of_int (31)))))
                        (Obj.magic uu___5)
                        (fun uu___6 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___7 -> Prims.strcat uu___6 ")")) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.PrettifyType.fst"
                               (Prims.of_int (43)) (Prims.of_int (44))
                               (Prims.of_int (43)) (Prims.of_int (73)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Prims.fst"
                               (Prims.of_int (613)) (Prims.of_int (19))
                               (Prims.of_int (613)) (Prims.of_int (31)))))
                      (Obj.magic uu___4)
                      (fun uu___5 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___6 -> Prims.strcat " + " uu___5)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.PrettifyType.fst"
                                (Prims.of_int (43)) (Prims.of_int (36))
                                (Prims.of_int (43)) (Prims.of_int (73)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Prims.fst"
                                (Prims.of_int (613)) (Prims.of_int (19))
                                (Prims.of_int (613)) (Prims.of_int (31)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___5 -> Prims.strcat uu___2 uu___4))))
                 uu___2) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                   (Prims.of_int (43)) (Prims.of_int (10))
                   (Prims.of_int (43)) (Prims.of_int (73)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (613))
                   (Prims.of_int (19)) (Prims.of_int (613))
                   (Prims.of_int (31))))) (Obj.magic uu___)
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 -> Prims.strcat "(" uu___1))
    | Named (s, a) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = parsed_type_to_string a in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                         (Prims.of_int (45)) (Prims.of_int (21))
                         (Prims.of_int (45)) (Prims.of_int (44)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Prims.fst" (Prims.of_int (613))
                         (Prims.of_int (19)) (Prims.of_int (613))
                         (Prims.of_int (31))))) (Obj.magic uu___3)
                (fun uu___4 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___5 -> Prims.strcat uu___4 ")")) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                       (Prims.of_int (45)) (Prims.of_int (21))
                       (Prims.of_int (45)) (Prims.of_int (50)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Prims.fst" (Prims.of_int (613))
                       (Prims.of_int (19)) (Prims.of_int (613))
                       (Prims.of_int (31))))) (Obj.magic uu___2)
              (fun uu___3 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___4 -> Prims.strcat ": " uu___3)) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                     (Prims.of_int (45)) (Prims.of_int (14))
                     (Prims.of_int (45)) (Prims.of_int (50)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Prims.fst" (Prims.of_int (613))
                     (Prims.of_int (19)) (Prims.of_int (613))
                     (Prims.of_int (31))))) (Obj.magic uu___1)
            (fun uu___2 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___3 -> Prims.strcat s uu___2)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                   (Prims.of_int (45)) (Prims.of_int (10))
                   (Prims.of_int (45)) (Prims.of_int (50)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (613))
                   (Prims.of_int (19)) (Prims.of_int (613))
                   (Prims.of_int (31))))) (Obj.magic uu___)
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 -> Prims.strcat "(" uu___1))
let rec (parse_prod_type :
  FStar_Tactics_NamedView.term ->
    (parsed_type, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Tactics_V2_SyntaxHelpers.collect_app t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (48)) (Prims.of_int (17)) (Prims.of_int (48))
               (Prims.of_int (30)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (47)) (Prims.of_int (52)) (Prims.of_int (62))
               (Prims.of_int (10))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | (hd, args) ->
                let uu___2 =
                  let uu___3 = FStar_Tactics_NamedView.inspect hd in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.PrettifyType.fst"
                             (Prims.of_int (49)) (Prims.of_int (8))
                             (Prims.of_int (49)) (Prims.of_int (18)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.PrettifyType.fst"
                             (Prims.of_int (49)) (Prims.of_int (8))
                             (Prims.of_int (49)) (Prims.of_int (24)))))
                    (Obj.magic uu___3)
                    (fun uu___4 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___5 -> (uu___4, args))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PrettifyType.fst"
                              (Prims.of_int (49)) (Prims.of_int (8))
                              (Prims.of_int (49)) (Prims.of_int (24)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PrettifyType.fst"
                              (Prims.of_int (49)) (Prims.of_int (2))
                              (Prims.of_int (62)) (Prims.of_int (10)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           match uu___3 with
                           | (FStar_Tactics_NamedView.Tv_UInst (fv, uu___4),
                              (a1, FStarC_Reflection_V2_Data.Q_Explicit)::
                              (a2, FStarC_Reflection_V2_Data.Q_Explicit)::[])
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (let uu___5 =
                                       FStar_Tactics_NamedView.inspect a1 in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.PrettifyType.fst"
                                                (Prims.of_int (52))
                                                (Prims.of_int (10))
                                                (Prims.of_int (52))
                                                (Prims.of_int (20)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.PrettifyType.fst"
                                                (Prims.of_int (51))
                                                (Prims.of_int (56))
                                                (Prims.of_int (60))
                                                (Prims.of_int (3)))))
                                       (Obj.magic uu___5)
                                       (fun uu___6 ->
                                          (fun uu___6 ->
                                             match uu___6 with
                                             | FStar_Tactics_NamedView.Tv_Const
                                                 (FStarC_Reflection_V2_Data.C_String
                                                 s) ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (let uu___7 =
                                                         parse_prod_type a2 in
                                                       FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.PrettifyType.fst"
                                                                  (Prims.of_int (54))
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (54))
                                                                  (Prims.of_int (34)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.PrettifyType.fst"
                                                                  (Prims.of_int (54))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (54))
                                                                  (Prims.of_int (34)))))
                                                         (Obj.magic uu___7)
                                                         (fun uu___8 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___9 ->
                                                                 Named
                                                                   (s,
                                                                    uu___8)))))
                                             | uu___7 ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (if
                                                         (FStarC_Reflection_V2_Builtins.inspect_fv
                                                            fv)
                                                           =
                                                           ["FStar";
                                                           "Pervasives";
                                                           "Native";
                                                           "tuple2"]
                                                       then
                                                         Obj.repr
                                                           (let uu___8 =
                                                              parse_prod_type
                                                                a1 in
                                                            FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (35)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (56)))))
                                                              (Obj.magic
                                                                 uu___8)
                                                              (fun uu___9 ->
                                                                 (fun uu___9
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    parse_prod_type
                                                                    a2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Tuple2
                                                                    (uu___9,
                                                                    uu___11)))))
                                                                   uu___9))
                                                       else
                                                         Obj.repr
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___9 ->
                                                                 Atom t)))))
                                            uu___6)))
                           | (FStar_Tactics_NamedView.Tv_FVar fv,
                              (a1, FStarC_Reflection_V2_Data.Q_Explicit)::
                              (a2, FStarC_Reflection_V2_Data.Q_Explicit)::[])
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (let uu___4 =
                                       FStar_Tactics_NamedView.inspect a1 in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.PrettifyType.fst"
                                                (Prims.of_int (52))
                                                (Prims.of_int (10))
                                                (Prims.of_int (52))
                                                (Prims.of_int (20)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.PrettifyType.fst"
                                                (Prims.of_int (51))
                                                (Prims.of_int (56))
                                                (Prims.of_int (60))
                                                (Prims.of_int (3)))))
                                       (Obj.magic uu___4)
                                       (fun uu___5 ->
                                          (fun uu___5 ->
                                             match uu___5 with
                                             | FStar_Tactics_NamedView.Tv_Const
                                                 (FStarC_Reflection_V2_Data.C_String
                                                 s) ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (let uu___6 =
                                                         parse_prod_type a2 in
                                                       FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.PrettifyType.fst"
                                                                  (Prims.of_int (54))
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (54))
                                                                  (Prims.of_int (34)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.PrettifyType.fst"
                                                                  (Prims.of_int (54))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (54))
                                                                  (Prims.of_int (34)))))
                                                         (Obj.magic uu___6)
                                                         (fun uu___7 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___8 ->
                                                                 Named
                                                                   (s,
                                                                    uu___7)))))
                                             | uu___6 ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (if
                                                         (FStarC_Reflection_V2_Builtins.inspect_fv
                                                            fv)
                                                           =
                                                           ["FStar";
                                                           "Pervasives";
                                                           "Native";
                                                           "tuple2"]
                                                       then
                                                         Obj.repr
                                                           (let uu___7 =
                                                              parse_prod_type
                                                                a1 in
                                                            FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (35)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (56)))))
                                                              (Obj.magic
                                                                 uu___7)
                                                              (fun uu___8 ->
                                                                 (fun uu___8
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    parse_prod_type
                                                                    a2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Tuple2
                                                                    (uu___8,
                                                                    uu___10)))))
                                                                   uu___8))
                                                       else
                                                         Obj.repr
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___8 ->
                                                                 Atom t)))))
                                            uu___5)))
                           | uu___4 ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___5 -> Atom t)))) uu___3)))
           uu___1)
let rec (parse_sum_type :
  FStar_Tactics_NamedView.term ->
    (parsed_type, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Tactics_V2_SyntaxHelpers.collect_app t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (65)) (Prims.of_int (17)) (Prims.of_int (65))
               (Prims.of_int (30)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (64)) (Prims.of_int (51)) (Prims.of_int (79))
               (Prims.of_int (21))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | (hd, args) ->
                let uu___2 =
                  let uu___3 = FStar_Tactics_NamedView.inspect hd in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.PrettifyType.fst"
                             (Prims.of_int (66)) (Prims.of_int (8))
                             (Prims.of_int (66)) (Prims.of_int (18)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.PrettifyType.fst"
                             (Prims.of_int (66)) (Prims.of_int (8))
                             (Prims.of_int (66)) (Prims.of_int (24)))))
                    (Obj.magic uu___3)
                    (fun uu___4 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___5 -> (uu___4, args))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PrettifyType.fst"
                              (Prims.of_int (66)) (Prims.of_int (8))
                              (Prims.of_int (66)) (Prims.of_int (24)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PrettifyType.fst"
                              (Prims.of_int (66)) (Prims.of_int (2))
                              (Prims.of_int (79)) (Prims.of_int (21)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           match uu___3 with
                           | (FStar_Tactics_NamedView.Tv_UInst (fv, uu___4),
                              (a1, FStarC_Reflection_V2_Data.Q_Explicit)::
                              (a2, FStarC_Reflection_V2_Data.Q_Explicit)::[])
                               ->
                               let uu___5 =
                                 FStar_Tactics_NamedView.inspect a1 in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.PrettifyType.fst"
                                             (Prims.of_int (69))
                                             (Prims.of_int (10))
                                             (Prims.of_int (69))
                                             (Prims.of_int (20)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.PrettifyType.fst"
                                             (Prims.of_int (68))
                                             (Prims.of_int (56))
                                             (Prims.of_int (77))
                                             (Prims.of_int (3)))))
                                    (Obj.magic uu___5)
                                    (fun uu___6 ->
                                       (fun uu___6 ->
                                          match uu___6 with
                                          | FStar_Tactics_NamedView.Tv_Const
                                              (FStarC_Reflection_V2_Data.C_String
                                              s) ->
                                              let uu___7 = parse_sum_type a2 in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.PrettifyType.fst"
                                                            (Prims.of_int (71))
                                                            (Prims.of_int (14))
                                                            (Prims.of_int (71))
                                                            (Prims.of_int (33)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.PrettifyType.fst"
                                                            (Prims.of_int (71))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (71))
                                                            (Prims.of_int (33)))))
                                                   (Obj.magic uu___7)
                                                   (fun uu___8 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___9 ->
                                                           Named (s, uu___8))))
                                          | uu___7 ->
                                              if
                                                (FStarC_Reflection_V2_Builtins.inspect_fv
                                                   fv)
                                                  =
                                                  ["FStar";
                                                  "Pervasives";
                                                  "either"]
                                              then
                                                let uu___8 =
                                                  parse_sum_type a1 in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.PrettifyType.fst"
                                                              (Prims.of_int (74))
                                                              (Prims.of_int (15))
                                                              (Prims.of_int (74))
                                                              (Prims.of_int (34)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.PrettifyType.fst"
                                                              (Prims.of_int (74))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (74))
                                                              (Prims.of_int (54)))))
                                                     (Obj.magic uu___8)
                                                     (fun uu___9 ->
                                                        (fun uu___9 ->
                                                           let uu___10 =
                                                             parse_sum_type
                                                               a2 in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (54)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (54)))))
                                                                (Obj.magic
                                                                   uu___10)
                                                                (fun uu___11
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Either
                                                                    (uu___9,
                                                                    uu___11)))))
                                                          uu___9))
                                              else
                                                Obj.magic (parse_prod_type t))
                                         uu___6))
                           | (FStar_Tactics_NamedView.Tv_FVar fv,
                              (a1, FStarC_Reflection_V2_Data.Q_Explicit)::
                              (a2, FStarC_Reflection_V2_Data.Q_Explicit)::[])
                               ->
                               let uu___4 =
                                 FStar_Tactics_NamedView.inspect a1 in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.PrettifyType.fst"
                                             (Prims.of_int (69))
                                             (Prims.of_int (10))
                                             (Prims.of_int (69))
                                             (Prims.of_int (20)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.PrettifyType.fst"
                                             (Prims.of_int (68))
                                             (Prims.of_int (56))
                                             (Prims.of_int (77))
                                             (Prims.of_int (3)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       (fun uu___5 ->
                                          match uu___5 with
                                          | FStar_Tactics_NamedView.Tv_Const
                                              (FStarC_Reflection_V2_Data.C_String
                                              s) ->
                                              let uu___6 = parse_sum_type a2 in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.PrettifyType.fst"
                                                            (Prims.of_int (71))
                                                            (Prims.of_int (14))
                                                            (Prims.of_int (71))
                                                            (Prims.of_int (33)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.PrettifyType.fst"
                                                            (Prims.of_int (71))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (71))
                                                            (Prims.of_int (33)))))
                                                   (Obj.magic uu___6)
                                                   (fun uu___7 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___8 ->
                                                           Named (s, uu___7))))
                                          | uu___6 ->
                                              if
                                                (FStarC_Reflection_V2_Builtins.inspect_fv
                                                   fv)
                                                  =
                                                  ["FStar";
                                                  "Pervasives";
                                                  "either"]
                                              then
                                                let uu___7 =
                                                  parse_sum_type a1 in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.PrettifyType.fst"
                                                              (Prims.of_int (74))
                                                              (Prims.of_int (15))
                                                              (Prims.of_int (74))
                                                              (Prims.of_int (34)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.PrettifyType.fst"
                                                              (Prims.of_int (74))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (74))
                                                              (Prims.of_int (54)))))
                                                     (Obj.magic uu___7)
                                                     (fun uu___8 ->
                                                        (fun uu___8 ->
                                                           let uu___9 =
                                                             parse_sum_type
                                                               a2 in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (54)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (54)))))
                                                                (Obj.magic
                                                                   uu___9)
                                                                (fun uu___10
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Either
                                                                    (uu___8,
                                                                    uu___10)))))
                                                          uu___8))
                                              else
                                                Obj.magic (parse_prod_type t))
                                         uu___5))
                           | uu___4 -> Obj.magic (parse_prod_type t)) uu___3)))
           uu___1)
let (parse_type :
  FStar_Tactics_NamedView.term ->
    (parsed_type, unit) FStar_Tactics_Effect.tac_repr)
  = parse_sum_type
let (prod_type_to_string :
  prod_type -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun t ->
    match t with
    | Prod ts ->
        let uu___ =
          FStar_Tactics_Util.map
            (fun uu___1 ->
               match uu___1 with
               | (s, t1) ->
                   let uu___2 =
                     let uu___3 =
                       FStarC_Tactics_V2_Builtins.term_to_string t1 in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.PrettifyType.fst"
                                (Prims.of_int (86)) (Prims.of_int (60))
                                (Prims.of_int (86)) (Prims.of_int (76)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Prims.fst"
                                (Prims.of_int (613)) (Prims.of_int (19))
                                (Prims.of_int (613)) (Prims.of_int (31)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___5 -> Prims.strcat ":" uu___4)) in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PrettifyType.fst"
                              (Prims.of_int (86)) (Prims.of_int (54))
                              (Prims.of_int (86)) (Prims.of_int (76)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Prims.fst"
                              (Prims.of_int (613)) (Prims.of_int (19))
                              (Prims.of_int (613)) (Prims.of_int (31)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___4 -> Prims.strcat s uu___3))) ts in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                   (Prims.of_int (86)) (Prims.of_int (13))
                   (Prims.of_int (86)) (Prims.of_int (77)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (613))
                   (Prims.of_int (19)) (Prims.of_int (613))
                   (Prims.of_int (31))))) (Obj.magic uu___)
          (fun ts1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  Prims.strcat "{"
                    (Prims.strcat (FStar_String.concat "; " ts1) "}")))
let (flat_type_to_string :
  flat_type -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun t ->
    match t with
    | Sum ts ->
        let uu___ =
          FStar_Tactics_Util.map
            (fun uu___1 ->
               match uu___1 with
               | (s, t1) ->
                   let uu___2 =
                     let uu___3 = prod_type_to_string t1 in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.PrettifyType.fst"
                                (Prims.of_int (92)) (Prims.of_int (63))
                                (Prims.of_int (92)) (Prims.of_int (84)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Prims.fst"
                                (Prims.of_int (613)) (Prims.of_int (19))
                                (Prims.of_int (613)) (Prims.of_int (31)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___5 -> Prims.strcat " of " uu___4)) in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PrettifyType.fst"
                              (Prims.of_int (92)) (Prims.of_int (54))
                              (Prims.of_int (92)) (Prims.of_int (84)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Prims.fst"
                              (Prims.of_int (613)) (Prims.of_int (19))
                              (Prims.of_int (613)) (Prims.of_int (31)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___4 -> Prims.strcat s uu___3))) ts in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                   (Prims.of_int (92)) (Prims.of_int (13))
                   (Prims.of_int (92)) (Prims.of_int (85)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (613))
                   (Prims.of_int (19)) (Prims.of_int (613))
                   (Prims.of_int (31))))) (Obj.magic uu___)
          (fun ts1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  Prims.strcat "("
                    (Prims.strcat (FStar_String.concat " | " ts1) ")")))
let rec (as_prod_type :
  Prims.nat ->
    parsed_type ->
      ((Prims.nat * prod_type), unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun ctr ->
         fun t ->
           match t with
           | Tuple2 (a, b) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = as_prod_type ctr a in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.PrettifyType.fst"
                                (Prims.of_int (98)) (Prims.of_int (23))
                                (Prims.of_int (98)) (Prims.of_int (41)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.PrettifyType.fst"
                                (Prims.of_int (97)) (Prims.of_int (17))
                                (Prims.of_int (100)) (Prims.of_int (23)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             match uu___1 with
                             | (ctr1, Prod aa) ->
                                 let uu___2 = as_prod_type ctr1 b in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.PrettifyType.fst"
                                               (Prims.of_int (99))
                                               (Prims.of_int (23))
                                               (Prims.of_int (99))
                                               (Prims.of_int (41)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.PrettifyType.fst"
                                               (Prims.of_int (98))
                                               (Prims.of_int (44))
                                               (Prims.of_int (100))
                                               (Prims.of_int (23)))))
                                      (Obj.magic uu___2)
                                      (fun uu___3 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 ->
                                              match uu___3 with
                                              | (ctr2, Prod bb) ->
                                                  (ctr2,
                                                    (Prod
                                                       (FStar_List_Tot_Base.op_At
                                                          aa bb))))))) uu___1)))
           | Named (s, Atom t1) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> (ctr, (Prod [(s, t1)])))))
           | Atom t1 ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          ((ctr + Prims.int_one),
                            (Prod
                               [((Prims.strcat "_x" (Prims.string_of_int ctr)),
                                  t1)])))))
           | Either (uu___, uu___1) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_V2_Derived.fail
                       "as_prod_type: not a product type"))
           | Named (uu___, t1) -> Obj.magic (Obj.repr (as_prod_type ctr t1)))
        uu___1 uu___
let rec (flatten_type :
  FStarC_Reflection_Types.name ->
    Prims.nat ->
      parsed_type ->
        ((Prims.nat * flat_type), unit) FStar_Tactics_Effect.tac_repr)
  =
  fun pretty_tynm ->
    fun ctr ->
      fun t ->
        match t with
        | Either (a, b) ->
            let uu___ = flatten_type pretty_tynm ctr a in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                       (Prims.of_int (111)) (Prims.of_int (22))
                       (Prims.of_int (111)) (Prims.of_int (52)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                       (Prims.of_int (110)) (Prims.of_int (17))
                       (Prims.of_int (113)) (Prims.of_int (22)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun uu___1 ->
                    match uu___1 with
                    | (ctr1, Sum aa) ->
                        let uu___2 = flatten_type pretty_tynm ctr1 b in
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.PrettifyType.fst"
                                      (Prims.of_int (112))
                                      (Prims.of_int (22))
                                      (Prims.of_int (112))
                                      (Prims.of_int (52)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.PrettifyType.fst"
                                      (Prims.of_int (111))
                                      (Prims.of_int (55))
                                      (Prims.of_int (113))
                                      (Prims.of_int (22)))))
                             (Obj.magic uu___2)
                             (fun uu___3 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___4 ->
                                     match uu___3 with
                                     | (ctr2, Sum bb) ->
                                         (ctr2,
                                           (Sum
                                              (FStar_List_Tot_Base.op_At aa
                                                 bb))))))) uu___1)
        | Named (s, t1) ->
            let uu___ = as_prod_type Prims.int_zero t1 in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                       (Prims.of_int (115)) (Prims.of_int (15))
                       (Prims.of_int (115)) (Prims.of_int (31)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                       (Prims.of_int (114)) (Prims.of_int (16))
                       (Prims.of_int (116)) (Prims.of_int (21)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      match uu___1 with
                      | (uu___3, p) -> (ctr, (Sum [(s, p)]))))
        | t1 ->
            let uu___ = as_prod_type Prims.int_zero t1 in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                       (Prims.of_int (118)) (Prims.of_int (15))
                       (Prims.of_int (118)) (Prims.of_int (31)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                       (Prims.of_int (117)) (Prims.of_int (8))
                       (Prims.of_int (121)) (Prims.of_int (48)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      match uu___1 with
                      | (uu___3, p) ->
                          (match FStar_List_Tot_Base.unsnoc pretty_tynm with
                           | (uu___4, s) ->
                               ((ctr + Prims.int_one),
                                 (Sum
                                    [((Prims.strcat "Mk"
                                         (Prims.strcat s
                                            (Prims.string_of_int ctr))), p)])))))
let (get_typ_def :
  FStarC_Reflection_Types.name ->
    (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm ->
    let uu___ = FStarC_Tactics_V2_Builtins.top_env () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (131)) (Prims.of_int (10)) (Prims.of_int (131))
               (Prims.of_int (20)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (131)) (Prims.of_int (23)) (Prims.of_int (141))
               (Prims.of_int (3))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun e ->
            let uu___1 =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      FStarC_Reflection_V2_Builtins.lookup_typ e nm)) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                          (Prims.of_int (132)) (Prims.of_int (11))
                          (Prims.of_int (132)) (Prims.of_int (26)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                          (Prims.of_int (133)) (Prims.of_int (2))
                          (Prims.of_int (141)) (Prims.of_int (3)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun se ->
                       match se with
                       | FStar_Pervasives_Native.None ->
                           Obj.magic
                             (FStar_Tactics_V2_Derived.fail
                                "ctors_of_typ: type not found")
                       | FStar_Pervasives_Native.Some se1 ->
                           let uu___2 =
                             FStar_Tactics_NamedView.inspect_sigelt se1 in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PrettifyType.fst"
                                         (Prims.of_int (136))
                                         (Prims.of_int (14))
                                         (Prims.of_int (136))
                                         (Prims.of_int (31)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PrettifyType.fst"
                                         (Prims.of_int (137))
                                         (Prims.of_int (4))
                                         (Prims.of_int (140))
                                         (Prims.of_int (44)))))
                                (Obj.magic uu___2)
                                (fun uu___3 ->
                                   (fun sev ->
                                      match sev with
                                      | FStar_Tactics_NamedView.Sg_Let
                                          {
                                            FStar_Tactics_NamedView.isrec =
                                              uu___3;
                                            FStar_Tactics_NamedView.lbs =
                                              lb::[];_}
                                          ->
                                          Obj.magic
                                            (Obj.repr
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___4 ->
                                                     lb.FStar_Tactics_NamedView.lb_def)))
                                      | uu___3 ->
                                          Obj.magic
                                            (Obj.repr
                                               (FStar_Tactics_V2_Derived.fail
                                                  "get_typ_def: not a let binding?")))
                                     uu___3))) uu___2))) uu___1)
let (mk_ctor :
  FStarC_Reflection_Types.name ->
    Prims.string ->
      prod_type ->
        (FStarC_Reflection_V2_Data.ctor, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tynm ->
    fun s ->
      fun fat ->
        let uu___ =
          Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> fat)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                   (Prims.of_int (144)) (Prims.of_int (20))
                   (Prims.of_int (144)) (Prims.of_int (23)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                   (Prims.of_int (143)) (Prims.of_int (67))
                   (Prims.of_int (157)) (Prims.of_int (8)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | Prod fields ->
                    let uu___2 =
                      FStar_Tactics_Util.map
                        (fun uu___3 ->
                           match uu___3 with
                           | (s1, f) ->
                               let uu___4 =
                                 FStar_Tactics_V2_Derived.fresh_binder f in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.PrettifyType.fst"
                                          (Prims.of_int (146))
                                          (Prims.of_int (32))
                                          (Prims.of_int (146))
                                          (Prims.of_int (46)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.PrettifyType.fst"
                                          (Prims.of_int (146))
                                          (Prims.of_int (52))
                                          (Prims.of_int (146))
                                          (Prims.of_int (81)))))
                                 (Obj.magic uu___4)
                                 (fun b ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___5 ->
                                         {
                                           FStar_Tactics_NamedView.uniq =
                                             (b.FStar_Tactics_NamedView.uniq);
                                           FStar_Tactics_NamedView.ppname =
                                             (FStar_Sealed.seal s1);
                                           FStar_Tactics_NamedView.sort =
                                             (b.FStar_Tactics_NamedView.sort);
                                           FStar_Tactics_NamedView.qual =
                                             (b.FStar_Tactics_NamedView.qual);
                                           FStar_Tactics_NamedView.attrs =
                                             (b.FStar_Tactics_NamedView.attrs)
                                         }))) fields in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PrettifyType.fst"
                                  (Prims.of_int (145)) (Prims.of_int (11))
                                  (Prims.of_int (146)) (Prims.of_int (84)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PrettifyType.fst"
                                  (Prims.of_int (147)) (Prims.of_int (4))
                                  (Prims.of_int (157)) (Prims.of_int (8)))))
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            (fun bs ->
                               let uu___3 =
                                 Obj.magic
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___4 ->
                                         match FStar_List_Tot_Base.unsnoc
                                                 tynm
                                         with
                                         | (mod1, uu___5) ->
                                             FStar_List_Tot_Base.op_At mod1
                                               [s])) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.PrettifyType.fst"
                                             (Prims.of_int (149))
                                             (Prims.of_int (4))
                                             (Prims.of_int (152))
                                             (Prims.of_int (6)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.PrettifyType.fst"
                                             (Prims.of_int (155))
                                             (Prims.of_int (4))
                                             (Prims.of_int (157))
                                             (Prims.of_int (8)))))
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       (fun nm ->
                                          let uu___4 =
                                            FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr
                                              bs
                                              (FStar_Tactics_NamedView.pack
                                                 (FStar_Tactics_NamedView.Tv_FVar
                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                       tynm))) in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.PrettifyType.fst"
                                                        (Prims.of_int (156))
                                                        (Prims.of_int (11))
                                                        (Prims.of_int (156))
                                                        (Prims.of_int (56)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.PrettifyType.fst"
                                                        (Prims.of_int (157))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (157))
                                                        (Prims.of_int (8)))))
                                               (Obj.magic uu___4)
                                               (fun ty ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___5 -> (nm, ty)))))
                                         uu___4))) uu___3))) uu___1)
let (mk_fancy_type :
  cfg_t ->
    (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun cfg ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              FStar_Tactics_NamedView.Sg_Inductive
                {
                  FStar_Tactics_NamedView.nm = (cfg.pretty_tynm);
                  FStar_Tactics_NamedView.univs1 = [];
                  FStar_Tactics_NamedView.params = [];
                  FStar_Tactics_NamedView.typ =
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_Type
                          (FStarC_Reflection_V2_Builtins.pack_universe
                             FStarC_Reflection_V2_Data.Uv_Zero)));
                  FStar_Tactics_NamedView.ctors = (cfg.ctors)
                })) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (162)) (Prims.of_int (11)) (Prims.of_int (168))
               (Prims.of_int (3)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (168)) (Prims.of_int (6)) (Prims.of_int (170))
               (Prims.of_int (6))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun sv ->
            let uu___1 = FStar_Tactics_NamedView.pack_sigelt sv in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                          (Prims.of_int (169)) (Prims.of_int (11))
                          (Prims.of_int (169)) (Prims.of_int (25)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                          (Prims.of_int (170)) (Prims.of_int (2))
                          (Prims.of_int (170)) (Prims.of_int (6)))))
                 (Obj.magic uu___1)
                 (fun se ->
                    FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> [se]))))
           uu___1)
let rec (parsed_type_pat :
  parsed_type ->
    ((FStar_Tactics_NamedView.pattern * FStar_Tactics_NamedView.binders),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun at ->
    match at with
    | Atom t ->
        let uu___ = FStar_Tactics_V2_Derived.fresh_binder t in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                   (Prims.of_int (175)) (Prims.of_int (12))
                   (Prims.of_int (175)) (Prims.of_int (26)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                   (Prims.of_int (176)) (Prims.of_int (4))
                   (Prims.of_int (176)) (Prims.of_int (49)))))
          (Obj.magic uu___)
          (fun b ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  ((FStar_Tactics_NamedView.Pat_Var
                      {
                        FStar_Tactics_NamedView.v =
                          (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                             b);
                        FStar_Tactics_NamedView.sort1 =
                          (FStar_Sealed.seal
                             (FStarC_Reflection_V2_Builtins.pack_ln
                                FStarC_Reflection_V2_Data.Tv_Unknown))
                      }), [b])))
    | Tuple2 (a, b) ->
        let uu___ = parsed_type_pat a in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                   (Prims.of_int (178)) (Prims.of_int (18))
                   (Prims.of_int (178)) (Prims.of_int (35)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                   (Prims.of_int (177)) (Prims.of_int (17))
                   (Prims.of_int (188)) (Prims.of_int (16)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | (p1, bs1) ->
                    let uu___2 = parsed_type_pat b in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PrettifyType.fst"
                                  (Prims.of_int (179)) (Prims.of_int (18))
                                  (Prims.of_int (179)) (Prims.of_int (35)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PrettifyType.fst"
                                  (Prims.of_int (178)) (Prims.of_int (38))
                                  (Prims.of_int (188)) (Prims.of_int (16)))))
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___4 ->
                                 match uu___3 with
                                 | (p2, bs2) ->
                                     ((FStar_Tactics_NamedView.Pat_Cons
                                         {
                                           FStar_Tactics_NamedView.head =
                                             (FStarC_Reflection_V2_Builtins.pack_fv
                                                ["FStar";
                                                "Pervasives";
                                                "Native";
                                                "Mktuple2"]);
                                           FStar_Tactics_NamedView.univs =
                                             FStar_Pervasives_Native.None;
                                           FStar_Tactics_NamedView.subpats =
                                             [(p1, false); (p2, false)]
                                         }),
                                       (FStar_List_Tot_Base.op_At bs1 bs2))))))
               uu___1)
    | Named (uu___, t) -> parsed_type_pat t
    | uu___ ->
        FStar_Tactics_V2_Derived.fail
          "should not happen: parsed_type_pat: not a product type"
let rec (parsed_type_expr :
  parsed_type ->
    FStar_Tactics_NamedView.binders ->
      ((FStar_Tactics_NamedView.term * FStar_Tactics_NamedView.binders),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun at ->
    fun bs ->
      match at with
      | Atom t ->
          let uu___ =
            FStar_Tactics_V2_Derived.guard
              (Prims.op_Negation (Prims.uu___is_Nil bs)) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                     (Prims.of_int (198)) (Prims.of_int (4))
                     (Prims.of_int (198)) (Prims.of_int (25)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                     (Prims.of_int (198)) (Prims.of_int (26))
                     (Prims.of_int (200)) (Prims.of_int (23)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___2 ->
                    match bs with
                    | b::bs1 ->
                        ((FStar_Tactics_NamedView.pack
                            (FStar_Tactics_NamedView.Tv_Var
                               (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                  b))), bs1)))
      | Tuple2 (a, b) ->
          let uu___ = parsed_type_expr a bs in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                     (Prims.of_int (202)) (Prims.of_int (17))
                     (Prims.of_int (202)) (Prims.of_int (38)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                     (Prims.of_int (201)) (Prims.of_int (17))
                     (Prims.of_int (206)) (Prims.of_int (9)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  match uu___1 with
                  | (e1, bs1) ->
                      let uu___2 = parsed_type_expr b bs1 in
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.PrettifyType.fst"
                                    (Prims.of_int (203)) (Prims.of_int (17))
                                    (Prims.of_int (203)) (Prims.of_int (38)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.PrettifyType.fst"
                                    (Prims.of_int (202)) (Prims.of_int (41))
                                    (Prims.of_int (206)) (Prims.of_int (9)))))
                           (Obj.magic uu___2)
                           (fun uu___3 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___4 ->
                                   match uu___3 with
                                   | (e2, bs2) ->
                                       ((FStar_Reflection_V2_Derived.mk_e_app
                                           (FStar_Tactics_NamedView.pack
                                              (FStar_Tactics_NamedView.Tv_FVar
                                                 (FStarC_Reflection_V2_Builtins.pack_fv
                                                    ["FStar";
                                                    "Pervasives";
                                                    "Native";
                                                    "Mktuple2"]))) [e1; e2]),
                                         bs2))))) uu___1)
      | Named (uu___, t) -> parsed_type_expr t bs
      | uu___ ->
          FStar_Tactics_V2_Derived.fail
            "should not happen: parsed_type_expr: not a product type"
let (mk_right_case :
  cfg_t ->
    Prims.nat ->
      parsed_type ->
        (FStar_Tactics_NamedView.branch, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun cfg ->
    fun i ->
      fun at ->
        let uu___ = parsed_type_pat at in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                   (Prims.of_int (212)) (Prims.of_int (14))
                   (Prims.of_int (212)) (Prims.of_int (32)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                   (Prims.of_int (211)) (Prims.of_int (106))
                   (Prims.of_int (216)) (Prims.of_int (9)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | (p, bs) ->
                    let uu___2 =
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___3 ->
                              FStar_List_Tot_Base.index cfg.ctors i)) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PrettifyType.fst"
                                  (Prims.of_int (213)) (Prims.of_int (19))
                                  (Prims.of_int (213)) (Prims.of_int (45)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PrettifyType.fst"
                                  (Prims.of_int (212)) (Prims.of_int (35))
                                  (Prims.of_int (216)) (Prims.of_int (9)))))
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            (fun uu___3 ->
                               match uu___3 with
                               | (ctor_nm, uu___4) ->
                                   let uu___5 =
                                     Obj.magic
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___6 ->
                                             FStar_Tactics_NamedView.pack
                                               (FStar_Tactics_NamedView.Tv_FVar
                                                  (FStarC_Reflection_V2_Builtins.pack_fv
                                                     ctor_nm)))) in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.PrettifyType.fst"
                                                 (Prims.of_int (214))
                                                 (Prims.of_int (13))
                                                 (Prims.of_int (214))
                                                 (Prims.of_int (45)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.PrettifyType.fst"
                                                 (Prims.of_int (214))
                                                 (Prims.of_int (48))
                                                 (Prims.of_int (216))
                                                 (Prims.of_int (9)))))
                                        (Obj.magic uu___5)
                                        (fun uu___6 ->
                                           (fun body ->
                                              let uu___6 =
                                                let uu___7 =
                                                  FStar_Tactics_Util.map
                                                    (fun uu___8 ->
                                                       (fun b ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___8 ->
                                                                  FStar_Tactics_NamedView.pack
                                                                    (
                                                                    FStar_Tactics_NamedView.Tv_Var
                                                                    (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                                                    b)))))
                                                         uu___8) bs in
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.PrettifyType.fst"
                                                           (Prims.of_int (215))
                                                           (Prims.of_int (27))
                                                           (Prims.of_int (215))
                                                           (Prims.of_int (84)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.PrettifyType.fst"
                                                           (Prims.of_int (215))
                                                           (Prims.of_int (13))
                                                           (Prims.of_int (215))
                                                           (Prims.of_int (84)))))
                                                  (Obj.magic uu___7)
                                                  (fun uu___8 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___9 ->
                                                          FStar_Reflection_V2_Derived.mk_e_app
                                                            body uu___8)) in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.PrettifyType.fst"
                                                            (Prims.of_int (215))
                                                            (Prims.of_int (13))
                                                            (Prims.of_int (215))
                                                            (Prims.of_int (84)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.PrettifyType.fst"
                                                            (Prims.of_int (216))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (216))
                                                            (Prims.of_int (9)))))
                                                   (Obj.magic uu___6)
                                                   (fun body1 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___7 ->
                                                           (p, body1)))))
                                             uu___6))) uu___3))) uu___1)
let rec (mk_right_body :
  cfg_t ->
    parsed_type ->
      Prims.nat ->
        FStar_Tactics_NamedView.term ->
          ((Prims.nat * FStar_Tactics_NamedView.term), unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun cfg ->
    fun at ->
      fun i ->
        fun sc ->
          match at with
          | Either (l, r) ->
              let uu___ =
                FStar_Tactics_V2_Derived.fresh_binder
                  (FStarC_Reflection_V2_Builtins.pack_ln
                     FStarC_Reflection_V2_Data.Tv_Unknown) in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                         (Prims.of_int (221)) (Prims.of_int (13))
                         (Prims.of_int (221)) (Prims.of_int (30)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                         (Prims.of_int (221)) (Prims.of_int (33))
                         (Prims.of_int (238)) (Prims.of_int (34)))))
                (Obj.magic uu___)
                (fun uu___1 ->
                   (fun v1 ->
                      let uu___1 =
                        FStar_Tactics_V2_Derived.fresh_binder
                          (FStarC_Reflection_V2_Builtins.pack_ln
                             FStarC_Reflection_V2_Data.Tv_Unknown) in
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.PrettifyType.fst"
                                    (Prims.of_int (222)) (Prims.of_int (13))
                                    (Prims.of_int (222)) (Prims.of_int (30)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.PrettifyType.fst"
                                    (Prims.of_int (222)) (Prims.of_int (33))
                                    (Prims.of_int (238)) (Prims.of_int (34)))))
                           (Obj.magic uu___1)
                           (fun uu___2 ->
                              (fun v2 ->
                                 let uu___2 =
                                   Obj.magic
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___3 ->
                                           FStar_Tactics_NamedView.Pat_Cons
                                             {
                                               FStar_Tactics_NamedView.head =
                                                 (FStarC_Reflection_V2_Builtins.pack_fv
                                                    ["FStar";
                                                    "Pervasives";
                                                    "Inl"]);
                                               FStar_Tactics_NamedView.univs
                                                 =
                                                 FStar_Pervasives_Native.None;
                                               FStar_Tactics_NamedView.subpats
                                                 =
                                                 [((FStar_Tactics_NamedView.Pat_Var
                                                      {
                                                        FStar_Tactics_NamedView.v
                                                          =
                                                          (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                                             v1);
                                                        FStar_Tactics_NamedView.sort1
                                                          =
                                                          (FStar_Sealed.seal
                                                             (FStarC_Reflection_V2_Builtins.pack_ln
                                                                FStarC_Reflection_V2_Data.Tv_Unknown))
                                                      }), false)]
                                             })) in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.PrettifyType.fst"
                                               (Prims.of_int (223))
                                               (Prims.of_int (18))
                                               (Prims.of_int (227))
                                               (Prims.of_int (5)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.PrettifyType.fst"
                                               (Prims.of_int (227))
                                               (Prims.of_int (8))
                                               (Prims.of_int (238))
                                               (Prims.of_int (34)))))
                                      (Obj.magic uu___2)
                                      (fun uu___3 ->
                                         (fun pat_inl ->
                                            let uu___3 =
                                              Obj.magic
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___4 ->
                                                      FStar_Tactics_NamedView.Pat_Cons
                                                        {
                                                          FStar_Tactics_NamedView.head
                                                            =
                                                            (FStarC_Reflection_V2_Builtins.pack_fv
                                                               ["FStar";
                                                               "Pervasives";
                                                               "Inr"]);
                                                          FStar_Tactics_NamedView.univs
                                                            =
                                                            FStar_Pervasives_Native.None;
                                                          FStar_Tactics_NamedView.subpats
                                                            =
                                                            [((FStar_Tactics_NamedView.Pat_Var
                                                                 {
                                                                   FStar_Tactics_NamedView.v
                                                                    =
                                                                    (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                                                    v2);
                                                                   FStar_Tactics_NamedView.sort1
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    FStarC_Reflection_V2_Data.Tv_Unknown))
                                                                 }), false)]
                                                        })) in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.PrettifyType.fst"
                                                          (Prims.of_int (228))
                                                          (Prims.of_int (18))
                                                          (Prims.of_int (232))
                                                          (Prims.of_int (5)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.PrettifyType.fst"
                                                          (Prims.of_int (232))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (238))
                                                          (Prims.of_int (34)))))
                                                 (Obj.magic uu___3)
                                                 (fun uu___4 ->
                                                    (fun pat_inr ->
                                                       let uu___4 =
                                                         mk_right_body cfg l
                                                           i
                                                           (FStar_Tactics_NamedView.pack
                                                              (FStar_Tactics_NamedView.Tv_Var
                                                                 (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                                                    v1))) in
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (59)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (34)))))
                                                            (Obj.magic uu___4)
                                                            (fun uu___5 ->
                                                               (fun uu___5 ->
                                                                  match uu___5
                                                                  with
                                                                  | (i1,
                                                                    body1) ->
                                                                    let uu___6
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (pat_inl,
                                                                    body1))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun br1
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    mk_right_body
                                                                    cfg r i1
                                                                    (FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_Var
                                                                    (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                                                    v2))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (i2,
                                                                    body2) ->
                                                                    (i2,
                                                                    (FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_Match
                                                                    (sc,
                                                                    FStar_Pervasives_Native.None,
                                                                    [br1;
                                                                    (pat_inr,
                                                                    body2)]))))))))
                                                                    uu___7)))
                                                                 uu___5)))
                                                      uu___4))) uu___3)))
                                uu___2))) uu___1)
          | uu___ ->
              let uu___1 = mk_right_case cfg i at in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                         (Prims.of_int (242)) (Prims.of_int (17))
                         (Prims.of_int (242)) (Prims.of_int (39)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                         (Prims.of_int (243)) (Prims.of_int (4))
                         (Prims.of_int (243)) (Prims.of_int (41)))))
                (Obj.magic uu___1)
                (fun branch ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        ((i + Prims.int_one),
                          (FStar_Tactics_NamedView.pack
                             (FStar_Tactics_NamedView.Tv_Match
                                (sc, FStar_Pervasives_Native.None, [branch]))))))
let (mk_right :
  cfg_t ->
    (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun cfg ->
    let uu___ =
      FStar_Tactics_V2_Derived.fresh_binder
        (FStar_Tactics_NamedView.pack
           (FStar_Tactics_NamedView.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv cfg.orig_tynm))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (246)) (Prims.of_int (10)) (Prims.of_int (246))
               (Prims.of_int (63)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (246)) (Prims.of_int (66)) (Prims.of_int (260))
               (Prims.of_int (18))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun b ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr [b]
                        (FStar_Tactics_NamedView.pack
                           (FStar_Tactics_NamedView.Tv_FVar
                              (FStarC_Reflection_V2_Builtins.pack_fv
                                 cfg.pretty_tynm))) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.PrettifyType.fst"
                               (Prims.of_int (253)) (Prims.of_int (17))
                               (Prims.of_int (254)) (Prims.of_int (70)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.PrettifyType.fst"
                               (Prims.of_int (251)) (Prims.of_int (8))
                               (Prims.of_int (255)) (Prims.of_int (82)))))
                      (Obj.magic uu___5)
                      (fun uu___6 ->
                         (fun uu___6 ->
                            let uu___7 =
                              let uu___8 =
                                let uu___9 =
                                  mk_right_body cfg cfg.at Prims.int_zero
                                    (FStar_Tactics_NamedView.pack
                                       (FStar_Tactics_NamedView.Tv_Var
                                          (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                             b))) in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.PrettifyType.fst"
                                           (Prims.of_int (255))
                                           (Prims.of_int (36))
                                           (Prims.of_int (255))
                                           (Prims.of_int (80)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.PrettifyType.fst"
                                           (Prims.of_int (255))
                                           (Prims.of_int (28))
                                           (Prims.of_int (255))
                                           (Prims.of_int (81)))))
                                  (Obj.magic uu___9)
                                  (fun uu___10 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___11 ->
                                          FStar_Pervasives_Native.snd uu___10)) in
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PrettifyType.fst"
                                         (Prims.of_int (255))
                                         (Prims.of_int (28))
                                         (Prims.of_int (255))
                                         (Prims.of_int (81)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PrettifyType.fst"
                                         (Prims.of_int (255))
                                         (Prims.of_int (17))
                                         (Prims.of_int (255))
                                         (Prims.of_int (81)))))
                                (Obj.magic uu___8)
                                (fun uu___9 ->
                                   (fun uu___9 ->
                                      Obj.magic
                                        (FStar_Tactics_V2_Derived.mk_abs 
                                           [b] uu___9)) uu___9) in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.PrettifyType.fst"
                                          (Prims.of_int (255))
                                          (Prims.of_int (17))
                                          (Prims.of_int (255))
                                          (Prims.of_int (81)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.PrettifyType.fst"
                                          (Prims.of_int (251))
                                          (Prims.of_int (8))
                                          (Prims.of_int (255))
                                          (Prims.of_int (82)))))
                                 (Obj.magic uu___7)
                                 (fun uu___8 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___9 ->
                                         {
                                           FStar_Tactics_NamedView.lb_fv =
                                             (FStarC_Reflection_V2_Builtins.pack_fv
                                                (add_suffix "_right"
                                                   cfg.pretty_tynm));
                                           FStar_Tactics_NamedView.lb_us = [];
                                           FStar_Tactics_NamedView.lb_typ =
                                             uu___6;
                                           FStar_Tactics_NamedView.lb_def =
                                             uu___8
                                         })))) uu___6) in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.PrettifyType.fst"
                             (Prims.of_int (251)) (Prims.of_int (8))
                             (Prims.of_int (255)) (Prims.of_int (82)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.PrettifyType.fst"
                             (Prims.of_int (249)) (Prims.of_int (10))
                             (Prims.of_int (257)) (Prims.of_int (5)))))
                    (Obj.magic uu___4)
                    (fun uu___5 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___6 -> [uu___5])) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.Tactics.PrettifyType.fst"
                           (Prims.of_int (249)) (Prims.of_int (10))
                           (Prims.of_int (257)) (Prims.of_int (5)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.Tactics.PrettifyType.fst"
                           (Prims.of_int (248)) (Prims.of_int (4))
                           (Prims.of_int (257)) (Prims.of_int (5)))))
                  (Obj.magic uu___3)
                  (fun uu___4 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___5 ->
                          {
                            FStar_Tactics_NamedView.isrec = false;
                            FStar_Tactics_NamedView.lbs = uu___4
                          })) in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                         (Prims.of_int (248)) (Prims.of_int (4))
                         (Prims.of_int (257)) (Prims.of_int (5)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                         (Prims.of_int (247)) (Prims.of_int (11))
                         (Prims.of_int (258)) (Prims.of_int (3)))))
                (Obj.magic uu___2)
                (fun uu___3 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___4 -> FStar_Tactics_NamedView.Sg_Let uu___3)) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                          (Prims.of_int (247)) (Prims.of_int (11))
                          (Prims.of_int (258)) (Prims.of_int (3)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                          (Prims.of_int (260)) (Prims.of_int (2))
                          (Prims.of_int (260)) (Prims.of_int (18)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun sv ->
                       let uu___2 = FStar_Tactics_NamedView.pack_sigelt sv in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.PrettifyType.fst"
                                     (Prims.of_int (260)) (Prims.of_int (3))
                                     (Prims.of_int (260)) (Prims.of_int (17)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.PrettifyType.fst"
                                     (Prims.of_int (260)) (Prims.of_int (2))
                                     (Prims.of_int (260)) (Prims.of_int (18)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___4 -> [uu___3])))) uu___2))) uu___1)
let (mk_left_case :
  cfg_t ->
    Prims.nat ->
      parsed_type ->
        (FStar_Tactics_NamedView.branch, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun cfg ->
    fun i ->
      fun at ->
        let uu___ = parsed_type_pat at in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                   (Prims.of_int (263)) (Prims.of_int (14))
                   (Prims.of_int (263)) (Prims.of_int (32)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                   (Prims.of_int (262)) (Prims.of_int (103))
                   (Prims.of_int (267)) (Prims.of_int (9)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | (p, bs) ->
                    let uu___2 =
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___3 ->
                              FStar_List_Tot_Base.index cfg.ctors i)) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PrettifyType.fst"
                                  (Prims.of_int (264)) (Prims.of_int (19))
                                  (Prims.of_int (264)) (Prims.of_int (45)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PrettifyType.fst"
                                  (Prims.of_int (263)) (Prims.of_int (35))
                                  (Prims.of_int (267)) (Prims.of_int (9)))))
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            (fun uu___3 ->
                               match uu___3 with
                               | (ctor_nm, uu___4) ->
                                   let uu___5 =
                                     Obj.magic
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___6 ->
                                             FStar_Tactics_NamedView.pack
                                               (FStar_Tactics_NamedView.Tv_FVar
                                                  (FStarC_Reflection_V2_Builtins.pack_fv
                                                     ctor_nm)))) in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.PrettifyType.fst"
                                                 (Prims.of_int (265))
                                                 (Prims.of_int (13))
                                                 (Prims.of_int (265))
                                                 (Prims.of_int (45)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.PrettifyType.fst"
                                                 (Prims.of_int (265))
                                                 (Prims.of_int (48))
                                                 (Prims.of_int (267))
                                                 (Prims.of_int (9)))))
                                        (Obj.magic uu___5)
                                        (fun uu___6 ->
                                           (fun body ->
                                              let uu___6 =
                                                let uu___7 =
                                                  FStar_Tactics_Util.map
                                                    (fun uu___8 ->
                                                       (fun b ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___8 ->
                                                                  FStar_Tactics_NamedView.pack
                                                                    (
                                                                    FStar_Tactics_NamedView.Tv_Var
                                                                    (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                                                    b)))))
                                                         uu___8) bs in
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.PrettifyType.fst"
                                                           (Prims.of_int (266))
                                                           (Prims.of_int (27))
                                                           (Prims.of_int (266))
                                                           (Prims.of_int (84)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.PrettifyType.fst"
                                                           (Prims.of_int (266))
                                                           (Prims.of_int (13))
                                                           (Prims.of_int (266))
                                                           (Prims.of_int (84)))))
                                                  (Obj.magic uu___7)
                                                  (fun uu___8 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___9 ->
                                                          FStar_Reflection_V2_Derived.mk_e_app
                                                            body uu___8)) in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.PrettifyType.fst"
                                                            (Prims.of_int (266))
                                                            (Prims.of_int (13))
                                                            (Prims.of_int (266))
                                                            (Prims.of_int (84)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.PrettifyType.fst"
                                                            (Prims.of_int (267))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (267))
                                                            (Prims.of_int (9)))))
                                                   (Obj.magic uu___6)
                                                   (fun body1 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___7 ->
                                                           (p, body1)))))
                                             uu___6))) uu___3))) uu___1)
let rec (mk_left_branches :
  (FStar_Tactics_NamedView.term ->
     (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
    ->
    FStarC_Reflection_V2_Data.ctor Prims.list ->
      parsed_type ->
        ((FStarC_Reflection_V2_Data.ctor Prims.list *
           (FStar_Tactics_NamedView.pattern * FStar_Tactics_NamedView.term)
           Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ff ->
    fun ctors ->
      fun at ->
        match at with
        | Either (l, r) ->
            let uu___ =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      fun t ->
                        FStar_Reflection_V2_Derived.mk_e_app
                          (FStar_Tactics_NamedView.pack
                             (FStar_Tactics_NamedView.Tv_FVar
                                (FStarC_Reflection_V2_Builtins.pack_fv
                                   ["FStar"; "Pervasives"; "Inl"]))) 
                          [t])) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                       (Prims.of_int (272)) (Prims.of_int (30))
                       (Prims.of_int (272)) (Prims.of_int (83)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                       (Prims.of_int (272)) (Prims.of_int (86))
                       (Prims.of_int (276)) (Prims.of_int (22)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun inl ->
                    let uu___1 =
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___2 ->
                              fun t ->
                                FStar_Reflection_V2_Derived.mk_e_app
                                  (FStar_Tactics_NamedView.pack
                                     (FStar_Tactics_NamedView.Tv_FVar
                                        (FStarC_Reflection_V2_Builtins.pack_fv
                                           ["FStar"; "Pervasives"; "Inr"])))
                                  [t])) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PrettifyType.fst"
                                  (Prims.of_int (273)) (Prims.of_int (30))
                                  (Prims.of_int (273)) (Prims.of_int (83)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PrettifyType.fst"
                                  (Prims.of_int (273)) (Prims.of_int (86))
                                  (Prims.of_int (276)) (Prims.of_int (22)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            (fun inr ->
                               let uu___2 =
                                 mk_left_branches (fun t -> ff (inl t)) ctors
                                   l in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.PrettifyType.fst"
                                             (Prims.of_int (274))
                                             (Prims.of_int (22))
                                             (Prims.of_int (274))
                                             (Prims.of_int (68)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.PrettifyType.fst"
                                             (Prims.of_int (273))
                                             (Prims.of_int (86))
                                             (Prims.of_int (276))
                                             (Prims.of_int (22)))))
                                    (Obj.magic uu___2)
                                    (fun uu___3 ->
                                       (fun uu___3 ->
                                          match uu___3 with
                                          | (ctors1, brs1) ->
                                              let uu___4 =
                                                mk_left_branches
                                                  (fun t -> ff (inr t))
                                                  ctors1 r in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.PrettifyType.fst"
                                                            (Prims.of_int (275))
                                                            (Prims.of_int (22))
                                                            (Prims.of_int (275))
                                                            (Prims.of_int (68)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.PrettifyType.fst"
                                                            (Prims.of_int (274))
                                                            (Prims.of_int (71))
                                                            (Prims.of_int (276))
                                                            (Prims.of_int (22)))))
                                                   (Obj.magic uu___4)
                                                   (fun uu___5 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___6 ->
                                                           match uu___5 with
                                                           | (ctors2, brs2)
                                                               ->
                                                               (ctors2,
                                                                 (FStar_List_Tot_Base.op_At
                                                                    brs1 brs2))))))
                                         uu___3))) uu___2))) uu___1)
        | uu___ ->
            let uu___1 =
              FStar_Tactics_V2_Derived.guard
                (Prims.op_Negation (Prims.uu___is_Nil ctors)) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                       (Prims.of_int (278)) (Prims.of_int (4))
                       (Prims.of_int (278)) (Prims.of_int (28)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                       (Prims.of_int (278)) (Prims.of_int (29))
                       (Prims.of_int (292)) (Prims.of_int (22)))))
              (Obj.magic uu___1)
              (fun uu___2 ->
                 (fun uu___2 ->
                    let uu___3 =
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___4 -> ctors)) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PrettifyType.fst"
                                  (Prims.of_int (279)) (Prims.of_int (30))
                                  (Prims.of_int (279)) (Prims.of_int (35)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PrettifyType.fst"
                                  (Prims.of_int (278)) (Prims.of_int (29))
                                  (Prims.of_int (292)) (Prims.of_int (22)))))
                         (Obj.magic uu___3)
                         (fun uu___4 ->
                            (fun uu___4 ->
                               match uu___4 with
                               | (c_nm, c_ty)::ctors1 ->
                                   let uu___5 =
                                     FStar_Tactics_V2_SyntaxHelpers.collect_arr
                                       c_ty in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.PrettifyType.fst"
                                                 (Prims.of_int (281))
                                                 (Prims.of_int (16))
                                                 (Prims.of_int (281))
                                                 (Prims.of_int (32)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.PrettifyType.fst"
                                                 (Prims.of_int (279))
                                                 (Prims.of_int (38))
                                                 (Prims.of_int (292))
                                                 (Prims.of_int (22)))))
                                        (Obj.magic uu___5)
                                        (fun uu___6 ->
                                           (fun uu___6 ->
                                              match uu___6 with
                                              | (bs, uu___7) ->
                                                  let uu___8 =
                                                    FStar_Tactics_Util.map
                                                      (fun b ->
                                                         FStar_Tactics_V2_Derived.fresh_binder
                                                           b) bs in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.PrettifyType.fst"
                                                                (Prims.of_int (282))
                                                                (Prims.of_int (13))
                                                                (Prims.of_int (282))
                                                                (Prims.of_int (71)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.PrettifyType.fst"
                                                                (Prims.of_int (282))
                                                                (Prims.of_int (74))
                                                                (Prims.of_int (292))
                                                                (Prims.of_int (22)))))
                                                       (Obj.magic uu___8)
                                                       (fun uu___9 ->
                                                          (fun bs1 ->
                                                             let uu___9 =
                                                               let uu___10 =
                                                                 let uu___11
                                                                   =
                                                                   FStar_Tactics_Util.map
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun b ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    ((FStar_Tactics_NamedView.Pat_Var
                                                                    {
                                                                    FStar_Tactics_NamedView.v
                                                                    =
                                                                    (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                                                    b);
                                                                    FStar_Tactics_NamedView.sort1
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    FStarC_Reflection_V2_Data.Tv_Unknown))
                                                                    }),
                                                                    false))))
                                                                    uu___12)
                                                                    bs1 in
                                                                 FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (99)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (100)))))
                                                                   (Obj.magic
                                                                    uu___11)
                                                                   (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    {
                                                                    FStar_Tactics_NamedView.head
                                                                    =
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    c_nm);
                                                                    FStar_Tactics_NamedView.univs
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    FStar_Tactics_NamedView.subpats
                                                                    = uu___12
                                                                    })) in
                                                               FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (100)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (5)))))
                                                                 (Obj.magic
                                                                    uu___10)
                                                                 (fun uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_NamedView.Pat_Cons
                                                                    uu___11)) in
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (5)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (22)))))
                                                                  (Obj.magic
                                                                    uu___9)
                                                                  (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun p ->
                                                                    let uu___10
                                                                    =
                                                                    parsed_type_expr
                                                                    at bs1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    (body,
                                                                    rest_bs)
                                                                    ->
                                                                    let uu___12
                                                                    = ff body in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    body1 ->
                                                                    let uu___13
                                                                    =
                                                                    FStar_Tactics_V2_Derived.guard
                                                                    (Prims.uu___is_Nil
                                                                    rest_bs) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (ctors1,
                                                                    [
                                                                    (p,
                                                                    body1)])))))
                                                                    uu___13)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                            uu___9))) uu___6)))
                              uu___4))) uu___2)
let (mk_left_body :
  cfg_t ->
    FStar_Tactics_NamedView.term ->
      (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun cfg ->
    fun sc ->
      let uu___ =
        mk_left_branches
          (fun uu___1 ->
             (fun t ->
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> t)))
               uu___1) cfg.ctors cfg.at in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                 (Prims.of_int (295)) (Prims.of_int (19))
                 (Prims.of_int (295)) (Prims.of_int (65)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                 (Prims.of_int (294)) (Prims.of_int (45))
                 (Prims.of_int (297)) (Prims.of_int (29)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | (ctors, brs) ->
                  let uu___2 =
                    FStar_Tactics_V2_Derived.guard (Prims.uu___is_Nil ctors) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.PrettifyType.fst"
                                (Prims.of_int (296)) (Prims.of_int (2))
                                (Prims.of_int (296)) (Prims.of_int (20)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.PrettifyType.fst"
                                (Prims.of_int (297)) (Prims.of_int (2))
                                (Prims.of_int (297)) (Prims.of_int (29)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___4 ->
                               FStar_Tactics_NamedView.pack
                                 (FStar_Tactics_NamedView.Tv_Match
                                    (sc, FStar_Pervasives_Native.None, brs))))))
             uu___1)
let (mk_left :
  cfg_t ->
    (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun cfg ->
    let uu___ =
      FStar_Tactics_V2_Derived.fresh_binder
        (FStar_Tactics_NamedView.pack
           (FStar_Tactics_NamedView.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv cfg.pretty_tynm))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (300)) (Prims.of_int (10)) (Prims.of_int (300))
               (Prims.of_int (65)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (300)) (Prims.of_int (68)) (Prims.of_int (314))
               (Prims.of_int (18))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun b ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          FStar_Tactics_V2_Derived.fresh_binder
                            (FStar_Tactics_NamedView.pack
                               (FStar_Tactics_NamedView.Tv_FVar
                                  (FStarC_Reflection_V2_Builtins.pack_fv
                                     cfg.pretty_tynm))) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.PrettifyType.fst"
                                   (Prims.of_int (307)) (Prims.of_int (29))
                                   (Prims.of_int (307)) (Prims.of_int (84)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.PrettifyType.fst"
                                   (Prims.of_int (307)) (Prims.of_int (28))
                                   (Prims.of_int (307)) (Prims.of_int (85)))))
                          (Obj.magic uu___7)
                          (fun uu___8 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___9 -> [uu___8])) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PrettifyType.fst"
                                 (Prims.of_int (307)) (Prims.of_int (28))
                                 (Prims.of_int (307)) (Prims.of_int (85)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PrettifyType.fst"
                                 (Prims.of_int (307)) (Prims.of_int (17))
                                 (Prims.of_int (308)) (Prims.of_int (68)))))
                        (Obj.magic uu___6)
                        (fun uu___7 ->
                           (fun uu___7 ->
                              Obj.magic
                                (FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr
                                   uu___7
                                   (FStar_Tactics_NamedView.pack
                                      (FStar_Tactics_NamedView.Tv_FVar
                                         (FStarC_Reflection_V2_Builtins.pack_fv
                                            cfg.orig_tynm))))) uu___7) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.PrettifyType.fst"
                               (Prims.of_int (307)) (Prims.of_int (17))
                               (Prims.of_int (308)) (Prims.of_int (68)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.PrettifyType.fst"
                               (Prims.of_int (305)) (Prims.of_int (8))
                               (Prims.of_int (309)) (Prims.of_int (58)))))
                      (Obj.magic uu___5)
                      (fun uu___6 ->
                         (fun uu___6 ->
                            let uu___7 =
                              let uu___8 =
                                mk_left_body cfg
                                  (FStar_Tactics_NamedView.pack
                                     (FStar_Tactics_NamedView.Tv_Var
                                        (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                           b))) in
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PrettifyType.fst"
                                         (Prims.of_int (309))
                                         (Prims.of_int (28))
                                         (Prims.of_int (309))
                                         (Prims.of_int (57)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PrettifyType.fst"
                                         (Prims.of_int (309))
                                         (Prims.of_int (17))
                                         (Prims.of_int (309))
                                         (Prims.of_int (57)))))
                                (Obj.magic uu___8)
                                (fun uu___9 ->
                                   (fun uu___9 ->
                                      Obj.magic
                                        (FStar_Tactics_V2_Derived.mk_abs 
                                           [b] uu___9)) uu___9) in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.PrettifyType.fst"
                                          (Prims.of_int (309))
                                          (Prims.of_int (17))
                                          (Prims.of_int (309))
                                          (Prims.of_int (57)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.PrettifyType.fst"
                                          (Prims.of_int (305))
                                          (Prims.of_int (8))
                                          (Prims.of_int (309))
                                          (Prims.of_int (58)))))
                                 (Obj.magic uu___7)
                                 (fun uu___8 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___9 ->
                                         {
                                           FStar_Tactics_NamedView.lb_fv =
                                             (FStarC_Reflection_V2_Builtins.pack_fv
                                                (add_suffix "_left"
                                                   cfg.pretty_tynm));
                                           FStar_Tactics_NamedView.lb_us = [];
                                           FStar_Tactics_NamedView.lb_typ =
                                             uu___6;
                                           FStar_Tactics_NamedView.lb_def =
                                             uu___8
                                         })))) uu___6) in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.PrettifyType.fst"
                             (Prims.of_int (305)) (Prims.of_int (8))
                             (Prims.of_int (309)) (Prims.of_int (58)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.PrettifyType.fst"
                             (Prims.of_int (303)) (Prims.of_int (10))
                             (Prims.of_int (311)) (Prims.of_int (5)))))
                    (Obj.magic uu___4)
                    (fun uu___5 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___6 -> [uu___5])) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.Tactics.PrettifyType.fst"
                           (Prims.of_int (303)) (Prims.of_int (10))
                           (Prims.of_int (311)) (Prims.of_int (5)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.Tactics.PrettifyType.fst"
                           (Prims.of_int (302)) (Prims.of_int (4))
                           (Prims.of_int (311)) (Prims.of_int (5)))))
                  (Obj.magic uu___3)
                  (fun uu___4 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___5 ->
                          {
                            FStar_Tactics_NamedView.isrec = false;
                            FStar_Tactics_NamedView.lbs = uu___4
                          })) in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                         (Prims.of_int (302)) (Prims.of_int (4))
                         (Prims.of_int (311)) (Prims.of_int (5)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                         (Prims.of_int (301)) (Prims.of_int (11))
                         (Prims.of_int (312)) (Prims.of_int (3)))))
                (Obj.magic uu___2)
                (fun uu___3 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___4 -> FStar_Tactics_NamedView.Sg_Let uu___3)) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                          (Prims.of_int (301)) (Prims.of_int (11))
                          (Prims.of_int (312)) (Prims.of_int (3)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                          (Prims.of_int (314)) (Prims.of_int (2))
                          (Prims.of_int (314)) (Prims.of_int (18)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun sv ->
                       let uu___2 = FStar_Tactics_NamedView.pack_sigelt sv in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.PrettifyType.fst"
                                     (Prims.of_int (314)) (Prims.of_int (3))
                                     (Prims.of_int (314)) (Prims.of_int (17)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.PrettifyType.fst"
                                     (Prims.of_int (314)) (Prims.of_int (2))
                                     (Prims.of_int (314)) (Prims.of_int (18)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___4 -> [uu___3])))) uu___2))) uu___1)
let rec (prove_left_right_aux :
  parsed_type ->
    FStar_Tactics_NamedView.term ->
      (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
        (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun at ->
    fun m ->
      fun k ->
        match at with
        | Atom uu___ -> k ()
        | Either (l, r) ->
            let uu___ = FStarC_Tactics_V2_Builtins.t_destruct m in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                       (Prims.of_int (323)) (Prims.of_int (16))
                       (Prims.of_int (323)) (Prims.of_int (28)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                       (Prims.of_int (324)) (Prims.of_int (4))
                       (Prims.of_int (333)) (Prims.of_int (5)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun cases ->
                    let uu___1 =
                      FStar_Tactics_V2_Derived.guard
                        ((FStar_List_Tot_Base.length cases) =
                           (Prims.of_int (2))) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PrettifyType.fst"
                                  (Prims.of_int (324)) (Prims.of_int (4))
                                  (Prims.of_int (324)) (Prims.of_int (33)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PrettifyType.fst"
                                  (Prims.of_int (325)) (Prims.of_int (4))
                                  (Prims.of_int (333)) (Prims.of_int (5)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            (fun uu___2 ->
                               let uu___3 =
                                 FStar_Tactics_Util.zip cases [l; r] in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.PrettifyType.fst"
                                             (Prims.of_int (325))
                                             (Prims.of_int (4))
                                             (Prims.of_int (325))
                                             (Prims.of_int (24)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.PrettifyType.fst"
                                             (Prims.of_int (325))
                                             (Prims.of_int (4))
                                             (Prims.of_int (333))
                                             (Prims.of_int (5)))))
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       (fun uu___4 ->
                                          Obj.magic
                                            (FStar_Tactics_Util.iter
                                               (fun uu___5 ->
                                                  match uu___5 with
                                                  | ((c, n), at') ->
                                                      FStar_Tactics_V2_Derived.focus
                                                        (fun uu___6 ->
                                                           let uu___7 =
                                                             FStar_Tactics_Util.repeatn
                                                               n
                                                               FStarC_Tactics_V2_Builtins.intro in
                                                           FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (327))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (327))
                                                                    (Prims.of_int (47)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (36)))))
                                                             (Obj.magic
                                                                uu___7)
                                                             (fun uu___8 ->
                                                                (fun bs ->
                                                                   let uu___8
                                                                    =
                                                                    FStar_Tactics_V2_Derived.guard
                                                                    ((FStar_List_Tot_Base.length
                                                                    bs) =
                                                                    Prims.int_one) in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    -> bs)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    b::[] ->
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.intro
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun b_eq
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.rewrite
                                                                    b_eq in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Obj.magic
                                                                    (prove_left_right_aux
                                                                    at'
                                                                    (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                                    b) k))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___11)))
                                                                    uu___9)))
                                                                  uu___8)))
                                               uu___4)) uu___4))) uu___2)))
                   uu___1)
        | Tuple2 (l, r) ->
            let uu___ = FStarC_Tactics_V2_Builtins.t_destruct m in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                       (Prims.of_int (336)) (Prims.of_int (16))
                       (Prims.of_int (336)) (Prims.of_int (28)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                       (Prims.of_int (337)) (Prims.of_int (4))
                       (Prims.of_int (346)) (Prims.of_int (6)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun cases ->
                    let uu___1 =
                      FStar_Tactics_V2_Derived.guard
                        ((FStar_List_Tot_Base.length cases) = Prims.int_one) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PrettifyType.fst"
                                  (Prims.of_int (337)) (Prims.of_int (4))
                                  (Prims.of_int (337)) (Prims.of_int (33)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PrettifyType.fst"
                                  (Prims.of_int (337)) (Prims.of_int (34))
                                  (Prims.of_int (346)) (Prims.of_int (6)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            (fun uu___2 ->
                               let uu___3 =
                                 Obj.magic
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___4 -> cases)) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.PrettifyType.fst"
                                             (Prims.of_int (338))
                                             (Prims.of_int (19))
                                             (Prims.of_int (338))
                                             (Prims.of_int (24)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.PrettifyType.fst"
                                             (Prims.of_int (337))
                                             (Prims.of_int (34))
                                             (Prims.of_int (346))
                                             (Prims.of_int (6)))))
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       (fun uu___4 ->
                                          match uu___4 with
                                          | (uu___5, n)::[] ->
                                              let uu___6 =
                                                FStar_Tactics_V2_Derived.guard
                                                  (n = (Prims.of_int (2))) in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.PrettifyType.fst"
                                                            (Prims.of_int (339))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (339))
                                                            (Prims.of_int (17)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.PrettifyType.fst"
                                                            (Prims.of_int (339))
                                                            (Prims.of_int (18))
                                                            (Prims.of_int (346))
                                                            (Prims.of_int (6)))))
                                                   (Obj.magic uu___6)
                                                   (fun uu___7 ->
                                                      (fun uu___7 ->
                                                         let uu___8 =
                                                           FStar_Tactics_Util.repeatn
                                                             n
                                                             FStarC_Tactics_V2_Builtins.intro in
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (43)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (6)))))
                                                              (Obj.magic
                                                                 uu___8)
                                                              (fun uu___9 ->
                                                                 (fun bs ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> bs)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    b1::b2::[]
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.intro
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun b_eq
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.rewrite
                                                                    b_eq in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    prove_left_right_aux
                                                                    l
                                                                    (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                                    b1)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    prove_left_right_aux
                                                                    r
                                                                    (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                                    b2) k) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    -> ()))))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                    uu___10)))
                                                                   uu___9)))
                                                        uu___7))) uu___4)))
                              uu___2))) uu___1)
        | Named (uu___, t) -> prove_left_right_aux t m k
let (prove_left_right :
  parsed_type -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun at ->
    let uu___ = FStarC_Tactics_V2_Builtins.intro () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (353)) (Prims.of_int (10)) (Prims.of_int (353))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (354)) (Prims.of_int (2)) (Prims.of_int (355))
               (Prims.of_int (4))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun b ->
            let uu___1 =
              prove_left_right_aux at
                (FStar_Tactics_V2_SyntaxCoercions.binding_to_term b)
                FStar_Tactics_V2_Derived.trefl in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                          (Prims.of_int (354)) (Prims.of_int (2))
                          (Prims.of_int (354)) (Prims.of_int (33)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                          (Prims.of_int (355)) (Prims.of_int (2))
                          (Prims.of_int (355)) (Prims.of_int (4)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))))
           uu___1)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.PrettifyType.prove_left_right" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.PrettifyType.prove_left_right (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  prove_left_right) e_parsed_type
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (prove_right_left : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = FStarC_Tactics_V2_Builtins.intro () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (360)) (Prims.of_int (10)) (Prims.of_int (360))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (360)) (Prims.of_int (21)) (Prims.of_int (370))
               (Prims.of_int (3))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun b ->
            let uu___2 =
              FStarC_Tactics_V2_Builtins.t_destruct
                (FStar_Tactics_V2_SyntaxCoercions.binding_to_term b) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                          (Prims.of_int (361)) (Prims.of_int (14))
                          (Prims.of_int (361)) (Prims.of_int (26)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                          (Prims.of_int (362)) (Prims.of_int (2))
                          (Prims.of_int (370)) (Prims.of_int (3)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun cases ->
                       Obj.magic
                         (FStar_Tactics_Util.iter
                            (fun uu___3 ->
                               match uu___3 with
                               | (c, n) ->
                                   FStar_Tactics_V2_Derived.focus
                                     (fun uu___4 ->
                                        let uu___5 =
                                          FStar_Tactics_Util.repeatn n
                                            FStarC_Tactics_V2_Builtins.intro in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.PrettifyType.fst"
                                                   (Prims.of_int (365))
                                                   (Prims.of_int (15))
                                                   (Prims.of_int (365))
                                                   (Prims.of_int (30)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.PrettifyType.fst"
                                                   (Prims.of_int (365))
                                                   (Prims.of_int (33))
                                                   (Prims.of_int (369))
                                                   (Prims.of_int (12)))))
                                          (Obj.magic uu___5)
                                          (fun uu___6 ->
                                             (fun bs ->
                                                let uu___6 =
                                                  FStarC_Tactics_V2_Builtins.intro
                                                    () in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.PrettifyType.fst"
                                                              (Prims.of_int (366))
                                                              (Prims.of_int (17))
                                                              (Prims.of_int (366))
                                                              (Prims.of_int (25)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.PrettifyType.fst"
                                                              (Prims.of_int (367))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (369))
                                                              (Prims.of_int (12)))))
                                                     (Obj.magic uu___6)
                                                     (fun uu___7 ->
                                                        (fun b_eq ->
                                                           let uu___7 =
                                                             FStarC_Tactics_V2_Builtins.rewrite
                                                               b_eq in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (18)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (12)))))
                                                                (Obj.magic
                                                                   uu___7)
                                                                (fun uu___8
                                                                   ->
                                                                   (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    FStar_Tactics_V2_Derived.trefl
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (14)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (12)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.qed
                                                                    ()))
                                                                    uu___10)))
                                                                    uu___8)))
                                                          uu___7))) uu___6)))
                            cases)) uu___3))) uu___2)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.PrettifyType.prove_right_left" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.PrettifyType.prove_right_left (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  prove_right_left)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let rec (quote_at :
  parsed_type ->
    (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun at ->
       match at with
       | Atom t ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      FStar_Reflection_V2_Derived.mk_e_app
                        (FStarC_Reflection_V2_Builtins.pack_ln
                           (FStarC_Reflection_V2_Data.Tv_FVar
                              (FStarC_Reflection_V2_Builtins.pack_fv
                                 ["FStar"; "Tactics"; "PrettifyType"; "Atom"])))
                        [FStarC_Reflection_V2_Builtins.pack_ln
                           (FStarC_Reflection_V2_Data.Tv_FVar
                              (FStarC_Reflection_V2_Builtins.pack_fv
                                 ["FStar";
                                 "Tactics";
                                 "PrettifyType";
                                 "fakeunit"]))])))
       | Tuple2 (a, b) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = quote_at a in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PrettifyType.fst"
                              (Prims.of_int (378)) (Prims.of_int (24))
                              (Prims.of_int (378)) (Prims.of_int (34)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PrettifyType.fst"
                              (Prims.of_int (378)) (Prims.of_int (23))
                              (Prims.of_int (378)) (Prims.of_int (47)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             let uu___4 = quote_at b in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.PrettifyType.fst"
                                        (Prims.of_int (378))
                                        (Prims.of_int (36))
                                        (Prims.of_int (378))
                                        (Prims.of_int (46)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.PrettifyType.fst"
                                        (Prims.of_int (378))
                                        (Prims.of_int (23))
                                        (Prims.of_int (378))
                                        (Prims.of_int (47)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 -> [uu___5])) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PrettifyType.fst"
                                         (Prims.of_int (378))
                                         (Prims.of_int (23))
                                         (Prims.of_int (378))
                                         (Prims.of_int (47)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PrettifyType.fst"
                                         (Prims.of_int (378))
                                         (Prims.of_int (23))
                                         (Prims.of_int (378))
                                         (Prims.of_int (47)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 -> uu___2 :: uu___4))))
                          uu___2) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PrettifyType.fst"
                            (Prims.of_int (378)) (Prims.of_int (23))
                            (Prims.of_int (378)) (Prims.of_int (47)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PrettifyType.fst"
                            (Prims.of_int (378)) (Prims.of_int (4))
                            (Prims.of_int (378)) (Prims.of_int (47)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           FStar_Reflection_V2_Derived.mk_e_app
                             (FStarC_Reflection_V2_Builtins.pack_ln
                                (FStarC_Reflection_V2_Data.Tv_FVar
                                   (FStarC_Reflection_V2_Builtins.pack_fv
                                      ["FStar";
                                      "Tactics";
                                      "PrettifyType";
                                      "Tuple2"]))) uu___1))))
       | Named (s, t) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 =
                     let uu___2 = quote_at t in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.PrettifyType.fst"
                                (Prims.of_int (380)) (Prims.of_int (53))
                                (Prims.of_int (380)) (Prims.of_int (63)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.PrettifyType.fst"
                                (Prims.of_int (380)) (Prims.of_int (22))
                                (Prims.of_int (380)) (Prims.of_int (64)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___4 -> [uu___3])) in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PrettifyType.fst"
                              (Prims.of_int (380)) (Prims.of_int (22))
                              (Prims.of_int (380)) (Prims.of_int (64)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PrettifyType.fst"
                              (Prims.of_int (380)) (Prims.of_int (22))
                              (Prims.of_int (380)) (Prims.of_int (64)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 ->
                             (FStar_Tactics_NamedView.pack
                                (FStar_Tactics_NamedView.Tv_Const
                                   (FStarC_Reflection_V2_Data.C_String s)))
                             :: uu___2)) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PrettifyType.fst"
                            (Prims.of_int (380)) (Prims.of_int (22))
                            (Prims.of_int (380)) (Prims.of_int (64)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PrettifyType.fst"
                            (Prims.of_int (380)) (Prims.of_int (4))
                            (Prims.of_int (380)) (Prims.of_int (64)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           FStar_Reflection_V2_Derived.mk_e_app
                             (FStarC_Reflection_V2_Builtins.pack_ln
                                (FStarC_Reflection_V2_Data.Tv_FVar
                                   (FStarC_Reflection_V2_Builtins.pack_fv
                                      ["FStar";
                                      "Tactics";
                                      "PrettifyType";
                                      "Named"]))) uu___1))))
       | Either (a, b) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = quote_at a in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PrettifyType.fst"
                              (Prims.of_int (382)) (Prims.of_int (24))
                              (Prims.of_int (382)) (Prims.of_int (34)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PrettifyType.fst"
                              (Prims.of_int (382)) (Prims.of_int (23))
                              (Prims.of_int (382)) (Prims.of_int (47)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             let uu___4 = quote_at b in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.PrettifyType.fst"
                                        (Prims.of_int (382))
                                        (Prims.of_int (36))
                                        (Prims.of_int (382))
                                        (Prims.of_int (46)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.PrettifyType.fst"
                                        (Prims.of_int (382))
                                        (Prims.of_int (23))
                                        (Prims.of_int (382))
                                        (Prims.of_int (47)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 -> [uu___5])) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PrettifyType.fst"
                                         (Prims.of_int (382))
                                         (Prims.of_int (23))
                                         (Prims.of_int (382))
                                         (Prims.of_int (47)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PrettifyType.fst"
                                         (Prims.of_int (382))
                                         (Prims.of_int (23))
                                         (Prims.of_int (382))
                                         (Prims.of_int (47)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 -> uu___2 :: uu___4))))
                          uu___2) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PrettifyType.fst"
                            (Prims.of_int (382)) (Prims.of_int (23))
                            (Prims.of_int (382)) (Prims.of_int (47)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PrettifyType.fst"
                            (Prims.of_int (382)) (Prims.of_int (4))
                            (Prims.of_int (382)) (Prims.of_int (47)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           FStar_Reflection_V2_Derived.mk_e_app
                             (FStarC_Reflection_V2_Builtins.pack_ln
                                (FStarC_Reflection_V2_Data.Tv_FVar
                                   (FStarC_Reflection_V2_Builtins.pack_fv
                                      ["FStar";
                                      "Tactics";
                                      "PrettifyType";
                                      "Either"]))) uu___1))))) uu___
let (mk_left_right :
  cfg_t ->
    (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun cfg ->
    let uu___ =
      FStar_Tactics_V2_Derived.fresh_binder
        (FStar_Tactics_NamedView.pack
           (FStar_Tactics_NamedView.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv cfg.orig_tynm))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (385)) (Prims.of_int (10)) (Prims.of_int (385))
               (Prims.of_int (63)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (385)) (Prims.of_int (66)) (Prims.of_int (403))
               (Prims.of_int (18))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun b ->
            let uu___1 =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      FStar_Tactics_NamedView.pack
                        (FStar_Tactics_NamedView.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              (add_suffix "_left" cfg.pretty_tynm))))) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                          (Prims.of_int (386)) (Prims.of_int (24))
                          (Prims.of_int (386)) (Prims.of_int (79)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                          (Prims.of_int (386)) (Prims.of_int (82))
                          (Prims.of_int (403)) (Prims.of_int (18)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun tm_left ->
                       let uu___2 =
                         Obj.magic
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___3 ->
                                 FStar_Tactics_NamedView.pack
                                   (FStar_Tactics_NamedView.Tv_FVar
                                      (FStarC_Reflection_V2_Builtins.pack_fv
                                         (add_suffix "_right" cfg.pretty_tynm))))) in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.PrettifyType.fst"
                                     (Prims.of_int (387)) (Prims.of_int (24))
                                     (Prims.of_int (387)) (Prims.of_int (80)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.PrettifyType.fst"
                                     (Prims.of_int (387)) (Prims.of_int (83))
                                     (Prims.of_int (403)) (Prims.of_int (18)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun tm_right ->
                                  let uu___3 =
                                    let uu___4 =
                                      let uu___5 =
                                        let uu___6 =
                                          let uu___7 =
                                            FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr
                                              [b]
                                              (FStarC_Reflection_V2_Builtins.pack_ln
                                                 (FStarC_Reflection_V2_Data.Tv_App
                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                        (FStarC_Reflection_V2_Data.Tv_App
                                                           ((FStarC_Reflection_V2_Builtins.pack_ln
                                                               (FStarC_Reflection_V2_Data.Tv_App
                                                                  ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "PrettifyType";
                                                                    "f_inverses"]))),
                                                                    (tm_left,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                             (tm_right,
                                                               FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                      ((FStar_Tactics_V2_SyntaxCoercions.binder_to_term
                                                          b),
                                                        FStarC_Reflection_V2_Data.Q_Explicit)))) in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.PrettifyType.fst"
                                                     (Prims.of_int (395))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (397))
                                                     (Prims.of_int (58)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.PrettifyType.fst"
                                                     (Prims.of_int (392))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (398))
                                                     (Prims.of_int (68)))))
                                            (Obj.magic uu___7)
                                            (fun uu___8 ->
                                               (fun uu___8 ->
                                                  let uu___9 =
                                                    let uu___10 =
                                                      quote_at cfg.at in
                                                    FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.PrettifyType.fst"
                                                               (Prims.of_int (398))
                                                               (Prims.of_int (46))
                                                               (Prims.of_int (398))
                                                               (Prims.of_int (63)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.PrettifyType.fst"
                                                               (Prims.of_int (398))
                                                               (Prims.of_int (17))
                                                               (Prims.of_int (398))
                                                               (Prims.of_int (67)))))
                                                      (Obj.magic uu___10)
                                                      (fun uu___11 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___12 ->
                                                              FStarC_Reflection_V2_Builtins.pack_ln
                                                                (FStarC_Reflection_V2_Data.Tv_App
                                                                   ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Effect";
                                                                    "synth_by_tactic"]))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Abs
                                                                    ((FStarC_Reflection_V2_Builtins.pack_binder
                                                                    {
                                                                    FStarC_Reflection_V2_Data.sort2
                                                                    =
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    FStarC_Reflection_V2_Data.Tv_Unknown);
                                                                    FStarC_Reflection_V2_Data.qual
                                                                    =
                                                                    FStarC_Reflection_V2_Data.Q_Explicit;
                                                                    FStarC_Reflection_V2_Data.attrs
                                                                    = [];
                                                                    FStarC_Reflection_V2_Data.ppname2
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "uu___")
                                                                    }),
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "PrettifyType";
                                                                    "prove_left_right"]))),
                                                                    (uu___11,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))))))),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))))) in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.PrettifyType.fst"
                                                                (Prims.of_int (398))
                                                                (Prims.of_int (17))
                                                                (Prims.of_int (398))
                                                                (Prims.of_int (67)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.PrettifyType.fst"
                                                                (Prims.of_int (392))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (398))
                                                                (Prims.of_int (68)))))
                                                       (Obj.magic uu___9)
                                                       (fun uu___10 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___11 ->
                                                               {
                                                                 FStar_Tactics_NamedView.lb_fv
                                                                   =
                                                                   (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    (add_suffix
                                                                    "_left_right"
                                                                    cfg.pretty_tynm));
                                                                 FStar_Tactics_NamedView.lb_us
                                                                   = [];
                                                                 FStar_Tactics_NamedView.lb_typ
                                                                   = uu___8;
                                                                 FStar_Tactics_NamedView.lb_def
                                                                   = uu___10
                                                               })))) uu___8) in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.PrettifyType.fst"
                                                   (Prims.of_int (392))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (398))
                                                   (Prims.of_int (68)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.PrettifyType.fst"
                                                   (Prims.of_int (390))
                                                   (Prims.of_int (10))
                                                   (Prims.of_int (400))
                                                   (Prims.of_int (5)))))
                                          (Obj.magic uu___6)
                                          (fun uu___7 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___8 -> [uu___7])) in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.PrettifyType.fst"
                                                 (Prims.of_int (390))
                                                 (Prims.of_int (10))
                                                 (Prims.of_int (400))
                                                 (Prims.of_int (5)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.PrettifyType.fst"
                                                 (Prims.of_int (389))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (400))
                                                 (Prims.of_int (5)))))
                                        (Obj.magic uu___5)
                                        (fun uu___6 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___7 ->
                                                {
                                                  FStar_Tactics_NamedView.isrec
                                                    = false;
                                                  FStar_Tactics_NamedView.lbs
                                                    = uu___6
                                                })) in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.PrettifyType.fst"
                                               (Prims.of_int (389))
                                               (Prims.of_int (4))
                                               (Prims.of_int (400))
                                               (Prims.of_int (5)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.PrettifyType.fst"
                                               (Prims.of_int (388))
                                               (Prims.of_int (11))
                                               (Prims.of_int (401))
                                               (Prims.of_int (3)))))
                                      (Obj.magic uu___4)
                                      (fun uu___5 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___6 ->
                                              FStar_Tactics_NamedView.Sg_Let
                                                uu___5)) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.PrettifyType.fst"
                                                (Prims.of_int (388))
                                                (Prims.of_int (11))
                                                (Prims.of_int (401))
                                                (Prims.of_int (3)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.PrettifyType.fst"
                                                (Prims.of_int (403))
                                                (Prims.of_int (2))
                                                (Prims.of_int (403))
                                                (Prims.of_int (18)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          (fun sv ->
                                             let uu___4 =
                                               FStar_Tactics_NamedView.pack_sigelt
                                                 sv in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.PrettifyType.fst"
                                                           (Prims.of_int (403))
                                                           (Prims.of_int (3))
                                                           (Prims.of_int (403))
                                                           (Prims.of_int (17)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.PrettifyType.fst"
                                                           (Prims.of_int (403))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (403))
                                                           (Prims.of_int (18)))))
                                                  (Obj.magic uu___4)
                                                  (fun uu___5 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___6 ->
                                                          [uu___5])))) uu___4)))
                                 uu___3))) uu___2))) uu___1)
let (mk_right_left :
  cfg_t ->
    (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun cfg ->
    let uu___ =
      FStar_Tactics_V2_Derived.fresh_binder
        (FStar_Tactics_NamedView.pack
           (FStar_Tactics_NamedView.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv cfg.pretty_tynm))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (406)) (Prims.of_int (10)) (Prims.of_int (406))
               (Prims.of_int (65)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (406)) (Prims.of_int (68)) (Prims.of_int (425))
               (Prims.of_int (18))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun b ->
            let uu___1 =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      FStar_Tactics_NamedView.pack
                        (FStar_Tactics_NamedView.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              (add_suffix "_left" cfg.pretty_tynm))))) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                          (Prims.of_int (407)) (Prims.of_int (24))
                          (Prims.of_int (407)) (Prims.of_int (79)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                          (Prims.of_int (407)) (Prims.of_int (82))
                          (Prims.of_int (425)) (Prims.of_int (18)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun tm_left ->
                       let uu___2 =
                         Obj.magic
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___3 ->
                                 FStar_Tactics_NamedView.pack
                                   (FStar_Tactics_NamedView.Tv_FVar
                                      (FStarC_Reflection_V2_Builtins.pack_fv
                                         (add_suffix "_right" cfg.pretty_tynm))))) in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.PrettifyType.fst"
                                     (Prims.of_int (408)) (Prims.of_int (24))
                                     (Prims.of_int (408)) (Prims.of_int (80)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.PrettifyType.fst"
                                     (Prims.of_int (408)) (Prims.of_int (83))
                                     (Prims.of_int (425)) (Prims.of_int (18)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun tm_right ->
                                  let uu___3 =
                                    Obj.magic
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___4 ->
                                            FStar_Tactics_V2_SyntaxCoercions.binder_to_term
                                              b)) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.PrettifyType.fst"
                                                (Prims.of_int (409))
                                                (Prims.of_int (18))
                                                (Prims.of_int (409))
                                                (Prims.of_int (19)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.PrettifyType.fst"
                                                (Prims.of_int (409))
                                                (Prims.of_int (22))
                                                (Prims.of_int (425))
                                                (Prims.of_int (18)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          (fun bt ->
                                             let uu___4 =
                                               let uu___5 =
                                                 let uu___6 =
                                                   let uu___7 =
                                                     let uu___8 =
                                                       FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr
                                                         [b]
                                                         (FStarC_Reflection_V2_Builtins.pack_ln
                                                            (FStarC_Reflection_V2_Data.Tv_App
                                                               ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                   (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "PrettifyType";
                                                                    "f_inverses"]))),
                                                                    (tm_right,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (tm_left,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                 (bt,
                                                                   FStarC_Reflection_V2_Data.Q_Explicit)))) in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.PrettifyType.fst"
                                                                (Prims.of_int (417))
                                                                (Prims.of_int (10))
                                                                (Prims.of_int (419))
                                                                (Prims.of_int (59)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.PrettifyType.fst"
                                                                (Prims.of_int (414))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (420))
                                                                (Prims.of_int (49)))))
                                                       (Obj.magic uu___8)
                                                       (fun uu___9 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___10 ->
                                                               {
                                                                 FStar_Tactics_NamedView.lb_fv
                                                                   =
                                                                   (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    (add_suffix
                                                                    "_right_left"
                                                                    cfg.pretty_tynm));
                                                                 FStar_Tactics_NamedView.lb_us
                                                                   = [];
                                                                 FStar_Tactics_NamedView.lb_typ
                                                                   = uu___9;
                                                                 FStar_Tactics_NamedView.lb_def
                                                                   =
                                                                   (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Effect";
                                                                    "synth_by_tactic"]))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Abs
                                                                    ((FStarC_Reflection_V2_Builtins.pack_binder
                                                                    {
                                                                    FStarC_Reflection_V2_Data.sort2
                                                                    =
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    FStarC_Reflection_V2_Data.Tv_Unknown);
                                                                    FStarC_Reflection_V2_Data.qual
                                                                    =
                                                                    FStarC_Reflection_V2_Data.Q_Explicit;
                                                                    FStarC_Reflection_V2_Data.attrs
                                                                    = [];
                                                                    FStarC_Reflection_V2_Data.ppname2
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "uu___")
                                                                    }),
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "PrettifyType";
                                                                    "prove_right_left"]))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Const
                                                                    FStarC_Reflection_V2_Data.C_Unit)),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))))))),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))))
                                                               })) in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.PrettifyType.fst"
                                                              (Prims.of_int (414))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (420))
                                                              (Prims.of_int (49)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.PrettifyType.fst"
                                                              (Prims.of_int (412))
                                                              (Prims.of_int (10))
                                                              (Prims.of_int (422))
                                                              (Prims.of_int (5)))))
                                                     (Obj.magic uu___7)
                                                     (fun uu___8 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___9 ->
                                                             [uu___8])) in
                                                 FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.PrettifyType.fst"
                                                            (Prims.of_int (412))
                                                            (Prims.of_int (10))
                                                            (Prims.of_int (422))
                                                            (Prims.of_int (5)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.PrettifyType.fst"
                                                            (Prims.of_int (411))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (422))
                                                            (Prims.of_int (5)))))
                                                   (Obj.magic uu___6)
                                                   (fun uu___7 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___8 ->
                                                           {
                                                             FStar_Tactics_NamedView.isrec
                                                               = false;
                                                             FStar_Tactics_NamedView.lbs
                                                               = uu___7
                                                           })) in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.PrettifyType.fst"
                                                          (Prims.of_int (411))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (422))
                                                          (Prims.of_int (5)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.PrettifyType.fst"
                                                          (Prims.of_int (410))
                                                          (Prims.of_int (11))
                                                          (Prims.of_int (423))
                                                          (Prims.of_int (3)))))
                                                 (Obj.magic uu___5)
                                                 (fun uu___6 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___7 ->
                                                         FStar_Tactics_NamedView.Sg_Let
                                                           uu___6)) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.PrettifyType.fst"
                                                           (Prims.of_int (410))
                                                           (Prims.of_int (11))
                                                           (Prims.of_int (423))
                                                           (Prims.of_int (3)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.PrettifyType.fst"
                                                           (Prims.of_int (425))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (425))
                                                           (Prims.of_int (18)))))
                                                  (Obj.magic uu___4)
                                                  (fun uu___5 ->
                                                     (fun sv ->
                                                        let uu___5 =
                                                          FStar_Tactics_NamedView.pack_sigelt
                                                            sv in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (3))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (17)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (18)))))
                                                             (Obj.magic
                                                                uu___5)
                                                             (fun uu___6 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___7
                                                                    ->
                                                                    [uu___6]))))
                                                       uu___5))) uu___4)))
                                 uu___3))) uu___2))) uu___1)
let (mk_bij :
  cfg_t ->
    (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun cfg ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              FStar_Tactics_NamedView.Sg_Let
                {
                  FStar_Tactics_NamedView.isrec = false;
                  FStar_Tactics_NamedView.lbs =
                    [{
                       FStar_Tactics_NamedView.lb_fv =
                         (FStarC_Reflection_V2_Builtins.pack_fv
                            (add_suffix "_bij" cfg.pretty_tynm));
                       FStar_Tactics_NamedView.lb_us = [];
                       FStar_Tactics_NamedView.lb_typ =
                         (FStarC_Reflection_V2_Builtins.pack_ln
                            (FStarC_Reflection_V2_Data.Tv_App
                               ((FStarC_Reflection_V2_Builtins.pack_ln
                                   (FStarC_Reflection_V2_Data.Tv_App
                                      ((FStarC_Reflection_V2_Builtins.pack_ln
                                          (FStarC_Reflection_V2_Data.Tv_FVar
                                             (FStarC_Reflection_V2_Builtins.pack_fv
                                                ["FStar";
                                                "Bijection";
                                                "bijection"]))),
                                        ((FStar_Tactics_NamedView.pack
                                            (FStar_Tactics_NamedView.Tv_FVar
                                               (FStarC_Reflection_V2_Builtins.pack_fv
                                                  cfg.orig_tynm))),
                                          FStarC_Reflection_V2_Data.Q_Explicit)))),
                                 ((FStar_Tactics_NamedView.pack
                                     (FStar_Tactics_NamedView.Tv_FVar
                                        (FStarC_Reflection_V2_Builtins.pack_fv
                                           cfg.pretty_tynm))),
                                   FStarC_Reflection_V2_Data.Q_Explicit))));
                       FStar_Tactics_NamedView.lb_def =
                         (FStar_Reflection_V2_Derived.mk_e_app
                            (FStarC_Reflection_V2_Builtins.pack_ln
                               (FStarC_Reflection_V2_Data.Tv_FVar
                                  (FStarC_Reflection_V2_Builtins.pack_fv
                                     ["FStar"; "Bijection"; "mk_bijection"])))
                            [FStar_Tactics_NamedView.pack
                               (FStar_Tactics_NamedView.Tv_FVar
                                  (FStarC_Reflection_V2_Builtins.pack_fv
                                     (add_suffix "_right" cfg.pretty_tynm)));
                            FStar_Tactics_NamedView.pack
                              (FStar_Tactics_NamedView.Tv_FVar
                                 (FStarC_Reflection_V2_Builtins.pack_fv
                                    (add_suffix "_left" cfg.pretty_tynm)));
                            FStar_Tactics_NamedView.pack
                              (FStar_Tactics_NamedView.Tv_FVar
                                 (FStarC_Reflection_V2_Builtins.pack_fv
                                    (add_suffix "_right_left" cfg.pretty_tynm)));
                            FStar_Tactics_NamedView.pack
                              (FStar_Tactics_NamedView.Tv_FVar
                                 (FStarC_Reflection_V2_Builtins.pack_fv
                                    (add_suffix "_left_right" cfg.pretty_tynm)))])
                     }]
                })) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (428)) (Prims.of_int (11)) (Prims.of_int (449))
               (Prims.of_int (3)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
               (Prims.of_int (451)) (Prims.of_int (2)) (Prims.of_int (451))
               (Prims.of_int (18))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun sv ->
            let uu___1 = FStar_Tactics_NamedView.pack_sigelt sv in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                          (Prims.of_int (451)) (Prims.of_int (3))
                          (Prims.of_int (451)) (Prims.of_int (17)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                          (Prims.of_int (451)) (Prims.of_int (2))
                          (Prims.of_int (451)) (Prims.of_int (18)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___3 -> [uu___2])))) uu___1)
let (entry :
  Prims.string ->
    Prims.string ->
      (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun suf ->
    fun nm ->
      let uu___ = FStarC_Tactics_V2_Builtins.splice_quals () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                 (Prims.of_int (457)) (Prims.of_int (14))
                 (Prims.of_int (457)) (Prims.of_int (29)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PrettifyType.fst"
                 (Prims.of_int (457)) (Prims.of_int (32))
                 (Prims.of_int (498)) (Prims.of_int (39)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun quals ->
              let uu___1 = FStarC_Tactics_V2_Builtins.splice_attrs () in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PrettifyType.fst"
                            (Prims.of_int (458)) (Prims.of_int (14))
                            (Prims.of_int (458)) (Prims.of_int (29)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PrettifyType.fst"
                            (Prims.of_int (458)) (Prims.of_int (32))
                            (Prims.of_int (498)) (Prims.of_int (39)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun attrs ->
                         let uu___2 =
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___3 ->
                                   FStarC_Reflection_V2_Builtins.explode_qn
                                     nm)) in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.PrettifyType.fst"
                                       (Prims.of_int (460))
                                       (Prims.of_int (11))
                                       (Prims.of_int (460))
                                       (Prims.of_int (24)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.PrettifyType.fst"
                                       (Prims.of_int (460))
                                       (Prims.of_int (27))
                                       (Prims.of_int (498))
                                       (Prims.of_int (39)))))
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 (fun nm1 ->
                                    let uu___3 = get_typ_def nm1 in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.PrettifyType.fst"
                                                  (Prims.of_int (461))
                                                  (Prims.of_int (12))
                                                  (Prims.of_int (461))
                                                  (Prims.of_int (26)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.PrettifyType.fst"
                                                  (Prims.of_int (461))
                                                  (Prims.of_int (29))
                                                  (Prims.of_int (498))
                                                  (Prims.of_int (39)))))
                                         (Obj.magic uu___3)
                                         (fun uu___4 ->
                                            (fun def ->
                                               let uu___4 = parse_type def in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.PrettifyType.fst"
                                                             (Prims.of_int (463))
                                                             (Prims.of_int (11))
                                                             (Prims.of_int (463))
                                                             (Prims.of_int (25)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.PrettifyType.fst"
                                                             (Prims.of_int (463))
                                                             (Prims.of_int (28))
                                                             (Prims.of_int (498))
                                                             (Prims.of_int (39)))))
                                                    (Obj.magic uu___4)
                                                    (fun uu___5 ->
                                                       (fun at ->
                                                          let uu___5 =
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___6
                                                                    ->
                                                                    add_suffix
                                                                    suf nm1)) in
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (37)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (39)))))
                                                               (Obj.magic
                                                                  uu___5)
                                                               (fun uu___6 ->
                                                                  (fun
                                                                    pretty_tynm
                                                                    ->
                                                                    let uu___6
                                                                    =
                                                                    flatten_type
                                                                    pretty_tynm
                                                                    Prims.int_zero
                                                                    at in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (uu___8,
                                                                    fat) ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> fat)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    Sum cases
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    FStar_Tactics_Util.map
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    (s, p) ->
                                                                    mk_ctor
                                                                    pretty_tynm
                                                                    s p)
                                                                    cases in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (470))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (470))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (470))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    ctors ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    {
                                                                    at;
                                                                    fat;
                                                                    orig_tynm
                                                                    = nm1;
                                                                    pretty_tynm;
                                                                    ctors
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (472))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun cfg
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    mk_fancy_type
                                                                    cfg in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun tds
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    mk_right
                                                                    cfg in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun ds
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    mk_left
                                                                    cfg in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    ds
                                                                    uu___17)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun ds1
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    mk_left_right
                                                                    cfg in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    ds1
                                                                    uu___18)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun ds2
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    mk_right_left
                                                                    cfg in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    ds2
                                                                    uu___19)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun ds3
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    fun se ->
                                                                    let uu___20
                                                                    =
                                                                    FStar_Tactics_Util.filter
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun q ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    Prims.op_Negation
                                                                    (FStarC_Reflection_V2_Data.uu___is_Unfold_for_unification_and_vcgen
                                                                    q))))
                                                                    uu___21)
                                                                    quals in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    quals1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.set_sigelt_attrs
                                                                    attrs
                                                                    (FStarC_Reflection_V2_Builtins.set_sigelt_quals
                                                                    quals1 se))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (489))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    post_type
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    fun se ->
                                                                    let uu___21
                                                                    =
                                                                    FStar_Tactics_Util.filter
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun q ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    Prims.op_Negation
                                                                    ((FStarC_Reflection_V2_Data.uu___is_Noeq
                                                                    q) ||
                                                                    (FStarC_Reflection_V2_Data.uu___is_Unopteq
                                                                    q)))))
                                                                    uu___22)
                                                                    quals in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    quals1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.set_sigelt_attrs
                                                                    (FStar_List_Tot_Base.op_At
                                                                    attrs
                                                                    [
                                                                    FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Const
                                                                    (FStarC_Reflection_V2_Data.C_String
                                                                    "KrmlPrivate"))])
                                                                    (FStarC_Reflection_V2_Builtins.set_sigelt_quals
                                                                    quals1 se))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (496))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    post_other
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    FStar_Tactics_Util.map
                                                                    post_type
                                                                    tds in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStar_Tactics_Util.map
                                                                    post_other
                                                                    ds3 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PrettifyType.fst"
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    uu___21
                                                                    uu___23))))
                                                                    uu___21)))
                                                                    uu___20)))
                                                                    uu___19)))
                                                                    uu___18)))
                                                                    uu___17)))
                                                                    uu___16)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                    uu___10)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                         uu___5))) uu___4)))
                                   uu___3))) uu___2))) uu___1)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.PrettifyType.entry" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.PrettifyType.entry (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_2 entry)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_sigelt) psc
               ncb us args)
