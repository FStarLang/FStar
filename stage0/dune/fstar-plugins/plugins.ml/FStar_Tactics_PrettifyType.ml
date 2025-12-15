open Fstarcompiler
open Prims
type ('s, 'a) named = 'a
let fakeunit : FStarC_Reflection_Types.term=
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
let uu___is_Atom (projectee : parsed_type) : Prims.bool=
  match projectee with | Atom _0 -> true | uu___ -> false
let __proj__Atom__item___0 (projectee : parsed_type) : atom=
  match projectee with | Atom _0 -> _0
let uu___is_Tuple2 (projectee : parsed_type) : Prims.bool=
  match projectee with | Tuple2 (_0, _1) -> true | uu___ -> false
let __proj__Tuple2__item___0 (projectee : parsed_type) : parsed_type=
  match projectee with | Tuple2 (_0, _1) -> _0
let __proj__Tuple2__item___1 (projectee : parsed_type) : parsed_type=
  match projectee with | Tuple2 (_0, _1) -> _1
let uu___is_Either (projectee : parsed_type) : Prims.bool=
  match projectee with | Either (_0, _1) -> true | uu___ -> false
let __proj__Either__item___0 (projectee : parsed_type) : parsed_type=
  match projectee with | Either (_0, _1) -> _0
let __proj__Either__item___1 (projectee : parsed_type) : parsed_type=
  match projectee with | Either (_0, _1) -> _1
let uu___is_Named (projectee : parsed_type) : Prims.bool=
  match projectee with | Named (_0, _1) -> true | uu___ -> false
let __proj__Named__item___0 (projectee : parsed_type) : Prims.string=
  match projectee with | Named (_0, _1) -> _0
let __proj__Named__item___1 (projectee : parsed_type) : parsed_type=
  match projectee with | Named (_0, _1) -> _1
let add_suffix (s : Prims.string) (nm : FStarC_Reflection_Types.name) :
  FStarC_Reflection_Types.name=
  FStarC_Reflection_V2_Builtins.explode_qn
    (Prims.strcat (FStarC_Reflection_V2_Builtins.implode_qn nm) s)
let add_prefix (s : Prims.string) (nm : FStarC_Reflection_Types.name) :
  FStarC_Reflection_Types.name=
  let uu___ = FStar_List_Tot_Base.unsnoc nm in
  match uu___ with
  | (first, last) -> FStar_List_Tot_Base.op_At first [Prims.strcat s last]
type prod_type =
  | Prod of (Prims.string * atom) Prims.list 
let uu___is_Prod (projectee : prod_type) : Prims.bool= true
let __proj__Prod__item___0 (projectee : prod_type) :
  (Prims.string * atom) Prims.list= match projectee with | Prod _0 -> _0
type flat_type =
  | Sum of (Prims.string * prod_type) Prims.list 
let uu___is_Sum (projectee : flat_type) : Prims.bool= true
let __proj__Sum__item___0 (projectee : flat_type) :
  (Prims.string * prod_type) Prims.list= match projectee with | Sum _0 -> _0
type cfg_t =
  {
  at: parsed_type ;
  fat: flat_type ;
  orig_tynm: FStarC_Reflection_Types.name ;
  pretty_tynm: FStarC_Reflection_Types.name ;
  ctors: FStarC_Reflection_V2_Data.ctor Prims.list }
let __proj__Mkcfg_t__item__at (projectee : cfg_t) : parsed_type=
  match projectee with | { at; fat; orig_tynm; pretty_tynm; ctors;_} -> at
let __proj__Mkcfg_t__item__fat (projectee : cfg_t) : flat_type=
  match projectee with | { at; fat; orig_tynm; pretty_tynm; ctors;_} -> fat
let __proj__Mkcfg_t__item__orig_tynm (projectee : cfg_t) :
  FStarC_Reflection_Types.name=
  match projectee with
  | { at; fat; orig_tynm; pretty_tynm; ctors;_} -> orig_tynm
let __proj__Mkcfg_t__item__pretty_tynm (projectee : cfg_t) :
  FStarC_Reflection_Types.name=
  match projectee with
  | { at; fat; orig_tynm; pretty_tynm; ctors;_} -> pretty_tynm
let __proj__Mkcfg_t__item__ctors (projectee : cfg_t) :
  FStarC_Reflection_V2_Data.ctor Prims.list=
  match projectee with | { at; fat; orig_tynm; pretty_tynm; ctors;_} -> ctors
let rec parsed_type_to_string (t : parsed_type) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  match t with
  | Atom t1 -> FStarC_Tactics_V2_Builtins.term_to_string t1
  | Tuple2 (a, b) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (Obj.magic (parsed_type_to_string a))
              (fun uu___ ->
                 (fun uu___ ->
                    Obj.magic
                      (fun ps ->
                         let x =
                           let x1 =
                             let x2 = parsed_type_to_string b ps in
                             Prims.strcat x2 ")" in
                           Prims.strcat ", " x1 in
                         Prims.strcat uu___ x)) uu___)))
        (fun uu___ uu___1 -> Prims.strcat "(" uu___)
  | Either (a, b) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (Obj.magic (parsed_type_to_string a))
              (fun uu___ ->
                 (fun uu___ ->
                    Obj.magic
                      (fun ps ->
                         let x =
                           let x1 =
                             let x2 = parsed_type_to_string b ps in
                             Prims.strcat x2 ")" in
                           Prims.strcat " + " x1 in
                         Prims.strcat uu___ x)) uu___)))
        (fun uu___ uu___1 -> Prims.strcat "(" uu___)
  | Named (s, a) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (Obj.magic
                       (FStar_Tactics_Effect.tac_bind
                          (Obj.magic (parsed_type_to_string a))
                          (fun uu___ uu___1 -> Prims.strcat uu___ ")")))
                    (fun uu___ uu___1 -> Prims.strcat ": " uu___)))
              (fun uu___ uu___1 -> Prims.strcat s uu___)))
        (fun uu___ uu___1 -> Prims.strcat "(" uu___)
let rec parse_prod_type (t : FStar_Tactics_NamedView.term) :
  (parsed_type, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_V2_SyntaxHelpers.collect_app t ps in
    match x with
    | (hd, args) ->
        let x1 = let x2 = FStar_Tactics_NamedView.inspect hd ps in (x2, args) in
        (match x1 with
         | (FStar_Tactics_NamedView.Tv_UInst (fv, uu___),
            (a1, FStarC_Reflection_V2_Data.Q_Explicit)::(a2,
                                                         FStarC_Reflection_V2_Data.Q_Explicit)::[])
             ->
             let x2 = FStar_Tactics_NamedView.inspect a1 ps in
             (match x2 with
              | FStar_Tactics_NamedView.Tv_Const
                  (FStarC_Reflection_V2_Data.C_String s) ->
                  let x3 = parse_prod_type a2 ps in Named (s, x3)
              | uu___1 ->
                  if
                    (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                      ["FStar"; "Pervasives"; "Native"; "tuple2"]
                  then
                    let x3 = parse_prod_type a1 ps in
                    let x4 = parse_prod_type a2 ps in Tuple2 (x3, x4)
                  else Atom t)
         | (FStar_Tactics_NamedView.Tv_FVar fv,
            (a1, FStarC_Reflection_V2_Data.Q_Explicit)::(a2,
                                                         FStarC_Reflection_V2_Data.Q_Explicit)::[])
             ->
             let x2 = FStar_Tactics_NamedView.inspect a1 ps in
             (match x2 with
              | FStar_Tactics_NamedView.Tv_Const
                  (FStarC_Reflection_V2_Data.C_String s) ->
                  let x3 = parse_prod_type a2 ps in Named (s, x3)
              | uu___ ->
                  if
                    (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                      ["FStar"; "Pervasives"; "Native"; "tuple2"]
                  then
                    let x3 = parse_prod_type a1 ps in
                    let x4 = parse_prod_type a2 ps in Tuple2 (x3, x4)
                  else Atom t)
         | uu___ -> Atom t)
let rec parse_sum_type (t : FStar_Tactics_NamedView.term) :
  (parsed_type, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_V2_SyntaxHelpers.collect_app t ps in
    match x with
    | (hd, args) ->
        let x1 = let x2 = FStar_Tactics_NamedView.inspect hd ps in (x2, args) in
        (match x1 with
         | (FStar_Tactics_NamedView.Tv_UInst (fv, uu___),
            (a1, FStarC_Reflection_V2_Data.Q_Explicit)::(a2,
                                                         FStarC_Reflection_V2_Data.Q_Explicit)::[])
             ->
             let x2 = FStar_Tactics_NamedView.inspect a1 ps in
             (match x2 with
              | FStar_Tactics_NamedView.Tv_Const
                  (FStarC_Reflection_V2_Data.C_String s) ->
                  let x3 = parse_sum_type a2 ps in Named (s, x3)
              | uu___1 ->
                  if
                    (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                      ["FStar"; "Pervasives"; "either"]
                  then
                    let x3 = parse_sum_type a1 ps in
                    let x4 = parse_sum_type a2 ps in Either (x3, x4)
                  else parse_prod_type t ps)
         | (FStar_Tactics_NamedView.Tv_FVar fv,
            (a1, FStarC_Reflection_V2_Data.Q_Explicit)::(a2,
                                                         FStarC_Reflection_V2_Data.Q_Explicit)::[])
             ->
             let x2 = FStar_Tactics_NamedView.inspect a1 ps in
             (match x2 with
              | FStar_Tactics_NamedView.Tv_Const
                  (FStarC_Reflection_V2_Data.C_String s) ->
                  let x3 = parse_sum_type a2 ps in Named (s, x3)
              | uu___ ->
                  if
                    (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                      ["FStar"; "Pervasives"; "either"]
                  then
                    let x3 = parse_sum_type a1 ps in
                    let x4 = parse_sum_type a2 ps in Either (x3, x4)
                  else parse_prod_type t ps)
         | uu___ -> parse_prod_type t ps)
let parse_type :
  FStar_Tactics_NamedView.term ->
    (parsed_type, unit) FStar_Tactics_Effect.tac_repr=
  parse_sum_type
let prod_type_to_string (t : prod_type) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  match t with
  | Prod ts ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_Util.map
              (fun uu___ ->
                 match uu___ with
                 | (s, t1) ->
                     FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (Obj.magic
                                (FStarC_Tactics_V2_Builtins.term_to_string t1))
                             (fun uu___1 uu___2 -> Prims.strcat ":" uu___1)))
                       (fun uu___1 uu___2 -> Prims.strcat s uu___1)) ts))
        (fun ts1 uu___ ->
           Prims.strcat "{" (Prims.strcat (FStar_String.concat "; " ts1) "}"))
let flat_type_to_string (t : flat_type) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  match t with
  | Sum ts ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_Util.map
              (fun uu___ ->
                 match uu___ with
                 | (s, t1) ->
                     FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (Obj.magic (prod_type_to_string t1))
                             (fun uu___1 uu___2 -> Prims.strcat " of " uu___1)))
                       (fun uu___1 uu___2 -> Prims.strcat s uu___1)) ts))
        (fun ts1 uu___ ->
           Prims.strcat "("
             (Prims.strcat (FStar_String.concat " | " ts1) ")"))
let rec as_prod_type (uu___1 : Prims.nat) (uu___ : parsed_type) :
  ((Prims.nat * prod_type), unit) FStar_Tactics_Effect.tac_repr=
  (fun ctr t ->
     match t with
     | Tuple2 (a, b) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind (Obj.magic (as_prod_type ctr a))
                 (fun uu___ ->
                    (fun uu___ ->
                       match uu___ with
                       | (ctr1, Prod aa) ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (Obj.magic (as_prod_type ctr1 b))
                                (fun uu___1 uu___2 ->
                                   match uu___1 with
                                   | (ctr2, Prod bb) ->
                                       (ctr2,
                                         (Prod
                                            (FStar_List_Tot_Base.op_At aa bb))))))
                      uu___)))
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
                         [((Prims.strcat "_x" (Prims.string_of_int ctr)), t1)])))))
     | Either (uu___, uu___1) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_V2_Derived.fail
                 "as_prod_type: not a product type"))
     | Named (uu___, t1) -> Obj.magic (Obj.repr (as_prod_type ctr t1)))
    uu___1 uu___
let rec flatten_type (pretty_tynm : FStarC_Reflection_Types.name)
  (ctr : Prims.nat) (t : parsed_type) :
  ((Prims.nat * flat_type), unit) FStar_Tactics_Effect.tac_repr=
  match t with
  | Either (a, b) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic (flatten_type pretty_tynm ctr a))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (ctr1, Sum aa) ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic (flatten_type pretty_tynm ctr1 b))
                       (fun uu___1 uu___2 ->
                          match uu___1 with
                          | (ctr2, Sum bb) ->
                              (ctr2, (Sum (FStar_List_Tot_Base.op_At aa bb))))))
             uu___)
  | Named (s, t1) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic (as_prod_type Prims.int_zero t1))
        (fun uu___ uu___1 ->
           match uu___ with
           | (uu___2, p) ->
               (match FStar_List_Tot_Base.unsnoc pretty_tynm with
                | (uu___3, s0) ->
                    (ctr,
                      (Sum
                         [((Prims.strcat "Mk"
                              (Prims.strcat s0 (Prims.strcat "_" s))), p)]))))
  | t1 ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic (as_prod_type Prims.int_zero t1))
        (fun uu___ uu___1 ->
           match uu___ with
           | (uu___2, p) ->
               (match FStar_List_Tot_Base.unsnoc pretty_tynm with
                | (uu___3, s) ->
                    ((ctr + Prims.int_one),
                      (Sum
                         [((Prims.strcat "Mk"
                              (Prims.strcat s (Prims.string_of_int ctr))), p)]))))
let get_typ_def (nm : FStarC_Reflection_Types.name) :
  (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.top_env () ps in
    let x1 = FStarC_Reflection_V2_Builtins.lookup_typ x nm in
    match x1 with
    | FStar_Pervasives_Native.None ->
        FStar_Tactics_V2_Derived.fail "ctors_of_typ: type not found" ps
    | FStar_Pervasives_Native.Some se ->
        let x2 = FStar_Tactics_NamedView.inspect_sigelt se ps in
        (match x2 with
         | FStar_Tactics_NamedView.Sg_Let
             { FStar_Tactics_NamedView.isrec = uu___;
               FStar_Tactics_NamedView.lbs = lb::[];_}
             -> lb.FStar_Tactics_NamedView.lb_def
         | uu___ ->
             FStar_Tactics_V2_Derived.fail "get_typ_def: not a let binding?"
               ps)
let mk_ctor (tynm : FStarC_Reflection_Types.name) (s : Prims.string)
  (fat : prod_type) :
  (FStarC_Reflection_V2_Data.ctor, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = fat in
    match x with
    | Prod fields ->
        let x1 =
          FStar_Tactics_Util.map
            (fun uu___ ->
               match uu___ with
               | (s1, f) ->
                   FStar_Tactics_Effect.tac_bind
                     (Obj.magic (FStar_Tactics_V2_Derived.fresh_binder f))
                     (fun b uu___1 ->
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
                        })) fields ps in
        let x2 =
          match FStar_List_Tot_Base.unsnoc tynm with
          | (mod1, uu___) -> FStar_List_Tot_Base.op_At mod1 [s] in
        let x3 =
          FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr x1
            (FStar_Tactics_NamedView.pack
               (FStar_Tactics_NamedView.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv tynm))) ps in
        (x2, x3)
let mk_fancy_type (cfg : cfg_t) :
  (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
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
        } in
    let x1 = FStar_Tactics_NamedView.pack_sigelt x ps in [x1]
let rec parsed_type_pat (at : parsed_type) :
  ((FStar_Tactics_NamedView.pattern * FStar_Tactics_NamedView.binders), 
    unit) FStar_Tactics_Effect.tac_repr=
  match at with
  | Atom t ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic (FStar_Tactics_V2_Derived.fresh_binder t))
        (fun b uu___ ->
           ((FStar_Tactics_NamedView.Pat_Var
               {
                 FStar_Tactics_NamedView.v =
                   (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv b);
                 FStar_Tactics_NamedView.sort1 =
                   (FStar_Sealed.seal
                      (FStarC_Reflection_V2_Builtins.pack_ln
                         FStarC_Reflection_V2_Data.Tv_Unknown))
               }), [b]))
  | Tuple2 (a, b) ->
      FStar_Tactics_Effect.tac_bind (Obj.magic (parsed_type_pat a))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (p1, bs1) ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic (parsed_type_pat b))
                       (fun uu___1 uu___2 ->
                          match uu___1 with
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
                                  }), (FStar_List_Tot_Base.op_At bs1 bs2)))))
             uu___)
  | Named (uu___, t) -> parsed_type_pat t
  | uu___ ->
      FStar_Tactics_V2_Derived.fail
        "should not happen: parsed_type_pat: not a product type"
let rec parsed_type_expr (at : parsed_type)
  (bs : FStar_Tactics_NamedView.binders) :
  ((FStar_Tactics_NamedView.term * FStar_Tactics_NamedView.binders), 
    unit) FStar_Tactics_Effect.tac_repr=
  match at with
  | Atom t ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.guard
              (Prims.op_Negation (Prims.uu___is_Nil bs))))
        (fun uu___ uu___1 ->
           match bs with
           | b::bs1 ->
               ((FStar_Tactics_NamedView.pack
                   (FStar_Tactics_NamedView.Tv_Var
                      (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv b))),
                 bs1))
  | Tuple2 (a, b) ->
      FStar_Tactics_Effect.tac_bind (Obj.magic (parsed_type_expr a bs))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (e1, bs1) ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic (parsed_type_expr b bs1))
                       (fun uu___1 uu___2 ->
                          match uu___1 with
                          | (e2, bs2) ->
                              ((FStar_Reflection_V2_Derived.mk_e_app
                                  (FStar_Tactics_NamedView.pack
                                     (FStar_Tactics_NamedView.Tv_FVar
                                        (FStarC_Reflection_V2_Builtins.pack_fv
                                           ["FStar";
                                           "Pervasives";
                                           "Native";
                                           "Mktuple2"]))) [e1; e2]), bs2))))
             uu___)
  | Named (uu___, t) -> parsed_type_expr t bs
  | uu___ ->
      FStar_Tactics_V2_Derived.fail
        "should not happen: parsed_type_expr: not a product type"
let mk_right_case (cfg : cfg_t) (i : Prims.nat) (at : parsed_type) :
  (FStar_Tactics_NamedView.branch, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = parsed_type_pat at ps in
    match x with
    | (p, bs) ->
        let x1 = FStar_List_Tot_Base.index cfg.ctors i in
        (match x1 with
         | (ctor_nm, uu___) ->
             let x2 =
               FStar_Tactics_NamedView.pack
                 (FStar_Tactics_NamedView.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv ctor_nm)) in
             let x3 =
               let x4 =
                 FStar_Tactics_Util.map
                   (fun uu___1 ->
                      (fun b ->
                         Obj.magic
                           (fun uu___1 ->
                              FStar_Tactics_NamedView.pack
                                (FStar_Tactics_NamedView.Tv_Var
                                   (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                      b)))) uu___1) bs ps in
               FStar_Reflection_V2_Derived.mk_e_app x2 x4 in
             (p, x3))
let rec mk_right_body (cfg : cfg_t) (at : parsed_type) (i : Prims.nat)
  (sc : FStar_Tactics_NamedView.term) :
  ((Prims.nat * FStar_Tactics_NamedView.term), unit)
    FStar_Tactics_Effect.tac_repr=
  match at with
  | Either (l, r) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.fresh_binder
              (FStarC_Reflection_V2_Builtins.pack_ln
                 FStarC_Reflection_V2_Data.Tv_Unknown)))
        (fun uu___ ->
           (fun v1 ->
              Obj.magic
                (fun ps ->
                   let x =
                     FStar_Tactics_V2_Derived.fresh_binder
                       (FStarC_Reflection_V2_Builtins.pack_ln
                          FStarC_Reflection_V2_Data.Tv_Unknown) ps in
                   let x1 =
                     FStar_Tactics_NamedView.Pat_Cons
                       {
                         FStar_Tactics_NamedView.head =
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar"; "Pervasives"; "Inl"]);
                         FStar_Tactics_NamedView.univs =
                           FStar_Pervasives_Native.None;
                         FStar_Tactics_NamedView.subpats =
                           [((FStar_Tactics_NamedView.Pat_Var
                                {
                                  FStar_Tactics_NamedView.v =
                                    (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                       v1);
                                  FStar_Tactics_NamedView.sort1 =
                                    (FStar_Sealed.seal
                                       (FStarC_Reflection_V2_Builtins.pack_ln
                                          FStarC_Reflection_V2_Data.Tv_Unknown))
                                }), false)]
                       } in
                   let x2 =
                     FStar_Tactics_NamedView.Pat_Cons
                       {
                         FStar_Tactics_NamedView.head =
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar"; "Pervasives"; "Inr"]);
                         FStar_Tactics_NamedView.univs =
                           FStar_Pervasives_Native.None;
                         FStar_Tactics_NamedView.subpats =
                           [((FStar_Tactics_NamedView.Pat_Var
                                {
                                  FStar_Tactics_NamedView.v =
                                    (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                       x);
                                  FStar_Tactics_NamedView.sort1 =
                                    (FStar_Sealed.seal
                                       (FStarC_Reflection_V2_Builtins.pack_ln
                                          FStarC_Reflection_V2_Data.Tv_Unknown))
                                }), false)]
                       } in
                   let x3 =
                     mk_right_body cfg l i
                       (FStar_Tactics_NamedView.pack
                          (FStar_Tactics_NamedView.Tv_Var
                             (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                v1))) ps in
                   match x3 with
                   | (i1, body1) ->
                       let x4 = (x1, body1) in
                       let x5 =
                         mk_right_body cfg r i1
                           (FStar_Tactics_NamedView.pack
                              (FStar_Tactics_NamedView.Tv_Var
                                 (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                    x))) ps in
                       (match x5 with
                        | (i2, body2) ->
                            (i2,
                              (FStar_Tactics_NamedView.pack
                                 (FStar_Tactics_NamedView.Tv_Match
                                    (sc, FStar_Pervasives_Native.None,
                                      [x4; (x2, body2)]))))))) uu___)
  | uu___ ->
      FStar_Tactics_Effect.tac_bind (Obj.magic (mk_right_case cfg i at))
        (fun branch uu___1 ->
           ((i + Prims.int_one),
             (FStar_Tactics_NamedView.pack
                (FStar_Tactics_NamedView.Tv_Match
                   (sc, FStar_Pervasives_Native.None, [branch])))))
let mk_right (cfg : cfg_t) :
  (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      FStar_Tactics_V2_Derived.fresh_binder
        (FStar_Tactics_NamedView.pack
           (FStar_Tactics_NamedView.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv cfg.orig_tynm))) ps in
    let x1 =
      let x2 =
        let x3 =
          let x4 =
            let x5 =
              FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr [x]
                (FStar_Tactics_NamedView.pack
                   (FStar_Tactics_NamedView.Tv_FVar
                      (FStarC_Reflection_V2_Builtins.pack_fv cfg.pretty_tynm)))
                ps in
            let x6 =
              let x7 =
                let x8 =
                  mk_right_body cfg cfg.at Prims.int_zero
                    (FStar_Tactics_NamedView.pack
                       (FStar_Tactics_NamedView.Tv_Var
                          (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                             x))) ps in
                FStar_Pervasives_Native.snd x8 in
              FStar_Tactics_V2_Derived.mk_abs [x] x7 ps in
            {
              FStar_Tactics_NamedView.lb_fv =
                (FStarC_Reflection_V2_Builtins.pack_fv
                   (add_suffix "_right" cfg.pretty_tynm));
              FStar_Tactics_NamedView.lb_us = [];
              FStar_Tactics_NamedView.lb_typ = x5;
              FStar_Tactics_NamedView.lb_def = x6
            } in
          [x4] in
        {
          FStar_Tactics_NamedView.isrec = false;
          FStar_Tactics_NamedView.lbs = x3
        } in
      FStar_Tactics_NamedView.Sg_Let x2 in
    let x2 = FStar_Tactics_NamedView.pack_sigelt x1 ps in [x2]
let mk_left_case (cfg : cfg_t) (i : Prims.nat) (at : parsed_type) :
  (FStar_Tactics_NamedView.branch, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = parsed_type_pat at ps in
    match x with
    | (p, bs) ->
        let x1 = FStar_List_Tot_Base.index cfg.ctors i in
        (match x1 with
         | (ctor_nm, uu___) ->
             let x2 =
               FStar_Tactics_NamedView.pack
                 (FStar_Tactics_NamedView.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv ctor_nm)) in
             let x3 =
               let x4 =
                 FStar_Tactics_Util.map
                   (fun uu___1 ->
                      (fun b ->
                         Obj.magic
                           (fun uu___1 ->
                              FStar_Tactics_NamedView.pack
                                (FStar_Tactics_NamedView.Tv_Var
                                   (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                      b)))) uu___1) bs ps in
               FStar_Reflection_V2_Derived.mk_e_app x2 x4 in
             (p, x3))
let rec mk_left_branches
  (ff :
    FStar_Tactics_NamedView.term ->
      (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  (ctors : FStarC_Reflection_V2_Data.ctor Prims.list) (at : parsed_type) :
  ((FStarC_Reflection_V2_Data.ctor Prims.list *
     (FStar_Tactics_NamedView.pattern * FStar_Tactics_NamedView.term)
     Prims.list),
    unit) FStar_Tactics_Effect.tac_repr=
  match at with
  | Either (l, r) ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ t ->
              FStar_Reflection_V2_Derived.mk_e_app
                (FStar_Tactics_NamedView.pack
                   (FStar_Tactics_NamedView.Tv_FVar
                      (FStarC_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "Pervasives"; "Inl"]))) [t]))
        (fun uu___ ->
           (fun inl ->
              Obj.magic
                (fun ps ->
                   let x t =
                     FStar_Reflection_V2_Derived.mk_e_app
                       (FStar_Tactics_NamedView.pack
                          (FStar_Tactics_NamedView.Tv_FVar
                             (FStarC_Reflection_V2_Builtins.pack_fv
                                ["FStar"; "Pervasives"; "Inr"]))) [t] in
                   let x1 = mk_left_branches (fun t -> ff (inl t)) ctors l ps in
                   match x1 with
                   | (ctors1, brs1) ->
                       let x2 =
                         mk_left_branches (fun t -> ff (x t)) ctors1 r ps in
                       (match x2 with
                        | (ctors2, brs2) ->
                            (ctors2, (FStar_List_Tot_Base.op_At brs1 brs2)))))
             uu___)
  | uu___ ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.guard
              (Prims.op_Negation (Prims.uu___is_Nil ctors))))
        (fun uu___1 ->
           (fun uu___1 ->
              Obj.magic
                (fun ps ->
                   let x = ctors in
                   match x with
                   | (c_nm, c_ty)::ctors1 ->
                       let x1 =
                         FStar_Tactics_V2_SyntaxHelpers.collect_arr c_ty ps in
                       (match x1 with
                        | (bs, uu___2) ->
                            let x2 =
                              FStar_Tactics_Util.map
                                (fun b ->
                                   FStar_Tactics_V2_Derived.fresh_binder b)
                                bs ps in
                            let x3 =
                              let x4 =
                                let x5 =
                                  FStar_Tactics_Util.map
                                    (fun uu___3 ->
                                       (fun b ->
                                          Obj.magic
                                            (fun uu___3 ->
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
                                                   }), false))) uu___3) x2 ps in
                                {
                                  FStar_Tactics_NamedView.head =
                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                       c_nm);
                                  FStar_Tactics_NamedView.univs =
                                    FStar_Pervasives_Native.None;
                                  FStar_Tactics_NamedView.subpats = x5
                                } in
                              FStar_Tactics_NamedView.Pat_Cons x4 in
                            let x4 = parsed_type_expr at x2 ps in
                            (match x4 with
                             | (body, rest_bs) ->
                                 let x5 = ff body ps in
                                 (FStar_Tactics_V2_Derived.guard
                                    (Prims.uu___is_Nil rest_bs) ps;
                                  (ctors1, [(x3, x5)])))))) uu___1)
let mk_left_body (cfg : cfg_t) (sc : FStar_Tactics_NamedView.term) :
  (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      mk_left_branches
        (fun uu___ -> (fun t -> Obj.magic (fun uu___ -> t)) uu___) cfg.ctors
        cfg.at ps in
    match x with
    | (ctors, brs) ->
        (FStar_Tactics_V2_Derived.guard (Prims.uu___is_Nil ctors) ps;
         FStar_Tactics_NamedView.pack
           (FStar_Tactics_NamedView.Tv_Match
              (sc, FStar_Pervasives_Native.None, brs)))
let mk_left (cfg : cfg_t) :
  (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      FStar_Tactics_V2_Derived.fresh_binder
        (FStar_Tactics_NamedView.pack
           (FStar_Tactics_NamedView.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv cfg.pretty_tynm))) ps in
    let x1 =
      let x2 =
        let x3 =
          let x4 =
            let x5 =
              let x6 =
                let x7 =
                  FStar_Tactics_V2_Derived.fresh_binder
                    (FStar_Tactics_NamedView.pack
                       (FStar_Tactics_NamedView.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             cfg.pretty_tynm))) ps in
                [x7] in
              FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr x6
                (FStar_Tactics_NamedView.pack
                   (FStar_Tactics_NamedView.Tv_FVar
                      (FStarC_Reflection_V2_Builtins.pack_fv cfg.orig_tynm)))
                ps in
            let x6 =
              let x7 =
                mk_left_body cfg
                  (FStar_Tactics_NamedView.pack
                     (FStar_Tactics_NamedView.Tv_Var
                        (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv x)))
                  ps in
              FStar_Tactics_V2_Derived.mk_abs [x] x7 ps in
            {
              FStar_Tactics_NamedView.lb_fv =
                (FStarC_Reflection_V2_Builtins.pack_fv
                   (add_suffix "_left" cfg.pretty_tynm));
              FStar_Tactics_NamedView.lb_us = [];
              FStar_Tactics_NamedView.lb_typ = x5;
              FStar_Tactics_NamedView.lb_def = x6
            } in
          [x4] in
        {
          FStar_Tactics_NamedView.isrec = false;
          FStar_Tactics_NamedView.lbs = x3
        } in
      FStar_Tactics_NamedView.Sg_Let x2 in
    let x2 = FStar_Tactics_NamedView.pack_sigelt x1 ps in [x2]
let rec prove_left_right_aux (at : parsed_type)
  (m : FStar_Tactics_NamedView.term)
  (k : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  match at with
  | Atom uu___ -> k ()
  | Either (l, r) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic (FStarC_Tactics_V2_Builtins.t_destruct m))
        (fun uu___ ->
           (fun cases ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.guard
                     ((FStar_List_Tot_Base.length cases) = (Prims.of_int (2)))
                     ps;
                   (let x1 = FStar_Tactics_Util.zip cases [l; r] ps in
                    FStar_Tactics_Util.iter
                      (fun uu___ ->
                         match uu___ with
                         | ((c, n), at') ->
                             FStar_Tactics_V2_Derived.focus
                               (fun uu___1 ps1 ->
                                  let x2 =
                                    FStar_Tactics_Util.repeatn n
                                      FStarC_Tactics_V2_Builtins.intro ps1 in
                                  FStar_Tactics_V2_Derived.guard
                                    ((FStar_List_Tot_Base.length x2) =
                                       Prims.int_one) ps1;
                                  (let x4 = x2 in
                                   match x4 with
                                   | b::[] ->
                                       let x5 =
                                         FStarC_Tactics_V2_Builtins.intro ()
                                           ps1 in
                                       (FStarC_Tactics_V2_Builtins.rewrite x5
                                          ps1;
                                        prove_left_right_aux at'
                                          (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                             b) k ps1)))) x1 ps))) uu___)
  | Tuple2 (l, r) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic (FStarC_Tactics_V2_Builtins.t_destruct m))
        (fun uu___ ->
           (fun cases ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.guard
                     ((FStar_List_Tot_Base.length cases) = Prims.int_one) ps;
                   (let x1 = cases in
                    match x1 with
                    | (uu___, n)::[] ->
                        (FStar_Tactics_V2_Derived.guard
                           (n = (Prims.of_int (2))) ps;
                         (let x3 =
                            FStar_Tactics_Util.repeatn n
                              FStarC_Tactics_V2_Builtins.intro ps in
                          let x4 = x3 in
                          match x4 with
                          | b1::b2::[] ->
                              let x5 = FStarC_Tactics_V2_Builtins.intro () ps in
                              (FStarC_Tactics_V2_Builtins.rewrite x5 ps;
                               prove_left_right_aux l
                                 (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                    b1)
                                 (fun uu___1 ->
                                    prove_left_right_aux r
                                      (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                         b2) k) ps)))))) uu___)
  | Named (uu___, t) -> prove_left_right_aux t m k
let prove_left_right (at : parsed_type) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.intro () ps in
    prove_left_right_aux at
      (FStar_Tactics_V2_SyntaxCoercions.binding_to_term x)
      FStar_Tactics_V2_Derived.trefl ps
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
let prove_right_left (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.intro () ps in
    let x1 =
      FStarC_Tactics_V2_Builtins.t_destruct
        (FStar_Tactics_V2_SyntaxCoercions.binding_to_term x) ps in
    FStar_Tactics_Util.iter
      (fun uu___1 ->
         match uu___1 with
         | (c, n) ->
             FStar_Tactics_V2_Derived.focus
               (fun uu___2 ps1 ->
                  let x2 =
                    FStar_Tactics_Util.repeatn n
                      FStarC_Tactics_V2_Builtins.intro ps1 in
                  let x3 = FStarC_Tactics_V2_Builtins.intro () ps1 in
                  FStarC_Tactics_V2_Builtins.rewrite x3 ps1;
                  FStar_Tactics_V2_Derived.trefl () ps1;
                  FStar_Tactics_V2_Derived.qed () ps1)) x1 ps
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
let rec quote_at (uu___ : parsed_type) :
  (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr=
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
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind (Obj.magic (quote_at a))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x = let x1 = quote_at b ps in [x1] in
                                  uu___ :: x)) uu___)))
                 (fun uu___ uu___1 ->
                    FStar_Reflection_V2_Derived.mk_e_app
                      (FStarC_Reflection_V2_Builtins.pack_ln
                         (FStarC_Reflection_V2_Data.Tv_FVar
                            (FStarC_Reflection_V2_Builtins.pack_fv
                               ["FStar"; "Tactics"; "PrettifyType"; "Tuple2"])))
                      uu___)))
     | Named (s, t) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (Obj.magic (quote_at t))
                             (fun uu___ uu___1 -> [uu___])))
                       (fun uu___ uu___1 ->
                          (FStar_Tactics_NamedView.pack
                             (FStar_Tactics_NamedView.Tv_Const
                                (FStarC_Reflection_V2_Data.C_String s)))
                          :: uu___)))
                 (fun uu___ uu___1 ->
                    FStar_Reflection_V2_Derived.mk_e_app
                      (FStarC_Reflection_V2_Builtins.pack_ln
                         (FStarC_Reflection_V2_Data.Tv_FVar
                            (FStarC_Reflection_V2_Builtins.pack_fv
                               ["FStar"; "Tactics"; "PrettifyType"; "Named"])))
                      uu___)))
     | Either (a, b) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind (Obj.magic (quote_at a))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x = let x1 = quote_at b ps in [x1] in
                                  uu___ :: x)) uu___)))
                 (fun uu___ uu___1 ->
                    FStar_Reflection_V2_Derived.mk_e_app
                      (FStarC_Reflection_V2_Builtins.pack_ln
                         (FStarC_Reflection_V2_Data.Tv_FVar
                            (FStarC_Reflection_V2_Builtins.pack_fv
                               ["FStar"; "Tactics"; "PrettifyType"; "Either"])))
                      uu___)))) uu___
let mk_left_right (cfg : cfg_t) :
  (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      FStar_Tactics_V2_Derived.fresh_binder
        (FStar_Tactics_NamedView.pack
           (FStar_Tactics_NamedView.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv cfg.orig_tynm))) ps in
    let x1 =
      FStar_Tactics_NamedView.pack
        (FStar_Tactics_NamedView.Tv_FVar
           (FStarC_Reflection_V2_Builtins.pack_fv
              (add_suffix "_left" cfg.pretty_tynm))) in
    let x2 =
      FStar_Tactics_NamedView.pack
        (FStar_Tactics_NamedView.Tv_FVar
           (FStarC_Reflection_V2_Builtins.pack_fv
              (add_suffix "_right" cfg.pretty_tynm))) in
    let x3 =
      let x4 =
        let x5 =
          let x6 =
            let x7 =
              FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr [x]
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
                                      (x1,
                                        FStarC_Reflection_V2_Data.Q_Explicit)))),
                               (x2, FStarC_Reflection_V2_Data.Q_Explicit)))),
                        ((FStar_Tactics_V2_SyntaxCoercions.binder_to_term x),
                          FStarC_Reflection_V2_Data.Q_Explicit)))) ps in
            let x8 =
              let x9 = quote_at cfg.at ps in
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
                                  FStarC_Reflection_V2_Data.sort2 =
                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                       FStarC_Reflection_V2_Data.Tv_Unknown);
                                  FStarC_Reflection_V2_Data.qual =
                                    FStarC_Reflection_V2_Data.Q_Explicit;
                                  FStarC_Reflection_V2_Data.attrs = [];
                                  FStarC_Reflection_V2_Data.ppname2 =
                                    (FStar_Sealed.seal "uu___")
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
                                      (x9,
                                        FStarC_Reflection_V2_Data.Q_Explicit))))))),
                       FStarC_Reflection_V2_Data.Q_Explicit))) in
            {
              FStar_Tactics_NamedView.lb_fv =
                (FStarC_Reflection_V2_Builtins.pack_fv
                   (add_suffix "_left_right" cfg.pretty_tynm));
              FStar_Tactics_NamedView.lb_us = [];
              FStar_Tactics_NamedView.lb_typ = x7;
              FStar_Tactics_NamedView.lb_def = x8
            } in
          [x6] in
        {
          FStar_Tactics_NamedView.isrec = false;
          FStar_Tactics_NamedView.lbs = x5
        } in
      FStar_Tactics_NamedView.Sg_Let x4 in
    let x4 = FStar_Tactics_NamedView.pack_sigelt x3 ps in [x4]
let mk_right_left (cfg : cfg_t) :
  (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      FStar_Tactics_V2_Derived.fresh_binder
        (FStar_Tactics_NamedView.pack
           (FStar_Tactics_NamedView.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv cfg.pretty_tynm))) ps in
    let x1 =
      FStar_Tactics_NamedView.pack
        (FStar_Tactics_NamedView.Tv_FVar
           (FStarC_Reflection_V2_Builtins.pack_fv
              (add_suffix "_left" cfg.pretty_tynm))) in
    let x2 =
      FStar_Tactics_NamedView.pack
        (FStar_Tactics_NamedView.Tv_FVar
           (FStarC_Reflection_V2_Builtins.pack_fv
              (add_suffix "_right" cfg.pretty_tynm))) in
    let x3 = FStar_Tactics_V2_SyntaxCoercions.binder_to_term x in
    let x4 =
      let x5 =
        let x6 =
          let x7 =
            let x8 =
              FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr [x]
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
                                      (x2,
                                        FStarC_Reflection_V2_Data.Q_Explicit)))),
                               (x1, FStarC_Reflection_V2_Data.Q_Explicit)))),
                        (x3, FStarC_Reflection_V2_Data.Q_Explicit)))) ps in
            {
              FStar_Tactics_NamedView.lb_fv =
                (FStarC_Reflection_V2_Builtins.pack_fv
                   (add_suffix "_right_left" cfg.pretty_tynm));
              FStar_Tactics_NamedView.lb_us = [];
              FStar_Tactics_NamedView.lb_typ = x8;
              FStar_Tactics_NamedView.lb_def =
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
                                     FStarC_Reflection_V2_Data.sort2 =
                                       (FStarC_Reflection_V2_Builtins.pack_ln
                                          FStarC_Reflection_V2_Data.Tv_Unknown);
                                     FStarC_Reflection_V2_Data.qual =
                                       FStarC_Reflection_V2_Data.Q_Explicit;
                                     FStarC_Reflection_V2_Data.attrs = [];
                                     FStarC_Reflection_V2_Data.ppname2 =
                                       (FStar_Sealed.seal "uu___")
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
            } in
          [x7] in
        {
          FStar_Tactics_NamedView.isrec = false;
          FStar_Tactics_NamedView.lbs = x6
        } in
      FStar_Tactics_NamedView.Sg_Let x5 in
    let x5 = FStar_Tactics_NamedView.pack_sigelt x4 ps in [x5]
let mk_bij (cfg : cfg_t) :
  (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
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
                                        ["FStar"; "Bijection"; "bijection"]))),
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
        } in
    let x1 = FStar_Tactics_NamedView.pack_sigelt x ps in [x1]
let entry (pretty_tynm : Prims.string) (nm : Prims.string) :
  (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.splice_quals () ps in
    let x1 = FStarC_Tactics_V2_Builtins.splice_attrs () ps in
    let x2 = FStarC_Reflection_V2_Builtins.explode_qn nm in
    let x3 = get_typ_def x2 ps in
    let x4 = parse_type x3 ps in
    let x5 = FStar_List_Tot_Base.unsnoc x2 in
    match x5 with
    | (qns, uu___) ->
        let x6 = FStar_List_Tot_Base.op_At qns [pretty_tynm] in
        let x7 = flatten_type x6 Prims.int_zero x4 ps in
        (match x7 with
         | (uu___1, fat) ->
             let x8 = fat in
             (match x8 with
              | Sum cases ->
                  let x9 =
                    FStar_Tactics_Util.map
                      (fun uu___2 ->
                         match uu___2 with | (s, p) -> mk_ctor x6 s p) cases
                      ps in
                  let x10 =
                    {
                      at = x4;
                      fat;
                      orig_tynm = x2;
                      pretty_tynm = x6;
                      ctors = x9
                    } in
                  let x11 = mk_fancy_type x10 ps in
                  let x12 = mk_right x10 ps in
                  let x13 =
                    let x14 = mk_left x10 ps in
                    FStar_List_Tot_Base.op_At x12 x14 in
                  let x14 =
                    let x15 = mk_left_right x10 ps in
                    FStar_List_Tot_Base.op_At x13 x15 in
                  let x15 =
                    let x16 = mk_right_left x10 ps in
                    FStar_List_Tot_Base.op_At x14 x16 in
                  let x16 se ps1 =
                    let x17 =
                      FStar_Tactics_Util.filter
                        (fun uu___2 ->
                           (fun q ->
                              Obj.magic
                                (fun uu___2 ->
                                   Prims.op_Negation
                                     (FStarC_Reflection_V2_Data.uu___is_Unfold_for_unification_and_vcgen
                                        q))) uu___2) x ps1 in
                    FStarC_Reflection_V2_Builtins.set_sigelt_attrs x1
                      (FStarC_Reflection_V2_Builtins.set_sigelt_quals x17 se) in
                  let x17 se ps1 =
                    let x18 =
                      FStar_Tactics_Util.filter
                        (fun uu___2 ->
                           (fun q ->
                              Obj.magic
                                (fun uu___2 ->
                                   Prims.op_Negation
                                     ((FStarC_Reflection_V2_Data.uu___is_Noeq
                                         q)
                                        ||
                                        (FStarC_Reflection_V2_Data.uu___is_Unopteq
                                           q)))) uu___2) x ps1 in
                    FStarC_Reflection_V2_Builtins.set_sigelt_attrs
                      (FStar_List_Tot_Base.op_At x1
                         [FStarC_Reflection_V2_Builtins.pack_ln
                            (FStarC_Reflection_V2_Data.Tv_Const
                               (FStarC_Reflection_V2_Data.C_String
                                  "KrmlPrivate"))])
                      (FStarC_Reflection_V2_Builtins.set_sigelt_quals x18 se) in
                  let x18 = FStar_Tactics_Util.map x16 x11 ps in
                  let x19 = FStar_Tactics_Util.map x17 x15 ps in
                  FStar_List_Tot_Base.op_At x18 x19))
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
