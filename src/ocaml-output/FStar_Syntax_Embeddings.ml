open Prims
type norm_cb =
  (FStar_Ident.lid, FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___0_16 ->
    match uu___0_16 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____23 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____23
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Embedding_failure -> true | uu____29 -> false
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Unembedding_failure -> true | uu____35 -> false
type shadow_term =
  FStar_Syntax_Syntax.term FStar_Thunk.t FStar_Pervasives_Native.option
let (map_shadow :
  shadow_term ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> shadow_term)
  = fun s -> fun f -> FStar_Util.map_opt s (FStar_Thunk.map f)
let (force_shadow :
  shadow_term -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun s -> FStar_Util.map_opt s FStar_Thunk.force
type embed_t =
  FStar_Range.range -> shadow_term -> norm_cb -> FStar_Syntax_Syntax.term
type 'a unembed_t =
  Prims.bool -> norm_cb -> 'a FStar_Pervasives_Native.option
type 'a raw_embedder = 'a -> embed_t
type 'a raw_unembedder = FStar_Syntax_Syntax.term -> 'a unembed_t
type 'a printer = 'a -> Prims.string
type 'a embedding =
  {
  em: 'a -> embed_t ;
  un: FStar_Syntax_Syntax.term -> 'a unembed_t ;
  typ: FStar_Syntax_Syntax.typ ;
  print: 'a printer ;
  emb_typ: FStar_Syntax_Syntax.emb_typ }
let __proj__Mkembedding__item__em : 'a . 'a embedding -> 'a -> embed_t =
  fun projectee ->
    match projectee with | { em; un; typ; print; emb_typ;_} -> em
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun projectee ->
    match projectee with | { em; un; typ; print; emb_typ;_} -> un
let __proj__Mkembedding__item__typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.typ =
  fun projectee ->
    match projectee with | { em; un; typ; print; emb_typ;_} -> typ
let __proj__Mkembedding__item__print : 'a . 'a embedding -> 'a printer =
  fun projectee ->
    match projectee with | { em; un; typ; print; emb_typ;_} -> print
let __proj__Mkembedding__item__emb_typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun projectee ->
    match projectee with | { em; un; typ; print; emb_typ;_} -> emb_typ
let emb_typ_of : 'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun e -> e.emb_typ
let unknown_printer :
  'uuuuuu396 . FStar_Syntax_Syntax.term -> 'uuuuuu396 -> Prims.string =
  fun typ ->
    fun uu____406 ->
      let uu____407 = FStar_Syntax_Print.term_to_string typ in
      FStar_Util.format1 "unknown %s" uu____407
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t ->
    let uu____413 =
      let uu____414 = FStar_Syntax_Subst.compress t in
      uu____414.FStar_Syntax_Syntax.n in
    match uu____413 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____418 ->
        let uu____419 =
          let uu____420 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____420 in
        failwith uu____419
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em ->
    fun un ->
      fun fv ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv in
        let uu____460 =
          let uu____461 =
            let uu____468 =
              let uu____469 = FStar_Syntax_Syntax.lid_of_fv fv in
              FStar_All.pipe_right uu____469 FStar_Ident.string_of_lid in
            (uu____468, []) in
          FStar_Syntax_Syntax.ET_app uu____461 in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____460 }
let mk_emb_full :
  'a .
    'a raw_embedder ->
      'a raw_unembedder ->
        FStar_Syntax_Syntax.typ ->
          ('a -> Prims.string) -> FStar_Syntax_Syntax.emb_typ -> 'a embedding
  =
  fun em ->
    fun un ->
      fun typ ->
        fun printer1 ->
          fun emb_typ -> { em; un; typ; print = printer1; emb_typ }
let embed : 'a . 'a embedding -> 'a -> embed_t = fun e -> fun x -> e.em x
let unembed : 'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun e -> fun t -> e.un t
let warn_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e -> fun t -> fun n -> let uu____610 = unembed e t in uu____610 true n
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e -> fun t -> fun n -> let uu____649 = unembed e t in uu____649 false n
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e -> e.typ
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty ->
    fun e ->
      let uu___77_693 = e in
      {
        em = (uu___77_693.em);
        un = (uu___77_693.un);
        typ = ty;
        print = (uu___77_693.print);
        emb_typ = (uu___77_693.emb_typ)
      }
let embed_as :
  'a 'b .
    'a embedding ->
      ('a -> 'b) ->
        ('b -> 'a) ->
          FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
            'b embedding
  =
  fun ea ->
    fun ab ->
      fun ba ->
        fun o ->
          let uu____750 =
            match o with
            | FStar_Pervasives_Native.Some t -> t
            | uu____752 -> type_of ea in
          mk_emb_full (fun x -> let uu____758 = ba x in embed ea uu____758)
            (fun t ->
               fun w ->
                 fun cb ->
                   let uu____767 =
                     let uu____770 = unembed ea t in uu____770 w cb in
                   FStar_Util.map_opt uu____767 ab) uu____750
            (fun x ->
               let uu____780 = let uu____781 = ba x in ea.print uu____781 in
               FStar_Util.format1 "(embed_as>> %s)\n" uu____780) ea.emb_typ
let lazy_embed :
  'a .
    'a printer ->
      FStar_Syntax_Syntax.emb_typ ->
        FStar_Range.range ->
          FStar_Syntax_Syntax.term ->
            'a ->
              (unit -> FStar_Syntax_Syntax.term) -> FStar_Syntax_Syntax.term
  =
  fun pa ->
    fun et ->
      fun rng ->
        fun ta ->
          fun x ->
            fun f ->
              (let uu____839 = FStar_ST.op_Bang FStar_Options.debug_embedding in
               if uu____839
               then
                 let uu____846 = FStar_Syntax_Print.term_to_string ta in
                 let uu____847 = FStar_Syntax_Print.emb_typ_to_string et in
                 let uu____848 = pa x in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu____846
                   uu____847 uu____848
               else ());
              (let uu____850 = FStar_ST.op_Bang FStar_Options.eager_embedding in
               if uu____850
               then f ()
               else
                 (let thunk = FStar_Thunk.mk f in
                  FStar_Syntax_Util.mk_lazy x FStar_Syntax_Syntax.tun
                    (FStar_Syntax_Syntax.Lazy_embedding (et, thunk))
                    (FStar_Pervasives_Native.Some rng)))
let lazy_unembed :
  'a .
    'a printer ->
      FStar_Syntax_Syntax.emb_typ ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option)
              -> 'a FStar_Pervasives_Native.option
  =
  fun pa ->
    fun et ->
      fun x ->
        fun ta ->
          fun f ->
            let x1 = FStar_Syntax_Subst.compress x in
            match x1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_lazy
                { FStar_Syntax_Syntax.blob = b;
                  FStar_Syntax_Syntax.lkind =
                    FStar_Syntax_Syntax.Lazy_embedding (et', t);
                  FStar_Syntax_Syntax.ltyp = uu____930;
                  FStar_Syntax_Syntax.rng = uu____931;_}
                ->
                let uu____942 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding) in
                if uu____942
                then
                  let res =
                    let uu____954 = FStar_Thunk.force t in f uu____954 in
                  ((let uu____958 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu____958
                    then
                      let uu____965 = FStar_Syntax_Print.emb_typ_to_string et in
                      let uu____966 =
                        FStar_Syntax_Print.emb_typ_to_string et' in
                      let uu____967 =
                        match res with
                        | FStar_Pervasives_Native.None -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____969 = pa x2 in
                            Prims.op_Hat "Some " uu____969 in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____965 uu____966 uu____967
                    else ());
                   res)
                else
                  (let a1 = FStar_Dyn.undyn b in
                   (let uu____974 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu____974
                    then
                      let uu____981 = FStar_Syntax_Print.emb_typ_to_string et in
                      let uu____982 = pa a1 in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n" uu____981
                        uu____982
                    else ());
                   FStar_Pervasives_Native.Some a1)
            | uu____984 ->
                let aopt = f x1 in
                ((let uu____989 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding in
                  if uu____989
                  then
                    let uu____996 = FStar_Syntax_Print.emb_typ_to_string et in
                    let uu____997 = FStar_Syntax_Print.term_to_string x1 in
                    let uu____998 =
                      match aopt with
                      | FStar_Pervasives_Native.None -> "None"
                      | FStar_Pervasives_Native.Some a1 ->
                          let uu____1000 = pa a1 in
                          Prims.op_Hat "Some " uu____1000 in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____996 uu____997 uu____998
                  else ());
                 aopt)
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ ->
    let em t _r _topt _norm =
      (let uu____1033 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu____1033
       then
         let uu____1040 = unknown_printer typ t in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____1040
       else ());
      t in
    let un t _w _n =
      (let uu____1063 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu____1063
       then
         let uu____1070 = unknown_printer typ t in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____1070
       else ());
      FStar_Pervasives_Native.Some t in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t in
  let un t _w _n = FStar_Pervasives_Native.Some t in
  let uu____1117 =
    let uu____1118 =
      let uu____1125 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid in
      (uu____1125, []) in
    FStar_Syntax_Syntax.ET_app uu____1118 in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____1117
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___167_1153 = FStar_Syntax_Util.exp_unit in
    {
      FStar_Syntax_Syntax.n = (uu___167_1153.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___167_1153.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit) ->
        FStar_Pervasives_Native.Some ()
    | uu____1179 ->
        (if w
         then
           (let uu____1181 =
              let uu____1186 =
                let uu____1187 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded unit: %s" uu____1187 in
              (FStar_Errors.Warning_NotEmbedded, uu____1186) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1181)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____1189 =
    let uu____1190 =
      let uu____1197 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid in
      (uu____1197, []) in
    FStar_Syntax_Syntax.ET_app uu____1190 in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____1201 -> "()")
    uu____1189
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool in
    let uu___187_1233 = t in
    {
      FStar_Syntax_Syntax.n = (uu___187_1233.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___187_1233.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____1262 ->
        (if w
         then
           (let uu____1264 =
              let uu____1269 =
                let uu____1270 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded bool: %s" uu____1270 in
              (FStar_Errors.Warning_NotEmbedded, uu____1269) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1264)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____1272 =
    let uu____1273 =
      let uu____1280 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid in
      (uu____1280, []) in
    FStar_Syntax_Syntax.ET_app uu____1273 in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____1272
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c in
    let uu___206_1309 = t in
    {
      FStar_Syntax_Syntax.n = (uu___206_1309.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___206_1309.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____1336 ->
        (if w
         then
           (let uu____1338 =
              let uu____1343 =
                let uu____1344 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded char: %s" uu____1344 in
              (FStar_Errors.Warning_NotEmbedded, uu____1343) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1338)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____1346 =
    let uu____1347 =
      let uu____1354 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid in
      (uu____1354, []) in
    FStar_Syntax_Syntax.ET_app uu____1347 in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____1346
let (e_int : FStar_BigInt.t embedding) =
  let t_int = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid in
  let emb_t_int =
    let uu____1361 =
      let uu____1368 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid in
      (uu____1368, []) in
    FStar_Syntax_Syntax.ET_app uu____1361 in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int i
      (fun uu____1396 ->
         let uu____1397 = FStar_BigInt.string_of_big_int i in
         FStar_Syntax_Util.exp_int uu____1397) in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int
      (fun t1 ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s, uu____1429)) ->
             let uu____1442 = FStar_BigInt.big_int_of_string s in
             FStar_Pervasives_Native.Some uu____1442
         | uu____1443 ->
             (if w
              then
                (let uu____1445 =
                   let uu____1450 =
                     let uu____1451 = FStar_Syntax_Print.term_to_string t0 in
                     FStar_Util.format1 "Not an embedded int: %s" uu____1451 in
                   (FStar_Errors.Warning_NotEmbedded, uu____1450) in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1445)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____1456 =
      let uu____1463 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid in
      (uu____1463, []) in
    FStar_Syntax_Syntax.ET_app uu____1456 in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      rng in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s, uu____1515)) -> FStar_Pervasives_Native.Some s
    | uu____1516 ->
        (if w
         then
           (let uu____1518 =
              let uu____1523 =
                let uu____1524 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded string: %s" uu____1524 in
              (FStar_Errors.Warning_NotEmbedded, uu____1523) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1518)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb_full em un FStar_Syntax_Syntax.t_string
    (fun x -> Prims.op_Hat "\"" (Prims.op_Hat x "\"")) emb_t_string
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea ->
    let t_option_a =
      let t_opt = FStar_Syntax_Util.fvar_const FStar_Parser_Const.option_lid in
      let uu____1548 =
        let uu____1549 = FStar_Syntax_Syntax.as_arg ea.typ in [uu____1549] in
      FStar_Syntax_Syntax.mk_Tm_app t_opt uu____1548 FStar_Range.dummyRange in
    let emb_t_option_a =
      let uu____1575 =
        let uu____1582 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid in
        (uu____1582, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu____1575 in
    let printer1 uu___1_1592 =
      match uu___1_1592 with
      | FStar_Pervasives_Native.None -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____1596 =
            let uu____1597 = ea.print x in Prims.op_Hat uu____1597 ")" in
          Prims.op_Hat "(Some " uu____1596 in
    let em o rng topt norm =
      lazy_embed printer1 emb_t_option_a rng t_option_a o
        (fun uu____1630 ->
           match o with
           | FStar_Pervasives_Native.None ->
               let uu____1631 =
                 let uu____1632 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.none_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____1632
                   [FStar_Syntax_Syntax.U_zero] in
               let uu____1633 =
                 let uu____1634 =
                   let uu____1643 = type_of ea in
                   FStar_Syntax_Syntax.iarg uu____1643 in
                 [uu____1634] in
               FStar_Syntax_Syntax.mk_Tm_app uu____1631 uu____1633 rng
           | FStar_Pervasives_Native.Some a1 ->
               let shadow_a =
                 map_shadow topt
                   (fun t ->
                      let v = FStar_Ident.mk_ident ("v", rng) in
                      let some_v =
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          FStar_Parser_Const.some_lid v in
                      let some_v_tm =
                        let uu____1672 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None in
                        FStar_Syntax_Syntax.fv_to_tm uu____1672 in
                      let uu____1673 =
                        FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                          [FStar_Syntax_Syntax.U_zero] in
                      let uu____1674 =
                        let uu____1675 =
                          let uu____1684 = type_of ea in
                          FStar_Syntax_Syntax.iarg uu____1684 in
                        let uu____1685 =
                          let uu____1696 = FStar_Syntax_Syntax.as_arg t in
                          [uu____1696] in
                        uu____1675 :: uu____1685 in
                      FStar_Syntax_Syntax.mk_Tm_app uu____1673 uu____1674 rng) in
               let uu____1729 =
                 let uu____1730 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.some_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____1730
                   [FStar_Syntax_Syntax.U_zero] in
               let uu____1731 =
                 let uu____1732 =
                   let uu____1741 = type_of ea in
                   FStar_Syntax_Syntax.iarg uu____1741 in
                 let uu____1742 =
                   let uu____1753 =
                     let uu____1762 =
                       let uu____1763 = embed ea a1 in
                       uu____1763 rng shadow_a norm in
                     FStar_Syntax_Syntax.as_arg uu____1762 in
                   [uu____1753] in
                 uu____1732 :: uu____1742 in
               FStar_Syntax_Syntax.mk_Tm_app uu____1729 uu____1731 rng) in
    let un t0 w norm =
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      lazy_unembed printer1 emb_t_option_a t t_option_a
        (fun t1 ->
           let uu____1831 = FStar_Syntax_Util.head_and_args' t1 in
           match uu____1831 with
           | (hd, args) ->
               let uu____1872 =
                 let uu____1887 =
                   let uu____1888 = FStar_Syntax_Util.un_uinst hd in
                   uu____1888.FStar_Syntax_Syntax.n in
                 (uu____1887, args) in
               (match uu____1872 with
                | (FStar_Syntax_Syntax.Tm_fvar fv, uu____1906) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   uu____1930::(a1, uu____1932)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____1983 =
                      let uu____1986 = unembed ea a1 in uu____1986 w norm in
                    FStar_Util.bind_opt uu____1983
                      (fun a2 ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a2))
                | uu____1999 ->
                    (if w
                     then
                       (let uu____2015 =
                          let uu____2020 =
                            let uu____2021 =
                              FStar_Syntax_Print.term_to_string t0 in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____2021 in
                          (FStar_Errors.Warning_NotEmbedded, uu____2020) in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____2015)
                     else ();
                     FStar_Pervasives_Native.None))) in
    let uu____2025 =
      let uu____2026 = type_of ea in
      FStar_Syntax_Syntax.t_option_of uu____2026 in
    mk_emb_full em un uu____2025 printer1 emb_t_option_a
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea ->
    fun eb ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2 in
        let uu____2065 =
          let uu____2066 = FStar_Syntax_Syntax.as_arg ea.typ in
          let uu____2075 =
            let uu____2086 = FStar_Syntax_Syntax.as_arg eb.typ in
            [uu____2086] in
          uu____2066 :: uu____2075 in
        FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____2065
          FStar_Range.dummyRange in
      let emb_t_pair_a_b =
        let uu____2120 =
          let uu____2127 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid in
          (uu____2127, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu____2120 in
      let printer1 uu____2139 =
        match uu____2139 with
        | (x, y) ->
            let uu____2146 = ea.print x in
            let uu____2147 = eb.print y in
            FStar_Util.format2 "(%s, %s)" uu____2146 uu____2147 in
      let em x rng topt norm =
        lazy_embed printer1 emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____2189 ->
             let proj i ab =
               let proj_1 =
                 let uu____2202 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.of_int (2))
                     rng in
                 let uu____2203 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun in
                 FStar_Syntax_Util.mk_field_projector_name uu____2202
                   uu____2203 i in
               let proj_1_tm =
                 let uu____2205 =
                   FStar_Syntax_Syntax.lid_as_fv proj_1
                     FStar_Syntax_Syntax.delta_equational
                     FStar_Pervasives_Native.None in
                 FStar_Syntax_Syntax.fv_to_tm uu____2205 in
               let uu____2206 =
                 FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                   [FStar_Syntax_Syntax.U_zero] in
               let uu____2207 =
                 let uu____2208 =
                   let uu____2217 = type_of ea in
                   FStar_Syntax_Syntax.iarg uu____2217 in
                 let uu____2218 =
                   let uu____2229 =
                     let uu____2238 = type_of eb in
                     FStar_Syntax_Syntax.iarg uu____2238 in
                   let uu____2239 =
                     let uu____2250 = FStar_Syntax_Syntax.as_arg ab in
                     [uu____2250] in
                   uu____2229 :: uu____2239 in
                 uu____2208 :: uu____2218 in
               FStar_Syntax_Syntax.mk_Tm_app uu____2206 uu____2207 rng in
             let shadow_a = map_shadow topt (proj Prims.int_one) in
             let shadow_b = map_shadow topt (proj (Prims.of_int (2))) in
             let uu____2293 =
               let uu____2294 =
                 FStar_Syntax_Syntax.tdataconstr
                   FStar_Parser_Const.lid_Mktuple2 in
               FStar_Syntax_Syntax.mk_Tm_uinst uu____2294
                 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
             let uu____2295 =
               let uu____2296 =
                 let uu____2305 = type_of ea in
                 FStar_Syntax_Syntax.iarg uu____2305 in
               let uu____2306 =
                 let uu____2317 =
                   let uu____2326 = type_of eb in
                   FStar_Syntax_Syntax.iarg uu____2326 in
                 let uu____2327 =
                   let uu____2338 =
                     let uu____2347 =
                       let uu____2348 =
                         embed ea (FStar_Pervasives_Native.fst x) in
                       uu____2348 rng shadow_a norm in
                     FStar_Syntax_Syntax.as_arg uu____2347 in
                   let uu____2355 =
                     let uu____2366 =
                       let uu____2375 =
                         let uu____2376 =
                           embed eb (FStar_Pervasives_Native.snd x) in
                         uu____2376 rng shadow_b norm in
                       FStar_Syntax_Syntax.as_arg uu____2375 in
                     [uu____2366] in
                   uu____2338 :: uu____2355 in
                 uu____2317 :: uu____2327 in
               uu____2296 :: uu____2306 in
             FStar_Syntax_Syntax.mk_Tm_app uu____2293 uu____2295 rng) in
      let un t0 w norm =
        let t = FStar_Syntax_Util.unmeta_safe t0 in
        lazy_unembed printer1 emb_t_pair_a_b t t_pair_a_b
          (fun t1 ->
             let uu____2472 = FStar_Syntax_Util.head_and_args' t1 in
             match uu____2472 with
             | (hd, args) ->
                 let uu____2515 =
                   let uu____2528 =
                     let uu____2529 = FStar_Syntax_Util.un_uinst hd in
                     uu____2529.FStar_Syntax_Syntax.n in
                   (uu____2528, args) in
                 (match uu____2515 with
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu____2547::uu____2548::(a1, uu____2550)::(b1,
                                                                uu____2552)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____2611 =
                        let uu____2614 = unembed ea a1 in uu____2614 w norm in
                      FStar_Util.bind_opt uu____2611
                        (fun a2 ->
                           let uu____2628 =
                             let uu____2631 = unembed eb b1 in
                             uu____2631 w norm in
                           FStar_Util.bind_opt uu____2628
                             (fun b2 -> FStar_Pervasives_Native.Some (a2, b2)))
                  | uu____2648 ->
                      (if w
                       then
                         (let uu____2662 =
                            let uu____2667 =
                              let uu____2668 =
                                FStar_Syntax_Print.term_to_string t0 in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____2668 in
                            (FStar_Errors.Warning_NotEmbedded, uu____2667) in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____2662)
                       else ();
                       FStar_Pervasives_Native.None))) in
      let uu____2674 =
        let uu____2675 = type_of ea in
        let uu____2676 = type_of eb in
        FStar_Syntax_Syntax.t_tuple2_of uu____2675 uu____2676 in
      mk_emb_full em un uu____2674 printer1 emb_t_pair_a_b
let e_either :
  'a 'b .
    'a embedding -> 'b embedding -> ('a, 'b) FStar_Util.either embedding
  =
  fun ea ->
    fun eb ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid in
        let uu____2717 =
          let uu____2718 = FStar_Syntax_Syntax.as_arg ea.typ in
          let uu____2727 =
            let uu____2738 = FStar_Syntax_Syntax.as_arg eb.typ in
            [uu____2738] in
          uu____2718 :: uu____2727 in
        FStar_Syntax_Syntax.mk_Tm_app t_either uu____2717
          FStar_Range.dummyRange in
      let emb_t_sum_a_b =
        let uu____2772 =
          let uu____2779 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid in
          (uu____2779, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu____2772 in
      let printer1 s =
        match s with
        | FStar_Util.Inl a1 ->
            let uu____2797 = ea.print a1 in
            FStar_Util.format1 "Inl %s" uu____2797
        | FStar_Util.Inr b1 ->
            let uu____2799 = eb.print b1 in
            FStar_Util.format1 "Inr %s" uu____2799 in
      let em s rng topt norm =
        lazy_embed printer1 emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a1 ->
               (fun uu____2844 ->
                  let shadow_a =
                    map_shadow topt
                      (fun t ->
                         let v = FStar_Ident.mk_ident ("v", rng) in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v in
                         let some_v_tm =
                           let uu____2856 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.fv_to_tm uu____2856 in
                         let uu____2857 =
                           FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                             [FStar_Syntax_Syntax.U_zero] in
                         let uu____2858 =
                           let uu____2859 =
                             let uu____2868 = type_of ea in
                             FStar_Syntax_Syntax.iarg uu____2868 in
                           let uu____2869 =
                             let uu____2880 =
                               let uu____2889 = type_of eb in
                               FStar_Syntax_Syntax.iarg uu____2889 in
                             let uu____2890 =
                               let uu____2901 = FStar_Syntax_Syntax.as_arg t in
                               [uu____2901] in
                             uu____2880 :: uu____2890 in
                           uu____2859 :: uu____2869 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2857 uu____2858
                           rng) in
                  let uu____2942 =
                    let uu____2943 =
                      FStar_Syntax_Syntax.tdataconstr
                        FStar_Parser_Const.inl_lid in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____2943
                      [FStar_Syntax_Syntax.U_zero;
                      FStar_Syntax_Syntax.U_zero] in
                  let uu____2944 =
                    let uu____2945 =
                      let uu____2954 = type_of ea in
                      FStar_Syntax_Syntax.iarg uu____2954 in
                    let uu____2955 =
                      let uu____2966 =
                        let uu____2975 = type_of eb in
                        FStar_Syntax_Syntax.iarg uu____2975 in
                      let uu____2976 =
                        let uu____2987 =
                          let uu____2996 =
                            let uu____2997 = embed ea a1 in
                            uu____2997 rng shadow_a norm in
                          FStar_Syntax_Syntax.as_arg uu____2996 in
                        [uu____2987] in
                      uu____2966 :: uu____2976 in
                    uu____2945 :: uu____2955 in
                  FStar_Syntax_Syntax.mk_Tm_app uu____2942 uu____2944 rng)
           | FStar_Util.Inr b1 ->
               (fun uu____3037 ->
                  let shadow_b =
                    map_shadow topt
                      (fun t ->
                         let v = FStar_Ident.mk_ident ("v", rng) in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v in
                         let some_v_tm =
                           let uu____3049 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.fv_to_tm uu____3049 in
                         let uu____3050 =
                           FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                             [FStar_Syntax_Syntax.U_zero] in
                         let uu____3051 =
                           let uu____3052 =
                             let uu____3061 = type_of ea in
                             FStar_Syntax_Syntax.iarg uu____3061 in
                           let uu____3062 =
                             let uu____3073 =
                               let uu____3082 = type_of eb in
                               FStar_Syntax_Syntax.iarg uu____3082 in
                             let uu____3083 =
                               let uu____3094 = FStar_Syntax_Syntax.as_arg t in
                               [uu____3094] in
                             uu____3073 :: uu____3083 in
                           uu____3052 :: uu____3062 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3050 uu____3051
                           rng) in
                  let uu____3135 =
                    let uu____3136 =
                      FStar_Syntax_Syntax.tdataconstr
                        FStar_Parser_Const.inr_lid in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3136
                      [FStar_Syntax_Syntax.U_zero;
                      FStar_Syntax_Syntax.U_zero] in
                  let uu____3137 =
                    let uu____3138 =
                      let uu____3147 = type_of ea in
                      FStar_Syntax_Syntax.iarg uu____3147 in
                    let uu____3148 =
                      let uu____3159 =
                        let uu____3168 = type_of eb in
                        FStar_Syntax_Syntax.iarg uu____3168 in
                      let uu____3169 =
                        let uu____3180 =
                          let uu____3189 =
                            let uu____3190 = embed eb b1 in
                            uu____3190 rng shadow_b norm in
                          FStar_Syntax_Syntax.as_arg uu____3189 in
                        [uu____3180] in
                      uu____3159 :: uu____3169 in
                    uu____3138 :: uu____3148 in
                  FStar_Syntax_Syntax.mk_Tm_app uu____3135 uu____3137 rng)) in
      let un t0 w norm =
        let t = FStar_Syntax_Util.unmeta_safe t0 in
        lazy_unembed printer1 emb_t_sum_a_b t t_sum_a_b
          (fun t1 ->
             let uu____3276 = FStar_Syntax_Util.head_and_args' t1 in
             match uu____3276 with
             | (hd, args) ->
                 let uu____3319 =
                   let uu____3334 =
                     let uu____3335 = FStar_Syntax_Util.un_uinst hd in
                     uu____3335.FStar_Syntax_Syntax.n in
                   (uu____3334, args) in
                 (match uu____3319 with
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu____3355::uu____3356::(a1, uu____3358)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____3425 =
                        let uu____3428 = unembed ea a1 in uu____3428 w norm in
                      FStar_Util.bind_opt uu____3425
                        (fun a2 ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a2))
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu____3446::uu____3447::(b1, uu____3449)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____3516 =
                        let uu____3519 = unembed eb b1 in uu____3519 w norm in
                      FStar_Util.bind_opt uu____3516
                        (fun b2 ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b2))
                  | uu____3536 ->
                      (if w
                       then
                         (let uu____3552 =
                            let uu____3557 =
                              let uu____3558 =
                                FStar_Syntax_Print.term_to_string t0 in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____3558 in
                            (FStar_Errors.Warning_NotEmbedded, uu____3557) in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____3552)
                       else ();
                       FStar_Pervasives_Native.None))) in
      let uu____3564 =
        let uu____3565 = type_of ea in
        let uu____3566 = type_of eb in
        FStar_Syntax_Syntax.t_either_of uu____3565 uu____3566 in
      mk_emb_full em un uu____3564 printer1 emb_t_sum_a_b
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid in
      let uu____3591 =
        let uu____3592 = FStar_Syntax_Syntax.as_arg ea.typ in [uu____3592] in
      FStar_Syntax_Syntax.mk_Tm_app t_list uu____3591 FStar_Range.dummyRange in
    let emb_t_list_a =
      let uu____3618 =
        let uu____3625 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid in
        (uu____3625, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu____3618 in
    let printer1 l =
      let uu____3638 =
        let uu____3639 =
          let uu____3640 = FStar_List.map ea.print l in
          FStar_All.pipe_right uu____3640 (FStar_String.concat "; ") in
        Prims.op_Hat uu____3639 "]" in
      Prims.op_Hat "[" uu____3638 in
    let rec em l rng shadow_l norm =
      lazy_embed printer1 emb_t_list_a rng t_list_a l
        (fun uu____3677 ->
           let t =
             let uu____3679 = type_of ea in
             FStar_Syntax_Syntax.iarg uu____3679 in
           match l with
           | [] ->
               let uu____3680 =
                 let uu____3681 =
                   FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3681
                   [FStar_Syntax_Syntax.U_zero] in
               FStar_Syntax_Syntax.mk_Tm_app uu____3680 [t] rng
           | hd::tl ->
               let cons =
                 let uu____3703 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3703
                   [FStar_Syntax_Syntax.U_zero] in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng) in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid in
                 let proj_tm =
                   let uu____3718 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None in
                   FStar_Syntax_Syntax.fv_to_tm uu____3718 in
                 let uu____3719 =
                   FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                     [FStar_Syntax_Syntax.U_zero] in
                 let uu____3720 =
                   let uu____3721 =
                     let uu____3730 = type_of ea in
                     FStar_Syntax_Syntax.iarg uu____3730 in
                   let uu____3731 =
                     let uu____3742 = FStar_Syntax_Syntax.as_arg cons_tm in
                     [uu____3742] in
                   uu____3721 :: uu____3731 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3719 uu____3720 rng in
               let shadow_hd = map_shadow shadow_l (proj "hd") in
               let shadow_tl = map_shadow shadow_l (proj "tl") in
               let uu____3777 =
                 let uu____3778 =
                   let uu____3789 =
                     let uu____3798 =
                       let uu____3799 = embed ea hd in
                       uu____3799 rng shadow_hd norm in
                     FStar_Syntax_Syntax.as_arg uu____3798 in
                   let uu____3806 =
                     let uu____3817 =
                       let uu____3826 = em tl rng shadow_tl norm in
                       FStar_Syntax_Syntax.as_arg uu____3826 in
                     [uu____3817] in
                   uu____3789 :: uu____3806 in
                 t :: uu____3778 in
               FStar_Syntax_Syntax.mk_Tm_app cons uu____3777 rng) in
    let rec un t0 w norm =
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      lazy_unembed printer1 emb_t_list_a t t_list_a
        (fun t1 ->
           let uu____3896 = FStar_Syntax_Util.head_and_args' t1 in
           match uu____3896 with
           | (hd, args) ->
               let uu____3937 =
                 let uu____3950 =
                   let uu____3951 = FStar_Syntax_Util.un_uinst hd in
                   uu____3951.FStar_Syntax_Syntax.n in
                 (uu____3950, args) in
               (match uu____3937 with
                | (FStar_Syntax_Syntax.Tm_fvar fv, uu____3967) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   (uu____3987, FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____3988))::(hd1,
                                                                 FStar_Pervasives_Native.None)::
                   (tl, FStar_Pervasives_Native.None)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4029 =
                      let uu____4032 = unembed ea hd1 in uu____4032 w norm in
                    FStar_Util.bind_opt uu____4029
                      (fun hd2 ->
                         let uu____4044 = un tl w norm in
                         FStar_Util.bind_opt uu____4044
                           (fun tl1 ->
                              FStar_Pervasives_Native.Some (hd2 :: tl1)))
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   (hd1, FStar_Pervasives_Native.None)::(tl,
                                                         FStar_Pervasives_Native.None)::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4092 =
                      let uu____4095 = unembed ea hd1 in uu____4095 w norm in
                    FStar_Util.bind_opt uu____4092
                      (fun hd2 ->
                         let uu____4107 = un tl w norm in
                         FStar_Util.bind_opt uu____4107
                           (fun tl1 ->
                              FStar_Pervasives_Native.Some (hd2 :: tl1)))
                | uu____4122 ->
                    (if w
                     then
                       (let uu____4136 =
                          let uu____4141 =
                            let uu____4142 =
                              FStar_Syntax_Print.term_to_string t0 in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____4142 in
                          (FStar_Errors.Warning_NotEmbedded, uu____4141) in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____4136)
                     else ();
                     FStar_Pervasives_Native.None))) in
    let uu____4146 =
      let uu____4147 = type_of ea in FStar_Syntax_Syntax.t_list_of uu____4147 in
    mk_emb_full em un uu____4146 printer1 emb_t_list_a
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string
type norm_step =
  | Simpl 
  | Weak 
  | HNF 
  | Primops 
  | Delta 
  | Zeta 
  | ZetaFull 
  | Iota 
  | Reify 
  | UnfoldOnly of Prims.string Prims.list 
  | UnfoldFully of Prims.string Prims.list 
  | UnfoldAttr of Prims.string Prims.list 
  | NBE 
let (uu___is_Simpl : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Simpl -> true | uu____4180 -> false
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Weak -> true | uu____4186 -> false
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | HNF -> true | uu____4192 -> false
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | Primops -> true | uu____4198 -> false
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Delta -> true | uu____4204 -> false
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Zeta -> true | uu____4210 -> false
let (uu___is_ZetaFull : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | ZetaFull -> true | uu____4216 -> false
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Iota -> true | uu____4222 -> false
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Reify -> true | uu____4228 -> false
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldOnly _0 -> true | uu____4237 -> false
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldOnly _0 -> _0
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldFully _0 -> true | uu____4258 -> false
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldFully _0 -> _0
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldAttr _0 -> true | uu____4279 -> false
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldAttr _0 -> _0
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | NBE -> true | uu____4297 -> false
let (steps_Simpl : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_simpl
let (steps_Weak : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_weak
let (steps_HNF : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_hnf
let (steps_Primops : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_primops
let (steps_Delta : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_delta
let (steps_Zeta : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_zeta
let (steps_ZetaFull : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_zeta_full
let (steps_Iota : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_iota
let (steps_Reify : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_reify
let (steps_UnfoldOnly : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_unfoldonly
let (steps_UnfoldFully : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_unfoldonly
let (steps_UnfoldAttr : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_unfoldattr
let (steps_NBE : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_nbe
let (e_norm_step : norm_step embedding) =
  let t_norm_step =
    let uu____4301 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step" in
    FStar_Syntax_Util.fvar_const uu____4301 in
  let emb_t_norm_step =
    let uu____4303 =
      let uu____4310 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid in
      (uu____4310, []) in
    FStar_Syntax_Syntax.ET_app uu____4303 in
  let printer1 uu____4318 = "norm_step" in
  let em n rng _topt norm =
    lazy_embed printer1 emb_t_norm_step rng t_norm_step n
      (fun uu____4343 ->
         match n with
         | Simpl -> steps_Simpl
         | Weak -> steps_Weak
         | HNF -> steps_HNF
         | Primops -> steps_Primops
         | Delta -> steps_Delta
         | Zeta -> steps_Zeta
         | ZetaFull -> steps_ZetaFull
         | Iota -> steps_Iota
         | NBE -> steps_NBE
         | Reify -> steps_Reify
         | UnfoldOnly l ->
             let uu____4347 =
               let uu____4348 =
                 let uu____4357 =
                   let uu____4358 =
                     let uu____4365 = e_list e_string in embed uu____4365 l in
                   uu____4358 rng FStar_Pervasives_Native.None norm in
                 FStar_Syntax_Syntax.as_arg uu____4357 in
               [uu____4348] in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____4347 rng
         | UnfoldFully l ->
             let uu____4393 =
               let uu____4394 =
                 let uu____4403 =
                   let uu____4404 =
                     let uu____4411 = e_list e_string in embed uu____4411 l in
                   uu____4404 rng FStar_Pervasives_Native.None norm in
                 FStar_Syntax_Syntax.as_arg uu____4403 in
               [uu____4394] in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____4393 rng
         | UnfoldAttr l ->
             let uu____4439 =
               let uu____4440 =
                 let uu____4449 =
                   let uu____4450 =
                     let uu____4457 = e_list e_string in embed uu____4457 l in
                   uu____4450 rng FStar_Pervasives_Native.None norm in
                 FStar_Syntax_Syntax.as_arg uu____4449 in
               [uu____4440] in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____4439 rng) in
  let un t0 w norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    lazy_unembed printer1 emb_t_norm_step t t_norm_step
      (fun t1 ->
         let uu____4512 = FStar_Syntax_Util.head_and_args t1 in
         match uu____4512 with
         | (hd, args) ->
             let uu____4557 =
               let uu____4572 =
                 let uu____4573 = FStar_Syntax_Util.un_uinst hd in
                 uu____4573.FStar_Syntax_Syntax.n in
               (uu____4572, args) in
             (match uu____4557 with
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_simpl
                  -> FStar_Pervasives_Native.Some Simpl
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_weak
                  -> FStar_Pervasives_Native.Some Weak
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_hnf
                  -> FStar_Pervasives_Native.Some HNF
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_primops
                  -> FStar_Pervasives_Native.Some Primops
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_delta
                  -> FStar_Pervasives_Native.Some Delta
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_zeta
                  -> FStar_Pervasives_Native.Some Zeta
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_zeta_full
                  -> FStar_Pervasives_Native.Some ZetaFull
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_iota
                  -> FStar_Pervasives_Native.Some Iota
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_nbe
                  -> FStar_Pervasives_Native.Some NBE
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_reify
                  -> FStar_Pervasives_Native.Some Reify
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____4780)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____4815 =
                    let uu____4820 =
                      let uu____4829 = e_list e_string in
                      unembed uu____4829 l in
                    uu____4820 w norm in
                  FStar_Util.bind_opt uu____4815
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun uu____4844 ->
                            FStar_Pervasives_Native.Some uu____4844)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____4847)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____4882 =
                    let uu____4887 =
                      let uu____4896 = e_list e_string in
                      unembed uu____4896 l in
                    uu____4887 w norm in
                  FStar_Util.bind_opt uu____4882
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun uu____4911 ->
                            FStar_Pervasives_Native.Some uu____4911)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____4914)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____4949 =
                    let uu____4954 =
                      let uu____4963 = e_list e_string in
                      unembed uu____4963 l in
                    uu____4954 w norm in
                  FStar_Util.bind_opt uu____4949
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun uu____4978 ->
                            FStar_Pervasives_Native.Some uu____4978)
                         (UnfoldAttr ss))
              | uu____4979 ->
                  (if w
                   then
                     (let uu____4995 =
                        let uu____5000 =
                          let uu____5001 =
                            FStar_Syntax_Print.term_to_string t0 in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____5001 in
                        (FStar_Errors.Warning_NotEmbedded, uu____5000) in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____4995)
                   else ();
                   FStar_Pervasives_Native.None))) in
  mk_emb_full em un FStar_Syntax_Syntax.t_norm_step printer1 emb_t_norm_step
let (e_range : FStar_Range.range embedding) =
  let em r rng _shadow _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r)) rng in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r) ->
        FStar_Pervasives_Native.Some r
    | uu____5054 ->
        (if w
         then
           (let uu____5056 =
              let uu____5061 =
                let uu____5062 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded range: %s" uu____5062 in
              (FStar_Errors.Warning_NotEmbedded, uu____5061) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____5056)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____5064 =
    let uu____5065 =
      let uu____5072 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid in
      (uu____5072, []) in
    FStar_Syntax_Syntax.ET_app uu____5065 in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____5064
let or_else : 'a . 'a FStar_Pervasives_Native.option -> (unit -> 'a) -> 'a =
  fun f ->
    fun g ->
      match f with
      | FStar_Pervasives_Native.Some x -> x
      | FStar_Pervasives_Native.None -> g ()
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea ->
    fun eb ->
      let t_arrow =
        let uu____5138 =
          let uu____5139 =
            let uu____5154 =
              let uu____5163 =
                let uu____5170 = FStar_Syntax_Syntax.null_bv ea.typ in
                (uu____5170, FStar_Pervasives_Native.None) in
              [uu____5163] in
            let uu____5185 = FStar_Syntax_Syntax.mk_Total eb.typ in
            (uu____5154, uu____5185) in
          FStar_Syntax_Syntax.Tm_arrow uu____5139 in
        FStar_Syntax_Syntax.mk uu____5138 FStar_Range.dummyRange in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ)) in
      let printer1 f = "<fun>" in
      let em f rng shadow_f norm =
        lazy_embed (fun uu____5253 -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____5258 ->
             let uu____5259 = force_shadow shadow_f in
             match uu____5259 with
             | FStar_Pervasives_Native.None ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____5264 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding in
                   if uu____5264
                   then
                     let uu____5271 =
                       FStar_Syntax_Print.term_to_string repr_f in
                     let uu____5272 = FStar_Util.stack_dump () in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____5271 uu____5272
                   else ());
                  (let res = norm (FStar_Util.Inr repr_f) in
                   (let uu____5276 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu____5276
                    then
                      let uu____5283 =
                        FStar_Syntax_Print.term_to_string repr_f in
                      let uu____5284 = FStar_Syntax_Print.term_to_string res in
                      let uu____5285 = FStar_Util.stack_dump () in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____5283 uu____5284 uu____5285
                    else ());
                   res))) in
      let un f w norm =
        lazy_unembed printer1 emb_t_arr_a_b f t_arrow
          (fun f1 ->
             let f_wrapped a1 =
               (let uu____5339 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding in
                if uu____5339
                then
                  let uu____5346 = FStar_Syntax_Print.term_to_string f1 in
                  let uu____5347 = FStar_Util.stack_dump () in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____5346
                    uu____5347
                else ());
               (let a_tm =
                  let uu____5350 = embed ea a1 in
                  uu____5350 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm in
                let b_tm =
                  let uu____5360 =
                    let uu____5365 =
                      let uu____5366 =
                        let uu____5367 = FStar_Syntax_Syntax.as_arg a_tm in
                        [uu____5367] in
                      FStar_Syntax_Syntax.mk_Tm_app f1 uu____5366
                        f1.FStar_Syntax_Syntax.pos in
                    FStar_Util.Inr uu____5365 in
                  norm uu____5360 in
                let uu____5392 =
                  let uu____5395 = unembed eb b_tm in uu____5395 w norm in
                match uu____5392 with
                | FStar_Pervasives_Native.None ->
                    FStar_Exn.raise Unembedding_failure
                | FStar_Pervasives_Native.Some b1 -> b1) in
             FStar_Pervasives_Native.Some f_wrapped) in
      mk_emb_full em un t_arrow printer1 emb_t_arr_a_b
let arrow_as_prim_step_1 :
  'a 'b .
    'a embedding ->
      'b embedding ->
        ('a -> 'b) ->
          Prims.int ->
            FStar_Ident.lid ->
              norm_cb ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun f ->
        fun n_tvars ->
          fun fv_lid ->
            fun norm ->
              let rng = FStar_Ident.range_of_lid fv_lid in
              let f_wrapped args =
                let uu____5486 = FStar_List.splitAt n_tvars args in
                match uu____5486 with
                | (_tvar_args, rest_args) ->
                    let uu____5563 = FStar_List.hd rest_args in
                    (match uu____5563 with
                     | (x, uu____5583) ->
                         let shadow_app =
                           let uu____5597 =
                             FStar_Thunk.mk
                               (fun uu____5602 ->
                                  let uu____5603 =
                                    norm (FStar_Util.Inl fv_lid) in
                                  FStar_Syntax_Syntax.mk_Tm_app uu____5603
                                    args rng) in
                           FStar_Pervasives_Native.Some uu____5597 in
                         let uu____5606 =
                           let uu____5609 =
                             let uu____5612 = unembed ea x in
                             uu____5612 true norm in
                           FStar_Util.map_opt uu____5609
                             (fun x1 ->
                                let uu____5622 =
                                  let uu____5629 = f x1 in
                                  embed eb uu____5629 in
                                uu____5622 rng shadow_app norm) in
                         (match uu____5606 with
                          | FStar_Pervasives_Native.Some x1 ->
                              FStar_Pervasives_Native.Some x1
                          | FStar_Pervasives_Native.None ->
                              force_shadow shadow_app)) in
              f_wrapped
let arrow_as_prim_step_2 :
  'a 'b 'c .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          ('a -> 'b -> 'c) ->
            Prims.int ->
              FStar_Ident.lid ->
                norm_cb ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun ec ->
        fun f ->
          fun n_tvars ->
            fun fv_lid ->
              fun norm ->
                let rng = FStar_Ident.range_of_lid fv_lid in
                let f_wrapped args =
                  let uu____5729 = FStar_List.splitAt n_tvars args in
                  match uu____5729 with
                  | (_tvar_args, rest_args) ->
                      let uu____5792 = FStar_List.hd rest_args in
                      (match uu____5792 with
                       | (x, uu____5808) ->
                           let uu____5813 =
                             let uu____5820 = FStar_List.tl rest_args in
                             FStar_List.hd uu____5820 in
                           (match uu____5813 with
                            | (y, uu____5844) ->
                                let shadow_app =
                                  let uu____5854 =
                                    FStar_Thunk.mk
                                      (fun uu____5859 ->
                                         let uu____5860 =
                                           norm (FStar_Util.Inl fv_lid) in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____5860 args rng) in
                                  FStar_Pervasives_Native.Some uu____5854 in
                                let uu____5863 =
                                  let uu____5866 =
                                    let uu____5869 = unembed ea x in
                                    uu____5869 true norm in
                                  FStar_Util.bind_opt uu____5866
                                    (fun x1 ->
                                       let uu____5879 =
                                         let uu____5882 = unembed eb y in
                                         uu____5882 true norm in
                                       FStar_Util.bind_opt uu____5879
                                         (fun y1 ->
                                            let uu____5892 =
                                              let uu____5893 =
                                                let uu____5900 = f x1 y1 in
                                                embed ec uu____5900 in
                                              uu____5893 rng shadow_app norm in
                                            FStar_Pervasives_Native.Some
                                              uu____5892)) in
                                (match uu____5863 with
                                 | FStar_Pervasives_Native.Some x1 ->
                                     FStar_Pervasives_Native.Some x1
                                 | FStar_Pervasives_Native.None ->
                                     force_shadow shadow_app))) in
                f_wrapped
let arrow_as_prim_step_3 :
  'a 'b 'c 'd .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          'd embedding ->
            ('a -> 'b -> 'c -> 'd) ->
              Prims.int ->
                FStar_Ident.lid ->
                  norm_cb ->
                    FStar_Syntax_Syntax.args ->
                      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun ec ->
        fun ed ->
          fun f ->
            fun n_tvars ->
              fun fv_lid ->
                fun norm ->
                  let rng = FStar_Ident.range_of_lid fv_lid in
                  let f_wrapped args =
                    let uu____6019 = FStar_List.splitAt n_tvars args in
                    match uu____6019 with
                    | (_tvar_args, rest_args) ->
                        let uu____6082 = FStar_List.hd rest_args in
                        (match uu____6082 with
                         | (x, uu____6098) ->
                             let uu____6103 =
                               let uu____6110 = FStar_List.tl rest_args in
                               FStar_List.hd uu____6110 in
                             (match uu____6103 with
                              | (y, uu____6134) ->
                                  let uu____6139 =
                                    let uu____6146 =
                                      let uu____6155 =
                                        FStar_List.tl rest_args in
                                      FStar_List.tl uu____6155 in
                                    FStar_List.hd uu____6146 in
                                  (match uu____6139 with
                                   | (z, uu____6185) ->
                                       let shadow_app =
                                         let uu____6195 =
                                           FStar_Thunk.mk
                                             (fun uu____6200 ->
                                                let uu____6201 =
                                                  norm
                                                    (FStar_Util.Inl fv_lid) in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____6201 args rng) in
                                         FStar_Pervasives_Native.Some
                                           uu____6195 in
                                       let uu____6204 =
                                         let uu____6207 =
                                           let uu____6210 = unembed ea x in
                                           uu____6210 true norm in
                                         FStar_Util.bind_opt uu____6207
                                           (fun x1 ->
                                              let uu____6220 =
                                                let uu____6223 = unembed eb y in
                                                uu____6223 true norm in
                                              FStar_Util.bind_opt uu____6220
                                                (fun y1 ->
                                                   let uu____6233 =
                                                     let uu____6236 =
                                                       unembed ec z in
                                                     uu____6236 true norm in
                                                   FStar_Util.bind_opt
                                                     uu____6233
                                                     (fun z1 ->
                                                        let uu____6246 =
                                                          let uu____6247 =
                                                            let uu____6254 =
                                                              f x1 y1 z1 in
                                                            embed ed
                                                              uu____6254 in
                                                          uu____6247 rng
                                                            shadow_app norm in
                                                        FStar_Pervasives_Native.Some
                                                          uu____6246))) in
                                       (match uu____6204 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None ->
                                            force_shadow shadow_app)))) in
                  f_wrapped
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s ->
    fun f ->
      (let uu____6281 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu____6281 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f () in
       (let uu____6291 = FStar_ST.op_Bang FStar_Options.debug_embedding in
        if uu____6291 then FStar_Util.print1 "------ending %s\n" s else ());
       res)