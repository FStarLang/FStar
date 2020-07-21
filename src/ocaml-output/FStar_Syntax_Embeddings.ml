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
              (unit -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun pa ->
    fun et ->
      fun rng ->
        fun ta ->
          fun x ->
            fun f ->
              (let uu____841 = FStar_ST.op_Bang FStar_Options.debug_embedding in
               if uu____841
               then
                 let uu____848 = FStar_Syntax_Print.term_to_string ta in
                 let uu____849 = FStar_Syntax_Print.emb_typ_to_string et in
                 let uu____850 = pa x in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu____848
                   uu____849 uu____850
               else ());
              (let uu____852 = FStar_ST.op_Bang FStar_Options.eager_embedding in
               if uu____852
               then f ()
               else
                 (let thunk = FStar_Thunk.mk f in
                  let uu____869 =
                    let uu____870 =
                      let uu____871 = FStar_Dyn.mkdyn x in
                      {
                        FStar_Syntax_Syntax.blob = uu____871;
                        FStar_Syntax_Syntax.lkind =
                          (FStar_Syntax_Syntax.Lazy_embedding (et, thunk));
                        FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                        FStar_Syntax_Syntax.rng = rng
                      } in
                    FStar_Syntax_Syntax.Tm_lazy uu____870 in
                  FStar_Syntax_Syntax.mk uu____869 rng))
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
                  FStar_Syntax_Syntax.ltyp = uu____937;
                  FStar_Syntax_Syntax.rng = uu____938;_}
                ->
                let uu____949 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding) in
                if uu____949
                then
                  let res =
                    let uu____961 = FStar_Thunk.force t in f uu____961 in
                  ((let uu____965 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu____965
                    then
                      let uu____972 = FStar_Syntax_Print.emb_typ_to_string et in
                      let uu____973 =
                        FStar_Syntax_Print.emb_typ_to_string et' in
                      let uu____974 =
                        match res with
                        | FStar_Pervasives_Native.None -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____976 = pa x2 in
                            Prims.op_Hat "Some " uu____976 in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____972 uu____973 uu____974
                    else ());
                   res)
                else
                  (let a1 = FStar_Dyn.undyn b in
                   (let uu____981 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu____981
                    then
                      let uu____988 = FStar_Syntax_Print.emb_typ_to_string et in
                      let uu____989 = pa a1 in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n" uu____988
                        uu____989
                    else ());
                   FStar_Pervasives_Native.Some a1)
            | uu____991 ->
                let aopt = f x1 in
                ((let uu____996 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding in
                  if uu____996
                  then
                    let uu____1003 = FStar_Syntax_Print.emb_typ_to_string et in
                    let uu____1004 = FStar_Syntax_Print.term_to_string x1 in
                    let uu____1005 =
                      match aopt with
                      | FStar_Pervasives_Native.None -> "None"
                      | FStar_Pervasives_Native.Some a1 ->
                          let uu____1007 = pa a1 in
                          Prims.op_Hat "Some " uu____1007 in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____1003 uu____1004 uu____1005
                  else ());
                 aopt)
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ ->
    let em t _r _topt _norm =
      (let uu____1040 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu____1040
       then
         let uu____1047 = unknown_printer typ t in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____1047
       else ());
      t in
    let un t _w _n =
      (let uu____1070 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu____1070
       then
         let uu____1077 = unknown_printer typ t in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____1077
       else ());
      FStar_Pervasives_Native.Some t in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t in
  let un t _w _n = FStar_Pervasives_Native.Some t in
  let uu____1124 =
    let uu____1125 =
      let uu____1132 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid in
      (uu____1132, []) in
    FStar_Syntax_Syntax.ET_app uu____1125 in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____1124
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___167_1160 = FStar_Syntax_Util.exp_unit in
    {
      FStar_Syntax_Syntax.n = (uu___167_1160.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___167_1160.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit) ->
        FStar_Pervasives_Native.Some ()
    | uu____1186 ->
        (if w
         then
           (let uu____1188 =
              let uu____1193 =
                let uu____1194 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded unit: %s" uu____1194 in
              (FStar_Errors.Warning_NotEmbedded, uu____1193) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1188)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____1196 =
    let uu____1197 =
      let uu____1204 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid in
      (uu____1204, []) in
    FStar_Syntax_Syntax.ET_app uu____1197 in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____1208 -> "()")
    uu____1196
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool in
    let uu___187_1240 = t in
    {
      FStar_Syntax_Syntax.n = (uu___187_1240.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___187_1240.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____1269 ->
        (if w
         then
           (let uu____1271 =
              let uu____1276 =
                let uu____1277 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded bool: %s" uu____1277 in
              (FStar_Errors.Warning_NotEmbedded, uu____1276) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1271)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____1279 =
    let uu____1280 =
      let uu____1287 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid in
      (uu____1287, []) in
    FStar_Syntax_Syntax.ET_app uu____1280 in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____1279
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c in
    let uu___206_1316 = t in
    {
      FStar_Syntax_Syntax.n = (uu___206_1316.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___206_1316.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____1343 ->
        (if w
         then
           (let uu____1345 =
              let uu____1350 =
                let uu____1351 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded char: %s" uu____1351 in
              (FStar_Errors.Warning_NotEmbedded, uu____1350) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1345)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____1353 =
    let uu____1354 =
      let uu____1361 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid in
      (uu____1361, []) in
    FStar_Syntax_Syntax.ET_app uu____1354 in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____1353
let (e_int : FStar_BigInt.t embedding) =
  let t_int = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid in
  let emb_t_int =
    let uu____1368 =
      let uu____1375 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid in
      (uu____1375, []) in
    FStar_Syntax_Syntax.ET_app uu____1368 in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int i
      (fun uu____1403 ->
         let uu____1404 = FStar_BigInt.string_of_big_int i in
         FStar_Syntax_Util.exp_int uu____1404) in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int
      (fun t1 ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s, uu____1436)) ->
             let uu____1449 = FStar_BigInt.big_int_of_string s in
             FStar_Pervasives_Native.Some uu____1449
         | uu____1450 ->
             (if w
              then
                (let uu____1452 =
                   let uu____1457 =
                     let uu____1458 = FStar_Syntax_Print.term_to_string t0 in
                     FStar_Util.format1 "Not an embedded int: %s" uu____1458 in
                   (FStar_Errors.Warning_NotEmbedded, uu____1457) in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1452)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____1463 =
      let uu____1470 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid in
      (uu____1470, []) in
    FStar_Syntax_Syntax.ET_app uu____1463 in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      rng in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s, uu____1522)) -> FStar_Pervasives_Native.Some s
    | uu____1523 ->
        (if w
         then
           (let uu____1525 =
              let uu____1530 =
                let uu____1531 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded string: %s" uu____1531 in
              (FStar_Errors.Warning_NotEmbedded, uu____1530) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1525)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb_full em un FStar_Syntax_Syntax.t_string
    (fun x -> Prims.op_Hat "\"" (Prims.op_Hat x "\"")) emb_t_string
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea ->
    let t_option_a =
      let t_opt = FStar_Syntax_Util.fvar_const FStar_Parser_Const.option_lid in
      let uu____1555 =
        let uu____1556 = FStar_Syntax_Syntax.as_arg ea.typ in [uu____1556] in
      FStar_Syntax_Syntax.mk_Tm_app t_opt uu____1555 FStar_Range.dummyRange in
    let emb_t_option_a =
      let uu____1582 =
        let uu____1589 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid in
        (uu____1589, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu____1582 in
    let printer1 uu___1_1599 =
      match uu___1_1599 with
      | FStar_Pervasives_Native.None -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____1603 =
            let uu____1604 = ea.print x in Prims.op_Hat uu____1604 ")" in
          Prims.op_Hat "(Some " uu____1603 in
    let em o rng topt norm =
      lazy_embed printer1 emb_t_option_a rng t_option_a o
        (fun uu____1637 ->
           match o with
           | FStar_Pervasives_Native.None ->
               let uu____1638 =
                 let uu____1639 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.none_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____1639
                   [FStar_Syntax_Syntax.U_zero] in
               let uu____1640 =
                 let uu____1641 =
                   let uu____1650 = type_of ea in
                   FStar_Syntax_Syntax.iarg uu____1650 in
                 [uu____1641] in
               FStar_Syntax_Syntax.mk_Tm_app uu____1638 uu____1640 rng
           | FStar_Pervasives_Native.Some a1 ->
               let shadow_a =
                 map_shadow topt
                   (fun t ->
                      let v = FStar_Ident.mk_ident ("v", rng) in
                      let some_v =
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          FStar_Parser_Const.some_lid v in
                      let some_v_tm =
                        let uu____1679 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None in
                        FStar_Syntax_Syntax.fv_to_tm uu____1679 in
                      let uu____1680 =
                        FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                          [FStar_Syntax_Syntax.U_zero] in
                      let uu____1681 =
                        let uu____1682 =
                          let uu____1691 = type_of ea in
                          FStar_Syntax_Syntax.iarg uu____1691 in
                        let uu____1692 =
                          let uu____1703 = FStar_Syntax_Syntax.as_arg t in
                          [uu____1703] in
                        uu____1682 :: uu____1692 in
                      FStar_Syntax_Syntax.mk_Tm_app uu____1680 uu____1681 rng) in
               let uu____1736 =
                 let uu____1737 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.some_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____1737
                   [FStar_Syntax_Syntax.U_zero] in
               let uu____1738 =
                 let uu____1739 =
                   let uu____1748 = type_of ea in
                   FStar_Syntax_Syntax.iarg uu____1748 in
                 let uu____1749 =
                   let uu____1760 =
                     let uu____1769 =
                       let uu____1770 = embed ea a1 in
                       uu____1770 rng shadow_a norm in
                     FStar_Syntax_Syntax.as_arg uu____1769 in
                   [uu____1760] in
                 uu____1739 :: uu____1749 in
               FStar_Syntax_Syntax.mk_Tm_app uu____1736 uu____1738 rng) in
    let un t0 w norm =
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      lazy_unembed printer1 emb_t_option_a t t_option_a
        (fun t1 ->
           let uu____1838 = FStar_Syntax_Util.head_and_args' t1 in
           match uu____1838 with
           | (hd, args) ->
               let uu____1879 =
                 let uu____1894 =
                   let uu____1895 = FStar_Syntax_Util.un_uinst hd in
                   uu____1895.FStar_Syntax_Syntax.n in
                 (uu____1894, args) in
               (match uu____1879 with
                | (FStar_Syntax_Syntax.Tm_fvar fv, uu____1913) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   uu____1937::(a1, uu____1939)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____1990 =
                      let uu____1993 = unembed ea a1 in uu____1993 w norm in
                    FStar_Util.bind_opt uu____1990
                      (fun a2 ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a2))
                | uu____2006 ->
                    (if w
                     then
                       (let uu____2022 =
                          let uu____2027 =
                            let uu____2028 =
                              FStar_Syntax_Print.term_to_string t0 in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____2028 in
                          (FStar_Errors.Warning_NotEmbedded, uu____2027) in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____2022)
                     else ();
                     FStar_Pervasives_Native.None))) in
    let uu____2032 =
      let uu____2033 = type_of ea in
      FStar_Syntax_Syntax.t_option_of uu____2033 in
    mk_emb_full em un uu____2032 printer1 emb_t_option_a
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea ->
    fun eb ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2 in
        let uu____2072 =
          let uu____2073 = FStar_Syntax_Syntax.as_arg ea.typ in
          let uu____2082 =
            let uu____2093 = FStar_Syntax_Syntax.as_arg eb.typ in
            [uu____2093] in
          uu____2073 :: uu____2082 in
        FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____2072
          FStar_Range.dummyRange in
      let emb_t_pair_a_b =
        let uu____2127 =
          let uu____2134 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid in
          (uu____2134, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu____2127 in
      let printer1 uu____2146 =
        match uu____2146 with
        | (x, y) ->
            let uu____2153 = ea.print x in
            let uu____2154 = eb.print y in
            FStar_Util.format2 "(%s, %s)" uu____2153 uu____2154 in
      let em x rng topt norm =
        lazy_embed printer1 emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____2196 ->
             let proj i ab =
               let proj_1 =
                 let uu____2209 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.of_int (2))
                     rng in
                 let uu____2210 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun in
                 FStar_Syntax_Util.mk_field_projector_name uu____2209
                   uu____2210 i in
               let proj_1_tm =
                 let uu____2212 =
                   FStar_Syntax_Syntax.lid_as_fv proj_1
                     FStar_Syntax_Syntax.delta_equational
                     FStar_Pervasives_Native.None in
                 FStar_Syntax_Syntax.fv_to_tm uu____2212 in
               let uu____2213 =
                 FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                   [FStar_Syntax_Syntax.U_zero] in
               let uu____2214 =
                 let uu____2215 =
                   let uu____2224 = type_of ea in
                   FStar_Syntax_Syntax.iarg uu____2224 in
                 let uu____2225 =
                   let uu____2236 =
                     let uu____2245 = type_of eb in
                     FStar_Syntax_Syntax.iarg uu____2245 in
                   let uu____2246 =
                     let uu____2257 = FStar_Syntax_Syntax.as_arg ab in
                     [uu____2257] in
                   uu____2236 :: uu____2246 in
                 uu____2215 :: uu____2225 in
               FStar_Syntax_Syntax.mk_Tm_app uu____2213 uu____2214 rng in
             let shadow_a = map_shadow topt (proj Prims.int_one) in
             let shadow_b = map_shadow topt (proj (Prims.of_int (2))) in
             let uu____2300 =
               let uu____2301 =
                 FStar_Syntax_Syntax.tdataconstr
                   FStar_Parser_Const.lid_Mktuple2 in
               FStar_Syntax_Syntax.mk_Tm_uinst uu____2301
                 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
             let uu____2302 =
               let uu____2303 =
                 let uu____2312 = type_of ea in
                 FStar_Syntax_Syntax.iarg uu____2312 in
               let uu____2313 =
                 let uu____2324 =
                   let uu____2333 = type_of eb in
                   FStar_Syntax_Syntax.iarg uu____2333 in
                 let uu____2334 =
                   let uu____2345 =
                     let uu____2354 =
                       let uu____2355 =
                         embed ea (FStar_Pervasives_Native.fst x) in
                       uu____2355 rng shadow_a norm in
                     FStar_Syntax_Syntax.as_arg uu____2354 in
                   let uu____2362 =
                     let uu____2373 =
                       let uu____2382 =
                         let uu____2383 =
                           embed eb (FStar_Pervasives_Native.snd x) in
                         uu____2383 rng shadow_b norm in
                       FStar_Syntax_Syntax.as_arg uu____2382 in
                     [uu____2373] in
                   uu____2345 :: uu____2362 in
                 uu____2324 :: uu____2334 in
               uu____2303 :: uu____2313 in
             FStar_Syntax_Syntax.mk_Tm_app uu____2300 uu____2302 rng) in
      let un t0 w norm =
        let t = FStar_Syntax_Util.unmeta_safe t0 in
        lazy_unembed printer1 emb_t_pair_a_b t t_pair_a_b
          (fun t1 ->
             let uu____2479 = FStar_Syntax_Util.head_and_args' t1 in
             match uu____2479 with
             | (hd, args) ->
                 let uu____2522 =
                   let uu____2535 =
                     let uu____2536 = FStar_Syntax_Util.un_uinst hd in
                     uu____2536.FStar_Syntax_Syntax.n in
                   (uu____2535, args) in
                 (match uu____2522 with
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu____2554::uu____2555::(a1, uu____2557)::(b1,
                                                                uu____2559)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____2618 =
                        let uu____2621 = unembed ea a1 in uu____2621 w norm in
                      FStar_Util.bind_opt uu____2618
                        (fun a2 ->
                           let uu____2635 =
                             let uu____2638 = unembed eb b1 in
                             uu____2638 w norm in
                           FStar_Util.bind_opt uu____2635
                             (fun b2 -> FStar_Pervasives_Native.Some (a2, b2)))
                  | uu____2655 ->
                      (if w
                       then
                         (let uu____2669 =
                            let uu____2674 =
                              let uu____2675 =
                                FStar_Syntax_Print.term_to_string t0 in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____2675 in
                            (FStar_Errors.Warning_NotEmbedded, uu____2674) in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____2669)
                       else ();
                       FStar_Pervasives_Native.None))) in
      let uu____2681 =
        let uu____2682 = type_of ea in
        let uu____2683 = type_of eb in
        FStar_Syntax_Syntax.t_tuple2_of uu____2682 uu____2683 in
      mk_emb_full em un uu____2681 printer1 emb_t_pair_a_b
let e_either :
  'a 'b .
    'a embedding -> 'b embedding -> ('a, 'b) FStar_Util.either embedding
  =
  fun ea ->
    fun eb ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid in
        let uu____2724 =
          let uu____2725 = FStar_Syntax_Syntax.as_arg ea.typ in
          let uu____2734 =
            let uu____2745 = FStar_Syntax_Syntax.as_arg eb.typ in
            [uu____2745] in
          uu____2725 :: uu____2734 in
        FStar_Syntax_Syntax.mk_Tm_app t_either uu____2724
          FStar_Range.dummyRange in
      let emb_t_sum_a_b =
        let uu____2779 =
          let uu____2786 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid in
          (uu____2786, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu____2779 in
      let printer1 s =
        match s with
        | FStar_Util.Inl a1 ->
            let uu____2804 = ea.print a1 in
            FStar_Util.format1 "Inl %s" uu____2804
        | FStar_Util.Inr b1 ->
            let uu____2806 = eb.print b1 in
            FStar_Util.format1 "Inr %s" uu____2806 in
      let em s rng topt norm =
        lazy_embed printer1 emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a1 ->
               (fun uu____2851 ->
                  let shadow_a =
                    map_shadow topt
                      (fun t ->
                         let v = FStar_Ident.mk_ident ("v", rng) in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v in
                         let some_v_tm =
                           let uu____2863 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.fv_to_tm uu____2863 in
                         let uu____2864 =
                           FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                             [FStar_Syntax_Syntax.U_zero] in
                         let uu____2865 =
                           let uu____2866 =
                             let uu____2875 = type_of ea in
                             FStar_Syntax_Syntax.iarg uu____2875 in
                           let uu____2876 =
                             let uu____2887 =
                               let uu____2896 = type_of eb in
                               FStar_Syntax_Syntax.iarg uu____2896 in
                             let uu____2897 =
                               let uu____2908 = FStar_Syntax_Syntax.as_arg t in
                               [uu____2908] in
                             uu____2887 :: uu____2897 in
                           uu____2866 :: uu____2876 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2864 uu____2865
                           rng) in
                  let uu____2949 =
                    let uu____2950 =
                      FStar_Syntax_Syntax.tdataconstr
                        FStar_Parser_Const.inl_lid in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____2950
                      [FStar_Syntax_Syntax.U_zero;
                      FStar_Syntax_Syntax.U_zero] in
                  let uu____2951 =
                    let uu____2952 =
                      let uu____2961 = type_of ea in
                      FStar_Syntax_Syntax.iarg uu____2961 in
                    let uu____2962 =
                      let uu____2973 =
                        let uu____2982 = type_of eb in
                        FStar_Syntax_Syntax.iarg uu____2982 in
                      let uu____2983 =
                        let uu____2994 =
                          let uu____3003 =
                            let uu____3004 = embed ea a1 in
                            uu____3004 rng shadow_a norm in
                          FStar_Syntax_Syntax.as_arg uu____3003 in
                        [uu____2994] in
                      uu____2973 :: uu____2983 in
                    uu____2952 :: uu____2962 in
                  FStar_Syntax_Syntax.mk_Tm_app uu____2949 uu____2951 rng)
           | FStar_Util.Inr b1 ->
               (fun uu____3044 ->
                  let shadow_b =
                    map_shadow topt
                      (fun t ->
                         let v = FStar_Ident.mk_ident ("v", rng) in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v in
                         let some_v_tm =
                           let uu____3056 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.fv_to_tm uu____3056 in
                         let uu____3057 =
                           FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                             [FStar_Syntax_Syntax.U_zero] in
                         let uu____3058 =
                           let uu____3059 =
                             let uu____3068 = type_of ea in
                             FStar_Syntax_Syntax.iarg uu____3068 in
                           let uu____3069 =
                             let uu____3080 =
                               let uu____3089 = type_of eb in
                               FStar_Syntax_Syntax.iarg uu____3089 in
                             let uu____3090 =
                               let uu____3101 = FStar_Syntax_Syntax.as_arg t in
                               [uu____3101] in
                             uu____3080 :: uu____3090 in
                           uu____3059 :: uu____3069 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3057 uu____3058
                           rng) in
                  let uu____3142 =
                    let uu____3143 =
                      FStar_Syntax_Syntax.tdataconstr
                        FStar_Parser_Const.inr_lid in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3143
                      [FStar_Syntax_Syntax.U_zero;
                      FStar_Syntax_Syntax.U_zero] in
                  let uu____3144 =
                    let uu____3145 =
                      let uu____3154 = type_of ea in
                      FStar_Syntax_Syntax.iarg uu____3154 in
                    let uu____3155 =
                      let uu____3166 =
                        let uu____3175 = type_of eb in
                        FStar_Syntax_Syntax.iarg uu____3175 in
                      let uu____3176 =
                        let uu____3187 =
                          let uu____3196 =
                            let uu____3197 = embed eb b1 in
                            uu____3197 rng shadow_b norm in
                          FStar_Syntax_Syntax.as_arg uu____3196 in
                        [uu____3187] in
                      uu____3166 :: uu____3176 in
                    uu____3145 :: uu____3155 in
                  FStar_Syntax_Syntax.mk_Tm_app uu____3142 uu____3144 rng)) in
      let un t0 w norm =
        let t = FStar_Syntax_Util.unmeta_safe t0 in
        lazy_unembed printer1 emb_t_sum_a_b t t_sum_a_b
          (fun t1 ->
             let uu____3283 = FStar_Syntax_Util.head_and_args' t1 in
             match uu____3283 with
             | (hd, args) ->
                 let uu____3326 =
                   let uu____3341 =
                     let uu____3342 = FStar_Syntax_Util.un_uinst hd in
                     uu____3342.FStar_Syntax_Syntax.n in
                   (uu____3341, args) in
                 (match uu____3326 with
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu____3362::uu____3363::(a1, uu____3365)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____3432 =
                        let uu____3435 = unembed ea a1 in uu____3435 w norm in
                      FStar_Util.bind_opt uu____3432
                        (fun a2 ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a2))
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu____3453::uu____3454::(b1, uu____3456)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____3523 =
                        let uu____3526 = unembed eb b1 in uu____3526 w norm in
                      FStar_Util.bind_opt uu____3523
                        (fun b2 ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b2))
                  | uu____3543 ->
                      (if w
                       then
                         (let uu____3559 =
                            let uu____3564 =
                              let uu____3565 =
                                FStar_Syntax_Print.term_to_string t0 in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____3565 in
                            (FStar_Errors.Warning_NotEmbedded, uu____3564) in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____3559)
                       else ();
                       FStar_Pervasives_Native.None))) in
      let uu____3571 =
        let uu____3572 = type_of ea in
        let uu____3573 = type_of eb in
        FStar_Syntax_Syntax.t_either_of uu____3572 uu____3573 in
      mk_emb_full em un uu____3571 printer1 emb_t_sum_a_b
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid in
      let uu____3598 =
        let uu____3599 = FStar_Syntax_Syntax.as_arg ea.typ in [uu____3599] in
      FStar_Syntax_Syntax.mk_Tm_app t_list uu____3598 FStar_Range.dummyRange in
    let emb_t_list_a =
      let uu____3625 =
        let uu____3632 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid in
        (uu____3632, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu____3625 in
    let printer1 l =
      let uu____3645 =
        let uu____3646 =
          let uu____3647 = FStar_List.map ea.print l in
          FStar_All.pipe_right uu____3647 (FStar_String.concat "; ") in
        Prims.op_Hat uu____3646 "]" in
      Prims.op_Hat "[" uu____3645 in
    let rec em l rng shadow_l norm =
      lazy_embed printer1 emb_t_list_a rng t_list_a l
        (fun uu____3684 ->
           let t =
             let uu____3686 = type_of ea in
             FStar_Syntax_Syntax.iarg uu____3686 in
           match l with
           | [] ->
               let uu____3687 =
                 let uu____3688 =
                   FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3688
                   [FStar_Syntax_Syntax.U_zero] in
               FStar_Syntax_Syntax.mk_Tm_app uu____3687 [t] rng
           | hd::tl ->
               let cons =
                 let uu____3710 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3710
                   [FStar_Syntax_Syntax.U_zero] in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng) in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid in
                 let proj_tm =
                   let uu____3725 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None in
                   FStar_Syntax_Syntax.fv_to_tm uu____3725 in
                 let uu____3726 =
                   FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                     [FStar_Syntax_Syntax.U_zero] in
                 let uu____3727 =
                   let uu____3728 =
                     let uu____3737 = type_of ea in
                     FStar_Syntax_Syntax.iarg uu____3737 in
                   let uu____3738 =
                     let uu____3749 = FStar_Syntax_Syntax.as_arg cons_tm in
                     [uu____3749] in
                   uu____3728 :: uu____3738 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3726 uu____3727 rng in
               let shadow_hd = map_shadow shadow_l (proj "hd") in
               let shadow_tl = map_shadow shadow_l (proj "tl") in
               let uu____3784 =
                 let uu____3785 =
                   let uu____3796 =
                     let uu____3805 =
                       let uu____3806 = embed ea hd in
                       uu____3806 rng shadow_hd norm in
                     FStar_Syntax_Syntax.as_arg uu____3805 in
                   let uu____3813 =
                     let uu____3824 =
                       let uu____3833 = em tl rng shadow_tl norm in
                       FStar_Syntax_Syntax.as_arg uu____3833 in
                     [uu____3824] in
                   uu____3796 :: uu____3813 in
                 t :: uu____3785 in
               FStar_Syntax_Syntax.mk_Tm_app cons uu____3784 rng) in
    let rec un t0 w norm =
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      lazy_unembed printer1 emb_t_list_a t t_list_a
        (fun t1 ->
           let uu____3903 = FStar_Syntax_Util.head_and_args' t1 in
           match uu____3903 with
           | (hd, args) ->
               let uu____3944 =
                 let uu____3957 =
                   let uu____3958 = FStar_Syntax_Util.un_uinst hd in
                   uu____3958.FStar_Syntax_Syntax.n in
                 (uu____3957, args) in
               (match uu____3944 with
                | (FStar_Syntax_Syntax.Tm_fvar fv, uu____3974) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   (uu____3994, FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____3995))::(hd1,
                                                                 FStar_Pervasives_Native.None)::
                   (tl, FStar_Pervasives_Native.None)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4036 =
                      let uu____4039 = unembed ea hd1 in uu____4039 w norm in
                    FStar_Util.bind_opt uu____4036
                      (fun hd2 ->
                         let uu____4051 = un tl w norm in
                         FStar_Util.bind_opt uu____4051
                           (fun tl1 ->
                              FStar_Pervasives_Native.Some (hd2 :: tl1)))
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   (hd1, FStar_Pervasives_Native.None)::(tl,
                                                         FStar_Pervasives_Native.None)::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4099 =
                      let uu____4102 = unembed ea hd1 in uu____4102 w norm in
                    FStar_Util.bind_opt uu____4099
                      (fun hd2 ->
                         let uu____4114 = un tl w norm in
                         FStar_Util.bind_opt uu____4114
                           (fun tl1 ->
                              FStar_Pervasives_Native.Some (hd2 :: tl1)))
                | uu____4129 ->
                    (if w
                     then
                       (let uu____4143 =
                          let uu____4148 =
                            let uu____4149 =
                              FStar_Syntax_Print.term_to_string t0 in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____4149 in
                          (FStar_Errors.Warning_NotEmbedded, uu____4148) in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____4143)
                     else ();
                     FStar_Pervasives_Native.None))) in
    let uu____4153 =
      let uu____4154 = type_of ea in FStar_Syntax_Syntax.t_list_of uu____4154 in
    mk_emb_full em un uu____4153 printer1 emb_t_list_a
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
  fun projectee -> match projectee with | Simpl -> true | uu____4187 -> false
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Weak -> true | uu____4193 -> false
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | HNF -> true | uu____4199 -> false
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | Primops -> true | uu____4205 -> false
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Delta -> true | uu____4211 -> false
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Zeta -> true | uu____4217 -> false
let (uu___is_ZetaFull : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | ZetaFull -> true | uu____4223 -> false
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Iota -> true | uu____4229 -> false
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Reify -> true | uu____4235 -> false
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldOnly _0 -> true | uu____4244 -> false
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldOnly _0 -> _0
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldFully _0 -> true | uu____4265 -> false
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldFully _0 -> _0
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldAttr _0 -> true | uu____4286 -> false
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldAttr _0 -> _0
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | NBE -> true | uu____4304 -> false
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
    let uu____4308 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step" in
    FStar_Syntax_Util.fvar_const uu____4308 in
  let emb_t_norm_step =
    let uu____4310 =
      let uu____4317 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid in
      (uu____4317, []) in
    FStar_Syntax_Syntax.ET_app uu____4310 in
  let printer1 uu____4325 = "norm_step" in
  let em n rng _topt norm =
    lazy_embed printer1 emb_t_norm_step rng t_norm_step n
      (fun uu____4350 ->
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
             let uu____4354 =
               let uu____4355 =
                 let uu____4364 =
                   let uu____4365 =
                     let uu____4372 = e_list e_string in embed uu____4372 l in
                   uu____4365 rng FStar_Pervasives_Native.None norm in
                 FStar_Syntax_Syntax.as_arg uu____4364 in
               [uu____4355] in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____4354 rng
         | UnfoldFully l ->
             let uu____4400 =
               let uu____4401 =
                 let uu____4410 =
                   let uu____4411 =
                     let uu____4418 = e_list e_string in embed uu____4418 l in
                   uu____4411 rng FStar_Pervasives_Native.None norm in
                 FStar_Syntax_Syntax.as_arg uu____4410 in
               [uu____4401] in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____4400 rng
         | UnfoldAttr l ->
             let uu____4446 =
               let uu____4447 =
                 let uu____4456 =
                   let uu____4457 =
                     let uu____4464 = e_list e_string in embed uu____4464 l in
                   uu____4457 rng FStar_Pervasives_Native.None norm in
                 FStar_Syntax_Syntax.as_arg uu____4456 in
               [uu____4447] in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____4446 rng) in
  let un t0 w norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    lazy_unembed printer1 emb_t_norm_step t t_norm_step
      (fun t1 ->
         let uu____4519 = FStar_Syntax_Util.head_and_args t1 in
         match uu____4519 with
         | (hd, args) ->
             let uu____4564 =
               let uu____4579 =
                 let uu____4580 = FStar_Syntax_Util.un_uinst hd in
                 uu____4580.FStar_Syntax_Syntax.n in
               (uu____4579, args) in
             (match uu____4564 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____4787)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____4822 =
                    let uu____4827 =
                      let uu____4836 = e_list e_string in
                      unembed uu____4836 l in
                    uu____4827 w norm in
                  FStar_Util.bind_opt uu____4822
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun uu____4851 ->
                            FStar_Pervasives_Native.Some uu____4851)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____4854)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____4889 =
                    let uu____4894 =
                      let uu____4903 = e_list e_string in
                      unembed uu____4903 l in
                    uu____4894 w norm in
                  FStar_Util.bind_opt uu____4889
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun uu____4918 ->
                            FStar_Pervasives_Native.Some uu____4918)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____4921)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____4956 =
                    let uu____4961 =
                      let uu____4970 = e_list e_string in
                      unembed uu____4970 l in
                    uu____4961 w norm in
                  FStar_Util.bind_opt uu____4956
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun uu____4985 ->
                            FStar_Pervasives_Native.Some uu____4985)
                         (UnfoldAttr ss))
              | uu____4986 ->
                  (if w
                   then
                     (let uu____5002 =
                        let uu____5007 =
                          let uu____5008 =
                            FStar_Syntax_Print.term_to_string t0 in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____5008 in
                        (FStar_Errors.Warning_NotEmbedded, uu____5007) in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____5002)
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
    | uu____5061 ->
        (if w
         then
           (let uu____5063 =
              let uu____5068 =
                let uu____5069 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded range: %s" uu____5069 in
              (FStar_Errors.Warning_NotEmbedded, uu____5068) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____5063)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____5071 =
    let uu____5072 =
      let uu____5079 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid in
      (uu____5079, []) in
    FStar_Syntax_Syntax.ET_app uu____5072 in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____5071
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
        let uu____5145 =
          let uu____5146 =
            let uu____5161 =
              let uu____5170 =
                let uu____5177 = FStar_Syntax_Syntax.null_bv ea.typ in
                (uu____5177, FStar_Pervasives_Native.None) in
              [uu____5170] in
            let uu____5192 = FStar_Syntax_Syntax.mk_Total eb.typ in
            (uu____5161, uu____5192) in
          FStar_Syntax_Syntax.Tm_arrow uu____5146 in
        FStar_Syntax_Syntax.mk uu____5145 FStar_Range.dummyRange in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ)) in
      let printer1 f = "<fun>" in
      let em f rng shadow_f norm =
        lazy_embed (fun uu____5262 -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____5267 ->
             let uu____5268 = force_shadow shadow_f in
             match uu____5268 with
             | FStar_Pervasives_Native.None ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____5273 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding in
                   if uu____5273
                   then
                     let uu____5280 =
                       FStar_Syntax_Print.term_to_string repr_f in
                     let uu____5281 = FStar_Util.stack_dump () in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____5280 uu____5281
                   else ());
                  (let res = norm (FStar_Util.Inr repr_f) in
                   (let uu____5285 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu____5285
                    then
                      let uu____5292 =
                        FStar_Syntax_Print.term_to_string repr_f in
                      let uu____5293 = FStar_Syntax_Print.term_to_string res in
                      let uu____5294 = FStar_Util.stack_dump () in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____5292 uu____5293 uu____5294
                    else ());
                   res))) in
      let un f w norm =
        lazy_unembed printer1 emb_t_arr_a_b f t_arrow
          (fun f1 ->
             let f_wrapped a1 =
               (let uu____5348 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding in
                if uu____5348
                then
                  let uu____5355 = FStar_Syntax_Print.term_to_string f1 in
                  let uu____5356 = FStar_Util.stack_dump () in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____5355
                    uu____5356
                else ());
               (let a_tm =
                  let uu____5359 = embed ea a1 in
                  uu____5359 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm in
                let b_tm =
                  let uu____5369 =
                    let uu____5374 =
                      let uu____5375 =
                        let uu____5376 = FStar_Syntax_Syntax.as_arg a_tm in
                        [uu____5376] in
                      FStar_Syntax_Syntax.mk_Tm_app f1 uu____5375
                        f1.FStar_Syntax_Syntax.pos in
                    FStar_Util.Inr uu____5374 in
                  norm uu____5369 in
                let uu____5401 =
                  let uu____5404 = unembed eb b_tm in uu____5404 w norm in
                match uu____5401 with
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
                let uu____5495 = FStar_List.splitAt n_tvars args in
                match uu____5495 with
                | (_tvar_args, rest_args) ->
                    let uu____5572 = FStar_List.hd rest_args in
                    (match uu____5572 with
                     | (x, uu____5592) ->
                         let shadow_app =
                           let uu____5606 =
                             FStar_Thunk.mk
                               (fun uu____5611 ->
                                  let uu____5612 =
                                    norm (FStar_Util.Inl fv_lid) in
                                  FStar_Syntax_Syntax.mk_Tm_app uu____5612
                                    args rng) in
                           FStar_Pervasives_Native.Some uu____5606 in
                         let uu____5615 =
                           let uu____5618 =
                             let uu____5621 = unembed ea x in
                             uu____5621 true norm in
                           FStar_Util.map_opt uu____5618
                             (fun x1 ->
                                let uu____5631 =
                                  let uu____5638 = f x1 in
                                  embed eb uu____5638 in
                                uu____5631 rng shadow_app norm) in
                         (match uu____5615 with
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
                  let uu____5738 = FStar_List.splitAt n_tvars args in
                  match uu____5738 with
                  | (_tvar_args, rest_args) ->
                      let uu____5801 = FStar_List.hd rest_args in
                      (match uu____5801 with
                       | (x, uu____5817) ->
                           let uu____5822 =
                             let uu____5829 = FStar_List.tl rest_args in
                             FStar_List.hd uu____5829 in
                           (match uu____5822 with
                            | (y, uu____5853) ->
                                let shadow_app =
                                  let uu____5863 =
                                    FStar_Thunk.mk
                                      (fun uu____5868 ->
                                         let uu____5869 =
                                           norm (FStar_Util.Inl fv_lid) in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____5869 args rng) in
                                  FStar_Pervasives_Native.Some uu____5863 in
                                let uu____5872 =
                                  let uu____5875 =
                                    let uu____5878 = unembed ea x in
                                    uu____5878 true norm in
                                  FStar_Util.bind_opt uu____5875
                                    (fun x1 ->
                                       let uu____5888 =
                                         let uu____5891 = unembed eb y in
                                         uu____5891 true norm in
                                       FStar_Util.bind_opt uu____5888
                                         (fun y1 ->
                                            let uu____5901 =
                                              let uu____5902 =
                                                let uu____5909 = f x1 y1 in
                                                embed ec uu____5909 in
                                              uu____5902 rng shadow_app norm in
                                            FStar_Pervasives_Native.Some
                                              uu____5901)) in
                                (match uu____5872 with
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
                    let uu____6028 = FStar_List.splitAt n_tvars args in
                    match uu____6028 with
                    | (_tvar_args, rest_args) ->
                        let uu____6091 = FStar_List.hd rest_args in
                        (match uu____6091 with
                         | (x, uu____6107) ->
                             let uu____6112 =
                               let uu____6119 = FStar_List.tl rest_args in
                               FStar_List.hd uu____6119 in
                             (match uu____6112 with
                              | (y, uu____6143) ->
                                  let uu____6148 =
                                    let uu____6155 =
                                      let uu____6164 =
                                        FStar_List.tl rest_args in
                                      FStar_List.tl uu____6164 in
                                    FStar_List.hd uu____6155 in
                                  (match uu____6148 with
                                   | (z, uu____6194) ->
                                       let shadow_app =
                                         let uu____6204 =
                                           FStar_Thunk.mk
                                             (fun uu____6209 ->
                                                let uu____6210 =
                                                  norm
                                                    (FStar_Util.Inl fv_lid) in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____6210 args rng) in
                                         FStar_Pervasives_Native.Some
                                           uu____6204 in
                                       let uu____6213 =
                                         let uu____6216 =
                                           let uu____6219 = unembed ea x in
                                           uu____6219 true norm in
                                         FStar_Util.bind_opt uu____6216
                                           (fun x1 ->
                                              let uu____6229 =
                                                let uu____6232 = unembed eb y in
                                                uu____6232 true norm in
                                              FStar_Util.bind_opt uu____6229
                                                (fun y1 ->
                                                   let uu____6242 =
                                                     let uu____6245 =
                                                       unembed ec z in
                                                     uu____6245 true norm in
                                                   FStar_Util.bind_opt
                                                     uu____6242
                                                     (fun z1 ->
                                                        let uu____6255 =
                                                          let uu____6256 =
                                                            let uu____6263 =
                                                              f x1 y1 z1 in
                                                            embed ed
                                                              uu____6263 in
                                                          uu____6256 rng
                                                            shadow_app norm in
                                                        FStar_Pervasives_Native.Some
                                                          uu____6255))) in
                                       (match uu____6213 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None ->
                                            force_shadow shadow_app)))) in
                  f_wrapped
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s ->
    fun f ->
      (let uu____6290 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu____6290 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f () in
       (let uu____6300 = FStar_ST.op_Bang FStar_Options.debug_embedding in
        if uu____6300 then FStar_Util.print1 "------ending %s\n" s else ());
       res)