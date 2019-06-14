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
    match projectee with | Embedding_failure -> true | uu____33 -> false
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Unembedding_failure -> true | uu____44 -> false
type shadow_term =
  FStar_Syntax_Syntax.term FStar_Common.thunk FStar_Pervasives_Native.option
let (map_shadow :
  shadow_term ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> shadow_term)
  =
  fun s ->
    fun f ->
      FStar_Util.map_opt s
        (fun s1 ->
           FStar_Common.mk_thunk
             (fun uu____76 ->
                let uu____77 = FStar_Common.force_thunk s1 in f uu____77))
let (force_shadow :
  shadow_term -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun s -> FStar_Util.map_opt s FStar_Common.force_thunk
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
    match projectee with | { em; un; typ; print = print7; emb_typ;_} -> em
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun projectee ->
    match projectee with | { em; un; typ; print = print7; emb_typ;_} -> un
let __proj__Mkembedding__item__typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.typ =
  fun projectee ->
    match projectee with | { em; un; typ; print = print7; emb_typ;_} -> typ
let __proj__Mkembedding__item__print : 'a . 'a embedding -> 'a printer =
  fun projectee ->
    match projectee with
    | { em; un; typ; print = print7; emb_typ;_} -> print7
let __proj__Mkembedding__item__emb_typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun projectee ->
    match projectee with
    | { em; un; typ; print = print7; emb_typ;_} -> emb_typ
let emb_typ_of : 'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun e -> e.emb_typ
let unknown_printer :
  'Auu____439 . FStar_Syntax_Syntax.term -> 'Auu____439 -> Prims.string =
  fun typ ->
    fun uu____450 ->
      let uu____451 = FStar_Syntax_Print.term_to_string typ in
      FStar_Util.format1 "unknown %s" uu____451
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t ->
    let uu____460 =
      let uu____461 = FStar_Syntax_Subst.compress t in
      uu____461.FStar_Syntax_Syntax.n in
    match uu____460 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____465 ->
        let uu____466 =
          let uu____468 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____468 in
        failwith uu____466
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em ->
    fun un ->
      fun fv ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv in
        let uu____511 =
          let uu____512 =
            let uu____520 =
              let uu____522 = FStar_Syntax_Syntax.lid_of_fv fv in
              FStar_All.pipe_right uu____522 FStar_Ident.string_of_lid in
            (uu____520, []) in
          FStar_Syntax_Syntax.ET_app uu____512 in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____511 }
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
        fun printer ->
          fun emb_typ -> { em; un; typ; print = printer; emb_typ }
let embed : 'a . 'a embedding -> 'a -> embed_t = fun e -> fun x -> e.em x
let unembed : 'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun e -> fun t -> e.un t
let warn_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e ->
    fun t -> fun n1 -> let uu____671 = unembed e t in uu____671 true n1
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e ->
    fun t -> fun n1 -> let uu____712 = unembed e t in uu____712 false n1
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e -> e.typ
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty ->
    fun e ->
      let uu___79_759 = e in
      {
        em = (uu___79_759.em);
        un = (uu___79_759.un);
        typ = ty;
        print = (uu___79_759.print);
        emb_typ = (uu___79_759.emb_typ)
      }
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
              (let uu____822 = FStar_ST.op_Bang FStar_Options.debug_embedding in
               if uu____822
               then
                 let uu____846 = FStar_Syntax_Print.term_to_string ta in
                 let uu____848 = FStar_Syntax_Print.emb_typ_to_string et in
                 let uu____850 = pa x in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu____846
                   uu____848 uu____850
               else ());
              (let uu____855 = FStar_ST.op_Bang FStar_Options.eager_embedding in
               if uu____855
               then f ()
               else
                 (let thunk1 = FStar_Common.mk_thunk f in
                  let uu____890 =
                    let uu____897 =
                      let uu____898 =
                        let uu____899 = FStar_Dyn.mkdyn x in
                        {
                          FStar_Syntax_Syntax.blob = uu____899;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk1));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        } in
                      FStar_Syntax_Syntax.Tm_lazy uu____898 in
                    FStar_Syntax_Syntax.mk uu____897 in
                  uu____890 FStar_Pervasives_Native.None rng))
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
                  FStar_Syntax_Syntax.ltyp = uu____966;
                  FStar_Syntax_Syntax.rng = uu____967;_}
                ->
                let uu____978 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding) in
                if uu____978
                then
                  let res =
                    let uu____1007 = FStar_Common.force_thunk t in
                    f uu____1007 in
                  ((let uu____1011 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu____1011
                    then
                      let uu____1035 =
                        FStar_Syntax_Print.emb_typ_to_string et in
                      let uu____1037 =
                        FStar_Syntax_Print.emb_typ_to_string et' in
                      let uu____1039 =
                        match res with
                        | FStar_Pervasives_Native.None -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____1044 = pa x2 in
                            Prims.op_Hat "Some " uu____1044 in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____1035 uu____1037 uu____1039
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b in
                   (let uu____1054 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu____1054
                    then
                      let uu____1078 =
                        FStar_Syntax_Print.emb_typ_to_string et in
                      let uu____1080 = pa a in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____1078 uu____1080
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____1085 ->
                let aopt = f x1 in
                ((let uu____1090 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding in
                  if uu____1090
                  then
                    let uu____1114 = FStar_Syntax_Print.emb_typ_to_string et in
                    let uu____1116 = FStar_Syntax_Print.term_to_string x1 in
                    let uu____1118 =
                      match aopt with
                      | FStar_Pervasives_Native.None -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____1123 = pa a in
                          Prims.op_Hat "Some " uu____1123 in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____1114 uu____1116 uu____1118
                  else ());
                 aopt)
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ ->
    let em t _r _topt _norm =
      (let uu____1161 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu____1161
       then
         let uu____1185 = unknown_printer typ t in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____1185
       else ());
      t in
    let un t _w _n =
      (let uu____1213 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu____1213
       then
         let uu____1237 = unknown_printer typ t in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____1237
       else ());
      FStar_Pervasives_Native.Some t in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t in
  let un t _w _n = FStar_Pervasives_Native.Some t in
  let uu____1290 =
    let uu____1291 =
      let uu____1299 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid in
      (uu____1299, []) in
    FStar_Syntax_Syntax.ET_app uu____1291 in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____1290
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___153_1331 = FStar_Syntax_Util.exp_unit in
    {
      FStar_Syntax_Syntax.n = (uu___153_1331.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___153_1331.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit) ->
        FStar_Pervasives_Native.Some ()
    | uu____1359 ->
        (if w
         then
           (let uu____1362 =
              let uu____1368 =
                let uu____1370 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded unit: %s" uu____1370 in
              (FStar_Errors.Warning_NotEmbedded, uu____1368) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1362)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____1376 =
    let uu____1377 =
      let uu____1385 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid in
      (uu____1385, []) in
    FStar_Syntax_Syntax.ET_app uu____1377 in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____1392 -> "()")
    uu____1376
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool in
    let uu___173_1431 = t in
    {
      FStar_Syntax_Syntax.n = (uu___173_1431.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___173_1431.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____1467 ->
        (if w
         then
           (let uu____1470 =
              let uu____1476 =
                let uu____1478 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded bool: %s" uu____1478 in
              (FStar_Errors.Warning_NotEmbedded, uu____1476) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1470)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____1485 =
    let uu____1486 =
      let uu____1494 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid in
      (uu____1494, []) in
    FStar_Syntax_Syntax.ET_app uu____1486 in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____1485
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c in
    let uu___192_1531 = t in
    {
      FStar_Syntax_Syntax.n = (uu___192_1531.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___192_1531.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____1565 ->
        (if w
         then
           (let uu____1568 =
              let uu____1574 =
                let uu____1576 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded char: %s" uu____1576 in
              (FStar_Errors.Warning_NotEmbedded, uu____1574) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1568)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____1583 =
    let uu____1584 =
      let uu____1592 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid in
      (uu____1592, []) in
    FStar_Syntax_Syntax.ET_app uu____1584 in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____1583
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid in
  let emb_t_int =
    let uu____1604 =
      let uu____1612 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid in
      (uu____1612, []) in
    FStar_Syntax_Syntax.ET_app uu____1604 in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____1643 ->
         let uu____1644 = FStar_BigInt.string_of_big_int i in
         FStar_Syntax_Util.exp_int uu____1644) in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1 ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s, uu____1679)) ->
             let uu____1694 = FStar_BigInt.big_int_of_string s in
             FStar_Pervasives_Native.Some uu____1694
         | uu____1695 ->
             (if w
              then
                (let uu____1698 =
                   let uu____1704 =
                     let uu____1706 = FStar_Syntax_Print.term_to_string t0 in
                     FStar_Util.format1 "Not an embedded int: %s" uu____1706 in
                   (FStar_Errors.Warning_NotEmbedded, uu____1704) in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1698)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____1717 =
      let uu____1725 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid in
      (uu____1725, []) in
    FStar_Syntax_Syntax.ET_app uu____1717 in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s, uu____1788)) -> FStar_Pervasives_Native.Some s
    | uu____1792 ->
        (if w
         then
           (let uu____1795 =
              let uu____1801 =
                let uu____1803 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded string: %s" uu____1803 in
              (FStar_Errors.Warning_NotEmbedded, uu____1801) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1795)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb_full em un FStar_Syntax_Syntax.t_string
    (fun x -> Prims.op_Hat "\"" (Prims.op_Hat x "\"")) emb_t_string
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea ->
    let t_option_a =
      let t_opt = FStar_Syntax_Util.fvar_const FStar_Parser_Const.option_lid in
      let uu____1839 =
        let uu____1844 =
          let uu____1845 = FStar_Syntax_Syntax.as_arg ea.typ in [uu____1845] in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____1844 in
      uu____1839 FStar_Pervasives_Native.None FStar_Range.dummyRange in
    let emb_t_option_a =
      let uu____1871 =
        let uu____1879 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid in
        (uu____1879, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu____1871 in
    let printer uu___1_1893 =
      match uu___1_1893 with
      | FStar_Pervasives_Native.None -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____1899 =
            let uu____1901 = ea.print x in Prims.op_Hat uu____1901 ")" in
          Prims.op_Hat "(Some " uu____1899 in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____1936 ->
           match o with
           | FStar_Pervasives_Native.None ->
               let uu____1937 =
                 let uu____1942 =
                   let uu____1943 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____1943
                     [FStar_Syntax_Syntax.U_zero] in
                 let uu____1944 =
                   let uu____1945 =
                     let uu____1954 = type_of ea in
                     FStar_Syntax_Syntax.iarg uu____1954 in
                   [uu____1945] in
                 FStar_Syntax_Syntax.mk_Tm_app uu____1942 uu____1944 in
               uu____1937 FStar_Pervasives_Native.None rng
           | FStar_Pervasives_Native.Some a ->
               let shadow_a =
                 map_shadow topt
                   (fun t ->
                      let v1 = FStar_Ident.mk_ident ("v", rng) in
                      let some_v =
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          FStar_Parser_Const.some_lid v1 in
                      let some_v_tm =
                        let uu____1984 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None in
                        FStar_Syntax_Syntax.fv_to_tm uu____1984 in
                      let uu____1985 =
                        let uu____1990 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero] in
                        let uu____1991 =
                          let uu____1992 =
                            let uu____2001 = type_of ea in
                            FStar_Syntax_Syntax.iarg uu____2001 in
                          let uu____2002 =
                            let uu____2013 = FStar_Syntax_Syntax.as_arg t in
                            [uu____2013] in
                          uu____1992 :: uu____2002 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____1990 uu____1991 in
                      uu____1985 FStar_Pervasives_Native.None rng) in
               let uu____2046 =
                 let uu____2051 =
                   let uu____2052 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2052
                     [FStar_Syntax_Syntax.U_zero] in
                 let uu____2053 =
                   let uu____2054 =
                     let uu____2063 = type_of ea in
                     FStar_Syntax_Syntax.iarg uu____2063 in
                   let uu____2064 =
                     let uu____2075 =
                       let uu____2084 =
                         let uu____2085 = embed ea a in
                         uu____2085 rng shadow_a norm1 in
                       FStar_Syntax_Syntax.as_arg uu____2084 in
                     [uu____2075] in
                   uu____2054 :: uu____2064 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2051 uu____2053 in
               uu____2046 FStar_Pervasives_Native.None rng) in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1 ->
           let uu____2155 = FStar_Syntax_Util.head_and_args' t1 in
           match uu____2155 with
           | (hd1, args) ->
               let uu____2196 =
                 let uu____2211 =
                   let uu____2212 = FStar_Syntax_Util.un_uinst hd1 in
                   uu____2212.FStar_Syntax_Syntax.n in
                 (uu____2211, args) in
               (match uu____2196 with
                | (FStar_Syntax_Syntax.Tm_fvar fv, uu____2230) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   uu____2254::(a, uu____2256)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____2307 =
                      let uu____2310 = unembed ea a in uu____2310 w norm1 in
                    FStar_Util.bind_opt uu____2307
                      (fun a1 ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____2323 ->
                    (if w
                     then
                       (let uu____2340 =
                          let uu____2346 =
                            let uu____2348 =
                              FStar_Syntax_Print.term_to_string t0 in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____2348 in
                          (FStar_Errors.Warning_NotEmbedded, uu____2346) in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____2340)
                     else ();
                     FStar_Pervasives_Native.None))) in
    let uu____2356 =
      let uu____2357 = type_of ea in
      FStar_Syntax_Syntax.t_option_of uu____2357 in
    mk_emb_full em un uu____2356 printer emb_t_option_a
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea ->
    fun eb ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2 in
        let uu____2399 =
          let uu____2404 =
            let uu____2405 = FStar_Syntax_Syntax.as_arg ea.typ in
            let uu____2414 =
              let uu____2425 = FStar_Syntax_Syntax.as_arg eb.typ in
              [uu____2425] in
            uu____2405 :: uu____2414 in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____2404 in
        uu____2399 FStar_Pervasives_Native.None FStar_Range.dummyRange in
      let emb_t_pair_a_b =
        let uu____2459 =
          let uu____2467 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid in
          (uu____2467, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu____2459 in
      let printer uu____2483 =
        match uu____2483 with
        | (x, y) ->
            let uu____2491 = ea.print x in
            let uu____2493 = eb.print y in
            FStar_Util.format2 "(%s, %s)" uu____2491 uu____2493 in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____2536 ->
             let proj i ab =
               let uu____2552 =
                 let uu____2557 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng in
                 let uu____2559 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun in
                 FStar_Syntax_Util.mk_field_projector_name uu____2557
                   uu____2559 i in
               match uu____2552 with
               | (proj_1, uu____2563) ->
                   let proj_1_tm =
                     let uu____2565 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None in
                     FStar_Syntax_Syntax.fv_to_tm uu____2565 in
                   let uu____2566 =
                     let uu____2571 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero] in
                     let uu____2572 =
                       let uu____2573 =
                         let uu____2582 = type_of ea in
                         FStar_Syntax_Syntax.iarg uu____2582 in
                       let uu____2583 =
                         let uu____2594 =
                           let uu____2603 = type_of eb in
                           FStar_Syntax_Syntax.iarg uu____2603 in
                         let uu____2604 =
                           let uu____2615 = FStar_Syntax_Syntax.as_arg ab in
                           [uu____2615] in
                         uu____2594 :: uu____2604 in
                       uu____2573 :: uu____2583 in
                     FStar_Syntax_Syntax.mk_Tm_app uu____2571 uu____2572 in
                   uu____2566 FStar_Pervasives_Native.None rng in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1")) in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2")) in
             let uu____2660 =
               let uu____2665 =
                 let uu____2666 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2 in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____2666
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
               let uu____2667 =
                 let uu____2668 =
                   let uu____2677 = type_of ea in
                   FStar_Syntax_Syntax.iarg uu____2677 in
                 let uu____2678 =
                   let uu____2689 =
                     let uu____2698 = type_of eb in
                     FStar_Syntax_Syntax.iarg uu____2698 in
                   let uu____2699 =
                     let uu____2710 =
                       let uu____2719 =
                         let uu____2720 =
                           embed ea (FStar_Pervasives_Native.fst x) in
                         uu____2720 rng shadow_a norm1 in
                       FStar_Syntax_Syntax.as_arg uu____2719 in
                     let uu____2727 =
                       let uu____2738 =
                         let uu____2747 =
                           let uu____2748 =
                             embed eb (FStar_Pervasives_Native.snd x) in
                           uu____2748 rng shadow_b norm1 in
                         FStar_Syntax_Syntax.as_arg uu____2747 in
                       [uu____2738] in
                     uu____2710 :: uu____2727 in
                   uu____2689 :: uu____2699 in
                 uu____2668 :: uu____2678 in
               FStar_Syntax_Syntax.mk_Tm_app uu____2665 uu____2667 in
             uu____2660 FStar_Pervasives_Native.None rng) in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0 in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1 ->
             let uu____2846 = FStar_Syntax_Util.head_and_args' t1 in
             match uu____2846 with
             | (hd1, args) ->
                 let uu____2889 =
                   let uu____2902 =
                     let uu____2903 = FStar_Syntax_Util.un_uinst hd1 in
                     uu____2903.FStar_Syntax_Syntax.n in
                   (uu____2902, args) in
                 (match uu____2889 with
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu____2921::uu____2922::(a, uu____2924)::(b, uu____2926)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____2985 =
                        let uu____2988 = unembed ea a in uu____2988 w norm1 in
                      FStar_Util.bind_opt uu____2985
                        (fun a1 ->
                           let uu____3002 =
                             let uu____3005 = unembed eb b in
                             uu____3005 w norm1 in
                           FStar_Util.bind_opt uu____3002
                             (fun b1 -> FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____3022 ->
                      (if w
                       then
                         (let uu____3037 =
                            let uu____3043 =
                              let uu____3045 =
                                FStar_Syntax_Print.term_to_string t0 in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____3045 in
                            (FStar_Errors.Warning_NotEmbedded, uu____3043) in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____3037)
                       else ();
                       FStar_Pervasives_Native.None))) in
      let uu____3055 =
        let uu____3056 = type_of ea in
        let uu____3057 = type_of eb in
        FStar_Syntax_Syntax.t_tuple2_of uu____3056 uu____3057 in
      mk_emb_full em un uu____3055 printer emb_t_pair_a_b
let e_either :
  'a 'b .
    'a embedding -> 'b embedding -> ('a, 'b) FStar_Util.either embedding
  =
  fun ea ->
    fun eb ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid in
        let uu____3101 =
          let uu____3106 =
            let uu____3107 = FStar_Syntax_Syntax.as_arg ea.typ in
            let uu____3116 =
              let uu____3127 = FStar_Syntax_Syntax.as_arg eb.typ in
              [uu____3127] in
            uu____3107 :: uu____3116 in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____3106 in
        uu____3101 FStar_Pervasives_Native.None FStar_Range.dummyRange in
      let emb_t_sum_a_b =
        let uu____3161 =
          let uu____3169 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid in
          (uu____3169, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu____3161 in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____3192 = ea.print a in
            FStar_Util.format1 "Inl %s" uu____3192
        | FStar_Util.Inr b ->
            let uu____3196 = eb.print b in
            FStar_Util.format1 "Inr %s" uu____3196 in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____3242 ->
                  let shadow_a =
                    map_shadow topt
                      (fun t ->
                         let v1 = FStar_Ident.mk_ident ("v", rng) in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1 in
                         let some_v_tm =
                           let uu____3255 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.fv_to_tm uu____3255 in
                         let uu____3256 =
                           let uu____3261 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero] in
                           let uu____3262 =
                             let uu____3263 =
                               let uu____3272 = type_of ea in
                               FStar_Syntax_Syntax.iarg uu____3272 in
                             let uu____3273 =
                               let uu____3284 =
                                 let uu____3293 = type_of eb in
                                 FStar_Syntax_Syntax.iarg uu____3293 in
                               let uu____3294 =
                                 let uu____3305 =
                                   FStar_Syntax_Syntax.as_arg t in
                                 [uu____3305] in
                               uu____3284 :: uu____3294 in
                             uu____3263 :: uu____3273 in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3261
                             uu____3262 in
                         uu____3256 FStar_Pervasives_Native.None rng) in
                  let uu____3346 =
                    let uu____3351 =
                      let uu____3352 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____3352
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero] in
                    let uu____3353 =
                      let uu____3354 =
                        let uu____3363 = type_of ea in
                        FStar_Syntax_Syntax.iarg uu____3363 in
                      let uu____3364 =
                        let uu____3375 =
                          let uu____3384 = type_of eb in
                          FStar_Syntax_Syntax.iarg uu____3384 in
                        let uu____3385 =
                          let uu____3396 =
                            let uu____3405 =
                              let uu____3406 = embed ea a in
                              uu____3406 rng shadow_a norm1 in
                            FStar_Syntax_Syntax.as_arg uu____3405 in
                          [uu____3396] in
                        uu____3375 :: uu____3385 in
                      uu____3354 :: uu____3364 in
                    FStar_Syntax_Syntax.mk_Tm_app uu____3351 uu____3353 in
                  uu____3346 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____3446 ->
                  let shadow_b =
                    map_shadow topt
                      (fun t ->
                         let v1 = FStar_Ident.mk_ident ("v", rng) in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1 in
                         let some_v_tm =
                           let uu____3459 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.fv_to_tm uu____3459 in
                         let uu____3460 =
                           let uu____3465 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero] in
                           let uu____3466 =
                             let uu____3467 =
                               let uu____3476 = type_of ea in
                               FStar_Syntax_Syntax.iarg uu____3476 in
                             let uu____3477 =
                               let uu____3488 =
                                 let uu____3497 = type_of eb in
                                 FStar_Syntax_Syntax.iarg uu____3497 in
                               let uu____3498 =
                                 let uu____3509 =
                                   FStar_Syntax_Syntax.as_arg t in
                                 [uu____3509] in
                               uu____3488 :: uu____3498 in
                             uu____3467 :: uu____3477 in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3465
                             uu____3466 in
                         uu____3460 FStar_Pervasives_Native.None rng) in
                  let uu____3550 =
                    let uu____3555 =
                      let uu____3556 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____3556
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero] in
                    let uu____3557 =
                      let uu____3558 =
                        let uu____3567 = type_of ea in
                        FStar_Syntax_Syntax.iarg uu____3567 in
                      let uu____3568 =
                        let uu____3579 =
                          let uu____3588 = type_of eb in
                          FStar_Syntax_Syntax.iarg uu____3588 in
                        let uu____3589 =
                          let uu____3600 =
                            let uu____3609 =
                              let uu____3610 = embed eb b in
                              uu____3610 rng shadow_b norm1 in
                            FStar_Syntax_Syntax.as_arg uu____3609 in
                          [uu____3600] in
                        uu____3579 :: uu____3589 in
                      uu____3558 :: uu____3568 in
                    FStar_Syntax_Syntax.mk_Tm_app uu____3555 uu____3557 in
                  uu____3550 FStar_Pervasives_Native.None rng)) in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0 in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1 ->
             let uu____3698 = FStar_Syntax_Util.head_and_args' t1 in
             match uu____3698 with
             | (hd1, args) ->
                 let uu____3741 =
                   let uu____3756 =
                     let uu____3757 = FStar_Syntax_Util.un_uinst hd1 in
                     uu____3757.FStar_Syntax_Syntax.n in
                   (uu____3756, args) in
                 (match uu____3741 with
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu____3777::uu____3778::(a, uu____3780)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____3847 =
                        let uu____3850 = unembed ea a in uu____3850 w norm1 in
                      FStar_Util.bind_opt uu____3847
                        (fun a1 ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu____3868::uu____3869::(b, uu____3871)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____3938 =
                        let uu____3941 = unembed eb b in uu____3941 w norm1 in
                      FStar_Util.bind_opt uu____3938
                        (fun b1 ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____3958 ->
                      (if w
                       then
                         (let uu____3975 =
                            let uu____3981 =
                              let uu____3983 =
                                FStar_Syntax_Print.term_to_string t0 in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____3983 in
                            (FStar_Errors.Warning_NotEmbedded, uu____3981) in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____3975)
                       else ();
                       FStar_Pervasives_Native.None))) in
      let uu____3993 =
        let uu____3994 = type_of ea in
        let uu____3995 = type_of eb in
        FStar_Syntax_Syntax.t_either_of uu____3994 uu____3995 in
      mk_emb_full em un uu____3993 printer emb_t_sum_a_b
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid in
      let uu____4023 =
        let uu____4028 =
          let uu____4029 = FStar_Syntax_Syntax.as_arg ea.typ in [uu____4029] in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____4028 in
      uu____4023 FStar_Pervasives_Native.None FStar_Range.dummyRange in
    let emb_t_list_a =
      let uu____4055 =
        let uu____4063 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid in
        (uu____4063, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu____4055 in
    let printer l =
      let uu____4080 =
        let uu____4082 =
          let uu____4084 = FStar_List.map ea.print l in
          FStar_All.pipe_right uu____4084 (FStar_String.concat "; ") in
        Prims.op_Hat uu____4082 "]" in
      Prims.op_Hat "[" uu____4080 in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____4128 ->
           let t =
             let uu____4130 = type_of ea in
             FStar_Syntax_Syntax.iarg uu____4130 in
           match l with
           | [] ->
               let uu____4131 =
                 let uu____4136 =
                   let uu____4137 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____4137
                     [FStar_Syntax_Syntax.U_zero] in
                 FStar_Syntax_Syntax.mk_Tm_app uu____4136 [t] in
               uu____4131 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____4159 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4159
                   [FStar_Syntax_Syntax.U_zero] in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng) in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid in
                 let proj_tm =
                   let uu____4179 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None in
                   FStar_Syntax_Syntax.fv_to_tm uu____4179 in
                 let uu____4180 =
                   let uu____4185 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero] in
                   let uu____4186 =
                     let uu____4187 =
                       let uu____4196 = type_of ea in
                       FStar_Syntax_Syntax.iarg uu____4196 in
                     let uu____4197 =
                       let uu____4208 = FStar_Syntax_Syntax.as_arg cons_tm in
                       [uu____4208] in
                     uu____4187 :: uu____4197 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4185 uu____4186 in
                 uu____4180 FStar_Pervasives_Native.None rng in
               let shadow_hd = map_shadow shadow_l (proj "hd") in
               let shadow_tl = map_shadow shadow_l (proj "tl") in
               let uu____4245 =
                 let uu____4250 =
                   let uu____4251 =
                     let uu____4262 =
                       let uu____4271 =
                         let uu____4272 = embed ea hd1 in
                         uu____4272 rng shadow_hd norm1 in
                       FStar_Syntax_Syntax.as_arg uu____4271 in
                     let uu____4279 =
                       let uu____4290 =
                         let uu____4299 = em tl1 rng shadow_tl norm1 in
                         FStar_Syntax_Syntax.as_arg uu____4299 in
                       [uu____4290] in
                     uu____4262 :: uu____4279 in
                   t :: uu____4251 in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____4250 in
               uu____4245 FStar_Pervasives_Native.None rng) in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1 ->
           let uu____4371 = FStar_Syntax_Util.head_and_args' t1 in
           match uu____4371 with
           | (hd1, args) ->
               let uu____4412 =
                 let uu____4425 =
                   let uu____4426 = FStar_Syntax_Util.un_uinst hd1 in
                   uu____4426.FStar_Syntax_Syntax.n in
                 (uu____4425, args) in
               (match uu____4412 with
                | (FStar_Syntax_Syntax.Tm_fvar fv, uu____4442) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   (uu____4462, FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____4463))::(hd2,
                                                                 FStar_Pervasives_Native.None)::
                   (tl1, FStar_Pervasives_Native.None)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4505 =
                      let uu____4508 = unembed ea hd2 in uu____4508 w norm1 in
                    FStar_Util.bind_opt uu____4505
                      (fun hd3 ->
                         let uu____4520 = un tl1 w norm1 in
                         FStar_Util.bind_opt uu____4520
                           (fun tl2 ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   (hd2, FStar_Pervasives_Native.None)::(tl1,
                                                         FStar_Pervasives_Native.None)::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4568 =
                      let uu____4571 = unembed ea hd2 in uu____4571 w norm1 in
                    FStar_Util.bind_opt uu____4568
                      (fun hd3 ->
                         let uu____4583 = un tl1 w norm1 in
                         FStar_Util.bind_opt uu____4583
                           (fun tl2 ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____4598 ->
                    (if w
                     then
                       (let uu____4613 =
                          let uu____4619 =
                            let uu____4621 =
                              FStar_Syntax_Print.term_to_string t0 in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____4621 in
                          (FStar_Errors.Warning_NotEmbedded, uu____4619) in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____4613)
                     else ();
                     FStar_Pervasives_Native.None))) in
    let uu____4629 =
      let uu____4630 = type_of ea in FStar_Syntax_Syntax.t_list_of uu____4630 in
    mk_emb_full em un uu____4629 printer emb_t_list_a
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string
type norm_step =
  | Simpl 
  | Weak 
  | HNF 
  | Primops 
  | Delta 
  | Zeta 
  | Iota 
  | Reify 
  | UnfoldOnly of Prims.string Prims.list 
  | UnfoldFully of Prims.string Prims.list 
  | UnfoldAttr of Prims.string Prims.list 
  | NBE 
let (uu___is_Simpl : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Simpl -> true | uu____4673 -> false
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Weak -> true | uu____4684 -> false
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | HNF -> true | uu____4695 -> false
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | Primops -> true | uu____4706 -> false
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Delta -> true | uu____4717 -> false
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Zeta -> true | uu____4728 -> false
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Iota -> true | uu____4739 -> false
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Reify -> true | uu____4750 -> false
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldOnly _0 -> true | uu____4765 -> false
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldOnly _0 -> _0
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldFully _0 -> true | uu____4796 -> false
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldFully _0 -> _0
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldAttr _0 -> true | uu____4827 -> false
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldAttr _0 -> _0
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | NBE -> true | uu____4854 -> false
let (steps_Simpl : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_simpl
let (steps_Weak : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_weak
let (steps_HNF : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_hnf
let (steps_Primops : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_primops
let (steps_Delta : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_delta
let (steps_Zeta : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_zeta
let (steps_Iota : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_iota
let (steps_Reify : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_reify
let (steps_UnfoldOnly : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldonly
let (steps_UnfoldFully : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldonly
let (steps_UnfoldAttr : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldattr
let (steps_NBE : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_nbe
let (e_norm_step : norm_step embedding) =
  let t_norm_step1 =
    let uu____4872 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step" in
    FStar_Syntax_Util.fvar_const uu____4872 in
  let emb_t_norm_step =
    let uu____4875 =
      let uu____4883 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid in
      (uu____4883, []) in
    FStar_Syntax_Syntax.ET_app uu____4875 in
  let printer uu____4895 = "norm_step" in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____4921 ->
         match n1 with
         | Simpl -> steps_Simpl
         | Weak -> steps_Weak
         | HNF -> steps_HNF
         | Primops -> steps_Primops
         | Delta -> steps_Delta
         | Zeta -> steps_Zeta
         | Iota -> steps_Iota
         | NBE -> steps_NBE
         | Reify -> steps_Reify
         | UnfoldOnly l ->
             let uu____4926 =
               let uu____4931 =
                 let uu____4932 =
                   let uu____4941 =
                     let uu____4942 =
                       let uu____4949 = e_list e_string in embed uu____4949 l in
                     uu____4942 rng FStar_Pervasives_Native.None norm1 in
                   FStar_Syntax_Syntax.as_arg uu____4941 in
                 [uu____4932] in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____4931 in
             uu____4926 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____4981 =
               let uu____4986 =
                 let uu____4987 =
                   let uu____4996 =
                     let uu____4997 =
                       let uu____5004 = e_list e_string in embed uu____5004 l in
                     uu____4997 rng FStar_Pervasives_Native.None norm1 in
                   FStar_Syntax_Syntax.as_arg uu____4996 in
                 [uu____4987] in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____4986 in
             uu____4981 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____5036 =
               let uu____5041 =
                 let uu____5042 =
                   let uu____5051 =
                     let uu____5052 =
                       let uu____5059 = e_list e_string in embed uu____5059 l in
                     uu____5052 rng FStar_Pervasives_Native.None norm1 in
                   FStar_Syntax_Syntax.as_arg uu____5051 in
                 [uu____5042] in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____5041 in
             uu____5036 FStar_Pervasives_Native.None rng) in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1 ->
         let uu____5119 = FStar_Syntax_Util.head_and_args t1 in
         match uu____5119 with
         | (hd1, args) ->
             let uu____5164 =
               let uu____5179 =
                 let uu____5180 = FStar_Syntax_Util.un_uinst hd1 in
                 uu____5180.FStar_Syntax_Syntax.n in
               (uu____5179, args) in
             (match uu____5164 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____5368)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____5403 =
                    let uu____5409 =
                      let uu____5419 = e_list e_string in
                      unembed uu____5419 l in
                    uu____5409 w norm1 in
                  FStar_Util.bind_opt uu____5403
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun _5439 -> FStar_Pervasives_Native.Some _5439)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____5442)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____5477 =
                    let uu____5483 =
                      let uu____5493 = e_list e_string in
                      unembed uu____5493 l in
                    uu____5483 w norm1 in
                  FStar_Util.bind_opt uu____5477
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun _5513 -> FStar_Pervasives_Native.Some _5513)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____5516)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____5551 =
                    let uu____5557 =
                      let uu____5567 = e_list e_string in
                      unembed uu____5567 l in
                    uu____5557 w norm1 in
                  FStar_Util.bind_opt uu____5551
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun _5587 -> FStar_Pervasives_Native.Some _5587)
                         (UnfoldAttr ss))
              | uu____5588 ->
                  (if w
                   then
                     (let uu____5605 =
                        let uu____5611 =
                          let uu____5613 =
                            FStar_Syntax_Print.term_to_string t0 in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____5613 in
                        (FStar_Errors.Warning_NotEmbedded, uu____5611) in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____5605)
                   else ();
                   FStar_Pervasives_Native.None))) in
  mk_emb_full em un FStar_Syntax_Syntax.t_norm_step printer emb_t_norm_step
let (e_range : FStar_Range.range embedding) =
  let em r rng _shadow _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None rng in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r) ->
        FStar_Pervasives_Native.Some r
    | uu____5673 ->
        (if w
         then
           (let uu____5676 =
              let uu____5682 =
                let uu____5684 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded range: %s" uu____5684 in
              (FStar_Errors.Warning_NotEmbedded, uu____5682) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____5676)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____5690 =
    let uu____5691 =
      let uu____5699 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid in
      (uu____5699, []) in
    FStar_Syntax_Syntax.ET_app uu____5691 in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____5690
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
        let uu____5770 =
          let uu____5777 =
            let uu____5778 =
              let uu____5793 =
                let uu____5802 =
                  let uu____5809 = FStar_Syntax_Syntax.null_bv ea.typ in
                  (uu____5809, FStar_Pervasives_Native.None) in
                [uu____5802] in
              let uu____5824 = FStar_Syntax_Syntax.mk_Total eb.typ in
              (uu____5793, uu____5824) in
            FStar_Syntax_Syntax.Tm_arrow uu____5778 in
          FStar_Syntax_Syntax.mk uu____5777 in
        uu____5770 FStar_Pervasives_Native.None FStar_Range.dummyRange in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ)) in
      let printer f = "<fun>" in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____5896 -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____5902 ->
             let uu____5903 = force_shadow shadow_f in
             match uu____5903 with
             | FStar_Pervasives_Native.None ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____5908 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding in
                   if uu____5908
                   then
                     let uu____5932 =
                       FStar_Syntax_Print.term_to_string repr_f in
                     let uu____5934 = FStar_Util.stack_dump () in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____5932 uu____5934
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f) in
                   (let uu____5941 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu____5941
                    then
                      let uu____5965 =
                        FStar_Syntax_Print.term_to_string repr_f in
                      let uu____5967 = FStar_Syntax_Print.term_to_string res in
                      let uu____5969 = FStar_Util.stack_dump () in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____5965 uu____5967 uu____5969
                    else ());
                   res))) in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1 ->
             let f_wrapped a =
               (let uu____6028 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding in
                if uu____6028
                then
                  let uu____6052 = FStar_Syntax_Print.term_to_string f1 in
                  let uu____6054 = FStar_Util.stack_dump () in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____6052
                    uu____6054
                else ());
               (let a_tm =
                  let uu____6060 = embed ea a in
                  uu____6060 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1 in
                let b_tm =
                  let uu____6070 =
                    let uu____6075 =
                      let uu____6076 =
                        let uu____6081 =
                          let uu____6082 = FStar_Syntax_Syntax.as_arg a_tm in
                          [uu____6082] in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____6081 in
                      uu____6076 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos in
                    FStar_Util.Inr uu____6075 in
                  norm1 uu____6070 in
                let uu____6107 =
                  let uu____6110 = unembed eb b_tm in uu____6110 w norm1 in
                match uu____6107 with
                | FStar_Pervasives_Native.None ->
                    FStar_Exn.raise Unembedding_failure
                | FStar_Pervasives_Native.Some b -> b) in
             FStar_Pervasives_Native.Some f_wrapped) in
      mk_emb_full em un t_arrow printer emb_t_arr_a_b
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
          fun fv_lid1 ->
            fun norm1 ->
              let rng = FStar_Ident.range_of_lid fv_lid1 in
              let f_wrapped args =
                let uu____6204 = FStar_List.splitAt n_tvars args in
                match uu____6204 with
                | (_tvar_args, rest_args) ->
                    let uu____6281 = FStar_List.hd rest_args in
                    (match uu____6281 with
                     | (x, uu____6301) ->
                         let shadow_app =
                           let uu____6315 =
                             FStar_Common.mk_thunk
                               (fun uu____6322 ->
                                  let uu____6323 =
                                    let uu____6328 =
                                      norm1 (FStar_Util.Inl fv_lid1) in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6328
                                      args in
                                  uu____6323 FStar_Pervasives_Native.None rng) in
                           FStar_Pervasives_Native.Some uu____6315 in
                         let uu____6331 =
                           let uu____6334 =
                             let uu____6337 = unembed ea x in
                             uu____6337 true norm1 in
                           FStar_Util.map_opt uu____6334
                             (fun x1 ->
                                let uu____6348 =
                                  let uu____6355 = f x1 in
                                  embed eb uu____6355 in
                                uu____6348 rng shadow_app norm1) in
                         (match uu____6331 with
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
            fun fv_lid1 ->
              fun norm1 ->
                let rng = FStar_Ident.range_of_lid fv_lid1 in
                let f_wrapped args =
                  let uu____6458 = FStar_List.splitAt n_tvars args in
                  match uu____6458 with
                  | (_tvar_args, rest_args) ->
                      let uu____6521 = FStar_List.hd rest_args in
                      (match uu____6521 with
                       | (x, uu____6537) ->
                           let uu____6542 =
                             let uu____6549 = FStar_List.tl rest_args in
                             FStar_List.hd uu____6549 in
                           (match uu____6542 with
                            | (y, uu____6573) ->
                                let shadow_app =
                                  let uu____6583 =
                                    FStar_Common.mk_thunk
                                      (fun uu____6590 ->
                                         let uu____6591 =
                                           let uu____6596 =
                                             norm1 (FStar_Util.Inl fv_lid1) in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6596 args in
                                         uu____6591
                                           FStar_Pervasives_Native.None rng) in
                                  FStar_Pervasives_Native.Some uu____6583 in
                                let uu____6599 =
                                  let uu____6602 =
                                    let uu____6605 = unembed ea x in
                                    uu____6605 true norm1 in
                                  FStar_Util.bind_opt uu____6602
                                    (fun x1 ->
                                       let uu____6616 =
                                         let uu____6619 = unembed eb y in
                                         uu____6619 true norm1 in
                                       FStar_Util.bind_opt uu____6616
                                         (fun y1 ->
                                            let uu____6630 =
                                              let uu____6631 =
                                                let uu____6638 = f x1 y1 in
                                                embed ec uu____6638 in
                                              uu____6631 rng shadow_app norm1 in
                                            FStar_Pervasives_Native.Some
                                              uu____6630)) in
                                (match uu____6599 with
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
              fun fv_lid1 ->
                fun norm1 ->
                  let rng = FStar_Ident.range_of_lid fv_lid1 in
                  let f_wrapped args =
                    let uu____6760 = FStar_List.splitAt n_tvars args in
                    match uu____6760 with
                    | (_tvar_args, rest_args) ->
                        let uu____6823 = FStar_List.hd rest_args in
                        (match uu____6823 with
                         | (x, uu____6839) ->
                             let uu____6844 =
                               let uu____6851 = FStar_List.tl rest_args in
                               FStar_List.hd uu____6851 in
                             (match uu____6844 with
                              | (y, uu____6875) ->
                                  let uu____6880 =
                                    let uu____6887 =
                                      let uu____6896 =
                                        FStar_List.tl rest_args in
                                      FStar_List.tl uu____6896 in
                                    FStar_List.hd uu____6887 in
                                  (match uu____6880 with
                                   | (z, uu____6926) ->
                                       let shadow_app =
                                         let uu____6936 =
                                           FStar_Common.mk_thunk
                                             (fun uu____6943 ->
                                                let uu____6944 =
                                                  let uu____6949 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1) in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____6949 args in
                                                uu____6944
                                                  FStar_Pervasives_Native.None
                                                  rng) in
                                         FStar_Pervasives_Native.Some
                                           uu____6936 in
                                       let uu____6952 =
                                         let uu____6955 =
                                           let uu____6958 = unembed ea x in
                                           uu____6958 true norm1 in
                                         FStar_Util.bind_opt uu____6955
                                           (fun x1 ->
                                              let uu____6969 =
                                                let uu____6972 = unembed eb y in
                                                uu____6972 true norm1 in
                                              FStar_Util.bind_opt uu____6969
                                                (fun y1 ->
                                                   let uu____6983 =
                                                     let uu____6986 =
                                                       unembed ec z in
                                                     uu____6986 true norm1 in
                                                   FStar_Util.bind_opt
                                                     uu____6983
                                                     (fun z1 ->
                                                        let uu____6997 =
                                                          let uu____6998 =
                                                            let uu____7005 =
                                                              f x1 y1 z1 in
                                                            embed ed
                                                              uu____7005 in
                                                          uu____6998 rng
                                                            shadow_app norm1 in
                                                        FStar_Pervasives_Native.Some
                                                          uu____6997))) in
                                       (match uu____6952 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None ->
                                            force_shadow shadow_app)))) in
                  f_wrapped
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s ->
    fun f ->
      (let uu____7035 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu____7035 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f () in
       (let uu____7064 = FStar_ST.op_Bang FStar_Options.debug_embedding in
        if uu____7064 then FStar_Util.print1 "------ending %s\n" s else ());
       res)