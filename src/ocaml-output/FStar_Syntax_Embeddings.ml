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
  'uuuuuu457 . FStar_Syntax_Syntax.term -> 'uuuuuu457 -> Prims.string =
  fun typ ->
    fun uu____468 ->
      let uu____469 = FStar_Syntax_Print.term_to_string typ in
      FStar_Util.format1 "unknown %s" uu____469
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t ->
    let uu____478 =
      let uu____479 = FStar_Syntax_Subst.compress t in
      uu____479.FStar_Syntax_Syntax.n in
    match uu____478 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____483 ->
        let uu____484 =
          let uu____486 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____486 in
        failwith uu____484
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em ->
    fun un ->
      fun fv ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv in
        let uu____529 =
          let uu____530 =
            let uu____538 =
              let uu____540 = FStar_Syntax_Syntax.lid_of_fv fv in
              FStar_All.pipe_right uu____540 FStar_Ident.string_of_lid in
            (uu____538, []) in
          FStar_Syntax_Syntax.ET_app uu____530 in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____529 }
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
  fun e -> fun t -> fun n -> let uu____689 = unembed e t in uu____689 true n
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e -> fun t -> fun n -> let uu____730 = unembed e t in uu____730 false n
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e -> e.typ
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty ->
    fun e ->
      let uu___77_777 = e in
      {
        em = (uu___77_777.em);
        un = (uu___77_777.un);
        typ = ty;
        print = (uu___77_777.print);
        emb_typ = (uu___77_777.emb_typ)
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
          let uu____835 =
            match o with
            | FStar_Pervasives_Native.Some t -> t
            | uu____837 -> type_of ea in
          mk_emb_full (fun x -> let uu____843 = ba x in embed ea uu____843)
            (fun t ->
               fun w ->
                 fun cb ->
                   let uu____853 =
                     let uu____856 = unembed ea t in uu____856 w cb in
                   FStar_Util.map_opt uu____853 ab) uu____835
            (fun x ->
               let uu____866 = let uu____868 = ba x in ea.print uu____868 in
               FStar_Util.format1 "(embed_as>> %s)\n" uu____866) ea.emb_typ
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
              (let uu____930 = FStar_ST.op_Bang FStar_Options.debug_embedding in
               if uu____930
               then
                 let uu____954 = FStar_Syntax_Print.term_to_string ta in
                 let uu____956 = FStar_Syntax_Print.emb_typ_to_string et in
                 let uu____958 = pa x in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu____954
                   uu____956 uu____958
               else ());
              (let uu____963 = FStar_ST.op_Bang FStar_Options.eager_embedding in
               if uu____963
               then f ()
               else
                 (let thunk = FStar_Thunk.mk f in
                  let uu____998 =
                    let uu____999 =
                      let uu____1000 = FStar_Dyn.mkdyn x in
                      {
                        FStar_Syntax_Syntax.blob = uu____1000;
                        FStar_Syntax_Syntax.lkind =
                          (FStar_Syntax_Syntax.Lazy_embedding (et, thunk));
                        FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                        FStar_Syntax_Syntax.rng = rng
                      } in
                    FStar_Syntax_Syntax.Tm_lazy uu____999 in
                  FStar_Syntax_Syntax.mk uu____998 rng))
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
                  FStar_Syntax_Syntax.ltyp = uu____1067;
                  FStar_Syntax_Syntax.rng = uu____1068;_}
                ->
                let uu____1079 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding) in
                if uu____1079
                then
                  let res =
                    let uu____1108 = FStar_Thunk.force t in f uu____1108 in
                  ((let uu____1112 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu____1112
                    then
                      let uu____1136 =
                        FStar_Syntax_Print.emb_typ_to_string et in
                      let uu____1138 =
                        FStar_Syntax_Print.emb_typ_to_string et' in
                      let uu____1140 =
                        match res with
                        | FStar_Pervasives_Native.None -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____1145 = pa x2 in
                            Prims.op_Hat "Some " uu____1145 in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____1136 uu____1138 uu____1140
                    else ());
                   res)
                else
                  (let a1 = FStar_Dyn.undyn b in
                   (let uu____1155 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu____1155
                    then
                      let uu____1179 =
                        FStar_Syntax_Print.emb_typ_to_string et in
                      let uu____1181 = pa a1 in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____1179 uu____1181
                    else ());
                   FStar_Pervasives_Native.Some a1)
            | uu____1186 ->
                let aopt = f x1 in
                ((let uu____1191 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding in
                  if uu____1191
                  then
                    let uu____1215 = FStar_Syntax_Print.emb_typ_to_string et in
                    let uu____1217 = FStar_Syntax_Print.term_to_string x1 in
                    let uu____1219 =
                      match aopt with
                      | FStar_Pervasives_Native.None -> "None"
                      | FStar_Pervasives_Native.Some a1 ->
                          let uu____1224 = pa a1 in
                          Prims.op_Hat "Some " uu____1224 in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____1215 uu____1217 uu____1219
                  else ());
                 aopt)
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ ->
    let em t _r _topt _norm =
      (let uu____1262 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu____1262
       then
         let uu____1286 = unknown_printer typ t in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____1286
       else ());
      t in
    let un t _w _n =
      (let uu____1314 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu____1314
       then
         let uu____1338 = unknown_printer typ t in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____1338
       else ());
      FStar_Pervasives_Native.Some t in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t in
  let un t _w _n = FStar_Pervasives_Native.Some t in
  let uu____1391 =
    let uu____1392 =
      let uu____1400 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid in
      (uu____1400, []) in
    FStar_Syntax_Syntax.ET_app uu____1392 in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____1391
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___167_1432 = FStar_Syntax_Util.exp_unit in
    {
      FStar_Syntax_Syntax.n = (uu___167_1432.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___167_1432.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit) ->
        FStar_Pervasives_Native.Some ()
    | uu____1460 ->
        (if w
         then
           (let uu____1463 =
              let uu____1469 =
                let uu____1471 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded unit: %s" uu____1471 in
              (FStar_Errors.Warning_NotEmbedded, uu____1469) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1463)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____1477 =
    let uu____1478 =
      let uu____1486 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid in
      (uu____1486, []) in
    FStar_Syntax_Syntax.ET_app uu____1478 in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____1493 -> "()")
    uu____1477
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool in
    let uu___187_1532 = t in
    {
      FStar_Syntax_Syntax.n = (uu___187_1532.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___187_1532.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____1568 ->
        (if w
         then
           (let uu____1571 =
              let uu____1577 =
                let uu____1579 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded bool: %s" uu____1579 in
              (FStar_Errors.Warning_NotEmbedded, uu____1577) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1571)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____1586 =
    let uu____1587 =
      let uu____1595 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid in
      (uu____1595, []) in
    FStar_Syntax_Syntax.ET_app uu____1587 in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____1586
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c in
    let uu___206_1632 = t in
    {
      FStar_Syntax_Syntax.n = (uu___206_1632.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___206_1632.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____1666 ->
        (if w
         then
           (let uu____1669 =
              let uu____1675 =
                let uu____1677 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded char: %s" uu____1677 in
              (FStar_Errors.Warning_NotEmbedded, uu____1675) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1669)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____1684 =
    let uu____1685 =
      let uu____1693 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid in
      (uu____1693, []) in
    FStar_Syntax_Syntax.ET_app uu____1685 in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____1684
let (e_int : FStar_BigInt.t embedding) =
  let t_int = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid in
  let emb_t_int =
    let uu____1705 =
      let uu____1713 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid in
      (uu____1713, []) in
    FStar_Syntax_Syntax.ET_app uu____1705 in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int i
      (fun uu____1744 ->
         let uu____1745 = FStar_BigInt.string_of_big_int i in
         FStar_Syntax_Util.exp_int uu____1745) in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int
      (fun t1 ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s, uu____1780)) ->
             let uu____1795 = FStar_BigInt.big_int_of_string s in
             FStar_Pervasives_Native.Some uu____1795
         | uu____1796 ->
             (if w
              then
                (let uu____1799 =
                   let uu____1805 =
                     let uu____1807 = FStar_Syntax_Print.term_to_string t0 in
                     FStar_Util.format1 "Not an embedded int: %s" uu____1807 in
                   (FStar_Errors.Warning_NotEmbedded, uu____1805) in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1799)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____1818 =
      let uu____1826 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid in
      (uu____1826, []) in
    FStar_Syntax_Syntax.ET_app uu____1818 in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      rng in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s, uu____1889)) -> FStar_Pervasives_Native.Some s
    | uu____1893 ->
        (if w
         then
           (let uu____1896 =
              let uu____1902 =
                let uu____1904 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded string: %s" uu____1904 in
              (FStar_Errors.Warning_NotEmbedded, uu____1902) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1896)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb_full em un FStar_Syntax_Syntax.t_string
    (fun x -> Prims.op_Hat "\"" (Prims.op_Hat x "\"")) emb_t_string
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea ->
    let t_option_a =
      let t_opt = FStar_Syntax_Util.fvar_const FStar_Parser_Const.option_lid in
      let uu____1938 =
        let uu____1939 = FStar_Syntax_Syntax.as_arg ea.typ in [uu____1939] in
      FStar_Syntax_Syntax.mk_Tm_app t_opt uu____1938 FStar_Range.dummyRange in
    let emb_t_option_a =
      let uu____1965 =
        let uu____1973 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid in
        (uu____1973, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu____1965 in
    let printer1 uu___1_1987 =
      match uu___1_1987 with
      | FStar_Pervasives_Native.None -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____1993 =
            let uu____1995 = ea.print x in Prims.op_Hat uu____1995 ")" in
          Prims.op_Hat "(Some " uu____1993 in
    let em o rng topt norm =
      lazy_embed printer1 emb_t_option_a rng t_option_a o
        (fun uu____2031 ->
           match o with
           | FStar_Pervasives_Native.None ->
               let uu____2032 =
                 let uu____2033 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.none_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____2033
                   [FStar_Syntax_Syntax.U_zero] in
               let uu____2034 =
                 let uu____2035 =
                   let uu____2044 = type_of ea in
                   FStar_Syntax_Syntax.iarg uu____2044 in
                 [uu____2035] in
               FStar_Syntax_Syntax.mk_Tm_app uu____2032 uu____2034 rng
           | FStar_Pervasives_Native.Some a1 ->
               let shadow_a =
                 map_shadow topt
                   (fun t ->
                      let v = FStar_Ident.mk_ident ("v", rng) in
                      let some_v =
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          FStar_Parser_Const.some_lid v in
                      let some_v_tm =
                        let uu____2075 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None in
                        FStar_Syntax_Syntax.fv_to_tm uu____2075 in
                      let uu____2076 =
                        FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                          [FStar_Syntax_Syntax.U_zero] in
                      let uu____2077 =
                        let uu____2078 =
                          let uu____2087 = type_of ea in
                          FStar_Syntax_Syntax.iarg uu____2087 in
                        let uu____2088 =
                          let uu____2099 = FStar_Syntax_Syntax.as_arg t in
                          [uu____2099] in
                        uu____2078 :: uu____2088 in
                      FStar_Syntax_Syntax.mk_Tm_app uu____2076 uu____2077 rng) in
               let uu____2132 =
                 let uu____2133 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.some_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____2133
                   [FStar_Syntax_Syntax.U_zero] in
               let uu____2134 =
                 let uu____2135 =
                   let uu____2144 = type_of ea in
                   FStar_Syntax_Syntax.iarg uu____2144 in
                 let uu____2145 =
                   let uu____2156 =
                     let uu____2165 =
                       let uu____2166 = embed ea a1 in
                       uu____2166 rng shadow_a norm in
                     FStar_Syntax_Syntax.as_arg uu____2165 in
                   [uu____2156] in
                 uu____2135 :: uu____2145 in
               FStar_Syntax_Syntax.mk_Tm_app uu____2132 uu____2134 rng) in
    let un t0 w norm =
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      lazy_unembed printer1 emb_t_option_a t t_option_a
        (fun t1 ->
           let uu____2236 = FStar_Syntax_Util.head_and_args' t1 in
           match uu____2236 with
           | (hd, args) ->
               let uu____2277 =
                 let uu____2292 =
                   let uu____2293 = FStar_Syntax_Util.un_uinst hd in
                   uu____2293.FStar_Syntax_Syntax.n in
                 (uu____2292, args) in
               (match uu____2277 with
                | (FStar_Syntax_Syntax.Tm_fvar fv, uu____2311) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   uu____2335::(a1, uu____2337)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____2388 =
                      let uu____2391 = unembed ea a1 in uu____2391 w norm in
                    FStar_Util.bind_opt uu____2388
                      (fun a2 ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a2))
                | uu____2404 ->
                    (if w
                     then
                       (let uu____2421 =
                          let uu____2427 =
                            let uu____2429 =
                              FStar_Syntax_Print.term_to_string t0 in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____2429 in
                          (FStar_Errors.Warning_NotEmbedded, uu____2427) in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____2421)
                     else ();
                     FStar_Pervasives_Native.None))) in
    let uu____2437 =
      let uu____2438 = type_of ea in
      FStar_Syntax_Syntax.t_option_of uu____2438 in
    mk_emb_full em un uu____2437 printer1 emb_t_option_a
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea ->
    fun eb ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2 in
        let uu____2478 =
          let uu____2479 = FStar_Syntax_Syntax.as_arg ea.typ in
          let uu____2488 =
            let uu____2499 = FStar_Syntax_Syntax.as_arg eb.typ in
            [uu____2499] in
          uu____2479 :: uu____2488 in
        FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____2478
          FStar_Range.dummyRange in
      let emb_t_pair_a_b =
        let uu____2533 =
          let uu____2541 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid in
          (uu____2541, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu____2533 in
      let printer1 uu____2557 =
        match uu____2557 with
        | (x, y) ->
            let uu____2565 = ea.print x in
            let uu____2567 = eb.print y in
            FStar_Util.format2 "(%s, %s)" uu____2565 uu____2567 in
      let em x rng topt norm =
        lazy_embed printer1 emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____2611 ->
             let proj i ab =
               let proj_1 =
                 let uu____2626 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.of_int (2))
                     rng in
                 let uu____2628 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun in
                 FStar_Syntax_Util.mk_field_projector_name uu____2626
                   uu____2628 i in
               let proj_1_tm =
                 let uu____2630 =
                   FStar_Syntax_Syntax.lid_as_fv proj_1
                     FStar_Syntax_Syntax.delta_equational
                     FStar_Pervasives_Native.None in
                 FStar_Syntax_Syntax.fv_to_tm uu____2630 in
               let uu____2631 =
                 FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                   [FStar_Syntax_Syntax.U_zero] in
               let uu____2632 =
                 let uu____2633 =
                   let uu____2642 = type_of ea in
                   FStar_Syntax_Syntax.iarg uu____2642 in
                 let uu____2643 =
                   let uu____2654 =
                     let uu____2663 = type_of eb in
                     FStar_Syntax_Syntax.iarg uu____2663 in
                   let uu____2664 =
                     let uu____2675 = FStar_Syntax_Syntax.as_arg ab in
                     [uu____2675] in
                   uu____2654 :: uu____2664 in
                 uu____2633 :: uu____2643 in
               FStar_Syntax_Syntax.mk_Tm_app uu____2631 uu____2632 rng in
             let shadow_a = map_shadow topt (proj Prims.int_one) in
             let shadow_b = map_shadow topt (proj (Prims.of_int (2))) in
             let uu____2720 =
               let uu____2721 =
                 FStar_Syntax_Syntax.tdataconstr
                   FStar_Parser_Const.lid_Mktuple2 in
               FStar_Syntax_Syntax.mk_Tm_uinst uu____2721
                 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
             let uu____2722 =
               let uu____2723 =
                 let uu____2732 = type_of ea in
                 FStar_Syntax_Syntax.iarg uu____2732 in
               let uu____2733 =
                 let uu____2744 =
                   let uu____2753 = type_of eb in
                   FStar_Syntax_Syntax.iarg uu____2753 in
                 let uu____2754 =
                   let uu____2765 =
                     let uu____2774 =
                       let uu____2775 =
                         embed ea (FStar_Pervasives_Native.fst x) in
                       uu____2775 rng shadow_a norm in
                     FStar_Syntax_Syntax.as_arg uu____2774 in
                   let uu____2782 =
                     let uu____2793 =
                       let uu____2802 =
                         let uu____2803 =
                           embed eb (FStar_Pervasives_Native.snd x) in
                         uu____2803 rng shadow_b norm in
                       FStar_Syntax_Syntax.as_arg uu____2802 in
                     [uu____2793] in
                   uu____2765 :: uu____2782 in
                 uu____2744 :: uu____2754 in
               uu____2723 :: uu____2733 in
             FStar_Syntax_Syntax.mk_Tm_app uu____2720 uu____2722 rng) in
      let un t0 w norm =
        let t = FStar_Syntax_Util.unmeta_safe t0 in
        lazy_unembed printer1 emb_t_pair_a_b t t_pair_a_b
          (fun t1 ->
             let uu____2901 = FStar_Syntax_Util.head_and_args' t1 in
             match uu____2901 with
             | (hd, args) ->
                 let uu____2944 =
                   let uu____2957 =
                     let uu____2958 = FStar_Syntax_Util.un_uinst hd in
                     uu____2958.FStar_Syntax_Syntax.n in
                   (uu____2957, args) in
                 (match uu____2944 with
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu____2976::uu____2977::(a1, uu____2979)::(b1,
                                                                uu____2981)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____3040 =
                        let uu____3043 = unembed ea a1 in uu____3043 w norm in
                      FStar_Util.bind_opt uu____3040
                        (fun a2 ->
                           let uu____3057 =
                             let uu____3060 = unembed eb b1 in
                             uu____3060 w norm in
                           FStar_Util.bind_opt uu____3057
                             (fun b2 -> FStar_Pervasives_Native.Some (a2, b2)))
                  | uu____3077 ->
                      (if w
                       then
                         (let uu____3092 =
                            let uu____3098 =
                              let uu____3100 =
                                FStar_Syntax_Print.term_to_string t0 in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____3100 in
                            (FStar_Errors.Warning_NotEmbedded, uu____3098) in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____3092)
                       else ();
                       FStar_Pervasives_Native.None))) in
      let uu____3110 =
        let uu____3111 = type_of ea in
        let uu____3112 = type_of eb in
        FStar_Syntax_Syntax.t_tuple2_of uu____3111 uu____3112 in
      mk_emb_full em un uu____3110 printer1 emb_t_pair_a_b
let e_either :
  'a 'b .
    'a embedding -> 'b embedding -> ('a, 'b) FStar_Util.either embedding
  =
  fun ea ->
    fun eb ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid in
        let uu____3154 =
          let uu____3155 = FStar_Syntax_Syntax.as_arg ea.typ in
          let uu____3164 =
            let uu____3175 = FStar_Syntax_Syntax.as_arg eb.typ in
            [uu____3175] in
          uu____3155 :: uu____3164 in
        FStar_Syntax_Syntax.mk_Tm_app t_either uu____3154
          FStar_Range.dummyRange in
      let emb_t_sum_a_b =
        let uu____3209 =
          let uu____3217 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid in
          (uu____3217, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu____3209 in
      let printer1 s =
        match s with
        | FStar_Util.Inl a1 ->
            let uu____3240 = ea.print a1 in
            FStar_Util.format1 "Inl %s" uu____3240
        | FStar_Util.Inr b1 ->
            let uu____3244 = eb.print b1 in
            FStar_Util.format1 "Inr %s" uu____3244 in
      let em s rng topt norm =
        lazy_embed printer1 emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a1 ->
               (fun uu____3291 ->
                  let shadow_a =
                    map_shadow topt
                      (fun t ->
                         let v = FStar_Ident.mk_ident ("v", rng) in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v in
                         let some_v_tm =
                           let uu____3305 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.fv_to_tm uu____3305 in
                         let uu____3306 =
                           FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                             [FStar_Syntax_Syntax.U_zero] in
                         let uu____3307 =
                           let uu____3308 =
                             let uu____3317 = type_of ea in
                             FStar_Syntax_Syntax.iarg uu____3317 in
                           let uu____3318 =
                             let uu____3329 =
                               let uu____3338 = type_of eb in
                               FStar_Syntax_Syntax.iarg uu____3338 in
                             let uu____3339 =
                               let uu____3350 = FStar_Syntax_Syntax.as_arg t in
                               [uu____3350] in
                             uu____3329 :: uu____3339 in
                           uu____3308 :: uu____3318 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3306 uu____3307
                           rng) in
                  let uu____3391 =
                    let uu____3392 =
                      FStar_Syntax_Syntax.tdataconstr
                        FStar_Parser_Const.inl_lid in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3392
                      [FStar_Syntax_Syntax.U_zero;
                      FStar_Syntax_Syntax.U_zero] in
                  let uu____3393 =
                    let uu____3394 =
                      let uu____3403 = type_of ea in
                      FStar_Syntax_Syntax.iarg uu____3403 in
                    let uu____3404 =
                      let uu____3415 =
                        let uu____3424 = type_of eb in
                        FStar_Syntax_Syntax.iarg uu____3424 in
                      let uu____3425 =
                        let uu____3436 =
                          let uu____3445 =
                            let uu____3446 = embed ea a1 in
                            uu____3446 rng shadow_a norm in
                          FStar_Syntax_Syntax.as_arg uu____3445 in
                        [uu____3436] in
                      uu____3415 :: uu____3425 in
                    uu____3394 :: uu____3404 in
                  FStar_Syntax_Syntax.mk_Tm_app uu____3391 uu____3393 rng)
           | FStar_Util.Inr b1 ->
               (fun uu____3486 ->
                  let shadow_b =
                    map_shadow topt
                      (fun t ->
                         let v = FStar_Ident.mk_ident ("v", rng) in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v in
                         let some_v_tm =
                           let uu____3500 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.fv_to_tm uu____3500 in
                         let uu____3501 =
                           FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                             [FStar_Syntax_Syntax.U_zero] in
                         let uu____3502 =
                           let uu____3503 =
                             let uu____3512 = type_of ea in
                             FStar_Syntax_Syntax.iarg uu____3512 in
                           let uu____3513 =
                             let uu____3524 =
                               let uu____3533 = type_of eb in
                               FStar_Syntax_Syntax.iarg uu____3533 in
                             let uu____3534 =
                               let uu____3545 = FStar_Syntax_Syntax.as_arg t in
                               [uu____3545] in
                             uu____3524 :: uu____3534 in
                           uu____3503 :: uu____3513 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3501 uu____3502
                           rng) in
                  let uu____3586 =
                    let uu____3587 =
                      FStar_Syntax_Syntax.tdataconstr
                        FStar_Parser_Const.inr_lid in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3587
                      [FStar_Syntax_Syntax.U_zero;
                      FStar_Syntax_Syntax.U_zero] in
                  let uu____3588 =
                    let uu____3589 =
                      let uu____3598 = type_of ea in
                      FStar_Syntax_Syntax.iarg uu____3598 in
                    let uu____3599 =
                      let uu____3610 =
                        let uu____3619 = type_of eb in
                        FStar_Syntax_Syntax.iarg uu____3619 in
                      let uu____3620 =
                        let uu____3631 =
                          let uu____3640 =
                            let uu____3641 = embed eb b1 in
                            uu____3641 rng shadow_b norm in
                          FStar_Syntax_Syntax.as_arg uu____3640 in
                        [uu____3631] in
                      uu____3610 :: uu____3620 in
                    uu____3589 :: uu____3599 in
                  FStar_Syntax_Syntax.mk_Tm_app uu____3586 uu____3588 rng)) in
      let un t0 w norm =
        let t = FStar_Syntax_Util.unmeta_safe t0 in
        lazy_unembed printer1 emb_t_sum_a_b t t_sum_a_b
          (fun t1 ->
             let uu____3729 = FStar_Syntax_Util.head_and_args' t1 in
             match uu____3729 with
             | (hd, args) ->
                 let uu____3772 =
                   let uu____3787 =
                     let uu____3788 = FStar_Syntax_Util.un_uinst hd in
                     uu____3788.FStar_Syntax_Syntax.n in
                   (uu____3787, args) in
                 (match uu____3772 with
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu____3808::uu____3809::(a1, uu____3811)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____3878 =
                        let uu____3881 = unembed ea a1 in uu____3881 w norm in
                      FStar_Util.bind_opt uu____3878
                        (fun a2 ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a2))
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu____3899::uu____3900::(b1, uu____3902)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____3969 =
                        let uu____3972 = unembed eb b1 in uu____3972 w norm in
                      FStar_Util.bind_opt uu____3969
                        (fun b2 ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b2))
                  | uu____3989 ->
                      (if w
                       then
                         (let uu____4006 =
                            let uu____4012 =
                              let uu____4014 =
                                FStar_Syntax_Print.term_to_string t0 in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____4014 in
                            (FStar_Errors.Warning_NotEmbedded, uu____4012) in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____4006)
                       else ();
                       FStar_Pervasives_Native.None))) in
      let uu____4024 =
        let uu____4025 = type_of ea in
        let uu____4026 = type_of eb in
        FStar_Syntax_Syntax.t_either_of uu____4025 uu____4026 in
      mk_emb_full em un uu____4024 printer1 emb_t_sum_a_b
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid in
      let uu____4052 =
        let uu____4053 = FStar_Syntax_Syntax.as_arg ea.typ in [uu____4053] in
      FStar_Syntax_Syntax.mk_Tm_app t_list uu____4052 FStar_Range.dummyRange in
    let emb_t_list_a =
      let uu____4079 =
        let uu____4087 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid in
        (uu____4087, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu____4079 in
    let printer1 l =
      let uu____4104 =
        let uu____4106 =
          let uu____4108 = FStar_List.map ea.print l in
          FStar_All.pipe_right uu____4108 (FStar_String.concat "; ") in
        Prims.op_Hat uu____4106 "]" in
      Prims.op_Hat "[" uu____4104 in
    let rec em l rng shadow_l norm =
      lazy_embed printer1 emb_t_list_a rng t_list_a l
        (fun uu____4152 ->
           let t =
             let uu____4154 = type_of ea in
             FStar_Syntax_Syntax.iarg uu____4154 in
           match l with
           | [] ->
               let uu____4155 =
                 let uu____4156 =
                   FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4156
                   [FStar_Syntax_Syntax.U_zero] in
               FStar_Syntax_Syntax.mk_Tm_app uu____4155 [t] rng
           | hd::tl ->
               let cons =
                 let uu____4178 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4178
                   [FStar_Syntax_Syntax.U_zero] in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng) in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid in
                 let proj_tm =
                   let uu____4196 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None in
                   FStar_Syntax_Syntax.fv_to_tm uu____4196 in
                 let uu____4197 =
                   FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                     [FStar_Syntax_Syntax.U_zero] in
                 let uu____4198 =
                   let uu____4199 =
                     let uu____4208 = type_of ea in
                     FStar_Syntax_Syntax.iarg uu____4208 in
                   let uu____4209 =
                     let uu____4220 = FStar_Syntax_Syntax.as_arg cons_tm in
                     [uu____4220] in
                   uu____4199 :: uu____4209 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____4197 uu____4198 rng in
               let shadow_hd = map_shadow shadow_l (proj "hd") in
               let shadow_tl = map_shadow shadow_l (proj "tl") in
               let uu____4257 =
                 let uu____4258 =
                   let uu____4269 =
                     let uu____4278 =
                       let uu____4279 = embed ea hd in
                       uu____4279 rng shadow_hd norm in
                     FStar_Syntax_Syntax.as_arg uu____4278 in
                   let uu____4286 =
                     let uu____4297 =
                       let uu____4306 = em tl rng shadow_tl norm in
                       FStar_Syntax_Syntax.as_arg uu____4306 in
                     [uu____4297] in
                   uu____4269 :: uu____4286 in
                 t :: uu____4258 in
               FStar_Syntax_Syntax.mk_Tm_app cons uu____4257 rng) in
    let rec un t0 w norm =
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      lazy_unembed printer1 emb_t_list_a t t_list_a
        (fun t1 ->
           let uu____4378 = FStar_Syntax_Util.head_and_args' t1 in
           match uu____4378 with
           | (hd, args) ->
               let uu____4419 =
                 let uu____4432 =
                   let uu____4433 = FStar_Syntax_Util.un_uinst hd in
                   uu____4433.FStar_Syntax_Syntax.n in
                 (uu____4432, args) in
               (match uu____4419 with
                | (FStar_Syntax_Syntax.Tm_fvar fv, uu____4449) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   (uu____4469, FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____4470))::(hd1,
                                                                 FStar_Pervasives_Native.None)::
                   (tl, FStar_Pervasives_Native.None)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4512 =
                      let uu____4515 = unembed ea hd1 in uu____4515 w norm in
                    FStar_Util.bind_opt uu____4512
                      (fun hd2 ->
                         let uu____4527 = un tl w norm in
                         FStar_Util.bind_opt uu____4527
                           (fun tl1 ->
                              FStar_Pervasives_Native.Some (hd2 :: tl1)))
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   (hd1, FStar_Pervasives_Native.None)::(tl,
                                                         FStar_Pervasives_Native.None)::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4575 =
                      let uu____4578 = unembed ea hd1 in uu____4578 w norm in
                    FStar_Util.bind_opt uu____4575
                      (fun hd2 ->
                         let uu____4590 = un tl w norm in
                         FStar_Util.bind_opt uu____4590
                           (fun tl1 ->
                              FStar_Pervasives_Native.Some (hd2 :: tl1)))
                | uu____4605 ->
                    (if w
                     then
                       (let uu____4620 =
                          let uu____4626 =
                            let uu____4628 =
                              FStar_Syntax_Print.term_to_string t0 in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____4628 in
                          (FStar_Errors.Warning_NotEmbedded, uu____4626) in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____4620)
                     else ();
                     FStar_Pervasives_Native.None))) in
    let uu____4636 =
      let uu____4637 = type_of ea in FStar_Syntax_Syntax.t_list_of uu____4637 in
    mk_emb_full em un uu____4636 printer1 emb_t_list_a
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
  fun projectee -> match projectee with | Simpl -> true | uu____4680 -> false
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Weak -> true | uu____4691 -> false
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | HNF -> true | uu____4702 -> false
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | Primops -> true | uu____4713 -> false
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Delta -> true | uu____4724 -> false
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Zeta -> true | uu____4735 -> false
let (uu___is_ZetaFull : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | ZetaFull -> true | uu____4746 -> false
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Iota -> true | uu____4757 -> false
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Reify -> true | uu____4768 -> false
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldOnly _0 -> true | uu____4783 -> false
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldOnly _0 -> _0
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldFully _0 -> true | uu____4814 -> false
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldFully _0 -> _0
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldAttr _0 -> true | uu____4845 -> false
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldAttr _0 -> _0
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | NBE -> true | uu____4872 -> false
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
    let uu____4891 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step" in
    FStar_Syntax_Util.fvar_const uu____4891 in
  let emb_t_norm_step =
    let uu____4894 =
      let uu____4902 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid in
      (uu____4902, []) in
    FStar_Syntax_Syntax.ET_app uu____4894 in
  let printer1 uu____4914 = "norm_step" in
  let em n rng _topt norm =
    lazy_embed printer1 emb_t_norm_step rng t_norm_step n
      (fun uu____4940 ->
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
             let uu____4945 =
               let uu____4946 =
                 let uu____4955 =
                   let uu____4956 =
                     let uu____4963 = e_list e_string in embed uu____4963 l in
                   uu____4956 rng FStar_Pervasives_Native.None norm in
                 FStar_Syntax_Syntax.as_arg uu____4955 in
               [uu____4946] in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____4945 rng
         | UnfoldFully l ->
             let uu____4995 =
               let uu____4996 =
                 let uu____5005 =
                   let uu____5006 =
                     let uu____5013 = e_list e_string in embed uu____5013 l in
                   uu____5006 rng FStar_Pervasives_Native.None norm in
                 FStar_Syntax_Syntax.as_arg uu____5005 in
               [uu____4996] in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____4995 rng
         | UnfoldAttr l ->
             let uu____5045 =
               let uu____5046 =
                 let uu____5055 =
                   let uu____5056 =
                     let uu____5063 = e_list e_string in embed uu____5063 l in
                   uu____5056 rng FStar_Pervasives_Native.None norm in
                 FStar_Syntax_Syntax.as_arg uu____5055 in
               [uu____5046] in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____5045 rng) in
  let un t0 w norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    lazy_unembed printer1 emb_t_norm_step t t_norm_step
      (fun t1 ->
         let uu____5123 = FStar_Syntax_Util.head_and_args t1 in
         match uu____5123 with
         | (hd, args) ->
             let uu____5168 =
               let uu____5183 =
                 let uu____5184 = FStar_Syntax_Util.un_uinst hd in
                 uu____5184.FStar_Syntax_Syntax.n in
               (uu____5183, args) in
             (match uu____5168 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____5391)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____5426 =
                    let uu____5432 =
                      let uu____5442 = e_list e_string in
                      unembed uu____5442 l in
                    uu____5432 w norm in
                  FStar_Util.bind_opt uu____5426
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun uu____5462 ->
                            FStar_Pervasives_Native.Some uu____5462)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____5465)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____5500 =
                    let uu____5506 =
                      let uu____5516 = e_list e_string in
                      unembed uu____5516 l in
                    uu____5506 w norm in
                  FStar_Util.bind_opt uu____5500
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun uu____5536 ->
                            FStar_Pervasives_Native.Some uu____5536)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____5539)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____5574 =
                    let uu____5580 =
                      let uu____5590 = e_list e_string in
                      unembed uu____5590 l in
                    uu____5580 w norm in
                  FStar_Util.bind_opt uu____5574
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun uu____5610 ->
                            FStar_Pervasives_Native.Some uu____5610)
                         (UnfoldAttr ss))
              | uu____5611 ->
                  (if w
                   then
                     (let uu____5628 =
                        let uu____5634 =
                          let uu____5636 =
                            FStar_Syntax_Print.term_to_string t0 in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____5636 in
                        (FStar_Errors.Warning_NotEmbedded, uu____5634) in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____5628)
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
    | uu____5696 ->
        (if w
         then
           (let uu____5699 =
              let uu____5705 =
                let uu____5707 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded range: %s" uu____5707 in
              (FStar_Errors.Warning_NotEmbedded, uu____5705) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____5699)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____5713 =
    let uu____5714 =
      let uu____5722 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid in
      (uu____5722, []) in
    FStar_Syntax_Syntax.ET_app uu____5714 in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____5713
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
        let uu____5793 =
          let uu____5794 =
            let uu____5809 =
              let uu____5818 =
                let uu____5825 = FStar_Syntax_Syntax.null_bv ea.typ in
                (uu____5825, FStar_Pervasives_Native.None) in
              [uu____5818] in
            let uu____5840 = FStar_Syntax_Syntax.mk_Total eb.typ in
            (uu____5809, uu____5840) in
          FStar_Syntax_Syntax.Tm_arrow uu____5794 in
        FStar_Syntax_Syntax.mk uu____5793 FStar_Range.dummyRange in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ)) in
      let printer1 f = "<fun>" in
      let em f rng shadow_f norm =
        lazy_embed (fun uu____5912 -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____5918 ->
             let uu____5919 = force_shadow shadow_f in
             match uu____5919 with
             | FStar_Pervasives_Native.None ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____5924 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding in
                   if uu____5924
                   then
                     let uu____5948 =
                       FStar_Syntax_Print.term_to_string repr_f in
                     let uu____5950 = FStar_Util.stack_dump () in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____5948 uu____5950
                   else ());
                  (let res = norm (FStar_Util.Inr repr_f) in
                   (let uu____5957 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu____5957
                    then
                      let uu____5981 =
                        FStar_Syntax_Print.term_to_string repr_f in
                      let uu____5983 = FStar_Syntax_Print.term_to_string res in
                      let uu____5985 = FStar_Util.stack_dump () in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____5981 uu____5983 uu____5985
                    else ());
                   res))) in
      let un f w norm =
        lazy_unembed printer1 emb_t_arr_a_b f t_arrow
          (fun f1 ->
             let f_wrapped a1 =
               (let uu____6044 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding in
                if uu____6044
                then
                  let uu____6068 = FStar_Syntax_Print.term_to_string f1 in
                  let uu____6070 = FStar_Util.stack_dump () in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____6068
                    uu____6070
                else ());
               (let a_tm =
                  let uu____6076 = embed ea a1 in
                  uu____6076 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm in
                let b_tm =
                  let uu____6086 =
                    let uu____6091 =
                      let uu____6092 =
                        let uu____6093 = FStar_Syntax_Syntax.as_arg a_tm in
                        [uu____6093] in
                      FStar_Syntax_Syntax.mk_Tm_app f1 uu____6092
                        f1.FStar_Syntax_Syntax.pos in
                    FStar_Util.Inr uu____6091 in
                  norm uu____6086 in
                let uu____6118 =
                  let uu____6121 = unembed eb b_tm in uu____6121 w norm in
                match uu____6118 with
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
                let uu____6215 = FStar_List.splitAt n_tvars args in
                match uu____6215 with
                | (_tvar_args, rest_args) ->
                    let uu____6292 = FStar_List.hd rest_args in
                    (match uu____6292 with
                     | (x, uu____6312) ->
                         let shadow_app =
                           let uu____6326 =
                             FStar_Thunk.mk
                               (fun uu____6331 ->
                                  let uu____6332 =
                                    norm (FStar_Util.Inl fv_lid) in
                                  FStar_Syntax_Syntax.mk_Tm_app uu____6332
                                    args rng) in
                           FStar_Pervasives_Native.Some uu____6326 in
                         let uu____6335 =
                           let uu____6338 =
                             let uu____6341 = unembed ea x in
                             uu____6341 true norm in
                           FStar_Util.map_opt uu____6338
                             (fun x1 ->
                                let uu____6352 =
                                  let uu____6359 = f x1 in
                                  embed eb uu____6359 in
                                uu____6352 rng shadow_app norm) in
                         (match uu____6335 with
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
                  let uu____6462 = FStar_List.splitAt n_tvars args in
                  match uu____6462 with
                  | (_tvar_args, rest_args) ->
                      let uu____6525 = FStar_List.hd rest_args in
                      (match uu____6525 with
                       | (x, uu____6541) ->
                           let uu____6546 =
                             let uu____6553 = FStar_List.tl rest_args in
                             FStar_List.hd uu____6553 in
                           (match uu____6546 with
                            | (y, uu____6577) ->
                                let shadow_app =
                                  let uu____6587 =
                                    FStar_Thunk.mk
                                      (fun uu____6592 ->
                                         let uu____6593 =
                                           norm (FStar_Util.Inl fv_lid) in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____6593 args rng) in
                                  FStar_Pervasives_Native.Some uu____6587 in
                                let uu____6596 =
                                  let uu____6599 =
                                    let uu____6602 = unembed ea x in
                                    uu____6602 true norm in
                                  FStar_Util.bind_opt uu____6599
                                    (fun x1 ->
                                       let uu____6613 =
                                         let uu____6616 = unembed eb y in
                                         uu____6616 true norm in
                                       FStar_Util.bind_opt uu____6613
                                         (fun y1 ->
                                            let uu____6627 =
                                              let uu____6628 =
                                                let uu____6635 = f x1 y1 in
                                                embed ec uu____6635 in
                                              uu____6628 rng shadow_app norm in
                                            FStar_Pervasives_Native.Some
                                              uu____6627)) in
                                (match uu____6596 with
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
                    let uu____6757 = FStar_List.splitAt n_tvars args in
                    match uu____6757 with
                    | (_tvar_args, rest_args) ->
                        let uu____6820 = FStar_List.hd rest_args in
                        (match uu____6820 with
                         | (x, uu____6836) ->
                             let uu____6841 =
                               let uu____6848 = FStar_List.tl rest_args in
                               FStar_List.hd uu____6848 in
                             (match uu____6841 with
                              | (y, uu____6872) ->
                                  let uu____6877 =
                                    let uu____6884 =
                                      let uu____6893 =
                                        FStar_List.tl rest_args in
                                      FStar_List.tl uu____6893 in
                                    FStar_List.hd uu____6884 in
                                  (match uu____6877 with
                                   | (z, uu____6923) ->
                                       let shadow_app =
                                         let uu____6933 =
                                           FStar_Thunk.mk
                                             (fun uu____6938 ->
                                                let uu____6939 =
                                                  norm
                                                    (FStar_Util.Inl fv_lid) in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____6939 args rng) in
                                         FStar_Pervasives_Native.Some
                                           uu____6933 in
                                       let uu____6942 =
                                         let uu____6945 =
                                           let uu____6948 = unembed ea x in
                                           uu____6948 true norm in
                                         FStar_Util.bind_opt uu____6945
                                           (fun x1 ->
                                              let uu____6959 =
                                                let uu____6962 = unembed eb y in
                                                uu____6962 true norm in
                                              FStar_Util.bind_opt uu____6959
                                                (fun y1 ->
                                                   let uu____6973 =
                                                     let uu____6976 =
                                                       unembed ec z in
                                                     uu____6976 true norm in
                                                   FStar_Util.bind_opt
                                                     uu____6973
                                                     (fun z1 ->
                                                        let uu____6987 =
                                                          let uu____6988 =
                                                            let uu____6995 =
                                                              f x1 y1 z1 in
                                                            embed ed
                                                              uu____6995 in
                                                          uu____6988 rng
                                                            shadow_app norm in
                                                        FStar_Pervasives_Native.Some
                                                          uu____6987))) in
                                       (match uu____6942 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None ->
                                            force_shadow shadow_app)))) in
                  f_wrapped
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s ->
    fun f ->
      (let uu____7025 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu____7025 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f () in
       (let uu____7054 = FStar_ST.op_Bang FStar_Options.debug_embedding in
        if uu____7054 then FStar_Util.print1 "------ending %s\n" s else ());
       res)