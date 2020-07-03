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
  'uuuuuu417 . FStar_Syntax_Syntax.term -> 'uuuuuu417 -> Prims.string =
  fun typ ->
    fun uu____428 ->
      let uu____429 = FStar_Syntax_Print.term_to_string typ in
      FStar_Util.format1 "unknown %s" uu____429
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t ->
    let uu____438 =
      let uu____439 = FStar_Syntax_Subst.compress t in
      uu____439.FStar_Syntax_Syntax.n in
    match uu____438 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____443 ->
        let uu____444 =
          let uu____446 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____446 in
        failwith uu____444
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em ->
    fun un ->
      fun fv ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv in
        let uu____489 =
          let uu____490 =
            let uu____498 =
              let uu____500 = FStar_Syntax_Syntax.lid_of_fv fv in
              FStar_All.pipe_right uu____500 FStar_Ident.string_of_lid in
            (uu____498, []) in
          FStar_Syntax_Syntax.ET_app uu____490 in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____489 }
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
  fun e -> fun t -> fun n -> let uu____649 = unembed e t in uu____649 true n
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e -> fun t -> fun n -> let uu____690 = unembed e t in uu____690 false n
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e -> e.typ
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty ->
    fun e ->
      let uu___77_737 = e in
      {
        em = (uu___77_737.em);
        un = (uu___77_737.un);
        typ = ty;
        print = (uu___77_737.print);
        emb_typ = (uu___77_737.emb_typ)
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
          let uu____795 =
            match o with
            | FStar_Pervasives_Native.Some t -> t
            | uu____797 -> type_of ea in
          mk_emb_full (fun x -> let uu____803 = ba x in embed ea uu____803)
            (fun t ->
               fun w ->
                 fun cb ->
                   let uu____813 =
                     let uu____816 = unembed ea t in uu____816 w cb in
                   FStar_Util.map_opt uu____813 ab) uu____795
            (fun x ->
               let uu____826 = let uu____828 = ba x in ea.print uu____828 in
               FStar_Util.format1 "(embed_as>> %s)\n" uu____826) ea.emb_typ
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
              (let uu____890 = FStar_ST.op_Bang FStar_Options.debug_embedding in
               if uu____890
               then
                 let uu____914 = FStar_Syntax_Print.term_to_string ta in
                 let uu____916 = FStar_Syntax_Print.emb_typ_to_string et in
                 let uu____918 = pa x in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu____914
                   uu____916 uu____918
               else ());
              (let uu____923 = FStar_ST.op_Bang FStar_Options.eager_embedding in
               if uu____923
               then f ()
               else
                 (let thunk = FStar_Thunk.mk f in
                  let uu____958 =
                    let uu____959 =
                      let uu____960 = FStar_Dyn.mkdyn x in
                      {
                        FStar_Syntax_Syntax.blob = uu____960;
                        FStar_Syntax_Syntax.lkind =
                          (FStar_Syntax_Syntax.Lazy_embedding (et, thunk));
                        FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                        FStar_Syntax_Syntax.rng = rng
                      } in
                    FStar_Syntax_Syntax.Tm_lazy uu____959 in
                  FStar_Syntax_Syntax.mk uu____958 rng))
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
                  FStar_Syntax_Syntax.ltyp = uu____1027;
                  FStar_Syntax_Syntax.rng = uu____1028;_}
                ->
                let uu____1039 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding) in
                if uu____1039
                then
                  let res =
                    let uu____1068 = FStar_Thunk.force t in f uu____1068 in
                  ((let uu____1072 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu____1072
                    then
                      let uu____1096 =
                        FStar_Syntax_Print.emb_typ_to_string et in
                      let uu____1098 =
                        FStar_Syntax_Print.emb_typ_to_string et' in
                      let uu____1100 =
                        match res with
                        | FStar_Pervasives_Native.None -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____1105 = pa x2 in
                            Prims.op_Hat "Some " uu____1105 in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____1096 uu____1098 uu____1100
                    else ());
                   res)
                else
                  (let a1 = FStar_Dyn.undyn b in
                   (let uu____1115 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu____1115
                    then
                      let uu____1139 =
                        FStar_Syntax_Print.emb_typ_to_string et in
                      let uu____1141 = pa a1 in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____1139 uu____1141
                    else ());
                   FStar_Pervasives_Native.Some a1)
            | uu____1146 ->
                let aopt = f x1 in
                ((let uu____1151 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding in
                  if uu____1151
                  then
                    let uu____1175 = FStar_Syntax_Print.emb_typ_to_string et in
                    let uu____1177 = FStar_Syntax_Print.term_to_string x1 in
                    let uu____1179 =
                      match aopt with
                      | FStar_Pervasives_Native.None -> "None"
                      | FStar_Pervasives_Native.Some a1 ->
                          let uu____1184 = pa a1 in
                          Prims.op_Hat "Some " uu____1184 in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____1175 uu____1177 uu____1179
                  else ());
                 aopt)
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ ->
    let em t _r _topt _norm =
      (let uu____1222 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu____1222
       then
         let uu____1246 = unknown_printer typ t in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____1246
       else ());
      t in
    let un t _w _n =
      (let uu____1274 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu____1274
       then
         let uu____1298 = unknown_printer typ t in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____1298
       else ());
      FStar_Pervasives_Native.Some t in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t in
  let un t _w _n = FStar_Pervasives_Native.Some t in
  let uu____1351 =
    let uu____1352 =
      let uu____1360 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid in
      (uu____1360, []) in
    FStar_Syntax_Syntax.ET_app uu____1352 in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____1351
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___167_1392 = FStar_Syntax_Util.exp_unit in
    {
      FStar_Syntax_Syntax.n = (uu___167_1392.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___167_1392.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit) ->
        FStar_Pervasives_Native.Some ()
    | uu____1420 ->
        (if w
         then
           (let uu____1423 =
              let uu____1429 =
                let uu____1431 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded unit: %s" uu____1431 in
              (FStar_Errors.Warning_NotEmbedded, uu____1429) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1423)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____1437 =
    let uu____1438 =
      let uu____1446 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid in
      (uu____1446, []) in
    FStar_Syntax_Syntax.ET_app uu____1438 in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____1453 -> "()")
    uu____1437
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool in
    let uu___187_1492 = t in
    {
      FStar_Syntax_Syntax.n = (uu___187_1492.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___187_1492.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____1528 ->
        (if w
         then
           (let uu____1531 =
              let uu____1537 =
                let uu____1539 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded bool: %s" uu____1539 in
              (FStar_Errors.Warning_NotEmbedded, uu____1537) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1531)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____1546 =
    let uu____1547 =
      let uu____1555 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid in
      (uu____1555, []) in
    FStar_Syntax_Syntax.ET_app uu____1547 in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____1546
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c in
    let uu___206_1592 = t in
    {
      FStar_Syntax_Syntax.n = (uu___206_1592.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___206_1592.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____1626 ->
        (if w
         then
           (let uu____1629 =
              let uu____1635 =
                let uu____1637 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded char: %s" uu____1637 in
              (FStar_Errors.Warning_NotEmbedded, uu____1635) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1629)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____1644 =
    let uu____1645 =
      let uu____1653 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid in
      (uu____1653, []) in
    FStar_Syntax_Syntax.ET_app uu____1645 in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____1644
let (e_int : FStar_BigInt.t embedding) =
  let t_int = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid in
  let emb_t_int =
    let uu____1665 =
      let uu____1673 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid in
      (uu____1673, []) in
    FStar_Syntax_Syntax.ET_app uu____1665 in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int i
      (fun uu____1704 ->
         let uu____1705 = FStar_BigInt.string_of_big_int i in
         FStar_Syntax_Util.exp_int uu____1705) in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int
      (fun t1 ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s, uu____1740)) ->
             let uu____1755 = FStar_BigInt.big_int_of_string s in
             FStar_Pervasives_Native.Some uu____1755
         | uu____1756 ->
             (if w
              then
                (let uu____1759 =
                   let uu____1765 =
                     let uu____1767 = FStar_Syntax_Print.term_to_string t0 in
                     FStar_Util.format1 "Not an embedded int: %s" uu____1767 in
                   (FStar_Errors.Warning_NotEmbedded, uu____1765) in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1759)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____1778 =
      let uu____1786 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid in
      (uu____1786, []) in
    FStar_Syntax_Syntax.ET_app uu____1778 in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      rng in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s, uu____1849)) -> FStar_Pervasives_Native.Some s
    | uu____1853 ->
        (if w
         then
           (let uu____1856 =
              let uu____1862 =
                let uu____1864 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded string: %s" uu____1864 in
              (FStar_Errors.Warning_NotEmbedded, uu____1862) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1856)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb_full em un FStar_Syntax_Syntax.t_string
    (fun x -> Prims.op_Hat "\"" (Prims.op_Hat x "\"")) emb_t_string
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea ->
    let t_option_a =
      let t_opt = FStar_Syntax_Util.fvar_const FStar_Parser_Const.option_lid in
      let uu____1898 =
        let uu____1899 = FStar_Syntax_Syntax.as_arg ea.typ in [uu____1899] in
      FStar_Syntax_Syntax.mk_Tm_app t_opt uu____1898 FStar_Range.dummyRange in
    let emb_t_option_a =
      let uu____1925 =
        let uu____1933 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid in
        (uu____1933, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu____1925 in
    let printer1 uu___1_1947 =
      match uu___1_1947 with
      | FStar_Pervasives_Native.None -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____1953 =
            let uu____1955 = ea.print x in Prims.op_Hat uu____1955 ")" in
          Prims.op_Hat "(Some " uu____1953 in
    let em o rng topt norm =
      lazy_embed printer1 emb_t_option_a rng t_option_a o
        (fun uu____1991 ->
           match o with
           | FStar_Pervasives_Native.None ->
               let uu____1992 =
                 let uu____1993 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.none_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____1993
                   [FStar_Syntax_Syntax.U_zero] in
               let uu____1994 =
                 let uu____1995 =
                   let uu____2004 = type_of ea in
                   FStar_Syntax_Syntax.iarg uu____2004 in
                 [uu____1995] in
               FStar_Syntax_Syntax.mk_Tm_app uu____1992 uu____1994 rng
           | FStar_Pervasives_Native.Some a1 ->
               let shadow_a =
                 map_shadow topt
                   (fun t ->
                      let v = FStar_Ident.mk_ident ("v", rng) in
                      let some_v =
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          FStar_Parser_Const.some_lid v in
                      let some_v_tm =
                        let uu____2035 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None in
                        FStar_Syntax_Syntax.fv_to_tm uu____2035 in
                      let uu____2036 =
                        FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                          [FStar_Syntax_Syntax.U_zero] in
                      let uu____2037 =
                        let uu____2038 =
                          let uu____2047 = type_of ea in
                          FStar_Syntax_Syntax.iarg uu____2047 in
                        let uu____2048 =
                          let uu____2059 = FStar_Syntax_Syntax.as_arg t in
                          [uu____2059] in
                        uu____2038 :: uu____2048 in
                      FStar_Syntax_Syntax.mk_Tm_app uu____2036 uu____2037 rng) in
               let uu____2092 =
                 let uu____2093 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.some_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____2093
                   [FStar_Syntax_Syntax.U_zero] in
               let uu____2094 =
                 let uu____2095 =
                   let uu____2104 = type_of ea in
                   FStar_Syntax_Syntax.iarg uu____2104 in
                 let uu____2105 =
                   let uu____2116 =
                     let uu____2125 =
                       let uu____2126 = embed ea a1 in
                       uu____2126 rng shadow_a norm in
                     FStar_Syntax_Syntax.as_arg uu____2125 in
                   [uu____2116] in
                 uu____2095 :: uu____2105 in
               FStar_Syntax_Syntax.mk_Tm_app uu____2092 uu____2094 rng) in
    let un t0 w norm =
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      lazy_unembed printer1 emb_t_option_a t t_option_a
        (fun t1 ->
           let uu____2196 = FStar_Syntax_Util.head_and_args' t1 in
           match uu____2196 with
           | (hd, args) ->
               let uu____2237 =
                 let uu____2252 =
                   let uu____2253 = FStar_Syntax_Util.un_uinst hd in
                   uu____2253.FStar_Syntax_Syntax.n in
                 (uu____2252, args) in
               (match uu____2237 with
                | (FStar_Syntax_Syntax.Tm_fvar fv, uu____2271) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   uu____2295::(a1, uu____2297)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____2348 =
                      let uu____2351 = unembed ea a1 in uu____2351 w norm in
                    FStar_Util.bind_opt uu____2348
                      (fun a2 ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a2))
                | uu____2364 ->
                    (if w
                     then
                       (let uu____2381 =
                          let uu____2387 =
                            let uu____2389 =
                              FStar_Syntax_Print.term_to_string t0 in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____2389 in
                          (FStar_Errors.Warning_NotEmbedded, uu____2387) in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____2381)
                     else ();
                     FStar_Pervasives_Native.None))) in
    let uu____2397 =
      let uu____2398 = type_of ea in
      FStar_Syntax_Syntax.t_option_of uu____2398 in
    mk_emb_full em un uu____2397 printer1 emb_t_option_a
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea ->
    fun eb ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2 in
        let uu____2438 =
          let uu____2439 = FStar_Syntax_Syntax.as_arg ea.typ in
          let uu____2448 =
            let uu____2459 = FStar_Syntax_Syntax.as_arg eb.typ in
            [uu____2459] in
          uu____2439 :: uu____2448 in
        FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____2438
          FStar_Range.dummyRange in
      let emb_t_pair_a_b =
        let uu____2493 =
          let uu____2501 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid in
          (uu____2501, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu____2493 in
      let printer1 uu____2517 =
        match uu____2517 with
        | (x, y) ->
            let uu____2525 = ea.print x in
            let uu____2527 = eb.print y in
            FStar_Util.format2 "(%s, %s)" uu____2525 uu____2527 in
      let em x rng topt norm =
        lazy_embed printer1 emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____2571 ->
             let proj i ab =
               let proj_1 =
                 let uu____2586 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.of_int (2))
                     rng in
                 let uu____2588 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun in
                 FStar_Syntax_Util.mk_field_projector_name uu____2586
                   uu____2588 i in
               let proj_1_tm =
                 let uu____2590 =
                   FStar_Syntax_Syntax.lid_as_fv proj_1
                     FStar_Syntax_Syntax.delta_equational
                     FStar_Pervasives_Native.None in
                 FStar_Syntax_Syntax.fv_to_tm uu____2590 in
               let uu____2591 =
                 FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                   [FStar_Syntax_Syntax.U_zero] in
               let uu____2592 =
                 let uu____2593 =
                   let uu____2602 = type_of ea in
                   FStar_Syntax_Syntax.iarg uu____2602 in
                 let uu____2603 =
                   let uu____2614 =
                     let uu____2623 = type_of eb in
                     FStar_Syntax_Syntax.iarg uu____2623 in
                   let uu____2624 =
                     let uu____2635 = FStar_Syntax_Syntax.as_arg ab in
                     [uu____2635] in
                   uu____2614 :: uu____2624 in
                 uu____2593 :: uu____2603 in
               FStar_Syntax_Syntax.mk_Tm_app uu____2591 uu____2592 rng in
             let shadow_a = map_shadow topt (proj Prims.int_one) in
             let shadow_b = map_shadow topt (proj (Prims.of_int (2))) in
             let uu____2680 =
               let uu____2681 =
                 FStar_Syntax_Syntax.tdataconstr
                   FStar_Parser_Const.lid_Mktuple2 in
               FStar_Syntax_Syntax.mk_Tm_uinst uu____2681
                 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
             let uu____2682 =
               let uu____2683 =
                 let uu____2692 = type_of ea in
                 FStar_Syntax_Syntax.iarg uu____2692 in
               let uu____2693 =
                 let uu____2704 =
                   let uu____2713 = type_of eb in
                   FStar_Syntax_Syntax.iarg uu____2713 in
                 let uu____2714 =
                   let uu____2725 =
                     let uu____2734 =
                       let uu____2735 =
                         embed ea (FStar_Pervasives_Native.fst x) in
                       uu____2735 rng shadow_a norm in
                     FStar_Syntax_Syntax.as_arg uu____2734 in
                   let uu____2742 =
                     let uu____2753 =
                       let uu____2762 =
                         let uu____2763 =
                           embed eb (FStar_Pervasives_Native.snd x) in
                         uu____2763 rng shadow_b norm in
                       FStar_Syntax_Syntax.as_arg uu____2762 in
                     [uu____2753] in
                   uu____2725 :: uu____2742 in
                 uu____2704 :: uu____2714 in
               uu____2683 :: uu____2693 in
             FStar_Syntax_Syntax.mk_Tm_app uu____2680 uu____2682 rng) in
      let un t0 w norm =
        let t = FStar_Syntax_Util.unmeta_safe t0 in
        lazy_unembed printer1 emb_t_pair_a_b t t_pair_a_b
          (fun t1 ->
             let uu____2861 = FStar_Syntax_Util.head_and_args' t1 in
             match uu____2861 with
             | (hd, args) ->
                 let uu____2904 =
                   let uu____2917 =
                     let uu____2918 = FStar_Syntax_Util.un_uinst hd in
                     uu____2918.FStar_Syntax_Syntax.n in
                   (uu____2917, args) in
                 (match uu____2904 with
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu____2936::uu____2937::(a1, uu____2939)::(b1,
                                                                uu____2941)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____3000 =
                        let uu____3003 = unembed ea a1 in uu____3003 w norm in
                      FStar_Util.bind_opt uu____3000
                        (fun a2 ->
                           let uu____3017 =
                             let uu____3020 = unembed eb b1 in
                             uu____3020 w norm in
                           FStar_Util.bind_opt uu____3017
                             (fun b2 -> FStar_Pervasives_Native.Some (a2, b2)))
                  | uu____3037 ->
                      (if w
                       then
                         (let uu____3052 =
                            let uu____3058 =
                              let uu____3060 =
                                FStar_Syntax_Print.term_to_string t0 in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____3060 in
                            (FStar_Errors.Warning_NotEmbedded, uu____3058) in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____3052)
                       else ();
                       FStar_Pervasives_Native.None))) in
      let uu____3070 =
        let uu____3071 = type_of ea in
        let uu____3072 = type_of eb in
        FStar_Syntax_Syntax.t_tuple2_of uu____3071 uu____3072 in
      mk_emb_full em un uu____3070 printer1 emb_t_pair_a_b
let e_either :
  'a 'b .
    'a embedding -> 'b embedding -> ('a, 'b) FStar_Util.either embedding
  =
  fun ea ->
    fun eb ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid in
        let uu____3114 =
          let uu____3115 = FStar_Syntax_Syntax.as_arg ea.typ in
          let uu____3124 =
            let uu____3135 = FStar_Syntax_Syntax.as_arg eb.typ in
            [uu____3135] in
          uu____3115 :: uu____3124 in
        FStar_Syntax_Syntax.mk_Tm_app t_either uu____3114
          FStar_Range.dummyRange in
      let emb_t_sum_a_b =
        let uu____3169 =
          let uu____3177 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid in
          (uu____3177, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu____3169 in
      let printer1 s =
        match s with
        | FStar_Util.Inl a1 ->
            let uu____3200 = ea.print a1 in
            FStar_Util.format1 "Inl %s" uu____3200
        | FStar_Util.Inr b1 ->
            let uu____3204 = eb.print b1 in
            FStar_Util.format1 "Inr %s" uu____3204 in
      let em s rng topt norm =
        lazy_embed printer1 emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a1 ->
               (fun uu____3251 ->
                  let shadow_a =
                    map_shadow topt
                      (fun t ->
                         let v = FStar_Ident.mk_ident ("v", rng) in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v in
                         let some_v_tm =
                           let uu____3265 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.fv_to_tm uu____3265 in
                         let uu____3266 =
                           FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                             [FStar_Syntax_Syntax.U_zero] in
                         let uu____3267 =
                           let uu____3268 =
                             let uu____3277 = type_of ea in
                             FStar_Syntax_Syntax.iarg uu____3277 in
                           let uu____3278 =
                             let uu____3289 =
                               let uu____3298 = type_of eb in
                               FStar_Syntax_Syntax.iarg uu____3298 in
                             let uu____3299 =
                               let uu____3310 = FStar_Syntax_Syntax.as_arg t in
                               [uu____3310] in
                             uu____3289 :: uu____3299 in
                           uu____3268 :: uu____3278 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3266 uu____3267
                           rng) in
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
                            let uu____3406 = embed ea a1 in
                            uu____3406 rng shadow_a norm in
                          FStar_Syntax_Syntax.as_arg uu____3405 in
                        [uu____3396] in
                      uu____3375 :: uu____3385 in
                    uu____3354 :: uu____3364 in
                  FStar_Syntax_Syntax.mk_Tm_app uu____3351 uu____3353 rng)
           | FStar_Util.Inr b1 ->
               (fun uu____3446 ->
                  let shadow_b =
                    map_shadow topt
                      (fun t ->
                         let v = FStar_Ident.mk_ident ("v", rng) in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v in
                         let some_v_tm =
                           let uu____3460 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.fv_to_tm uu____3460 in
                         let uu____3461 =
                           FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                             [FStar_Syntax_Syntax.U_zero] in
                         let uu____3462 =
                           let uu____3463 =
                             let uu____3472 = type_of ea in
                             FStar_Syntax_Syntax.iarg uu____3472 in
                           let uu____3473 =
                             let uu____3484 =
                               let uu____3493 = type_of eb in
                               FStar_Syntax_Syntax.iarg uu____3493 in
                             let uu____3494 =
                               let uu____3505 = FStar_Syntax_Syntax.as_arg t in
                               [uu____3505] in
                             uu____3484 :: uu____3494 in
                           uu____3463 :: uu____3473 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3461 uu____3462
                           rng) in
                  let uu____3546 =
                    let uu____3547 =
                      FStar_Syntax_Syntax.tdataconstr
                        FStar_Parser_Const.inr_lid in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3547
                      [FStar_Syntax_Syntax.U_zero;
                      FStar_Syntax_Syntax.U_zero] in
                  let uu____3548 =
                    let uu____3549 =
                      let uu____3558 = type_of ea in
                      FStar_Syntax_Syntax.iarg uu____3558 in
                    let uu____3559 =
                      let uu____3570 =
                        let uu____3579 = type_of eb in
                        FStar_Syntax_Syntax.iarg uu____3579 in
                      let uu____3580 =
                        let uu____3591 =
                          let uu____3600 =
                            let uu____3601 = embed eb b1 in
                            uu____3601 rng shadow_b norm in
                          FStar_Syntax_Syntax.as_arg uu____3600 in
                        [uu____3591] in
                      uu____3570 :: uu____3580 in
                    uu____3549 :: uu____3559 in
                  FStar_Syntax_Syntax.mk_Tm_app uu____3546 uu____3548 rng)) in
      let un t0 w norm =
        let t = FStar_Syntax_Util.unmeta_safe t0 in
        lazy_unembed printer1 emb_t_sum_a_b t t_sum_a_b
          (fun t1 ->
             let uu____3689 = FStar_Syntax_Util.head_and_args' t1 in
             match uu____3689 with
             | (hd, args) ->
                 let uu____3732 =
                   let uu____3747 =
                     let uu____3748 = FStar_Syntax_Util.un_uinst hd in
                     uu____3748.FStar_Syntax_Syntax.n in
                   (uu____3747, args) in
                 (match uu____3732 with
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu____3768::uu____3769::(a1, uu____3771)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____3838 =
                        let uu____3841 = unembed ea a1 in uu____3841 w norm in
                      FStar_Util.bind_opt uu____3838
                        (fun a2 ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a2))
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu____3859::uu____3860::(b1, uu____3862)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____3929 =
                        let uu____3932 = unembed eb b1 in uu____3932 w norm in
                      FStar_Util.bind_opt uu____3929
                        (fun b2 ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b2))
                  | uu____3949 ->
                      (if w
                       then
                         (let uu____3966 =
                            let uu____3972 =
                              let uu____3974 =
                                FStar_Syntax_Print.term_to_string t0 in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____3974 in
                            (FStar_Errors.Warning_NotEmbedded, uu____3972) in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____3966)
                       else ();
                       FStar_Pervasives_Native.None))) in
      let uu____3984 =
        let uu____3985 = type_of ea in
        let uu____3986 = type_of eb in
        FStar_Syntax_Syntax.t_either_of uu____3985 uu____3986 in
      mk_emb_full em un uu____3984 printer1 emb_t_sum_a_b
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid in
      let uu____4012 =
        let uu____4013 = FStar_Syntax_Syntax.as_arg ea.typ in [uu____4013] in
      FStar_Syntax_Syntax.mk_Tm_app t_list uu____4012 FStar_Range.dummyRange in
    let emb_t_list_a =
      let uu____4039 =
        let uu____4047 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid in
        (uu____4047, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu____4039 in
    let printer1 l =
      let uu____4064 =
        let uu____4066 =
          let uu____4068 = FStar_List.map ea.print l in
          FStar_All.pipe_right uu____4068 (FStar_String.concat "; ") in
        Prims.op_Hat uu____4066 "]" in
      Prims.op_Hat "[" uu____4064 in
    let rec em l rng shadow_l norm =
      lazy_embed printer1 emb_t_list_a rng t_list_a l
        (fun uu____4112 ->
           let t =
             let uu____4114 = type_of ea in
             FStar_Syntax_Syntax.iarg uu____4114 in
           match l with
           | [] ->
               let uu____4115 =
                 let uu____4116 =
                   FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4116
                   [FStar_Syntax_Syntax.U_zero] in
               FStar_Syntax_Syntax.mk_Tm_app uu____4115 [t] rng
           | hd::tl ->
               let cons =
                 let uu____4138 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4138
                   [FStar_Syntax_Syntax.U_zero] in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng) in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid in
                 let proj_tm =
                   let uu____4156 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None in
                   FStar_Syntax_Syntax.fv_to_tm uu____4156 in
                 let uu____4157 =
                   FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                     [FStar_Syntax_Syntax.U_zero] in
                 let uu____4158 =
                   let uu____4159 =
                     let uu____4168 = type_of ea in
                     FStar_Syntax_Syntax.iarg uu____4168 in
                   let uu____4169 =
                     let uu____4180 = FStar_Syntax_Syntax.as_arg cons_tm in
                     [uu____4180] in
                   uu____4159 :: uu____4169 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____4157 uu____4158 rng in
               let shadow_hd = map_shadow shadow_l (proj "hd") in
               let shadow_tl = map_shadow shadow_l (proj "tl") in
               let uu____4217 =
                 let uu____4218 =
                   let uu____4229 =
                     let uu____4238 =
                       let uu____4239 = embed ea hd in
                       uu____4239 rng shadow_hd norm in
                     FStar_Syntax_Syntax.as_arg uu____4238 in
                   let uu____4246 =
                     let uu____4257 =
                       let uu____4266 = em tl rng shadow_tl norm in
                       FStar_Syntax_Syntax.as_arg uu____4266 in
                     [uu____4257] in
                   uu____4229 :: uu____4246 in
                 t :: uu____4218 in
               FStar_Syntax_Syntax.mk_Tm_app cons uu____4217 rng) in
    let rec un t0 w norm =
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      lazy_unembed printer1 emb_t_list_a t t_list_a
        (fun t1 ->
           let uu____4338 = FStar_Syntax_Util.head_and_args' t1 in
           match uu____4338 with
           | (hd, args) ->
               let uu____4379 =
                 let uu____4392 =
                   let uu____4393 = FStar_Syntax_Util.un_uinst hd in
                   uu____4393.FStar_Syntax_Syntax.n in
                 (uu____4392, args) in
               (match uu____4379 with
                | (FStar_Syntax_Syntax.Tm_fvar fv, uu____4409) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   (uu____4429, FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____4430))::(hd1,
                                                                 FStar_Pervasives_Native.None)::
                   (tl, FStar_Pervasives_Native.None)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4472 =
                      let uu____4475 = unembed ea hd1 in uu____4475 w norm in
                    FStar_Util.bind_opt uu____4472
                      (fun hd2 ->
                         let uu____4487 = un tl w norm in
                         FStar_Util.bind_opt uu____4487
                           (fun tl1 ->
                              FStar_Pervasives_Native.Some (hd2 :: tl1)))
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   (hd1, FStar_Pervasives_Native.None)::(tl,
                                                         FStar_Pervasives_Native.None)::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4535 =
                      let uu____4538 = unembed ea hd1 in uu____4538 w norm in
                    FStar_Util.bind_opt uu____4535
                      (fun hd2 ->
                         let uu____4550 = un tl w norm in
                         FStar_Util.bind_opt uu____4550
                           (fun tl1 ->
                              FStar_Pervasives_Native.Some (hd2 :: tl1)))
                | uu____4565 ->
                    (if w
                     then
                       (let uu____4580 =
                          let uu____4586 =
                            let uu____4588 =
                              FStar_Syntax_Print.term_to_string t0 in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____4588 in
                          (FStar_Errors.Warning_NotEmbedded, uu____4586) in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____4580)
                     else ();
                     FStar_Pervasives_Native.None))) in
    let uu____4596 =
      let uu____4597 = type_of ea in FStar_Syntax_Syntax.t_list_of uu____4597 in
    mk_emb_full em un uu____4596 printer1 emb_t_list_a
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
  fun projectee -> match projectee with | Simpl -> true | uu____4640 -> false
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Weak -> true | uu____4651 -> false
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | HNF -> true | uu____4662 -> false
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | Primops -> true | uu____4673 -> false
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Delta -> true | uu____4684 -> false
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Zeta -> true | uu____4695 -> false
let (uu___is_ZetaFull : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | ZetaFull -> true | uu____4706 -> false
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Iota -> true | uu____4717 -> false
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Reify -> true | uu____4728 -> false
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldOnly _0 -> true | uu____4743 -> false
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldOnly _0 -> _0
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldFully _0 -> true | uu____4774 -> false
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldFully _0 -> _0
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldAttr _0 -> true | uu____4805 -> false
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldAttr _0 -> _0
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | NBE -> true | uu____4832 -> false
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
    let uu____4851 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step" in
    FStar_Syntax_Util.fvar_const uu____4851 in
  let emb_t_norm_step =
    let uu____4854 =
      let uu____4862 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid in
      (uu____4862, []) in
    FStar_Syntax_Syntax.ET_app uu____4854 in
  let printer1 uu____4874 = "norm_step" in
  let em n rng _topt norm =
    lazy_embed printer1 emb_t_norm_step rng t_norm_step n
      (fun uu____4900 ->
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
             let uu____4905 =
               let uu____4906 =
                 let uu____4915 =
                   let uu____4916 =
                     let uu____4923 = e_list e_string in embed uu____4923 l in
                   uu____4916 rng FStar_Pervasives_Native.None norm in
                 FStar_Syntax_Syntax.as_arg uu____4915 in
               [uu____4906] in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____4905 rng
         | UnfoldFully l ->
             let uu____4955 =
               let uu____4956 =
                 let uu____4965 =
                   let uu____4966 =
                     let uu____4973 = e_list e_string in embed uu____4973 l in
                   uu____4966 rng FStar_Pervasives_Native.None norm in
                 FStar_Syntax_Syntax.as_arg uu____4965 in
               [uu____4956] in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____4955 rng
         | UnfoldAttr l ->
             let uu____5005 =
               let uu____5006 =
                 let uu____5015 =
                   let uu____5016 =
                     let uu____5023 = e_list e_string in embed uu____5023 l in
                   uu____5016 rng FStar_Pervasives_Native.None norm in
                 FStar_Syntax_Syntax.as_arg uu____5015 in
               [uu____5006] in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____5005 rng) in
  let un t0 w norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    lazy_unembed printer1 emb_t_norm_step t t_norm_step
      (fun t1 ->
         let uu____5083 = FStar_Syntax_Util.head_and_args t1 in
         match uu____5083 with
         | (hd, args) ->
             let uu____5128 =
               let uu____5143 =
                 let uu____5144 = FStar_Syntax_Util.un_uinst hd in
                 uu____5144.FStar_Syntax_Syntax.n in
               (uu____5143, args) in
             (match uu____5128 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____5351)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____5386 =
                    let uu____5392 =
                      let uu____5402 = e_list e_string in
                      unembed uu____5402 l in
                    uu____5392 w norm in
                  FStar_Util.bind_opt uu____5386
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun uu____5422 ->
                            FStar_Pervasives_Native.Some uu____5422)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____5425)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____5460 =
                    let uu____5466 =
                      let uu____5476 = e_list e_string in
                      unembed uu____5476 l in
                    uu____5466 w norm in
                  FStar_Util.bind_opt uu____5460
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun uu____5496 ->
                            FStar_Pervasives_Native.Some uu____5496)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____5499)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____5534 =
                    let uu____5540 =
                      let uu____5550 = e_list e_string in
                      unembed uu____5550 l in
                    uu____5540 w norm in
                  FStar_Util.bind_opt uu____5534
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun uu____5570 ->
                            FStar_Pervasives_Native.Some uu____5570)
                         (UnfoldAttr ss))
              | uu____5571 ->
                  (if w
                   then
                     (let uu____5588 =
                        let uu____5594 =
                          let uu____5596 =
                            FStar_Syntax_Print.term_to_string t0 in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____5596 in
                        (FStar_Errors.Warning_NotEmbedded, uu____5594) in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____5588)
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
    | uu____5656 ->
        (if w
         then
           (let uu____5659 =
              let uu____5665 =
                let uu____5667 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded range: %s" uu____5667 in
              (FStar_Errors.Warning_NotEmbedded, uu____5665) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____5659)
         else ();
         FStar_Pervasives_Native.None) in
  let uu____5673 =
    let uu____5674 =
      let uu____5682 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid in
      (uu____5682, []) in
    FStar_Syntax_Syntax.ET_app uu____5674 in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____5673
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
        let uu____5753 =
          let uu____5754 =
            let uu____5769 =
              let uu____5778 =
                let uu____5785 = FStar_Syntax_Syntax.null_bv ea.typ in
                (uu____5785, FStar_Pervasives_Native.None) in
              [uu____5778] in
            let uu____5800 = FStar_Syntax_Syntax.mk_Total eb.typ in
            (uu____5769, uu____5800) in
          FStar_Syntax_Syntax.Tm_arrow uu____5754 in
        FStar_Syntax_Syntax.mk uu____5753 FStar_Range.dummyRange in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ)) in
      let printer1 f = "<fun>" in
      let em f rng shadow_f norm =
        lazy_embed (fun uu____5872 -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____5878 ->
             let uu____5879 = force_shadow shadow_f in
             match uu____5879 with
             | FStar_Pervasives_Native.None ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____5884 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding in
                   if uu____5884
                   then
                     let uu____5908 =
                       FStar_Syntax_Print.term_to_string repr_f in
                     let uu____5910 = FStar_Util.stack_dump () in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____5908 uu____5910
                   else ());
                  (let res = norm (FStar_Util.Inr repr_f) in
                   (let uu____5917 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu____5917
                    then
                      let uu____5941 =
                        FStar_Syntax_Print.term_to_string repr_f in
                      let uu____5943 = FStar_Syntax_Print.term_to_string res in
                      let uu____5945 = FStar_Util.stack_dump () in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____5941 uu____5943 uu____5945
                    else ());
                   res))) in
      let un f w norm =
        lazy_unembed printer1 emb_t_arr_a_b f t_arrow
          (fun f1 ->
             let f_wrapped a1 =
               (let uu____6004 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding in
                if uu____6004
                then
                  let uu____6028 = FStar_Syntax_Print.term_to_string f1 in
                  let uu____6030 = FStar_Util.stack_dump () in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____6028
                    uu____6030
                else ());
               (let a_tm =
                  let uu____6036 = embed ea a1 in
                  uu____6036 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm in
                let b_tm =
                  let uu____6046 =
                    let uu____6051 =
                      let uu____6052 =
                        let uu____6053 = FStar_Syntax_Syntax.as_arg a_tm in
                        [uu____6053] in
                      FStar_Syntax_Syntax.mk_Tm_app f1 uu____6052
                        f1.FStar_Syntax_Syntax.pos in
                    FStar_Util.Inr uu____6051 in
                  norm uu____6046 in
                let uu____6078 =
                  let uu____6081 = unembed eb b_tm in uu____6081 w norm in
                match uu____6078 with
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
                let uu____6175 = FStar_List.splitAt n_tvars args in
                match uu____6175 with
                | (_tvar_args, rest_args) ->
                    let uu____6252 = FStar_List.hd rest_args in
                    (match uu____6252 with
                     | (x, uu____6272) ->
                         let shadow_app =
                           let uu____6286 =
                             FStar_Thunk.mk
                               (fun uu____6291 ->
                                  let uu____6292 =
                                    norm (FStar_Util.Inl fv_lid) in
                                  FStar_Syntax_Syntax.mk_Tm_app uu____6292
                                    args rng) in
                           FStar_Pervasives_Native.Some uu____6286 in
                         let uu____6295 =
                           let uu____6298 =
                             let uu____6301 = unembed ea x in
                             uu____6301 true norm in
                           FStar_Util.map_opt uu____6298
                             (fun x1 ->
                                let uu____6312 =
                                  let uu____6319 = f x1 in
                                  embed eb uu____6319 in
                                uu____6312 rng shadow_app norm) in
                         (match uu____6295 with
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
                  let uu____6422 = FStar_List.splitAt n_tvars args in
                  match uu____6422 with
                  | (_tvar_args, rest_args) ->
                      let uu____6485 = FStar_List.hd rest_args in
                      (match uu____6485 with
                       | (x, uu____6501) ->
                           let uu____6506 =
                             let uu____6513 = FStar_List.tl rest_args in
                             FStar_List.hd uu____6513 in
                           (match uu____6506 with
                            | (y, uu____6537) ->
                                let shadow_app =
                                  let uu____6547 =
                                    FStar_Thunk.mk
                                      (fun uu____6552 ->
                                         let uu____6553 =
                                           norm (FStar_Util.Inl fv_lid) in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____6553 args rng) in
                                  FStar_Pervasives_Native.Some uu____6547 in
                                let uu____6556 =
                                  let uu____6559 =
                                    let uu____6562 = unembed ea x in
                                    uu____6562 true norm in
                                  FStar_Util.bind_opt uu____6559
                                    (fun x1 ->
                                       let uu____6573 =
                                         let uu____6576 = unembed eb y in
                                         uu____6576 true norm in
                                       FStar_Util.bind_opt uu____6573
                                         (fun y1 ->
                                            let uu____6587 =
                                              let uu____6588 =
                                                let uu____6595 = f x1 y1 in
                                                embed ec uu____6595 in
                                              uu____6588 rng shadow_app norm in
                                            FStar_Pervasives_Native.Some
                                              uu____6587)) in
                                (match uu____6556 with
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
                    let uu____6717 = FStar_List.splitAt n_tvars args in
                    match uu____6717 with
                    | (_tvar_args, rest_args) ->
                        let uu____6780 = FStar_List.hd rest_args in
                        (match uu____6780 with
                         | (x, uu____6796) ->
                             let uu____6801 =
                               let uu____6808 = FStar_List.tl rest_args in
                               FStar_List.hd uu____6808 in
                             (match uu____6801 with
                              | (y, uu____6832) ->
                                  let uu____6837 =
                                    let uu____6844 =
                                      let uu____6853 =
                                        FStar_List.tl rest_args in
                                      FStar_List.tl uu____6853 in
                                    FStar_List.hd uu____6844 in
                                  (match uu____6837 with
                                   | (z, uu____6883) ->
                                       let shadow_app =
                                         let uu____6893 =
                                           FStar_Thunk.mk
                                             (fun uu____6898 ->
                                                let uu____6899 =
                                                  norm
                                                    (FStar_Util.Inl fv_lid) in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____6899 args rng) in
                                         FStar_Pervasives_Native.Some
                                           uu____6893 in
                                       let uu____6902 =
                                         let uu____6905 =
                                           let uu____6908 = unembed ea x in
                                           uu____6908 true norm in
                                         FStar_Util.bind_opt uu____6905
                                           (fun x1 ->
                                              let uu____6919 =
                                                let uu____6922 = unembed eb y in
                                                uu____6922 true norm in
                                              FStar_Util.bind_opt uu____6919
                                                (fun y1 ->
                                                   let uu____6933 =
                                                     let uu____6936 =
                                                       unembed ec z in
                                                     uu____6936 true norm in
                                                   FStar_Util.bind_opt
                                                     uu____6933
                                                     (fun z1 ->
                                                        let uu____6947 =
                                                          let uu____6948 =
                                                            let uu____6955 =
                                                              f x1 y1 z1 in
                                                            embed ed
                                                              uu____6955 in
                                                          uu____6948 rng
                                                            shadow_app norm in
                                                        FStar_Pervasives_Native.Some
                                                          uu____6947))) in
                                       (match uu____6902 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None ->
                                            force_shadow shadow_app)))) in
                  f_wrapped
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s ->
    fun f ->
      (let uu____6985 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu____6985 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f () in
       (let uu____7014 = FStar_ST.op_Bang FStar_Options.debug_embedding in
        if uu____7014 then FStar_Util.print1 "------ending %s\n" s else ());
       res)