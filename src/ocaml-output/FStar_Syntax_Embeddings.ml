open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___204_13  ->
    match uu___204_13 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____20 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____20
  
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embedding_failure  -> true | uu____26 -> false
  
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unembedding_failure  -> true | uu____32 -> false
  
type shadow_term =
  FStar_Syntax_Syntax.term FStar_Common.thunk FStar_Pervasives_Native.option
let (map_shadow :
  shadow_term ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> shadow_term)
  =
  fun s  ->
    fun f  ->
      FStar_Util.map_opt s
        (fun s1  ->
           FStar_Common.mk_thunk
             (fun uu____196  ->
                let uu____197 = FStar_Common.force_thunk s1  in f uu____197))
  
let (force_shadow :
  shadow_term -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun s  -> FStar_Util.map_opt s FStar_Common.force_thunk 
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
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;
        print = __fname__print; emb_typ = __fname__emb_typ;_} -> __fname__em
  
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;
        print = __fname__print; emb_typ = __fname__emb_typ;_} -> __fname__un
  
let __proj__Mkembedding__item__typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;
        print = __fname__print; emb_typ = __fname__emb_typ;_} -> __fname__typ
  
let __proj__Mkembedding__item__print : 'a . 'a embedding -> 'a printer =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;
        print = __fname__print; emb_typ = __fname__emb_typ;_} ->
        __fname__print
  
let __proj__Mkembedding__item__emb_typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;
        print = __fname__print; emb_typ = __fname__emb_typ;_} ->
        __fname__emb_typ
  
let emb_typ_of : 'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun e  -> e.emb_typ 
let unknown_printer :
  'Auu____821 . FStar_Syntax_Syntax.term -> 'Auu____821 -> Prims.string =
  fun typ  ->
    fun uu____831  ->
      let uu____832 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____832
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____838 =
      let uu____839 = FStar_Syntax_Subst.compress t  in
      uu____839.FStar_Syntax_Syntax.n  in
    match uu____838 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____843 ->
        let uu____844 =
          let uu____845 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____845
           in
        failwith uu____844
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____970 =
          let uu____971 =
            let uu____978 =
              let uu____979 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____979 FStar_Ident.string_of_lid  in
            (uu____978, [])  in
          FStar_Syntax_Syntax.ET_app uu____971  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____970 }
  
let mk_emb_full :
  'a .
    'a raw_embedder ->
      'a raw_unembedder ->
        FStar_Syntax_Syntax.typ ->
          ('a -> Prims.string) -> FStar_Syntax_Syntax.emb_typ -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun typ  ->
        fun printer  ->
          fun emb_typ  -> { em; un; typ; print = printer; emb_typ }
  
let embed : 'a . 'a embedding -> 'a -> embed_t = fun e  -> fun x  -> e.em x 
let unembed : 'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun e  -> fun t  -> e.un t 
let warn_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  -> fun n1  -> let uu____1381 = unembed e t  in uu____1381 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  -> fun n1  -> let uu____1428 = unembed e t  in uu____1428 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___207_1478 = e  in
      {
        em = (uu___207_1478.em);
        un = (uu___207_1478.un);
        typ = ty;
        print = (uu___207_1478.print);
        emb_typ = (uu___207_1478.emb_typ)
      }
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___205_1485  ->
    match uu___205_1485 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____1495 =
          let uu____1496 =
            let uu____1497 =
              let uu____1498 =
                let uu____1499 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____1499 (FStar_String.concat " ")  in
              Prims.strcat uu____1498 ")"  in
            Prims.strcat " " uu____1497  in
          Prims.strcat h uu____1496  in
        Prims.strcat "(" uu____1495
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____1506 =
          let uu____1507 = emb_typ_to_string a  in
          let uu____1508 =
            let uu____1509 = emb_typ_to_string b  in
            Prims.strcat ") -> " uu____1509  in
          Prims.strcat uu____1507 uu____1508  in
        Prims.strcat "(" uu____1506
  
let lazy_embed :
  'Auu____1528 'a .
    'a printer ->
      FStar_Syntax_Syntax.emb_typ ->
        FStar_Range.range ->
          'Auu____1528 ->
            'a ->
              (unit -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun pa  ->
    fun et  ->
      fun rng  ->
        fun ta  ->
          fun x  ->
            fun f  ->
              let uu____1577 = FStar_Options.eager_embedding ()  in
              if uu____1577
              then f ()
              else
                (let thunk = FStar_Common.mk_thunk f  in
                 let uu____1588 =
                   let uu____1595 =
                     let uu____1596 =
                       let uu____1597 = FStar_Dyn.mkdyn x  in
                       {
                         FStar_Syntax_Syntax.blob = uu____1597;
                         FStar_Syntax_Syntax.lkind =
                           (FStar_Syntax_Syntax.Lazy_embedding (et, thunk));
                         FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                         FStar_Syntax_Syntax.rng = rng
                       }  in
                     FStar_Syntax_Syntax.Tm_lazy uu____1596  in
                   FStar_Syntax_Syntax.mk uu____1595  in
                 uu____1588 FStar_Pervasives_Native.None rng)
  
let lazy_unembed :
  'a .
    'a printer ->
      FStar_Syntax_Syntax.emb_typ ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option)
              -> 'a FStar_Pervasives_Native.option
  =
  fun pa  ->
    fun et  ->
      fun x  ->
        fun ta  ->
          fun f  ->
            let x1 = FStar_Syntax_Subst.compress x  in
            match x1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_lazy
                { FStar_Syntax_Syntax.blob = b;
                  FStar_Syntax_Syntax.lkind =
                    FStar_Syntax_Syntax.Lazy_embedding (et',t);
                  FStar_Syntax_Syntax.ltyp = uu____1712;
                  FStar_Syntax_Syntax.rng = uu____1713;_}
                ->
                let uu____1724 =
                  (FStar_Options.eager_embedding ()) || (et <> et')  in
                if uu____1724
                then
                  ((let uu____1728 = FStar_Options.debug_any ()  in
                    if uu____1728
                    then
                      let uu____1729 = emb_typ_to_string et  in
                      let uu____1730 = emb_typ_to_string et'  in
                      let uu____1731 =
                        let uu____1732 = FStar_Dyn.undyn b  in pa uu____1732
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\n\tvalue is %s\n"
                        uu____1729 uu____1730 uu____1731
                    else ());
                   (let aopt =
                      let uu____1739 = FStar_Common.force_thunk t  in
                      f uu____1739  in
                    let uu____1782 = FStar_Common.force_thunk t  in
                    f uu____1782))
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____1828 = FStar_Options.debug_any ()  in
                    if uu____1828
                    then
                      let uu____1829 = emb_typ_to_string et  in
                      let uu____1830 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____1829 uu____1830
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____1834 -> let aopt = f x1  in aopt
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____1909 = FStar_Options.debug_any ()  in
       if uu____1909
       then
         let uu____1910 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____1910
       else ());
      t  in
    let un t _w _n =
      (let uu____1935 = FStar_Options.debug_any ()  in
       if uu____1935
       then
         let uu____1936 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____1936
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____2025 =
    let uu____2026 =
      let uu____2033 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____2033, [])  in
    FStar_Syntax_Syntax.ET_app uu____2026  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____2025
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___208_2101 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___208_2101.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___208_2101.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____2129 ->
        (if w
         then
           (let uu____2131 =
              let uu____2136 =
                let uu____2137 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____2137  in
              (FStar_Errors.Warning_NotEmbedded, uu____2136)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2131)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2139 =
    let uu____2140 =
      let uu____2147 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____2147, [])  in
    FStar_Syntax_Syntax.ET_app uu____2140  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____2151  -> "()")
    uu____2139
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___209_2223 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___209_2223.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___209_2223.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____2254 ->
        (if w
         then
           (let uu____2256 =
              let uu____2261 =
                let uu____2262 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____2262  in
              (FStar_Errors.Warning_NotEmbedded, uu____2261)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2256)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2264 =
    let uu____2265 =
      let uu____2272 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____2272, [])  in
    FStar_Syntax_Syntax.ET_app uu____2265  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____2264
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___210_2344 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___210_2344.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___210_2344.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____2378 ->
        (if w
         then
           (let uu____2380 =
              let uu____2385 =
                let uu____2386 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____2386  in
              (FStar_Errors.Warning_NotEmbedded, uu____2385)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2380)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2389 =
    let uu____2390 =
      let uu____2397 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____2397, [])  in
    FStar_Syntax_Syntax.ET_app uu____2390  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____2389
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____2405 =
      let uu____2412 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____2412, [])  in
    FStar_Syntax_Syntax.ET_app uu____2405  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____2480  ->
         let uu____2481 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____2481)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____2515)) ->
             let uu____2528 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____2528
         | uu____2529 ->
             (if w
              then
                (let uu____2531 =
                   let uu____2536 =
                     let uu____2537 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____2537
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2536)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2531)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____2542 =
      let uu____2549 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____2549, [])  in
    FStar_Syntax_Syntax.ET_app uu____2542  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____2643)) -> FStar_Pervasives_Native.Some s
    | uu____2644 ->
        (if w
         then
           (let uu____2646 =
              let uu____2651 =
                let uu____2652 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____2652
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2651)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2646)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_string
    (fun x  -> Prims.strcat "\"" (Prims.strcat x "\"")) emb_t_string
  
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let t_option_a =
      let t_opt = FStar_Syntax_Util.fvar_const FStar_Parser_Const.option_lid
         in
      let uu____2678 =
        let uu____2683 =
          let uu____2684 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____2684]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____2683  in
      uu____2678 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____2712 =
        let uu____2719 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____2719, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____2712  in
    let printer uu___206_2729 =
      match uu___206_2729 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____2733 =
            let uu____2734 = ea.print x  in Prims.strcat uu____2734 ")"  in
          Prims.strcat "(Some " uu____2733
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____2810  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____2811 =
                 let uu____2816 =
                   let uu____2817 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2817
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2818 =
                   let uu____2819 =
                     let uu____2828 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2828  in
                   [uu____2819]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2816 uu____2818  in
               uu____2811 FStar_Pervasives_Native.None rng
           | FStar_Pervasives_Native.Some a ->
               let shadow_a =
                 map_shadow topt
                   (fun t  ->
                      let v1 = FStar_Ident.mk_ident ("v", rng)  in
                      let some_v =
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          FStar_Parser_Const.some_lid v1
                         in
                      let some_v_tm =
                        let uu____2917 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____2917  in
                      let uu____2918 =
                        let uu____2923 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____2924 =
                          let uu____2925 =
                            let uu____2934 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____2934  in
                          let uu____2935 =
                            let uu____2946 = FStar_Syntax_Syntax.as_arg t  in
                            [uu____2946]  in
                          uu____2925 :: uu____2935  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____2923 uu____2924
                         in
                      uu____2918 FStar_Pervasives_Native.None rng)
                  in
               let uu____2981 =
                 let uu____2986 =
                   let uu____2987 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2987
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2988 =
                   let uu____2989 =
                     let uu____2998 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2998  in
                   let uu____2999 =
                     let uu____3010 =
                       let uu____3019 =
                         let uu____3020 = embed ea a  in
                         uu____3020 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3019  in
                     [uu____3010]  in
                   uu____2989 :: uu____2999  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2986 uu____2988  in
               uu____2981 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____3155 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____3155 with
           | (hd1,args) ->
               let uu____3196 =
                 let uu____3211 =
                   let uu____3212 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____3212.FStar_Syntax_Syntax.n  in
                 (uu____3211, args)  in
               (match uu____3196 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3230) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____3254::(a,uu____3256)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____3307 =
                      let uu____3310 = unembed ea a  in uu____3310 w norm1
                       in
                    FStar_Util.bind_opt uu____3307
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____3329 ->
                    (if w
                     then
                       (let uu____3345 =
                          let uu____3350 =
                            let uu____3351 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____3351
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____3350)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____3345)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____3355 =
      let uu____3356 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____3356  in
    mk_emb_full em un uu____3355 printer emb_t_option_a
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2  in
        let uu____3397 =
          let uu____3402 =
            let uu____3403 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____3412 =
              let uu____3423 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____3423]  in
            uu____3403 :: uu____3412  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____3402  in
        uu____3397 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____3459 =
          let uu____3466 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____3466, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____3459  in
      let printer uu____3478 =
        match uu____3478 with
        | (x,y) ->
            let uu____3485 = ea.print x  in
            let uu____3486 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____3485 uu____3486
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____3571  ->
             let proj i ab =
               let uu____3585 =
                 let uu____3590 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____3591 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____3590
                   uu____3591 i
                  in
               match uu____3585 with
               | (proj_1,uu____3595) ->
                   let proj_1_tm =
                     let uu____3597 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____3597  in
                   let uu____3598 =
                     let uu____3603 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____3604 =
                       let uu____3605 =
                         let uu____3614 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____3614  in
                       let uu____3615 =
                         let uu____3626 =
                           let uu____3635 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____3635  in
                         let uu____3636 =
                           let uu____3647 = FStar_Syntax_Syntax.as_arg ab  in
                           [uu____3647]  in
                         uu____3626 :: uu____3636  in
                       uu____3605 :: uu____3615  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3603 uu____3604  in
                   uu____3598 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____3806 =
               let uu____3811 =
                 let uu____3812 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3812
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____3813 =
                 let uu____3814 =
                   let uu____3823 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____3823  in
                 let uu____3824 =
                   let uu____3835 =
                     let uu____3844 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____3844  in
                   let uu____3845 =
                     let uu____3856 =
                       let uu____3865 =
                         let uu____3866 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____3866 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3865  in
                     let uu____3936 =
                       let uu____3947 =
                         let uu____3956 =
                           let uu____3957 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____3957 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____3956  in
                       [uu____3947]  in
                     uu____3856 :: uu____3936  in
                   uu____3835 :: uu____3845  in
                 uu____3814 :: uu____3824  in
               FStar_Syntax_Syntax.mk_Tm_app uu____3811 uu____3813  in
             uu____3806 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____4120 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____4120 with
             | (hd1,args) ->
                 let uu____4163 =
                   let uu____4176 =
                     let uu____4177 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____4177.FStar_Syntax_Syntax.n  in
                   (uu____4176, args)  in
                 (match uu____4163 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____4195::uu____4196::(a,uu____4198)::(b,uu____4200)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____4259 =
                        let uu____4262 = unembed ea a  in uu____4262 w norm1
                         in
                      FStar_Util.bind_opt uu____4259
                        (fun a1  ->
                           let uu____4282 =
                             let uu____4285 = unembed eb b  in
                             uu____4285 w norm1  in
                           FStar_Util.bind_opt uu____4282
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____4308 ->
                      (if w
                       then
                         (let uu____4322 =
                            let uu____4327 =
                              let uu____4328 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____4328
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____4327)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____4322)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____4334 =
        let uu____4335 = type_of ea  in
        let uu____4336 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____4335 uu____4336  in
      mk_emb_full em un uu____4334 printer emb_t_pair_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____4363 =
        let uu____4368 =
          let uu____4369 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____4369]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____4368  in
      uu____4363 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____4397 =
        let uu____4404 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____4404, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4397  in
    let printer l =
      let uu____4417 =
        let uu____4418 =
          let uu____4419 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____4419 (FStar_String.concat "; ")  in
        Prims.strcat uu____4418 "]"  in
      Prims.strcat "[" uu____4417  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____4500  ->
           let t =
             let uu____4502 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____4502  in
           match l with
           | [] ->
               let uu____4503 =
                 let uu____4508 =
                   let uu____4509 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____4509
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____4508 [t]  in
               uu____4503 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____4533 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4533
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____4550 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____4550  in
                 let uu____4551 =
                   let uu____4556 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____4557 =
                     let uu____4558 =
                       let uu____4567 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____4567  in
                     let uu____4568 =
                       let uu____4579 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____4579]  in
                     uu____4558 :: uu____4568  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4556 uu____4557  in
                 uu____4551 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____4730 =
                 let uu____4735 =
                   let uu____4736 =
                     let uu____4747 =
                       let uu____4756 =
                         let uu____4757 = embed ea hd1  in
                         uu____4757 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____4756  in
                     let uu____4827 =
                       let uu____4838 =
                         let uu____4847 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4847  in
                       [uu____4838]  in
                     uu____4747 :: uu____4827  in
                   t :: uu____4736  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____4735  in
               uu____4730 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____4961 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____4961 with
           | (hd1,args) ->
               let uu____5002 =
                 let uu____5015 =
                   let uu____5016 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____5016.FStar_Syntax_Syntax.n  in
                 (uu____5015, args)  in
               (match uu____5002 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5032) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____5052,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____5053))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____5094 =
                      let uu____5097 = unembed ea hd2  in uu____5097 w norm1
                       in
                    FStar_Util.bind_opt uu____5094
                      (fun hd3  ->
                         let uu____5115 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____5115
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____5165 =
                      let uu____5168 = unembed ea hd2  in uu____5168 w norm1
                       in
                    FStar_Util.bind_opt uu____5165
                      (fun hd3  ->
                         let uu____5186 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____5186
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____5203 ->
                    (if w
                     then
                       (let uu____5217 =
                          let uu____5222 =
                            let uu____5223 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____5223
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____5222)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____5217)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____5227 =
      let uu____5228 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____5228  in
    mk_emb_full em un uu____5227 printer emb_t_list_a
  
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
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
  | NBE 
let (uu___is_Simpl : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____5259 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____5265 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____5271 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____5277 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____5283 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____5289 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____5295 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____5301 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____5310 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____5332 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____5352 -> false
  
let (__proj__UnfoldAttr__item___0 :
  norm_step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____5365 -> false 
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
    let uu____5369 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____5369  in
  let emb_t_norm_step =
    let uu____5371 =
      let uu____5378 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____5378, [])  in
    FStar_Syntax_Syntax.ET_app uu____5371  in
  let printer uu____5386 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____5451  ->
         match n1 with
         | Simpl  -> steps_Simpl
         | Weak  -> steps_Weak
         | HNF  -> steps_HNF
         | Primops  -> steps_Primops
         | Delta  -> steps_Delta
         | Zeta  -> steps_Zeta
         | Iota  -> steps_Iota
         | NBE  -> steps_NBE
         | Reify  -> steps_Reify
         | UnfoldOnly l ->
             let uu____5455 =
               let uu____5460 =
                 let uu____5461 =
                   let uu____5470 =
                     let uu____5471 =
                       let uu____5478 = e_list e_string  in
                       embed uu____5478 l  in
                     uu____5471 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5470  in
                 [uu____5461]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____5460  in
             uu____5455 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____5533 =
               let uu____5538 =
                 let uu____5539 =
                   let uu____5548 =
                     let uu____5549 =
                       let uu____5556 = e_list e_string  in
                       embed uu____5556 l  in
                     uu____5549 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5548  in
                 [uu____5539]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____5538  in
             uu____5533 FStar_Pervasives_Native.None rng
         | UnfoldAttr a ->
             let uu____5609 =
               let uu____5614 =
                 let uu____5615 = FStar_Syntax_Syntax.as_arg a  in
                 [uu____5615]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____5614  in
             uu____5609 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____5674 = FStar_Syntax_Util.head_and_args t1  in
         match uu____5674 with
         | (hd1,args) ->
             let uu____5719 =
               let uu____5734 =
                 let uu____5735 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____5735.FStar_Syntax_Syntax.n  in
               (uu____5734, args)  in
             (match uu____5719 with
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_simpl
                  -> FStar_Pervasives_Native.Some Simpl
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_weak
                  -> FStar_Pervasives_Native.Some Weak
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_hnf
                  -> FStar_Pervasives_Native.Some HNF
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_primops
                  -> FStar_Pervasives_Native.Some Primops
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_delta
                  -> FStar_Pervasives_Native.Some Delta
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_zeta
                  -> FStar_Pervasives_Native.Some Zeta
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_iota
                  -> FStar_Pervasives_Native.Some Iota
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_nbe
                  -> FStar_Pervasives_Native.Some NBE
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_reify
                  -> FStar_Pervasives_Native.Some Reify
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5923)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____5958 =
                    let uu____5963 =
                      let uu____5972 = e_list e_string  in
                      unembed uu____5972 l  in
                    uu____5963 w norm1  in
                  FStar_Util.bind_opt uu____5958
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5995)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____6030 =
                    let uu____6035 =
                      let uu____6044 = e_list e_string  in
                      unembed uu____6044 l  in
                    uu____6035 w norm1  in
                  FStar_Util.bind_opt uu____6030
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____6066::(a,uu____6068)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  -> FStar_Pervasives_Native.Some (UnfoldAttr a)
              | uu____6119 ->
                  (if w
                   then
                     (let uu____6135 =
                        let uu____6140 =
                          let uu____6141 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____6141
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____6140)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____6135)
                   else ();
                   FStar_Pervasives_Native.None)))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_norm_step printer emb_t_norm_step 
let (e_range : FStar_Range.range embedding) =
  let em r rng _shadow _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r) ->
        FStar_Pervasives_Native.Some r
    | uu____6236 ->
        (if w
         then
           (let uu____6238 =
              let uu____6243 =
                let uu____6244 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____6244  in
              (FStar_Errors.Warning_NotEmbedded, uu____6243)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____6238)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____6246 =
    let uu____6247 =
      let uu____6254 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____6254, [])  in
    FStar_Syntax_Syntax.ET_app uu____6247  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____6246
  
let or_else : 'a . 'a FStar_Pervasives_Native.option -> (unit -> 'a) -> 'a =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Pervasives_Native.Some x -> x
      | FStar_Pervasives_Native.None  -> g ()
  
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_arrow =
        let uu____6320 =
          let uu____6327 =
            let uu____6328 =
              let uu____6343 =
                let uu____6352 =
                  let uu____6359 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____6359, FStar_Pervasives_Native.None)  in
                [uu____6352]  in
              let uu____6374 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____6343, uu____6374)  in
            FStar_Syntax_Syntax.Tm_arrow uu____6328  in
          FStar_Syntax_Syntax.mk uu____6327  in
        uu____6320 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        let f_wrapped x =
          let shadow_app =
            map_shadow shadow_f
              (fun f1  ->
                 let uu____6541 =
                   let uu____6546 =
                     let uu____6547 = FStar_Syntax_Syntax.as_arg x  in
                     [uu____6547]  in
                   FStar_Syntax_Syntax.mk_Tm_app f1 uu____6546  in
                 uu____6541 FStar_Pervasives_Native.None rng)
             in
          let uu____6574 =
            let uu____6577 =
              let uu____6580 = unembed ea x  in uu____6580 true norm1  in
            FStar_Util.map_opt uu____6577
              (fun x1  ->
                 let uu____6619 =
                   let uu____6626 = f x1  in embed eb uu____6626  in
                 uu____6619 rng shadow_app norm1)
             in
          or_else uu____6574
            (fun uu____6692  ->
               let uu____6693 = force_shadow shadow_app  in
               match uu____6693 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise Embedding_failure
               | FStar_Pervasives_Native.Some app ->
                   norm1 (FStar_Util.Inr app))
           in
        lazy_embed (fun uu____6761  -> "<fun>") emb_t_arr_a_b rng t_arrow
          f_wrapped
          (fun uu____6766  ->
             let uu____6767 = force_shadow shadow_f  in
             match uu____6767 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 norm1 (FStar_Util.Inr repr_f))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               let a_tm =
                 let uu____6881 = embed ea a  in
                 uu____6881 f1.FStar_Syntax_Syntax.pos
                   FStar_Pervasives_Native.None norm1
                  in
               let b_tm =
                 let uu____6914 =
                   let uu____6919 =
                     let uu____6920 =
                       let uu____6925 =
                         let uu____6926 = FStar_Syntax_Syntax.as_arg a_tm  in
                         [uu____6926]  in
                       FStar_Syntax_Syntax.mk_Tm_app f1 uu____6925  in
                     uu____6920 FStar_Pervasives_Native.None
                       f1.FStar_Syntax_Syntax.pos
                      in
                   FStar_Util.Inr uu____6919  in
                 norm1 uu____6914  in
               let uu____6953 =
                 let uu____6956 = unembed eb b_tm  in uu____6956 w norm1  in
               match uu____6953 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise Unembedding_failure
               | FStar_Pervasives_Native.Some b -> b  in
             FStar_Pervasives_Native.Some f_wrapped)
         in
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
  fun ea  ->
    fun eb  ->
      fun f  ->
        fun n_tvars  ->
          fun fv_lid1  ->
            fun norm1  ->
              let rng = FStar_Ident.range_of_lid fv_lid1  in
              let f_wrapped args =
                let uu____7053 = FStar_List.splitAt n_tvars args  in
                match uu____7053 with
                | (_tvar_args,rest_args) ->
                    let uu____7130 = FStar_List.hd rest_args  in
                    (match uu____7130 with
                     | (x,uu____7150) ->
                         let shadow_app =
                           let uu____7164 =
                             FStar_Common.mk_thunk
                               (fun uu____7173  ->
                                  let uu____7174 =
                                    let uu____7179 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____7179
                                      args
                                     in
                                  uu____7174 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____7164  in
                         let uu____7225 =
                           let uu____7228 =
                             let uu____7231 = unembed ea x  in
                             uu____7231 true norm1  in
                           FStar_Util.map_opt uu____7228
                             (fun x1  ->
                                let uu____7270 =
                                  let uu____7277 = f x1  in
                                  embed eb uu____7277  in
                                uu____7270 rng shadow_app norm1)
                            in
                         (match uu____7225 with
                          | FStar_Pervasives_Native.Some x1 ->
                              FStar_Pervasives_Native.Some x1
                          | FStar_Pervasives_Native.None  ->
                              force_shadow shadow_app))
                 in
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
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun f  ->
          fun n_tvars  ->
            fun fv_lid1  ->
              fun norm1  ->
                let rng = FStar_Ident.range_of_lid fv_lid1  in
                let f_wrapped args =
                  let uu____7404 = FStar_List.splitAt n_tvars args  in
                  match uu____7404 with
                  | (_tvar_args,rest_args) ->
                      let uu____7467 = FStar_List.hd rest_args  in
                      (match uu____7467 with
                       | (x,uu____7483) ->
                           let uu____7488 =
                             let uu____7495 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____7495  in
                           (match uu____7488 with
                            | (y,uu____7519) ->
                                let shadow_app =
                                  let uu____7529 =
                                    FStar_Common.mk_thunk
                                      (fun uu____7538  ->
                                         let uu____7539 =
                                           let uu____7544 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____7544 args
                                            in
                                         uu____7539
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____7529  in
                                let uu____7590 =
                                  let uu____7593 =
                                    let uu____7596 = unembed ea x  in
                                    uu____7596 true norm1  in
                                  FStar_Util.bind_opt uu____7593
                                    (fun x1  ->
                                       let uu____7612 =
                                         let uu____7615 = unembed eb y  in
                                         uu____7615 true norm1  in
                                       FStar_Util.bind_opt uu____7612
                                         (fun y1  ->
                                            let uu____7631 =
                                              let uu____7632 =
                                                let uu____7639 = f x1 y1  in
                                                embed ec uu____7639  in
                                              uu____7632 rng shadow_app norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____7631))
                                   in
                                (match uu____7590 with
                                 | FStar_Pervasives_Native.Some x1 ->
                                     FStar_Pervasives_Native.Some x1
                                 | FStar_Pervasives_Native.None  ->
                                     force_shadow shadow_app)))
                   in
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
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun f  ->
            fun n_tvars  ->
              fun fv_lid1  ->
                fun norm1  ->
                  let rng = FStar_Ident.range_of_lid fv_lid1  in
                  let f_wrapped args =
                    let uu____7785 = FStar_List.splitAt n_tvars args  in
                    match uu____7785 with
                    | (_tvar_args,rest_args) ->
                        let uu____7848 = FStar_List.hd rest_args  in
                        (match uu____7848 with
                         | (x,uu____7864) ->
                             let uu____7869 =
                               let uu____7876 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____7876  in
                             (match uu____7869 with
                              | (y,uu____7900) ->
                                  let uu____7905 =
                                    let uu____7912 =
                                      let uu____7921 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____7921  in
                                    FStar_List.hd uu____7912  in
                                  (match uu____7905 with
                                   | (z,uu____7951) ->
                                       let shadow_app =
                                         let uu____7961 =
                                           FStar_Common.mk_thunk
                                             (fun uu____7970  ->
                                                let uu____7971 =
                                                  let uu____7976 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____7976 args
                                                   in
                                                uu____7971
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____7961
                                          in
                                       let uu____8022 =
                                         let uu____8025 =
                                           let uu____8028 = unembed ea x  in
                                           uu____8028 true norm1  in
                                         FStar_Util.bind_opt uu____8025
                                           (fun x1  ->
                                              let uu____8044 =
                                                let uu____8047 = unembed eb y
                                                   in
                                                uu____8047 true norm1  in
                                              FStar_Util.bind_opt uu____8044
                                                (fun y1  ->
                                                   let uu____8063 =
                                                     let uu____8066 =
                                                       unembed ec z  in
                                                     uu____8066 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____8063
                                                     (fun z1  ->
                                                        let uu____8082 =
                                                          let uu____8083 =
                                                            let uu____8090 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____8090
                                                             in
                                                          uu____8083 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____8082)))
                                          in
                                       (match uu____8022 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  