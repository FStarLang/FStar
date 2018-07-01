open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___205_13  ->
    match uu___205_13 with
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
      let uu___208_1478 = e  in
      {
        em = (uu___208_1478.em);
        un = (uu___208_1478.un);
        typ = ty;
        print = (uu___208_1478.print);
        emb_typ = (uu___208_1478.emb_typ)
      }
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___206_1485  ->
    match uu___206_1485 with
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
  'a .
    'a printer ->
      FStar_Syntax_Syntax.emb_typ ->
        FStar_Range.range ->
          FStar_Syntax_Syntax.term ->
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
              (let uu____1575 = FStar_Options.debug_any ()  in
               if uu____1575
               then
                 let uu____1576 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____1577 = emb_typ_to_string et  in
                 let uu____1578 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu____1576
                   uu____1577 uu____1578
               else ());
              (let uu____1582 = FStar_Options.eager_embedding ()  in
               if uu____1582
               then f ()
               else
                 (let thunk = FStar_Common.mk_thunk f  in
                  let uu____1593 =
                    let uu____1600 =
                      let uu____1601 =
                        let uu____1602 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____1602;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____1601  in
                    FStar_Syntax_Syntax.mk uu____1600  in
                  uu____1593 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____1717;
                  FStar_Syntax_Syntax.rng = uu____1718;_}
                ->
                let uu____1729 =
                  (FStar_Options.eager_embedding ()) || (et <> et')  in
                if uu____1729
                then
                  ((let uu____1733 = FStar_Options.debug_any ()  in
                    if uu____1733
                    then
                      let uu____1734 = emb_typ_to_string et  in
                      let uu____1735 = emb_typ_to_string et'  in
                      let uu____1736 =
                        let uu____1737 = FStar_Dyn.undyn b  in pa uu____1737
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\n\tvalue is %s\n"
                        uu____1734 uu____1735 uu____1736
                    else ());
                   (let aopt =
                      let uu____1744 = FStar_Common.force_thunk t  in
                      f uu____1744  in
                    let uu____1787 = FStar_Common.force_thunk t  in
                    f uu____1787))
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____1833 = FStar_Options.debug_any ()  in
                    if uu____1833
                    then
                      let uu____1834 = emb_typ_to_string et  in
                      let uu____1835 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____1834 uu____1835
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____1839 ->
                let aopt = f x1  in
                ((let uu____1844 = FStar_Options.debug_any ()  in
                  if uu____1844
                  then
                    let uu____1845 = emb_typ_to_string et  in
                    let uu____1846 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____1848 = pa a  in
                          Prims.strcat "Some " uu____1848
                       in
                    FStar_Util.print2
                      "Unembedding:\n\temb_typ=%s\n\tvalue is %s\n"
                      uu____1845 uu____1846
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____1923 = FStar_Options.debug_any ()  in
       if uu____1923
       then
         let uu____1924 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____1924
       else ());
      t  in
    let un t _w _n =
      (let uu____1949 = FStar_Options.debug_any ()  in
       if uu____1949
       then
         let uu____1950 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____1950
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____2039 =
    let uu____2040 =
      let uu____2047 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____2047, [])  in
    FStar_Syntax_Syntax.ET_app uu____2040  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____2039
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___209_2115 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___209_2115.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___209_2115.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____2143 ->
        (if w
         then
           (let uu____2145 =
              let uu____2150 =
                let uu____2151 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____2151  in
              (FStar_Errors.Warning_NotEmbedded, uu____2150)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2145)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2153 =
    let uu____2154 =
      let uu____2161 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____2161, [])  in
    FStar_Syntax_Syntax.ET_app uu____2154  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____2165  -> "()")
    uu____2153
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___210_2237 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___210_2237.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___210_2237.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____2268 ->
        (if w
         then
           (let uu____2270 =
              let uu____2275 =
                let uu____2276 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____2276  in
              (FStar_Errors.Warning_NotEmbedded, uu____2275)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2270)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2278 =
    let uu____2279 =
      let uu____2286 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____2286, [])  in
    FStar_Syntax_Syntax.ET_app uu____2279  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____2278
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___211_2358 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___211_2358.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___211_2358.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____2392 ->
        (if w
         then
           (let uu____2394 =
              let uu____2399 =
                let uu____2400 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____2400  in
              (FStar_Errors.Warning_NotEmbedded, uu____2399)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2394)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2403 =
    let uu____2404 =
      let uu____2411 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____2411, [])  in
    FStar_Syntax_Syntax.ET_app uu____2404  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____2403
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____2419 =
      let uu____2426 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____2426, [])  in
    FStar_Syntax_Syntax.ET_app uu____2419  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____2494  ->
         let uu____2495 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____2495)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____2529)) ->
             let uu____2542 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____2542
         | uu____2543 ->
             (if w
              then
                (let uu____2545 =
                   let uu____2550 =
                     let uu____2551 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____2551
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2550)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2545)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____2556 =
      let uu____2563 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____2563, [])  in
    FStar_Syntax_Syntax.ET_app uu____2556  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____2657)) -> FStar_Pervasives_Native.Some s
    | uu____2658 ->
        (if w
         then
           (let uu____2660 =
              let uu____2665 =
                let uu____2666 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____2666
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2665)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2660)
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
      let uu____2692 =
        let uu____2697 =
          let uu____2698 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____2698]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____2697  in
      uu____2692 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____2726 =
        let uu____2733 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____2733, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____2726  in
    let printer uu___207_2743 =
      match uu___207_2743 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____2747 =
            let uu____2748 = ea.print x  in Prims.strcat uu____2748 ")"  in
          Prims.strcat "(Some " uu____2747
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____2822  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____2823 =
                 let uu____2828 =
                   let uu____2829 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2829
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2830 =
                   let uu____2831 =
                     let uu____2840 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2840  in
                   [uu____2831]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2828 uu____2830  in
               uu____2823 FStar_Pervasives_Native.None rng
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
                        let uu____2929 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____2929  in
                      let uu____2930 =
                        let uu____2935 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____2936 =
                          let uu____2937 =
                            let uu____2946 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____2946  in
                          let uu____2947 =
                            let uu____2958 = FStar_Syntax_Syntax.as_arg t  in
                            [uu____2958]  in
                          uu____2937 :: uu____2947  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____2935 uu____2936
                         in
                      uu____2930 FStar_Pervasives_Native.None rng)
                  in
               let uu____2993 =
                 let uu____2998 =
                   let uu____2999 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2999
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____3000 =
                   let uu____3001 =
                     let uu____3010 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____3010  in
                   let uu____3011 =
                     let uu____3022 =
                       let uu____3031 =
                         let uu____3032 = embed ea a  in
                         uu____3032 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3031  in
                     [uu____3022]  in
                   uu____3001 :: uu____3011  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2998 uu____3000  in
               uu____2993 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____3167 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____3167 with
           | (hd1,args) ->
               let uu____3208 =
                 let uu____3223 =
                   let uu____3224 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____3224.FStar_Syntax_Syntax.n  in
                 (uu____3223, args)  in
               (match uu____3208 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3242) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____3266::(a,uu____3268)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____3319 =
                      let uu____3322 = unembed ea a  in uu____3322 w norm1
                       in
                    FStar_Util.bind_opt uu____3319
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____3341 ->
                    (if w
                     then
                       (let uu____3357 =
                          let uu____3362 =
                            let uu____3363 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____3363
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____3362)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____3357)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____3367 =
      let uu____3368 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____3368  in
    mk_emb_full em un uu____3367 printer emb_t_option_a
  
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
        let uu____3409 =
          let uu____3414 =
            let uu____3415 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____3424 =
              let uu____3435 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____3435]  in
            uu____3415 :: uu____3424  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____3414  in
        uu____3409 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____3471 =
          let uu____3478 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____3478, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____3471  in
      let printer uu____3490 =
        match uu____3490 with
        | (x,y) ->
            let uu____3497 = ea.print x  in
            let uu____3498 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____3497 uu____3498
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____3581  ->
             let proj i ab =
               let uu____3595 =
                 let uu____3600 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____3601 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____3600
                   uu____3601 i
                  in
               match uu____3595 with
               | (proj_1,uu____3605) ->
                   let proj_1_tm =
                     let uu____3607 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____3607  in
                   let uu____3608 =
                     let uu____3613 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____3614 =
                       let uu____3615 =
                         let uu____3624 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____3624  in
                       let uu____3625 =
                         let uu____3636 =
                           let uu____3645 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____3645  in
                         let uu____3646 =
                           let uu____3657 = FStar_Syntax_Syntax.as_arg ab  in
                           [uu____3657]  in
                         uu____3636 :: uu____3646  in
                       uu____3615 :: uu____3625  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3613 uu____3614  in
                   uu____3608 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____3816 =
               let uu____3821 =
                 let uu____3822 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3822
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____3823 =
                 let uu____3824 =
                   let uu____3833 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____3833  in
                 let uu____3834 =
                   let uu____3845 =
                     let uu____3854 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____3854  in
                   let uu____3855 =
                     let uu____3866 =
                       let uu____3875 =
                         let uu____3876 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____3876 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3875  in
                     let uu____3946 =
                       let uu____3957 =
                         let uu____3966 =
                           let uu____3967 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____3967 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____3966  in
                       [uu____3957]  in
                     uu____3866 :: uu____3946  in
                   uu____3845 :: uu____3855  in
                 uu____3824 :: uu____3834  in
               FStar_Syntax_Syntax.mk_Tm_app uu____3821 uu____3823  in
             uu____3816 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____4130 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____4130 with
             | (hd1,args) ->
                 let uu____4173 =
                   let uu____4186 =
                     let uu____4187 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____4187.FStar_Syntax_Syntax.n  in
                   (uu____4186, args)  in
                 (match uu____4173 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____4205::uu____4206::(a,uu____4208)::(b,uu____4210)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____4269 =
                        let uu____4272 = unembed ea a  in uu____4272 w norm1
                         in
                      FStar_Util.bind_opt uu____4269
                        (fun a1  ->
                           let uu____4292 =
                             let uu____4295 = unembed eb b  in
                             uu____4295 w norm1  in
                           FStar_Util.bind_opt uu____4292
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____4318 ->
                      (if w
                       then
                         (let uu____4332 =
                            let uu____4337 =
                              let uu____4338 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____4338
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____4337)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____4332)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____4344 =
        let uu____4345 = type_of ea  in
        let uu____4346 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____4345 uu____4346  in
      mk_emb_full em un uu____4344 printer emb_t_pair_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____4373 =
        let uu____4378 =
          let uu____4379 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____4379]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____4378  in
      uu____4373 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____4407 =
        let uu____4414 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____4414, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4407  in
    let printer l =
      let uu____4427 =
        let uu____4428 =
          let uu____4429 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____4429 (FStar_String.concat "; ")  in
        Prims.strcat uu____4428 "]"  in
      Prims.strcat "[" uu____4427  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____4508  ->
           let t =
             let uu____4510 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____4510  in
           match l with
           | [] ->
               let uu____4511 =
                 let uu____4516 =
                   let uu____4517 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____4517
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____4516 [t]  in
               uu____4511 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____4541 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4541
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____4558 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____4558  in
                 let uu____4559 =
                   let uu____4564 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____4565 =
                     let uu____4566 =
                       let uu____4575 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____4575  in
                     let uu____4576 =
                       let uu____4587 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____4587]  in
                     uu____4566 :: uu____4576  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4564 uu____4565  in
                 uu____4559 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____4738 =
                 let uu____4743 =
                   let uu____4744 =
                     let uu____4755 =
                       let uu____4764 =
                         let uu____4765 = embed ea hd1  in
                         uu____4765 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____4764  in
                     let uu____4835 =
                       let uu____4846 =
                         let uu____4855 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4855  in
                       [uu____4846]  in
                     uu____4755 :: uu____4835  in
                   t :: uu____4744  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____4743  in
               uu____4738 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____4969 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____4969 with
           | (hd1,args) ->
               let uu____5010 =
                 let uu____5023 =
                   let uu____5024 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____5024.FStar_Syntax_Syntax.n  in
                 (uu____5023, args)  in
               (match uu____5010 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5040) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____5060,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____5061))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____5102 =
                      let uu____5105 = unembed ea hd2  in uu____5105 w norm1
                       in
                    FStar_Util.bind_opt uu____5102
                      (fun hd3  ->
                         let uu____5123 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____5123
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____5173 =
                      let uu____5176 = unembed ea hd2  in uu____5176 w norm1
                       in
                    FStar_Util.bind_opt uu____5173
                      (fun hd3  ->
                         let uu____5194 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____5194
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____5211 ->
                    (if w
                     then
                       (let uu____5225 =
                          let uu____5230 =
                            let uu____5231 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____5231
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____5230)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____5225)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____5235 =
      let uu____5236 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____5236  in
    mk_emb_full em un uu____5235 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____5267 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____5273 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____5279 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____5285 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____5291 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____5297 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____5303 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____5309 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____5318 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____5340 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____5360 -> false
  
let (__proj__UnfoldAttr__item___0 :
  norm_step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____5373 -> false 
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
    let uu____5377 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____5377  in
  let emb_t_norm_step =
    let uu____5379 =
      let uu____5386 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____5386, [])  in
    FStar_Syntax_Syntax.ET_app uu____5379  in
  let printer uu____5394 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____5459  ->
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
             let uu____5463 =
               let uu____5468 =
                 let uu____5469 =
                   let uu____5478 =
                     let uu____5479 =
                       let uu____5486 = e_list e_string  in
                       embed uu____5486 l  in
                     uu____5479 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5478  in
                 [uu____5469]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____5468  in
             uu____5463 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____5541 =
               let uu____5546 =
                 let uu____5547 =
                   let uu____5556 =
                     let uu____5557 =
                       let uu____5564 = e_list e_string  in
                       embed uu____5564 l  in
                     uu____5557 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5556  in
                 [uu____5547]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____5546  in
             uu____5541 FStar_Pervasives_Native.None rng
         | UnfoldAttr a ->
             let uu____5617 =
               let uu____5622 =
                 let uu____5623 = FStar_Syntax_Syntax.as_arg a  in
                 [uu____5623]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____5622  in
             uu____5617 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____5682 = FStar_Syntax_Util.head_and_args t1  in
         match uu____5682 with
         | (hd1,args) ->
             let uu____5727 =
               let uu____5742 =
                 let uu____5743 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____5743.FStar_Syntax_Syntax.n  in
               (uu____5742, args)  in
             (match uu____5727 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5931)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____5966 =
                    let uu____5971 =
                      let uu____5980 = e_list e_string  in
                      unembed uu____5980 l  in
                    uu____5971 w norm1  in
                  FStar_Util.bind_opt uu____5966
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____6003)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____6038 =
                    let uu____6043 =
                      let uu____6052 = e_list e_string  in
                      unembed uu____6052 l  in
                    uu____6043 w norm1  in
                  FStar_Util.bind_opt uu____6038
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____6074::(a,uu____6076)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  -> FStar_Pervasives_Native.Some (UnfoldAttr a)
              | uu____6127 ->
                  (if w
                   then
                     (let uu____6143 =
                        let uu____6148 =
                          let uu____6149 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____6149
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____6148)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____6143)
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
    | uu____6244 ->
        (if w
         then
           (let uu____6246 =
              let uu____6251 =
                let uu____6252 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____6252  in
              (FStar_Errors.Warning_NotEmbedded, uu____6251)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____6246)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____6254 =
    let uu____6255 =
      let uu____6262 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____6262, [])  in
    FStar_Syntax_Syntax.ET_app uu____6255  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____6254
  
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
        let uu____6328 =
          let uu____6335 =
            let uu____6336 =
              let uu____6351 =
                let uu____6360 =
                  let uu____6367 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____6367, FStar_Pervasives_Native.None)  in
                [uu____6360]  in
              let uu____6382 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____6351, uu____6382)  in
            FStar_Syntax_Syntax.Tm_arrow uu____6336  in
          FStar_Syntax_Syntax.mk uu____6335  in
        uu____6328 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        let f_wrapped x =
          let shadow_app =
            map_shadow shadow_f
              (fun f1  ->
                 let uu____6549 =
                   let uu____6554 =
                     let uu____6555 = FStar_Syntax_Syntax.as_arg x  in
                     [uu____6555]  in
                   FStar_Syntax_Syntax.mk_Tm_app f1 uu____6554  in
                 uu____6549 FStar_Pervasives_Native.None rng)
             in
          let uu____6582 =
            let uu____6585 =
              let uu____6588 = unembed ea x  in uu____6588 true norm1  in
            FStar_Util.map_opt uu____6585
              (fun x1  ->
                 let uu____6627 =
                   let uu____6634 = f x1  in embed eb uu____6634  in
                 uu____6627 rng shadow_app norm1)
             in
          or_else uu____6582
            (fun uu____6700  ->
               let uu____6701 = force_shadow shadow_app  in
               match uu____6701 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise Embedding_failure
               | FStar_Pervasives_Native.Some app ->
                   norm1 (FStar_Util.Inr app))
           in
        lazy_embed (fun uu____6767  -> "<fun>") emb_t_arr_a_b rng t_arrow
          f_wrapped
          (fun uu____6772  ->
             let uu____6773 = force_shadow shadow_f  in
             match uu____6773 with
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
                 let uu____6887 = embed ea a  in
                 uu____6887 f1.FStar_Syntax_Syntax.pos
                   FStar_Pervasives_Native.None norm1
                  in
               let b_tm =
                 let uu____6920 =
                   let uu____6925 =
                     let uu____6926 =
                       let uu____6931 =
                         let uu____6932 = FStar_Syntax_Syntax.as_arg a_tm  in
                         [uu____6932]  in
                       FStar_Syntax_Syntax.mk_Tm_app f1 uu____6931  in
                     uu____6926 FStar_Pervasives_Native.None
                       f1.FStar_Syntax_Syntax.pos
                      in
                   FStar_Util.Inr uu____6925  in
                 norm1 uu____6920  in
               let uu____6959 =
                 let uu____6962 = unembed eb b_tm  in uu____6962 w norm1  in
               match uu____6959 with
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
                let uu____7059 = FStar_List.splitAt n_tvars args  in
                match uu____7059 with
                | (_tvar_args,rest_args) ->
                    let uu____7136 = FStar_List.hd rest_args  in
                    (match uu____7136 with
                     | (x,uu____7156) ->
                         let shadow_app =
                           let uu____7170 =
                             FStar_Common.mk_thunk
                               (fun uu____7179  ->
                                  let uu____7180 =
                                    let uu____7185 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____7185
                                      args
                                     in
                                  uu____7180 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____7170  in
                         let uu____7231 =
                           let uu____7234 =
                             let uu____7237 = unembed ea x  in
                             uu____7237 true norm1  in
                           FStar_Util.map_opt uu____7234
                             (fun x1  ->
                                let uu____7276 =
                                  let uu____7283 = f x1  in
                                  embed eb uu____7283  in
                                uu____7276 rng shadow_app norm1)
                            in
                         (match uu____7231 with
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
                  let uu____7410 = FStar_List.splitAt n_tvars args  in
                  match uu____7410 with
                  | (_tvar_args,rest_args) ->
                      let uu____7473 = FStar_List.hd rest_args  in
                      (match uu____7473 with
                       | (x,uu____7489) ->
                           let uu____7494 =
                             let uu____7501 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____7501  in
                           (match uu____7494 with
                            | (y,uu____7525) ->
                                let shadow_app =
                                  let uu____7535 =
                                    FStar_Common.mk_thunk
                                      (fun uu____7544  ->
                                         let uu____7545 =
                                           let uu____7550 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____7550 args
                                            in
                                         uu____7545
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____7535  in
                                let uu____7596 =
                                  let uu____7599 =
                                    let uu____7602 = unembed ea x  in
                                    uu____7602 true norm1  in
                                  FStar_Util.bind_opt uu____7599
                                    (fun x1  ->
                                       let uu____7618 =
                                         let uu____7621 = unembed eb y  in
                                         uu____7621 true norm1  in
                                       FStar_Util.bind_opt uu____7618
                                         (fun y1  ->
                                            let uu____7637 =
                                              let uu____7638 =
                                                let uu____7645 = f x1 y1  in
                                                embed ec uu____7645  in
                                              uu____7638 rng shadow_app norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____7637))
                                   in
                                (match uu____7596 with
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
                    let uu____7791 = FStar_List.splitAt n_tvars args  in
                    match uu____7791 with
                    | (_tvar_args,rest_args) ->
                        let uu____7854 = FStar_List.hd rest_args  in
                        (match uu____7854 with
                         | (x,uu____7870) ->
                             let uu____7875 =
                               let uu____7882 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____7882  in
                             (match uu____7875 with
                              | (y,uu____7906) ->
                                  let uu____7911 =
                                    let uu____7918 =
                                      let uu____7927 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____7927  in
                                    FStar_List.hd uu____7918  in
                                  (match uu____7911 with
                                   | (z,uu____7957) ->
                                       let shadow_app =
                                         let uu____7967 =
                                           FStar_Common.mk_thunk
                                             (fun uu____7976  ->
                                                let uu____7977 =
                                                  let uu____7982 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____7982 args
                                                   in
                                                uu____7977
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____7967
                                          in
                                       let uu____8028 =
                                         let uu____8031 =
                                           let uu____8034 = unembed ea x  in
                                           uu____8034 true norm1  in
                                         FStar_Util.bind_opt uu____8031
                                           (fun x1  ->
                                              let uu____8050 =
                                                let uu____8053 = unembed eb y
                                                   in
                                                uu____8053 true norm1  in
                                              FStar_Util.bind_opt uu____8050
                                                (fun y1  ->
                                                   let uu____8069 =
                                                     let uu____8072 =
                                                       unembed ec z  in
                                                     uu____8072 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____8069
                                                     (fun z1  ->
                                                        let uu____8088 =
                                                          let uu____8089 =
                                                            let uu____8096 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____8096
                                                             in
                                                          uu____8089 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____8088)))
                                          in
                                       (match uu____8028 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  