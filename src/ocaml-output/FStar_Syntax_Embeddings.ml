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
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___205_1459  ->
    match uu___205_1459 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____1469 =
          let uu____1470 =
            let uu____1471 =
              let uu____1472 =
                let uu____1473 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____1473 (FStar_String.concat " ")  in
              Prims.strcat uu____1472 ")"  in
            Prims.strcat " " uu____1471  in
          Prims.strcat h uu____1470  in
        Prims.strcat "(" uu____1469
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____1480 =
          let uu____1481 = emb_typ_to_string a  in
          let uu____1482 =
            let uu____1483 = emb_typ_to_string b  in
            Prims.strcat ") -> " uu____1483  in
          Prims.strcat uu____1481 uu____1482  in
        Prims.strcat "(" uu____1480
  
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
              (let uu____1549 = FStar_Options.debug_any ()  in
               if uu____1549
               then
                 let uu____1550 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____1551 = emb_typ_to_string et  in
                 let uu____1552 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu____1550
                   uu____1551 uu____1552
               else ());
              (let uu____1556 = FStar_Options.eager_embedding ()  in
               if uu____1556
               then f ()
               else
                 (let thunk = FStar_Common.mk_thunk f  in
                  let uu____1567 =
                    let uu____1574 =
                      let uu____1575 =
                        let uu____1576 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____1576;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____1575  in
                    FStar_Syntax_Syntax.mk uu____1574  in
                  uu____1567 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____1691;
                  FStar_Syntax_Syntax.rng = uu____1692;_}
                ->
                let uu____1703 =
                  (FStar_Options.eager_embedding ()) || (et <> et')  in
                if uu____1703
                then
                  ((let uu____1707 = FStar_Options.debug_any ()  in
                    if uu____1707
                    then
                      let uu____1708 = emb_typ_to_string et  in
                      let uu____1709 = emb_typ_to_string et'  in
                      let uu____1710 =
                        let uu____1711 = FStar_Dyn.undyn b  in pa uu____1711
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\n\tvalue is %s\n"
                        uu____1708 uu____1709 uu____1710
                    else ());
                   (let aopt =
                      let uu____1718 = FStar_Common.force_thunk t  in
                      f uu____1718  in
                    let uu____1761 = FStar_Common.force_thunk t  in
                    f uu____1761))
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____1807 = FStar_Options.debug_any ()  in
                    if uu____1807
                    then
                      let uu____1808 = emb_typ_to_string et  in
                      let uu____1809 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____1808 uu____1809
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____1813 ->
                let aopt = f x1  in
                ((let uu____1818 = FStar_Options.debug_any ()  in
                  if uu____1818
                  then
                    let uu____1819 = emb_typ_to_string et  in
                    let uu____1820 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____1822 = pa a  in
                          Prims.strcat "Some " uu____1822
                       in
                    FStar_Util.print2
                      "Unembedding:\n\temb_typ=%s\n\tvalue is %s\n"
                      uu____1819 uu____1820
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____1897 = FStar_Options.debug_any ()  in
       if uu____1897
       then
         let uu____1898 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____1898
       else ());
      t  in
    let un t _w _n =
      (let uu____1923 = FStar_Options.debug_any ()  in
       if uu____1923
       then
         let uu____1924 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____1924
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____2013 =
    let uu____2014 =
      let uu____2021 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____2021, [])  in
    FStar_Syntax_Syntax.ET_app uu____2014  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____2013
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___207_2089 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___207_2089.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___207_2089.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____2117 ->
        (if w
         then
           (let uu____2119 =
              let uu____2124 =
                let uu____2125 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____2125  in
              (FStar_Errors.Warning_NotEmbedded, uu____2124)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2119)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2127 =
    let uu____2128 =
      let uu____2135 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____2135, [])  in
    FStar_Syntax_Syntax.ET_app uu____2128  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____2139  -> "()")
    uu____2127
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___208_2211 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___208_2211.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___208_2211.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____2242 ->
        (if w
         then
           (let uu____2244 =
              let uu____2249 =
                let uu____2250 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____2250  in
              (FStar_Errors.Warning_NotEmbedded, uu____2249)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2244)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2252 =
    let uu____2253 =
      let uu____2260 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____2260, [])  in
    FStar_Syntax_Syntax.ET_app uu____2253  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____2252
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___209_2332 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___209_2332.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___209_2332.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____2366 ->
        (if w
         then
           (let uu____2368 =
              let uu____2373 =
                let uu____2374 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____2374  in
              (FStar_Errors.Warning_NotEmbedded, uu____2373)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2368)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2377 =
    let uu____2378 =
      let uu____2385 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____2385, [])  in
    FStar_Syntax_Syntax.ET_app uu____2378  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____2377
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____2393 =
      let uu____2400 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____2400, [])  in
    FStar_Syntax_Syntax.ET_app uu____2393  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____2468  ->
         let uu____2469 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____2469)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____2503)) ->
             let uu____2516 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____2516
         | uu____2517 ->
             (if w
              then
                (let uu____2519 =
                   let uu____2524 =
                     let uu____2525 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____2525
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2524)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2519)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____2530 =
      let uu____2537 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____2537, [])  in
    FStar_Syntax_Syntax.ET_app uu____2530  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____2631)) -> FStar_Pervasives_Native.Some s
    | uu____2632 ->
        (if w
         then
           (let uu____2634 =
              let uu____2639 =
                let uu____2640 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____2640
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2639)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2634)
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
      let uu____2666 =
        let uu____2671 =
          let uu____2672 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____2672]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____2671  in
      uu____2666 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____2700 =
        let uu____2707 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____2707, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____2700  in
    let printer uu___206_2717 =
      match uu___206_2717 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____2721 =
            let uu____2722 = ea.print x  in Prims.strcat uu____2722 ")"  in
          Prims.strcat "(Some " uu____2721
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____2796  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____2797 =
                 let uu____2802 =
                   let uu____2803 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2803
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2804 =
                   let uu____2805 =
                     let uu____2814 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2814  in
                   [uu____2805]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2802 uu____2804  in
               uu____2797 FStar_Pervasives_Native.None rng
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
                        let uu____2903 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____2903  in
                      let uu____2904 =
                        let uu____2909 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____2910 =
                          let uu____2911 =
                            let uu____2920 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____2920  in
                          let uu____2921 =
                            let uu____2932 = FStar_Syntax_Syntax.as_arg t  in
                            [uu____2932]  in
                          uu____2911 :: uu____2921  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____2909 uu____2910
                         in
                      uu____2904 FStar_Pervasives_Native.None rng)
                  in
               let uu____2967 =
                 let uu____2972 =
                   let uu____2973 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2973
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2974 =
                   let uu____2975 =
                     let uu____2984 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2984  in
                   let uu____2985 =
                     let uu____2996 =
                       let uu____3005 =
                         let uu____3006 = embed ea a  in
                         uu____3006 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3005  in
                     [uu____2996]  in
                   uu____2975 :: uu____2985  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2972 uu____2974  in
               uu____2967 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____3141 = FStar_Syntax_Util.head_and_args t1  in
           match uu____3141 with
           | (hd1,args) ->
               let uu____3188 =
                 let uu____3203 =
                   let uu____3204 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____3204.FStar_Syntax_Syntax.n  in
                 (uu____3203, args)  in
               (match uu____3188 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3222) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____3246::(a,uu____3248)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____3299 =
                      let uu____3302 = unembed ea a  in uu____3302 w norm1
                       in
                    FStar_Util.bind_opt uu____3299
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____3321 ->
                    (if w
                     then
                       (let uu____3337 =
                          let uu____3342 =
                            let uu____3343 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____3343
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____3342)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____3337)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____3347 =
      let uu____3348 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____3348  in
    mk_emb_full em un uu____3347 printer emb_t_option_a
  
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
        let uu____3389 =
          let uu____3394 =
            let uu____3395 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____3404 =
              let uu____3415 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____3415]  in
            uu____3395 :: uu____3404  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____3394  in
        uu____3389 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____3451 =
          let uu____3458 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____3458, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____3451  in
      let printer uu____3470 =
        match uu____3470 with
        | (x,y) ->
            let uu____3477 = ea.print x  in
            let uu____3478 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____3477 uu____3478
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____3561  ->
             let proj i ab =
               let uu____3575 =
                 let uu____3580 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____3581 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____3580
                   uu____3581 i
                  in
               match uu____3575 with
               | (proj_1,uu____3585) ->
                   let proj_1_tm =
                     let uu____3587 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____3587  in
                   let uu____3588 =
                     let uu____3593 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____3594 =
                       let uu____3595 =
                         let uu____3604 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____3604  in
                       let uu____3605 =
                         let uu____3616 =
                           let uu____3625 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____3625  in
                         let uu____3626 =
                           let uu____3637 = FStar_Syntax_Syntax.as_arg ab  in
                           [uu____3637]  in
                         uu____3616 :: uu____3626  in
                       uu____3595 :: uu____3605  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3593 uu____3594  in
                   uu____3588 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____3796 =
               let uu____3801 =
                 let uu____3802 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3802
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____3803 =
                 let uu____3804 =
                   let uu____3813 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____3813  in
                 let uu____3814 =
                   let uu____3825 =
                     let uu____3834 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____3834  in
                   let uu____3835 =
                     let uu____3846 =
                       let uu____3855 =
                         let uu____3856 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____3856 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3855  in
                     let uu____3926 =
                       let uu____3937 =
                         let uu____3946 =
                           let uu____3947 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____3947 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____3946  in
                       [uu____3937]  in
                     uu____3846 :: uu____3926  in
                   uu____3825 :: uu____3835  in
                 uu____3804 :: uu____3814  in
               FStar_Syntax_Syntax.mk_Tm_app uu____3801 uu____3803  in
             uu____3796 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____4110 = FStar_Syntax_Util.head_and_args t1  in
             match uu____4110 with
             | (hd1,args) ->
                 let uu____4159 =
                   let uu____4172 =
                     let uu____4173 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____4173.FStar_Syntax_Syntax.n  in
                   (uu____4172, args)  in
                 (match uu____4159 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____4191::uu____4192::(a,uu____4194)::(b,uu____4196)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____4255 =
                        let uu____4258 = unembed ea a  in uu____4258 w norm1
                         in
                      FStar_Util.bind_opt uu____4255
                        (fun a1  ->
                           let uu____4278 =
                             let uu____4281 = unembed eb b  in
                             uu____4281 w norm1  in
                           FStar_Util.bind_opt uu____4278
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____4304 ->
                      (if w
                       then
                         (let uu____4318 =
                            let uu____4323 =
                              let uu____4324 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____4324
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____4323)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____4318)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____4330 =
        let uu____4331 = type_of ea  in
        let uu____4332 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____4331 uu____4332  in
      mk_emb_full em un uu____4330 printer emb_t_pair_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____4359 =
        let uu____4364 =
          let uu____4365 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____4365]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____4364  in
      uu____4359 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____4393 =
        let uu____4400 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____4400, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4393  in
    let printer l =
      let uu____4413 =
        let uu____4414 =
          let uu____4415 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____4415 (FStar_String.concat "; ")  in
        Prims.strcat uu____4414 "]"  in
      Prims.strcat "[" uu____4413  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____4494  ->
           let t =
             let uu____4496 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____4496  in
           match l with
           | [] ->
               let uu____4497 =
                 let uu____4502 =
                   let uu____4503 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____4503
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____4502 [t]  in
               uu____4497 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____4527 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4527
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____4544 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____4544  in
                 let uu____4545 =
                   let uu____4550 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____4551 =
                     let uu____4552 =
                       let uu____4561 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____4561  in
                     let uu____4562 =
                       let uu____4573 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____4573]  in
                     uu____4552 :: uu____4562  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4550 uu____4551  in
                 uu____4545 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____4724 =
                 let uu____4729 =
                   let uu____4730 =
                     let uu____4741 =
                       let uu____4750 =
                         let uu____4751 = embed ea hd1  in
                         uu____4751 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____4750  in
                     let uu____4821 =
                       let uu____4832 =
                         let uu____4841 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4841  in
                       [uu____4832]  in
                     uu____4741 :: uu____4821  in
                   t :: uu____4730  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____4729  in
               uu____4724 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____4955 = FStar_Syntax_Util.head_and_args t1  in
           match uu____4955 with
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
  | UnfoldOnly of Prims.string Prims.list 
  | UnfoldFully of Prims.string Prims.list 
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
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
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____5304 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____5326 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____5346 -> false
  
let (__proj__UnfoldAttr__item___0 :
  norm_step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
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
let (steps_UnfoldOnly : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldonly 
let (steps_UnfoldFully : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldonly 
let (steps_UnfoldAttr : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldattr 
let (e_norm_step : norm_step embedding) =
  let t_norm_step1 =
    let uu____5357 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____5357  in
  let emb_t_norm_step =
    let uu____5359 =
      let uu____5366 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____5366, [])  in
    FStar_Syntax_Syntax.ET_app uu____5359  in
  let printer uu____5374 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____5439  ->
         match n1 with
         | Simpl  -> steps_Simpl
         | Weak  -> steps_Weak
         | HNF  -> steps_HNF
         | Primops  -> steps_Primops
         | Delta  -> steps_Delta
         | Zeta  -> steps_Zeta
         | Iota  -> steps_Iota
         | UnfoldOnly l ->
             let uu____5443 =
               let uu____5448 =
                 let uu____5449 =
                   let uu____5458 =
                     let uu____5459 =
                       let uu____5466 = e_list e_string  in
                       embed uu____5466 l  in
                     uu____5459 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5458  in
                 [uu____5449]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____5448  in
             uu____5443 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____5521 =
               let uu____5526 =
                 let uu____5527 =
                   let uu____5536 =
                     let uu____5537 =
                       let uu____5544 = e_list e_string  in
                       embed uu____5544 l  in
                     uu____5537 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5536  in
                 [uu____5527]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____5526  in
             uu____5521 FStar_Pervasives_Native.None rng
         | UnfoldAttr a ->
             let uu____5597 =
               let uu____5602 =
                 let uu____5603 = FStar_Syntax_Syntax.as_arg a  in
                 [uu____5603]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____5602  in
             uu____5597 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____5662 = FStar_Syntax_Util.head_and_args t1  in
         match uu____5662 with
         | (hd1,args) ->
             let uu____5707 =
               let uu____5722 =
                 let uu____5723 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____5723.FStar_Syntax_Syntax.n  in
               (uu____5722, args)  in
             (match uu____5707 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5873)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____5908 =
                    let uu____5913 =
                      let uu____5922 = e_list e_string  in
                      unembed uu____5922 l  in
                    uu____5913 w norm1  in
                  FStar_Util.bind_opt uu____5908
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5945)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____5980 =
                    let uu____5985 =
                      let uu____5994 = e_list e_string  in
                      unembed uu____5994 l  in
                    uu____5985 w norm1  in
                  FStar_Util.bind_opt uu____5980
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____6016::(a,uu____6018)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  -> FStar_Pervasives_Native.Some (UnfoldAttr a)
              | uu____6069 ->
                  (if w
                   then
                     (let uu____6085 =
                        let uu____6090 =
                          let uu____6091 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____6091
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____6090)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____6085)
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
    | uu____6186 ->
        (if w
         then
           (let uu____6188 =
              let uu____6193 =
                let uu____6194 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____6194  in
              (FStar_Errors.Warning_NotEmbedded, uu____6193)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____6188)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____6196 =
    let uu____6197 =
      let uu____6204 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____6204, [])  in
    FStar_Syntax_Syntax.ET_app uu____6197  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____6196
  
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
        let uu____6270 =
          let uu____6277 =
            let uu____6278 =
              let uu____6293 =
                let uu____6302 =
                  let uu____6309 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____6309, FStar_Pervasives_Native.None)  in
                [uu____6302]  in
              let uu____6324 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____6293, uu____6324)  in
            FStar_Syntax_Syntax.Tm_arrow uu____6278  in
          FStar_Syntax_Syntax.mk uu____6277  in
        uu____6270 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        let f_wrapped x =
          let shadow_app =
            map_shadow shadow_f
              (fun f1  ->
                 let uu____6491 =
                   let uu____6496 =
                     let uu____6497 = FStar_Syntax_Syntax.as_arg x  in
                     [uu____6497]  in
                   FStar_Syntax_Syntax.mk_Tm_app f1 uu____6496  in
                 uu____6491 FStar_Pervasives_Native.None rng)
             in
          let uu____6524 =
            let uu____6527 =
              let uu____6530 = unembed ea x  in uu____6530 true norm1  in
            FStar_Util.map_opt uu____6527
              (fun x1  ->
                 let uu____6569 =
                   let uu____6576 = f x1  in embed eb uu____6576  in
                 uu____6569 rng shadow_app norm1)
             in
          or_else uu____6524
            (fun uu____6642  ->
               let uu____6643 = force_shadow shadow_app  in
               match uu____6643 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise Embedding_failure
               | FStar_Pervasives_Native.Some app ->
                   norm1 (FStar_Util.Inr app))
           in
        lazy_embed (fun uu____6709  -> "<fun>") emb_t_arr_a_b rng t_arrow
          f_wrapped
          (fun uu____6714  ->
             let uu____6715 = force_shadow shadow_f  in
             match uu____6715 with
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
                 let uu____6829 = embed ea a  in
                 uu____6829 f1.FStar_Syntax_Syntax.pos
                   FStar_Pervasives_Native.None norm1
                  in
               let b_tm =
                 let uu____6862 =
                   let uu____6867 =
                     let uu____6868 =
                       let uu____6873 =
                         let uu____6874 = FStar_Syntax_Syntax.as_arg a_tm  in
                         [uu____6874]  in
                       FStar_Syntax_Syntax.mk_Tm_app f1 uu____6873  in
                     uu____6868 FStar_Pervasives_Native.None
                       f1.FStar_Syntax_Syntax.pos
                      in
                   FStar_Util.Inr uu____6867  in
                 norm1 uu____6862  in
               let uu____6901 =
                 let uu____6904 = unembed eb b_tm  in uu____6904 w norm1  in
               match uu____6901 with
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
                let uu____7001 = FStar_List.splitAt n_tvars args  in
                match uu____7001 with
                | (_tvar_args,rest_args) ->
                    let uu____7078 = FStar_List.hd rest_args  in
                    (match uu____7078 with
                     | (x,uu____7098) ->
                         let shadow_app =
                           let uu____7112 =
                             FStar_Common.mk_thunk
                               (fun uu____7121  ->
                                  let uu____7122 =
                                    let uu____7127 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____7127
                                      args
                                     in
                                  uu____7122 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____7112  in
                         let uu____7173 =
                           let uu____7176 =
                             let uu____7179 = unembed ea x  in
                             uu____7179 true norm1  in
                           FStar_Util.map_opt uu____7176
                             (fun x1  ->
                                let uu____7218 =
                                  let uu____7225 = f x1  in
                                  embed eb uu____7225  in
                                uu____7218 rng shadow_app norm1)
                            in
                         (match uu____7173 with
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
                  let uu____7352 = FStar_List.splitAt n_tvars args  in
                  match uu____7352 with
                  | (_tvar_args,rest_args) ->
                      let uu____7415 = FStar_List.hd rest_args  in
                      (match uu____7415 with
                       | (x,uu____7431) ->
                           let uu____7436 =
                             let uu____7443 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____7443  in
                           (match uu____7436 with
                            | (y,uu____7467) ->
                                let shadow_app =
                                  let uu____7477 =
                                    FStar_Common.mk_thunk
                                      (fun uu____7486  ->
                                         let uu____7487 =
                                           let uu____7492 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____7492 args
                                            in
                                         uu____7487
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____7477  in
                                let uu____7538 =
                                  let uu____7541 =
                                    let uu____7544 = unembed ea x  in
                                    uu____7544 true norm1  in
                                  FStar_Util.bind_opt uu____7541
                                    (fun x1  ->
                                       let uu____7560 =
                                         let uu____7563 = unembed eb y  in
                                         uu____7563 true norm1  in
                                       FStar_Util.bind_opt uu____7560
                                         (fun y1  ->
                                            let uu____7579 =
                                              let uu____7580 =
                                                let uu____7587 = f x1 y1  in
                                                embed ec uu____7587  in
                                              uu____7580 rng shadow_app norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____7579))
                                   in
                                (match uu____7538 with
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
                    let uu____7733 = FStar_List.splitAt n_tvars args  in
                    match uu____7733 with
                    | (_tvar_args,rest_args) ->
                        let uu____7796 = FStar_List.hd rest_args  in
                        (match uu____7796 with
                         | (x,uu____7812) ->
                             let uu____7817 =
                               let uu____7824 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____7824  in
                             (match uu____7817 with
                              | (y,uu____7848) ->
                                  let uu____7853 =
                                    let uu____7860 =
                                      let uu____7869 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____7869  in
                                    FStar_List.hd uu____7860  in
                                  (match uu____7853 with
                                   | (z,uu____7899) ->
                                       let shadow_app =
                                         let uu____7909 =
                                           FStar_Common.mk_thunk
                                             (fun uu____7918  ->
                                                let uu____7919 =
                                                  let uu____7924 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____7924 args
                                                   in
                                                uu____7919
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____7909
                                          in
                                       let uu____7970 =
                                         let uu____7973 =
                                           let uu____7976 = unembed ea x  in
                                           uu____7976 true norm1  in
                                         FStar_Util.bind_opt uu____7973
                                           (fun x1  ->
                                              let uu____7992 =
                                                let uu____7995 = unembed eb y
                                                   in
                                                uu____7995 true norm1  in
                                              FStar_Util.bind_opt uu____7992
                                                (fun y1  ->
                                                   let uu____8011 =
                                                     let uu____8014 =
                                                       unembed ec z  in
                                                     uu____8014 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____8011
                                                     (fun z1  ->
                                                        let uu____8030 =
                                                          let uu____8031 =
                                                            let uu____8038 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____8038
                                                             in
                                                          uu____8031 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____8030)))
                                          in
                                       (match uu____7970 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  