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
              (let uu____1575 =
                 FStar_ST.op_Bang FStar_Options.debug_embedding  in
               if uu____1575
               then
                 let uu____1595 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____1596 = emb_typ_to_string et  in
                 let uu____1597 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu____1595
                   uu____1596 uu____1597
               else ());
              (let uu____1601 =
                 FStar_ST.op_Bang FStar_Options.eager_embedding  in
               if uu____1601
               then f ()
               else
                 (let thunk = FStar_Common.mk_thunk f  in
                  let uu____1631 =
                    let uu____1638 =
                      let uu____1639 =
                        let uu____1640 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____1640;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____1639  in
                    FStar_Syntax_Syntax.mk uu____1638  in
                  uu____1631 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____1755;
                  FStar_Syntax_Syntax.rng = uu____1756;_}
                ->
                let uu____1767 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____1767
                then
                  let res =
                    let uu____1792 = FStar_Common.force_thunk t  in
                    f uu____1792  in
                  ((let uu____1836 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1836
                    then
                      let uu____1856 = emb_typ_to_string et  in
                      let uu____1857 = emb_typ_to_string et'  in
                      let uu____1858 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____1860 = pa x2  in
                            Prims.strcat "Some " uu____1860
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____1856 uu____1857 uu____1858
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____1867 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1867
                    then
                      let uu____1887 = emb_typ_to_string et  in
                      let uu____1888 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____1887 uu____1888
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____1892 ->
                let aopt = f x1  in
                ((let uu____1897 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____1897
                  then
                    let uu____1917 = emb_typ_to_string et  in
                    let uu____1918 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____1920 = pa a  in
                          Prims.strcat "Some " uu____1920
                       in
                    FStar_Util.print2
                      "Unembedding:\n\temb_typ=%s\n\tvalue is %s\n"
                      uu____1917 uu____1918
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____1995 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____1995
       then
         let uu____2015 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____2015
       else ());
      t  in
    let un t _w _n =
      (let uu____2040 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____2040
       then
         let uu____2060 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____2060
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____2149 =
    let uu____2150 =
      let uu____2157 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____2157, [])  in
    FStar_Syntax_Syntax.ET_app uu____2150  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____2149
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___209_2225 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___209_2225.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___209_2225.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____2253 ->
        (if w
         then
           (let uu____2255 =
              let uu____2260 =
                let uu____2261 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____2261  in
              (FStar_Errors.Warning_NotEmbedded, uu____2260)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2255)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2263 =
    let uu____2264 =
      let uu____2271 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____2271, [])  in
    FStar_Syntax_Syntax.ET_app uu____2264  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____2275  -> "()")
    uu____2263
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___210_2347 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___210_2347.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___210_2347.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____2378 ->
        (if w
         then
           (let uu____2380 =
              let uu____2385 =
                let uu____2386 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____2386  in
              (FStar_Errors.Warning_NotEmbedded, uu____2385)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2380)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2388 =
    let uu____2389 =
      let uu____2396 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____2396, [])  in
    FStar_Syntax_Syntax.ET_app uu____2389  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____2388
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___211_2468 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___211_2468.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___211_2468.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____2502 ->
        (if w
         then
           (let uu____2504 =
              let uu____2509 =
                let uu____2510 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____2510  in
              (FStar_Errors.Warning_NotEmbedded, uu____2509)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2504)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2513 =
    let uu____2514 =
      let uu____2521 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____2521, [])  in
    FStar_Syntax_Syntax.ET_app uu____2514  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____2513
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____2529 =
      let uu____2536 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____2536, [])  in
    FStar_Syntax_Syntax.ET_app uu____2529  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____2604  ->
         let uu____2605 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____2605)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____2639)) ->
             let uu____2652 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____2652
         | uu____2653 ->
             (if w
              then
                (let uu____2655 =
                   let uu____2660 =
                     let uu____2661 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____2661
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2660)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2655)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____2666 =
      let uu____2673 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____2673, [])  in
    FStar_Syntax_Syntax.ET_app uu____2666  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____2767)) -> FStar_Pervasives_Native.Some s
    | uu____2768 ->
        (if w
         then
           (let uu____2770 =
              let uu____2775 =
                let uu____2776 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____2776
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2775)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2770)
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
      let uu____2802 =
        let uu____2807 =
          let uu____2808 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____2808]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____2807  in
      uu____2802 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____2836 =
        let uu____2843 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____2843, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____2836  in
    let printer uu___207_2853 =
      match uu___207_2853 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____2857 =
            let uu____2858 = ea.print x  in Prims.strcat uu____2858 ")"  in
          Prims.strcat "(Some " uu____2857
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____2932  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____2933 =
                 let uu____2938 =
                   let uu____2939 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2939
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2940 =
                   let uu____2941 =
                     let uu____2950 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2950  in
                   [uu____2941]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2938 uu____2940  in
               uu____2933 FStar_Pervasives_Native.None rng
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
                        let uu____3039 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____3039  in
                      let uu____3040 =
                        let uu____3045 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____3046 =
                          let uu____3047 =
                            let uu____3056 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____3056  in
                          let uu____3057 =
                            let uu____3068 = FStar_Syntax_Syntax.as_arg t  in
                            [uu____3068]  in
                          uu____3047 :: uu____3057  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3045 uu____3046
                         in
                      uu____3040 FStar_Pervasives_Native.None rng)
                  in
               let uu____3103 =
                 let uu____3108 =
                   let uu____3109 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____3109
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____3110 =
                   let uu____3111 =
                     let uu____3120 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____3120  in
                   let uu____3121 =
                     let uu____3132 =
                       let uu____3141 =
                         let uu____3142 = embed ea a  in
                         uu____3142 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3141  in
                     [uu____3132]  in
                   uu____3111 :: uu____3121  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3108 uu____3110  in
               uu____3103 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____3277 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____3277 with
           | (hd1,args) ->
               let uu____3318 =
                 let uu____3333 =
                   let uu____3334 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____3334.FStar_Syntax_Syntax.n  in
                 (uu____3333, args)  in
               (match uu____3318 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3352) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____3376::(a,uu____3378)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____3429 =
                      let uu____3432 = unembed ea a  in uu____3432 w norm1
                       in
                    FStar_Util.bind_opt uu____3429
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____3451 ->
                    (if w
                     then
                       (let uu____3467 =
                          let uu____3472 =
                            let uu____3473 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____3473
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____3472)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____3467)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____3477 =
      let uu____3478 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____3478  in
    mk_emb_full em un uu____3477 printer emb_t_option_a
  
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
        let uu____3519 =
          let uu____3524 =
            let uu____3525 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____3534 =
              let uu____3545 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____3545]  in
            uu____3525 :: uu____3534  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____3524  in
        uu____3519 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____3581 =
          let uu____3588 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____3588, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____3581  in
      let printer uu____3600 =
        match uu____3600 with
        | (x,y) ->
            let uu____3607 = ea.print x  in
            let uu____3608 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____3607 uu____3608
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____3691  ->
             let proj i ab =
               let uu____3705 =
                 let uu____3710 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____3711 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____3710
                   uu____3711 i
                  in
               match uu____3705 with
               | (proj_1,uu____3715) ->
                   let proj_1_tm =
                     let uu____3717 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____3717  in
                   let uu____3718 =
                     let uu____3723 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____3724 =
                       let uu____3725 =
                         let uu____3734 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____3734  in
                       let uu____3735 =
                         let uu____3746 =
                           let uu____3755 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____3755  in
                         let uu____3756 =
                           let uu____3767 = FStar_Syntax_Syntax.as_arg ab  in
                           [uu____3767]  in
                         uu____3746 :: uu____3756  in
                       uu____3725 :: uu____3735  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3723 uu____3724  in
                   uu____3718 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____3926 =
               let uu____3931 =
                 let uu____3932 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3932
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____3933 =
                 let uu____3934 =
                   let uu____3943 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____3943  in
                 let uu____3944 =
                   let uu____3955 =
                     let uu____3964 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____3964  in
                   let uu____3965 =
                     let uu____3976 =
                       let uu____3985 =
                         let uu____3986 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____3986 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3985  in
                     let uu____4056 =
                       let uu____4067 =
                         let uu____4076 =
                           let uu____4077 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____4077 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4076  in
                       [uu____4067]  in
                     uu____3976 :: uu____4056  in
                   uu____3955 :: uu____3965  in
                 uu____3934 :: uu____3944  in
               FStar_Syntax_Syntax.mk_Tm_app uu____3931 uu____3933  in
             uu____3926 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____4240 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____4240 with
             | (hd1,args) ->
                 let uu____4283 =
                   let uu____4296 =
                     let uu____4297 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____4297.FStar_Syntax_Syntax.n  in
                   (uu____4296, args)  in
                 (match uu____4283 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____4315::uu____4316::(a,uu____4318)::(b,uu____4320)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____4379 =
                        let uu____4382 = unembed ea a  in uu____4382 w norm1
                         in
                      FStar_Util.bind_opt uu____4379
                        (fun a1  ->
                           let uu____4402 =
                             let uu____4405 = unembed eb b  in
                             uu____4405 w norm1  in
                           FStar_Util.bind_opt uu____4402
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____4428 ->
                      (if w
                       then
                         (let uu____4442 =
                            let uu____4447 =
                              let uu____4448 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____4448
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____4447)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____4442)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____4454 =
        let uu____4455 = type_of ea  in
        let uu____4456 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____4455 uu____4456  in
      mk_emb_full em un uu____4454 printer emb_t_pair_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____4483 =
        let uu____4488 =
          let uu____4489 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____4489]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____4488  in
      uu____4483 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____4517 =
        let uu____4524 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____4524, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4517  in
    let printer l =
      let uu____4537 =
        let uu____4538 =
          let uu____4539 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____4539 (FStar_String.concat "; ")  in
        Prims.strcat uu____4538 "]"  in
      Prims.strcat "[" uu____4537  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____4618  ->
           let t =
             let uu____4620 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____4620  in
           match l with
           | [] ->
               let uu____4621 =
                 let uu____4626 =
                   let uu____4627 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____4627
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____4626 [t]  in
               uu____4621 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____4651 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4651
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____4668 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____4668  in
                 let uu____4669 =
                   let uu____4674 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____4675 =
                     let uu____4676 =
                       let uu____4685 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____4685  in
                     let uu____4686 =
                       let uu____4697 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____4697]  in
                     uu____4676 :: uu____4686  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4674 uu____4675  in
                 uu____4669 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____4848 =
                 let uu____4853 =
                   let uu____4854 =
                     let uu____4865 =
                       let uu____4874 =
                         let uu____4875 = embed ea hd1  in
                         uu____4875 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____4874  in
                     let uu____4945 =
                       let uu____4956 =
                         let uu____4965 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4965  in
                       [uu____4956]  in
                     uu____4865 :: uu____4945  in
                   t :: uu____4854  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____4853  in
               uu____4848 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____5079 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____5079 with
           | (hd1,args) ->
               let uu____5120 =
                 let uu____5133 =
                   let uu____5134 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____5134.FStar_Syntax_Syntax.n  in
                 (uu____5133, args)  in
               (match uu____5120 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5150) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____5170,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____5171))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____5212 =
                      let uu____5215 = unembed ea hd2  in uu____5215 w norm1
                       in
                    FStar_Util.bind_opt uu____5212
                      (fun hd3  ->
                         let uu____5233 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____5233
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____5283 =
                      let uu____5286 = unembed ea hd2  in uu____5286 w norm1
                       in
                    FStar_Util.bind_opt uu____5283
                      (fun hd3  ->
                         let uu____5304 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____5304
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____5321 ->
                    (if w
                     then
                       (let uu____5335 =
                          let uu____5340 =
                            let uu____5341 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____5341
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____5340)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____5335)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____5345 =
      let uu____5346 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____5346  in
    mk_emb_full em un uu____5345 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____5377 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____5383 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____5389 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____5395 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____5401 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____5407 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____5413 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____5419 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____5428 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____5450 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____5470 -> false
  
let (__proj__UnfoldAttr__item___0 :
  norm_step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____5483 -> false 
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
    let uu____5487 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____5487  in
  let emb_t_norm_step =
    let uu____5489 =
      let uu____5496 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____5496, [])  in
    FStar_Syntax_Syntax.ET_app uu____5489  in
  let printer uu____5504 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____5569  ->
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
             let uu____5573 =
               let uu____5578 =
                 let uu____5579 =
                   let uu____5588 =
                     let uu____5589 =
                       let uu____5596 = e_list e_string  in
                       embed uu____5596 l  in
                     uu____5589 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5588  in
                 [uu____5579]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____5578  in
             uu____5573 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____5651 =
               let uu____5656 =
                 let uu____5657 =
                   let uu____5666 =
                     let uu____5667 =
                       let uu____5674 = e_list e_string  in
                       embed uu____5674 l  in
                     uu____5667 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5666  in
                 [uu____5657]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____5656  in
             uu____5651 FStar_Pervasives_Native.None rng
         | UnfoldAttr a ->
             let uu____5727 =
               let uu____5732 =
                 let uu____5733 = FStar_Syntax_Syntax.as_arg a  in
                 [uu____5733]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____5732  in
             uu____5727 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____5792 = FStar_Syntax_Util.head_and_args t1  in
         match uu____5792 with
         | (hd1,args) ->
             let uu____5837 =
               let uu____5852 =
                 let uu____5853 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____5853.FStar_Syntax_Syntax.n  in
               (uu____5852, args)  in
             (match uu____5837 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____6041)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____6076 =
                    let uu____6081 =
                      let uu____6090 = e_list e_string  in
                      unembed uu____6090 l  in
                    uu____6081 w norm1  in
                  FStar_Util.bind_opt uu____6076
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____6113)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____6148 =
                    let uu____6153 =
                      let uu____6162 = e_list e_string  in
                      unembed uu____6162 l  in
                    uu____6153 w norm1  in
                  FStar_Util.bind_opt uu____6148
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____6184::(a,uu____6186)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  -> FStar_Pervasives_Native.Some (UnfoldAttr a)
              | uu____6237 ->
                  (if w
                   then
                     (let uu____6253 =
                        let uu____6258 =
                          let uu____6259 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____6259
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____6258)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____6253)
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
    | uu____6354 ->
        (if w
         then
           (let uu____6356 =
              let uu____6361 =
                let uu____6362 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____6362  in
              (FStar_Errors.Warning_NotEmbedded, uu____6361)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____6356)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____6364 =
    let uu____6365 =
      let uu____6372 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____6372, [])  in
    FStar_Syntax_Syntax.ET_app uu____6365  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____6364
  
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
        let uu____6438 =
          let uu____6445 =
            let uu____6446 =
              let uu____6461 =
                let uu____6470 =
                  let uu____6477 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____6477, FStar_Pervasives_Native.None)  in
                [uu____6470]  in
              let uu____6492 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____6461, uu____6492)  in
            FStar_Syntax_Syntax.Tm_arrow uu____6446  in
          FStar_Syntax_Syntax.mk uu____6445  in
        uu____6438 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____6603  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____6608  ->
             let uu____6609 = force_shadow shadow_f  in
             match uu____6609 with
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
                 let uu____6722 = embed ea a  in
                 uu____6722 f1.FStar_Syntax_Syntax.pos
                   FStar_Pervasives_Native.None norm1
                  in
               let b_tm =
                 let uu____6755 =
                   let uu____6760 =
                     let uu____6761 =
                       let uu____6766 =
                         let uu____6767 = FStar_Syntax_Syntax.as_arg a_tm  in
                         [uu____6767]  in
                       FStar_Syntax_Syntax.mk_Tm_app f1 uu____6766  in
                     uu____6761 FStar_Pervasives_Native.None
                       f1.FStar_Syntax_Syntax.pos
                      in
                   FStar_Util.Inr uu____6760  in
                 norm1 uu____6755  in
               let uu____6794 =
                 let uu____6797 = unembed eb b_tm  in uu____6797 w norm1  in
               match uu____6794 with
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
                let uu____6894 = FStar_List.splitAt n_tvars args  in
                match uu____6894 with
                | (_tvar_args,rest_args) ->
                    let uu____6971 = FStar_List.hd rest_args  in
                    (match uu____6971 with
                     | (x,uu____6991) ->
                         let shadow_app =
                           let uu____7005 =
                             FStar_Common.mk_thunk
                               (fun uu____7014  ->
                                  let uu____7015 =
                                    let uu____7020 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____7020
                                      args
                                     in
                                  uu____7015 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____7005  in
                         let uu____7066 =
                           let uu____7069 =
                             let uu____7072 = unembed ea x  in
                             uu____7072 true norm1  in
                           FStar_Util.map_opt uu____7069
                             (fun x1  ->
                                let uu____7111 =
                                  let uu____7118 = f x1  in
                                  embed eb uu____7118  in
                                uu____7111 rng shadow_app norm1)
                            in
                         (match uu____7066 with
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
                  let uu____7245 = FStar_List.splitAt n_tvars args  in
                  match uu____7245 with
                  | (_tvar_args,rest_args) ->
                      let uu____7308 = FStar_List.hd rest_args  in
                      (match uu____7308 with
                       | (x,uu____7324) ->
                           let uu____7329 =
                             let uu____7336 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____7336  in
                           (match uu____7329 with
                            | (y,uu____7360) ->
                                let shadow_app =
                                  let uu____7370 =
                                    FStar_Common.mk_thunk
                                      (fun uu____7379  ->
                                         let uu____7380 =
                                           let uu____7385 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____7385 args
                                            in
                                         uu____7380
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____7370  in
                                let uu____7431 =
                                  let uu____7434 =
                                    let uu____7437 = unembed ea x  in
                                    uu____7437 true norm1  in
                                  FStar_Util.bind_opt uu____7434
                                    (fun x1  ->
                                       let uu____7453 =
                                         let uu____7456 = unembed eb y  in
                                         uu____7456 true norm1  in
                                       FStar_Util.bind_opt uu____7453
                                         (fun y1  ->
                                            let uu____7472 =
                                              let uu____7473 =
                                                let uu____7480 = f x1 y1  in
                                                embed ec uu____7480  in
                                              uu____7473 rng shadow_app norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____7472))
                                   in
                                (match uu____7431 with
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
                    let uu____7626 = FStar_List.splitAt n_tvars args  in
                    match uu____7626 with
                    | (_tvar_args,rest_args) ->
                        let uu____7689 = FStar_List.hd rest_args  in
                        (match uu____7689 with
                         | (x,uu____7705) ->
                             let uu____7710 =
                               let uu____7717 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____7717  in
                             (match uu____7710 with
                              | (y,uu____7741) ->
                                  let uu____7746 =
                                    let uu____7753 =
                                      let uu____7762 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____7762  in
                                    FStar_List.hd uu____7753  in
                                  (match uu____7746 with
                                   | (z,uu____7792) ->
                                       let shadow_app =
                                         let uu____7802 =
                                           FStar_Common.mk_thunk
                                             (fun uu____7811  ->
                                                let uu____7812 =
                                                  let uu____7817 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____7817 args
                                                   in
                                                uu____7812
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____7802
                                          in
                                       let uu____7863 =
                                         let uu____7866 =
                                           let uu____7869 = unembed ea x  in
                                           uu____7869 true norm1  in
                                         FStar_Util.bind_opt uu____7866
                                           (fun x1  ->
                                              let uu____7885 =
                                                let uu____7888 = unembed eb y
                                                   in
                                                uu____7888 true norm1  in
                                              FStar_Util.bind_opt uu____7885
                                                (fun y1  ->
                                                   let uu____7904 =
                                                     let uu____7907 =
                                                       unembed ec z  in
                                                     uu____7907 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____7904
                                                     (fun z1  ->
                                                        let uu____7923 =
                                                          let uu____7924 =
                                                            let uu____7931 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____7931
                                                             in
                                                          uu____7924 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____7923)))
                                          in
                                       (match uu____7863 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____7983 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____7983 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____8006 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____8006 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  