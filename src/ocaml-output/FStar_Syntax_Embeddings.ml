open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___206_13  ->
    match uu___206_13 with
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
      let uu___209_1478 = e  in
      {
        em = (uu___209_1478.em);
        un = (uu___209_1478.un);
        typ = ty;
        print = (uu___209_1478.print);
        emb_typ = (uu___209_1478.emb_typ)
      }
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___207_1485  ->
    match uu___207_1485 with
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
    let uu___210_2225 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___210_2225.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___210_2225.FStar_Syntax_Syntax.vars)
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
    let uu___211_2347 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___211_2347.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___211_2347.FStar_Syntax_Syntax.vars)
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
    let uu___212_2468 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___212_2468.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___212_2468.FStar_Syntax_Syntax.vars)
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
    let printer uu___208_2853 =
      match uu___208_2853 with
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
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____4499 =
          let uu____4504 =
            let uu____4505 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____4514 =
              let uu____4525 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____4525]  in
            uu____4505 :: uu____4514  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____4504  in
        uu____4499 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____4561 =
          let uu____4568 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____4568, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4561  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____4586 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____4586
        | FStar_Util.Inr b ->
            let uu____4588 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____4588
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____4674  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____4744 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____4744  in
                         let uu____4745 =
                           let uu____4750 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____4751 =
                             let uu____4752 =
                               let uu____4761 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____4761  in
                             let uu____4762 =
                               let uu____4773 =
                                 let uu____4782 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____4782  in
                               let uu____4783 =
                                 let uu____4794 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____4794]  in
                               uu____4773 :: uu____4783  in
                             uu____4752 :: uu____4762  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____4750
                             uu____4751
                            in
                         uu____4745 FStar_Pervasives_Native.None rng)
                     in
                  let uu____4837 =
                    let uu____4842 =
                      let uu____4843 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____4843
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____4844 =
                      let uu____4845 =
                        let uu____4854 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____4854  in
                      let uu____4855 =
                        let uu____4866 =
                          let uu____4875 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____4875  in
                        let uu____4876 =
                          let uu____4887 =
                            let uu____4896 =
                              let uu____4897 = embed ea a  in
                              uu____4897 rng shadow_a norm1  in
                            FStar_Syntax_Syntax.as_arg uu____4896  in
                          [uu____4887]  in
                        uu____4866 :: uu____4876  in
                      uu____4845 :: uu____4855  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____4842 uu____4844  in
                  uu____4837 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____5002  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____5072 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____5072  in
                         let uu____5073 =
                           let uu____5078 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____5079 =
                             let uu____5080 =
                               let uu____5089 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____5089  in
                             let uu____5090 =
                               let uu____5101 =
                                 let uu____5110 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____5110  in
                               let uu____5111 =
                                 let uu____5122 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____5122]  in
                               uu____5101 :: uu____5111  in
                             uu____5080 :: uu____5090  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____5078
                             uu____5079
                            in
                         uu____5073 FStar_Pervasives_Native.None rng)
                     in
                  let uu____5165 =
                    let uu____5170 =
                      let uu____5171 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____5171
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____5172 =
                      let uu____5173 =
                        let uu____5182 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____5182  in
                      let uu____5183 =
                        let uu____5194 =
                          let uu____5203 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____5203  in
                        let uu____5204 =
                          let uu____5215 =
                            let uu____5224 =
                              let uu____5225 = embed eb b  in
                              uu____5225 rng shadow_b norm1  in
                            FStar_Syntax_Syntax.as_arg uu____5224  in
                          [uu____5215]  in
                        uu____5194 :: uu____5204  in
                      uu____5173 :: uu____5183  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____5170 uu____5172  in
                  uu____5165 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____5378 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____5378 with
             | (hd1,args) ->
                 let uu____5421 =
                   let uu____5436 =
                     let uu____5437 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____5437.FStar_Syntax_Syntax.n  in
                   (uu____5436, args)  in
                 (match uu____5421 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____5457::uu____5458::(a,uu____5460)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____5527 =
                        let uu____5530 = unembed ea a  in uu____5530 w norm1
                         in
                      FStar_Util.bind_opt uu____5527
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____5554::uu____5555::(b,uu____5557)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____5624 =
                        let uu____5627 = unembed eb b  in uu____5627 w norm1
                         in
                      FStar_Util.bind_opt uu____5624
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____5650 ->
                      (if w
                       then
                         (let uu____5666 =
                            let uu____5671 =
                              let uu____5672 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____5672
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____5671)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____5666)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____5678 =
        let uu____5679 = type_of ea  in
        let uu____5680 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____5679 uu____5680  in
      mk_emb_full em un uu____5678 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____5707 =
        let uu____5712 =
          let uu____5713 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____5713]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____5712  in
      uu____5707 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____5741 =
        let uu____5748 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____5748, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____5741  in
    let printer l =
      let uu____5761 =
        let uu____5762 =
          let uu____5763 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____5763 (FStar_String.concat "; ")  in
        Prims.strcat uu____5762 "]"  in
      Prims.strcat "[" uu____5761  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____5842  ->
           let t =
             let uu____5844 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____5844  in
           match l with
           | [] ->
               let uu____5845 =
                 let uu____5850 =
                   let uu____5851 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____5851
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____5850 [t]  in
               uu____5845 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____5875 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____5875
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____5892 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____5892  in
                 let uu____5893 =
                   let uu____5898 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____5899 =
                     let uu____5900 =
                       let uu____5909 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____5909  in
                     let uu____5910 =
                       let uu____5921 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____5921]  in
                     uu____5900 :: uu____5910  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____5898 uu____5899  in
                 uu____5893 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____6072 =
                 let uu____6077 =
                   let uu____6078 =
                     let uu____6089 =
                       let uu____6098 =
                         let uu____6099 = embed ea hd1  in
                         uu____6099 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____6098  in
                     let uu____6169 =
                       let uu____6180 =
                         let uu____6189 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____6189  in
                       [uu____6180]  in
                     uu____6089 :: uu____6169  in
                   t :: uu____6078  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____6077  in
               uu____6072 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____6303 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____6303 with
           | (hd1,args) ->
               let uu____6344 =
                 let uu____6357 =
                   let uu____6358 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____6358.FStar_Syntax_Syntax.n  in
                 (uu____6357, args)  in
               (match uu____6344 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6374) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____6394,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____6395))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____6436 =
                      let uu____6439 = unembed ea hd2  in uu____6439 w norm1
                       in
                    FStar_Util.bind_opt uu____6436
                      (fun hd3  ->
                         let uu____6457 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____6457
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____6507 =
                      let uu____6510 = unembed ea hd2  in uu____6510 w norm1
                       in
                    FStar_Util.bind_opt uu____6507
                      (fun hd3  ->
                         let uu____6528 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____6528
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____6545 ->
                    (if w
                     then
                       (let uu____6559 =
                          let uu____6564 =
                            let uu____6565 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____6565
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____6564)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____6559)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____6569 =
      let uu____6570 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____6570  in
    mk_emb_full em un uu____6569 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____6601 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____6607 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____6613 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____6619 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____6625 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____6631 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____6637 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____6643 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____6652 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____6674 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____6694 -> false
  
let (__proj__UnfoldAttr__item___0 :
  norm_step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____6707 -> false 
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
    let uu____6711 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____6711  in
  let emb_t_norm_step =
    let uu____6713 =
      let uu____6720 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____6720, [])  in
    FStar_Syntax_Syntax.ET_app uu____6713  in
  let printer uu____6728 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____6793  ->
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
             let uu____6797 =
               let uu____6802 =
                 let uu____6803 =
                   let uu____6812 =
                     let uu____6813 =
                       let uu____6820 = e_list e_string  in
                       embed uu____6820 l  in
                     uu____6813 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____6812  in
                 [uu____6803]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____6802  in
             uu____6797 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____6875 =
               let uu____6880 =
                 let uu____6881 =
                   let uu____6890 =
                     let uu____6891 =
                       let uu____6898 = e_list e_string  in
                       embed uu____6898 l  in
                     uu____6891 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____6890  in
                 [uu____6881]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____6880  in
             uu____6875 FStar_Pervasives_Native.None rng
         | UnfoldAttr a ->
             let uu____6951 =
               let uu____6956 =
                 let uu____6957 = FStar_Syntax_Syntax.as_arg a  in
                 [uu____6957]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____6956  in
             uu____6951 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____7016 = FStar_Syntax_Util.head_and_args t1  in
         match uu____7016 with
         | (hd1,args) ->
             let uu____7061 =
               let uu____7076 =
                 let uu____7077 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____7077.FStar_Syntax_Syntax.n  in
               (uu____7076, args)  in
             (match uu____7061 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7265)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____7300 =
                    let uu____7305 =
                      let uu____7314 = e_list e_string  in
                      unembed uu____7314 l  in
                    uu____7305 w norm1  in
                  FStar_Util.bind_opt uu____7300
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7337)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____7372 =
                    let uu____7377 =
                      let uu____7386 = e_list e_string  in
                      unembed uu____7386 l  in
                    uu____7377 w norm1  in
                  FStar_Util.bind_opt uu____7372
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____7408::(a,uu____7410)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  -> FStar_Pervasives_Native.Some (UnfoldAttr a)
              | uu____7461 ->
                  (if w
                   then
                     (let uu____7477 =
                        let uu____7482 =
                          let uu____7483 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____7483
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____7482)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____7477)
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
    | uu____7578 ->
        (if w
         then
           (let uu____7580 =
              let uu____7585 =
                let uu____7586 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____7586  in
              (FStar_Errors.Warning_NotEmbedded, uu____7585)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____7580)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____7588 =
    let uu____7589 =
      let uu____7596 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____7596, [])  in
    FStar_Syntax_Syntax.ET_app uu____7589  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____7588
  
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
        let uu____7662 =
          let uu____7669 =
            let uu____7670 =
              let uu____7685 =
                let uu____7694 =
                  let uu____7701 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____7701, FStar_Pervasives_Native.None)  in
                [uu____7694]  in
              let uu____7716 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____7685, uu____7716)  in
            FStar_Syntax_Syntax.Tm_arrow uu____7670  in
          FStar_Syntax_Syntax.mk uu____7669  in
        uu____7662 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____7827  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____7832  ->
             let uu____7833 = force_shadow shadow_f  in
             match uu____7833 with
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
                 let uu____7946 = embed ea a  in
                 uu____7946 f1.FStar_Syntax_Syntax.pos
                   FStar_Pervasives_Native.None norm1
                  in
               let b_tm =
                 let uu____7979 =
                   let uu____7984 =
                     let uu____7985 =
                       let uu____7990 =
                         let uu____7991 = FStar_Syntax_Syntax.as_arg a_tm  in
                         [uu____7991]  in
                       FStar_Syntax_Syntax.mk_Tm_app f1 uu____7990  in
                     uu____7985 FStar_Pervasives_Native.None
                       f1.FStar_Syntax_Syntax.pos
                      in
                   FStar_Util.Inr uu____7984  in
                 norm1 uu____7979  in
               let uu____8018 =
                 let uu____8021 = unembed eb b_tm  in uu____8021 w norm1  in
               match uu____8018 with
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
                let uu____8118 = FStar_List.splitAt n_tvars args  in
                match uu____8118 with
                | (_tvar_args,rest_args) ->
                    let uu____8195 = FStar_List.hd rest_args  in
                    (match uu____8195 with
                     | (x,uu____8215) ->
                         let shadow_app =
                           let uu____8229 =
                             FStar_Common.mk_thunk
                               (fun uu____8238  ->
                                  let uu____8239 =
                                    let uu____8244 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____8244
                                      args
                                     in
                                  uu____8239 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____8229  in
                         let uu____8290 =
                           let uu____8293 =
                             let uu____8296 = unembed ea x  in
                             uu____8296 true norm1  in
                           FStar_Util.map_opt uu____8293
                             (fun x1  ->
                                let uu____8335 =
                                  let uu____8342 = f x1  in
                                  embed eb uu____8342  in
                                uu____8335 rng shadow_app norm1)
                            in
                         (match uu____8290 with
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
                  let uu____8469 = FStar_List.splitAt n_tvars args  in
                  match uu____8469 with
                  | (_tvar_args,rest_args) ->
                      let uu____8532 = FStar_List.hd rest_args  in
                      (match uu____8532 with
                       | (x,uu____8548) ->
                           let uu____8553 =
                             let uu____8560 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____8560  in
                           (match uu____8553 with
                            | (y,uu____8584) ->
                                let shadow_app =
                                  let uu____8594 =
                                    FStar_Common.mk_thunk
                                      (fun uu____8603  ->
                                         let uu____8604 =
                                           let uu____8609 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____8609 args
                                            in
                                         uu____8604
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____8594  in
                                let uu____8655 =
                                  let uu____8658 =
                                    let uu____8661 = unembed ea x  in
                                    uu____8661 true norm1  in
                                  FStar_Util.bind_opt uu____8658
                                    (fun x1  ->
                                       let uu____8677 =
                                         let uu____8680 = unembed eb y  in
                                         uu____8680 true norm1  in
                                       FStar_Util.bind_opt uu____8677
                                         (fun y1  ->
                                            let uu____8696 =
                                              let uu____8697 =
                                                let uu____8704 = f x1 y1  in
                                                embed ec uu____8704  in
                                              uu____8697 rng shadow_app norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____8696))
                                   in
                                (match uu____8655 with
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
                    let uu____8850 = FStar_List.splitAt n_tvars args  in
                    match uu____8850 with
                    | (_tvar_args,rest_args) ->
                        let uu____8913 = FStar_List.hd rest_args  in
                        (match uu____8913 with
                         | (x,uu____8929) ->
                             let uu____8934 =
                               let uu____8941 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____8941  in
                             (match uu____8934 with
                              | (y,uu____8965) ->
                                  let uu____8970 =
                                    let uu____8977 =
                                      let uu____8986 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____8986  in
                                    FStar_List.hd uu____8977  in
                                  (match uu____8970 with
                                   | (z,uu____9016) ->
                                       let shadow_app =
                                         let uu____9026 =
                                           FStar_Common.mk_thunk
                                             (fun uu____9035  ->
                                                let uu____9036 =
                                                  let uu____9041 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____9041 args
                                                   in
                                                uu____9036
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____9026
                                          in
                                       let uu____9087 =
                                         let uu____9090 =
                                           let uu____9093 = unembed ea x  in
                                           uu____9093 true norm1  in
                                         FStar_Util.bind_opt uu____9090
                                           (fun x1  ->
                                              let uu____9109 =
                                                let uu____9112 = unembed eb y
                                                   in
                                                uu____9112 true norm1  in
                                              FStar_Util.bind_opt uu____9109
                                                (fun y1  ->
                                                   let uu____9128 =
                                                     let uu____9131 =
                                                       unembed ec z  in
                                                     uu____9131 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____9128
                                                     (fun z1  ->
                                                        let uu____9147 =
                                                          let uu____9148 =
                                                            let uu____9155 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____9155
                                                             in
                                                          uu____9148 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____9147)))
                                          in
                                       (match uu____9087 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____9207 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____9207 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____9230 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____9230 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  