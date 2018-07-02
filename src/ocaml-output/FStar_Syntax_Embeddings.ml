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
              (let uu____1601 = FStar_Options.eager_embedding ()  in
               if uu____1601
               then f ()
               else
                 (let thunk = FStar_Common.mk_thunk f  in
                  let uu____1612 =
                    let uu____1619 =
                      let uu____1620 =
                        let uu____1621 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____1621;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____1620  in
                    FStar_Syntax_Syntax.mk uu____1619  in
                  uu____1612 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____1736;
                  FStar_Syntax_Syntax.rng = uu____1737;_}
                ->
                let uu____1748 =
                  (et <> et') || (FStar_Options.eager_embedding ())  in
                if uu____1748
                then
                  let res =
                    let uu____1754 = FStar_Common.force_thunk t  in
                    f uu____1754  in
                  ((let uu____1798 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1798
                    then
                      let uu____1818 = emb_typ_to_string et  in
                      let uu____1819 = emb_typ_to_string et'  in
                      let uu____1820 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____1822 = pa x2  in
                            Prims.strcat "Some " uu____1822
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____1818 uu____1819 uu____1820
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____1829 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1829
                    then
                      let uu____1849 = emb_typ_to_string et  in
                      let uu____1850 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____1849 uu____1850
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____1854 ->
                let aopt = f x1  in
                ((let uu____1859 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____1859
                  then
                    let uu____1879 = emb_typ_to_string et  in
                    let uu____1880 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____1882 = pa a  in
                          Prims.strcat "Some " uu____1882
                       in
                    FStar_Util.print2
                      "Unembedding:\n\temb_typ=%s\n\tvalue is %s\n"
                      uu____1879 uu____1880
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____1957 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____1957
       then
         let uu____1977 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____1977
       else ());
      t  in
    let un t _w _n =
      (let uu____2002 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____2002
       then
         let uu____2022 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____2022
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____2111 =
    let uu____2112 =
      let uu____2119 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____2119, [])  in
    FStar_Syntax_Syntax.ET_app uu____2112  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____2111
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___209_2187 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___209_2187.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___209_2187.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____2215 ->
        (if w
         then
           (let uu____2217 =
              let uu____2222 =
                let uu____2223 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____2223  in
              (FStar_Errors.Warning_NotEmbedded, uu____2222)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2217)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2225 =
    let uu____2226 =
      let uu____2233 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____2233, [])  in
    FStar_Syntax_Syntax.ET_app uu____2226  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____2237  -> "()")
    uu____2225
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___210_2309 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___210_2309.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___210_2309.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____2340 ->
        (if w
         then
           (let uu____2342 =
              let uu____2347 =
                let uu____2348 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____2348  in
              (FStar_Errors.Warning_NotEmbedded, uu____2347)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2342)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2350 =
    let uu____2351 =
      let uu____2358 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____2358, [])  in
    FStar_Syntax_Syntax.ET_app uu____2351  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____2350
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___211_2430 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___211_2430.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___211_2430.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____2464 ->
        (if w
         then
           (let uu____2466 =
              let uu____2471 =
                let uu____2472 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____2472  in
              (FStar_Errors.Warning_NotEmbedded, uu____2471)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2466)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2475 =
    let uu____2476 =
      let uu____2483 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____2483, [])  in
    FStar_Syntax_Syntax.ET_app uu____2476  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____2475
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____2491 =
      let uu____2498 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____2498, [])  in
    FStar_Syntax_Syntax.ET_app uu____2491  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____2566  ->
         let uu____2567 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____2567)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____2601)) ->
             let uu____2614 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____2614
         | uu____2615 ->
             (if w
              then
                (let uu____2617 =
                   let uu____2622 =
                     let uu____2623 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____2623
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2622)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2617)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____2628 =
      let uu____2635 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____2635, [])  in
    FStar_Syntax_Syntax.ET_app uu____2628  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____2729)) -> FStar_Pervasives_Native.Some s
    | uu____2730 ->
        (if w
         then
           (let uu____2732 =
              let uu____2737 =
                let uu____2738 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____2738
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2737)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2732)
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
      let uu____2764 =
        let uu____2769 =
          let uu____2770 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____2770]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____2769  in
      uu____2764 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____2798 =
        let uu____2805 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____2805, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____2798  in
    let printer uu___207_2815 =
      match uu___207_2815 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____2819 =
            let uu____2820 = ea.print x  in Prims.strcat uu____2820 ")"  in
          Prims.strcat "(Some " uu____2819
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____2894  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____2895 =
                 let uu____2900 =
                   let uu____2901 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2901
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2902 =
                   let uu____2903 =
                     let uu____2912 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2912  in
                   [uu____2903]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2900 uu____2902  in
               uu____2895 FStar_Pervasives_Native.None rng
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
                        let uu____3001 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____3001  in
                      let uu____3002 =
                        let uu____3007 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____3008 =
                          let uu____3009 =
                            let uu____3018 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____3018  in
                          let uu____3019 =
                            let uu____3030 = FStar_Syntax_Syntax.as_arg t  in
                            [uu____3030]  in
                          uu____3009 :: uu____3019  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3007 uu____3008
                         in
                      uu____3002 FStar_Pervasives_Native.None rng)
                  in
               let uu____3065 =
                 let uu____3070 =
                   let uu____3071 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____3071
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____3072 =
                   let uu____3073 =
                     let uu____3082 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____3082  in
                   let uu____3083 =
                     let uu____3094 =
                       let uu____3103 =
                         let uu____3104 = embed ea a  in
                         uu____3104 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3103  in
                     [uu____3094]  in
                   uu____3073 :: uu____3083  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3070 uu____3072  in
               uu____3065 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____3239 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____3239 with
           | (hd1,args) ->
               let uu____3280 =
                 let uu____3295 =
                   let uu____3296 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____3296.FStar_Syntax_Syntax.n  in
                 (uu____3295, args)  in
               (match uu____3280 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3314) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____3338::(a,uu____3340)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____3391 =
                      let uu____3394 = unembed ea a  in uu____3394 w norm1
                       in
                    FStar_Util.bind_opt uu____3391
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____3413 ->
                    (if w
                     then
                       (let uu____3429 =
                          let uu____3434 =
                            let uu____3435 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____3435
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____3434)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____3429)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____3439 =
      let uu____3440 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____3440  in
    mk_emb_full em un uu____3439 printer emb_t_option_a
  
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
        let uu____3481 =
          let uu____3486 =
            let uu____3487 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____3496 =
              let uu____3507 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____3507]  in
            uu____3487 :: uu____3496  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____3486  in
        uu____3481 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____3543 =
          let uu____3550 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____3550, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____3543  in
      let printer uu____3562 =
        match uu____3562 with
        | (x,y) ->
            let uu____3569 = ea.print x  in
            let uu____3570 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____3569 uu____3570
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____3653  ->
             let proj i ab =
               let uu____3667 =
                 let uu____3672 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____3673 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____3672
                   uu____3673 i
                  in
               match uu____3667 with
               | (proj_1,uu____3677) ->
                   let proj_1_tm =
                     let uu____3679 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____3679  in
                   let uu____3680 =
                     let uu____3685 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____3686 =
                       let uu____3687 =
                         let uu____3696 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____3696  in
                       let uu____3697 =
                         let uu____3708 =
                           let uu____3717 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____3717  in
                         let uu____3718 =
                           let uu____3729 = FStar_Syntax_Syntax.as_arg ab  in
                           [uu____3729]  in
                         uu____3708 :: uu____3718  in
                       uu____3687 :: uu____3697  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3685 uu____3686  in
                   uu____3680 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____3888 =
               let uu____3893 =
                 let uu____3894 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3894
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____3895 =
                 let uu____3896 =
                   let uu____3905 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____3905  in
                 let uu____3906 =
                   let uu____3917 =
                     let uu____3926 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____3926  in
                   let uu____3927 =
                     let uu____3938 =
                       let uu____3947 =
                         let uu____3948 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____3948 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3947  in
                     let uu____4018 =
                       let uu____4029 =
                         let uu____4038 =
                           let uu____4039 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____4039 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4038  in
                       [uu____4029]  in
                     uu____3938 :: uu____4018  in
                   uu____3917 :: uu____3927  in
                 uu____3896 :: uu____3906  in
               FStar_Syntax_Syntax.mk_Tm_app uu____3893 uu____3895  in
             uu____3888 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____4202 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____4202 with
             | (hd1,args) ->
                 let uu____4245 =
                   let uu____4258 =
                     let uu____4259 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____4259.FStar_Syntax_Syntax.n  in
                   (uu____4258, args)  in
                 (match uu____4245 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____4277::uu____4278::(a,uu____4280)::(b,uu____4282)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____4341 =
                        let uu____4344 = unembed ea a  in uu____4344 w norm1
                         in
                      FStar_Util.bind_opt uu____4341
                        (fun a1  ->
                           let uu____4364 =
                             let uu____4367 = unembed eb b  in
                             uu____4367 w norm1  in
                           FStar_Util.bind_opt uu____4364
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____4390 ->
                      (if w
                       then
                         (let uu____4404 =
                            let uu____4409 =
                              let uu____4410 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____4410
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____4409)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____4404)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____4416 =
        let uu____4417 = type_of ea  in
        let uu____4418 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____4417 uu____4418  in
      mk_emb_full em un uu____4416 printer emb_t_pair_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____4445 =
        let uu____4450 =
          let uu____4451 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____4451]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____4450  in
      uu____4445 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____4479 =
        let uu____4486 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____4486, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4479  in
    let printer l =
      let uu____4499 =
        let uu____4500 =
          let uu____4501 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____4501 (FStar_String.concat "; ")  in
        Prims.strcat uu____4500 "]"  in
      Prims.strcat "[" uu____4499  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____4580  ->
           let t =
             let uu____4582 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____4582  in
           match l with
           | [] ->
               let uu____4583 =
                 let uu____4588 =
                   let uu____4589 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____4589
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____4588 [t]  in
               uu____4583 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____4613 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4613
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____4630 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____4630  in
                 let uu____4631 =
                   let uu____4636 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____4637 =
                     let uu____4638 =
                       let uu____4647 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____4647  in
                     let uu____4648 =
                       let uu____4659 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____4659]  in
                     uu____4638 :: uu____4648  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4636 uu____4637  in
                 uu____4631 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____4810 =
                 let uu____4815 =
                   let uu____4816 =
                     let uu____4827 =
                       let uu____4836 =
                         let uu____4837 = embed ea hd1  in
                         uu____4837 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____4836  in
                     let uu____4907 =
                       let uu____4918 =
                         let uu____4927 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4927  in
                       [uu____4918]  in
                     uu____4827 :: uu____4907  in
                   t :: uu____4816  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____4815  in
               uu____4810 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____5041 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____5041 with
           | (hd1,args) ->
               let uu____5082 =
                 let uu____5095 =
                   let uu____5096 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____5096.FStar_Syntax_Syntax.n  in
                 (uu____5095, args)  in
               (match uu____5082 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5112) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____5132,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____5133))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____5174 =
                      let uu____5177 = unembed ea hd2  in uu____5177 w norm1
                       in
                    FStar_Util.bind_opt uu____5174
                      (fun hd3  ->
                         let uu____5195 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____5195
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____5245 =
                      let uu____5248 = unembed ea hd2  in uu____5248 w norm1
                       in
                    FStar_Util.bind_opt uu____5245
                      (fun hd3  ->
                         let uu____5266 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____5266
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____5283 ->
                    (if w
                     then
                       (let uu____5297 =
                          let uu____5302 =
                            let uu____5303 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____5303
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____5302)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____5297)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____5307 =
      let uu____5308 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____5308  in
    mk_emb_full em un uu____5307 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____5339 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____5345 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____5351 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____5357 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____5363 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____5369 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____5375 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____5381 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____5390 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____5412 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____5432 -> false
  
let (__proj__UnfoldAttr__item___0 :
  norm_step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____5445 -> false 
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
    let uu____5449 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____5449  in
  let emb_t_norm_step =
    let uu____5451 =
      let uu____5458 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____5458, [])  in
    FStar_Syntax_Syntax.ET_app uu____5451  in
  let printer uu____5466 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____5531  ->
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
             let uu____5535 =
               let uu____5540 =
                 let uu____5541 =
                   let uu____5550 =
                     let uu____5551 =
                       let uu____5558 = e_list e_string  in
                       embed uu____5558 l  in
                     uu____5551 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5550  in
                 [uu____5541]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____5540  in
             uu____5535 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____5613 =
               let uu____5618 =
                 let uu____5619 =
                   let uu____5628 =
                     let uu____5629 =
                       let uu____5636 = e_list e_string  in
                       embed uu____5636 l  in
                     uu____5629 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5628  in
                 [uu____5619]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____5618  in
             uu____5613 FStar_Pervasives_Native.None rng
         | UnfoldAttr a ->
             let uu____5689 =
               let uu____5694 =
                 let uu____5695 = FStar_Syntax_Syntax.as_arg a  in
                 [uu____5695]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____5694  in
             uu____5689 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____5754 = FStar_Syntax_Util.head_and_args t1  in
         match uu____5754 with
         | (hd1,args) ->
             let uu____5799 =
               let uu____5814 =
                 let uu____5815 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____5815.FStar_Syntax_Syntax.n  in
               (uu____5814, args)  in
             (match uu____5799 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____6003)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____6038 =
                    let uu____6043 =
                      let uu____6052 = e_list e_string  in
                      unembed uu____6052 l  in
                    uu____6043 w norm1  in
                  FStar_Util.bind_opt uu____6038
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____6075)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____6110 =
                    let uu____6115 =
                      let uu____6124 = e_list e_string  in
                      unembed uu____6124 l  in
                    uu____6115 w norm1  in
                  FStar_Util.bind_opt uu____6110
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____6146::(a,uu____6148)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  -> FStar_Pervasives_Native.Some (UnfoldAttr a)
              | uu____6199 ->
                  (if w
                   then
                     (let uu____6215 =
                        let uu____6220 =
                          let uu____6221 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____6221
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____6220)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____6215)
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
    | uu____6316 ->
        (if w
         then
           (let uu____6318 =
              let uu____6323 =
                let uu____6324 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____6324  in
              (FStar_Errors.Warning_NotEmbedded, uu____6323)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____6318)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____6326 =
    let uu____6327 =
      let uu____6334 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____6334, [])  in
    FStar_Syntax_Syntax.ET_app uu____6327  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____6326
  
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
        let uu____6400 =
          let uu____6407 =
            let uu____6408 =
              let uu____6423 =
                let uu____6432 =
                  let uu____6439 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____6439, FStar_Pervasives_Native.None)  in
                [uu____6432]  in
              let uu____6454 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____6423, uu____6454)  in
            FStar_Syntax_Syntax.Tm_arrow uu____6408  in
          FStar_Syntax_Syntax.mk uu____6407  in
        uu____6400 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        let f_wrapped x =
          let shadow_app =
            map_shadow shadow_f
              (fun f1  ->
                 let uu____6621 =
                   let uu____6626 =
                     let uu____6627 = FStar_Syntax_Syntax.as_arg x  in
                     [uu____6627]  in
                   FStar_Syntax_Syntax.mk_Tm_app f1 uu____6626  in
                 uu____6621 FStar_Pervasives_Native.None rng)
             in
          let uu____6654 =
            let uu____6657 =
              let uu____6660 = unembed ea x  in uu____6660 true norm1  in
            FStar_Util.map_opt uu____6657
              (fun x1  ->
                 let uu____6699 =
                   let uu____6706 = f x1  in embed eb uu____6706  in
                 uu____6699 rng shadow_app norm1)
             in
          or_else uu____6654
            (fun uu____6772  ->
               let uu____6773 = force_shadow shadow_app  in
               match uu____6773 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise Embedding_failure
               | FStar_Pervasives_Native.Some app ->
                   norm1 (FStar_Util.Inr app))
           in
        lazy_embed (fun uu____6839  -> "<fun>") emb_t_arr_a_b rng t_arrow
          f_wrapped
          (fun uu____6844  ->
             let uu____6845 = force_shadow shadow_f  in
             match uu____6845 with
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
                 let uu____6959 = embed ea a  in
                 uu____6959 f1.FStar_Syntax_Syntax.pos
                   FStar_Pervasives_Native.None norm1
                  in
               let b_tm =
                 let uu____6992 =
                   let uu____6997 =
                     let uu____6998 =
                       let uu____7003 =
                         let uu____7004 = FStar_Syntax_Syntax.as_arg a_tm  in
                         [uu____7004]  in
                       FStar_Syntax_Syntax.mk_Tm_app f1 uu____7003  in
                     uu____6998 FStar_Pervasives_Native.None
                       f1.FStar_Syntax_Syntax.pos
                      in
                   FStar_Util.Inr uu____6997  in
                 norm1 uu____6992  in
               let uu____7031 =
                 let uu____7034 = unembed eb b_tm  in uu____7034 w norm1  in
               match uu____7031 with
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
                let uu____7131 = FStar_List.splitAt n_tvars args  in
                match uu____7131 with
                | (_tvar_args,rest_args) ->
                    let uu____7208 = FStar_List.hd rest_args  in
                    (match uu____7208 with
                     | (x,uu____7228) ->
                         let shadow_app =
                           let uu____7242 =
                             FStar_Common.mk_thunk
                               (fun uu____7251  ->
                                  let uu____7252 =
                                    let uu____7257 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____7257
                                      args
                                     in
                                  uu____7252 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____7242  in
                         let uu____7303 =
                           let uu____7306 =
                             let uu____7309 = unembed ea x  in
                             uu____7309 true norm1  in
                           FStar_Util.map_opt uu____7306
                             (fun x1  ->
                                let uu____7348 =
                                  let uu____7355 = f x1  in
                                  embed eb uu____7355  in
                                uu____7348 rng shadow_app norm1)
                            in
                         (match uu____7303 with
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
                  let uu____7482 = FStar_List.splitAt n_tvars args  in
                  match uu____7482 with
                  | (_tvar_args,rest_args) ->
                      let uu____7545 = FStar_List.hd rest_args  in
                      (match uu____7545 with
                       | (x,uu____7561) ->
                           let uu____7566 =
                             let uu____7573 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____7573  in
                           (match uu____7566 with
                            | (y,uu____7597) ->
                                let shadow_app =
                                  let uu____7607 =
                                    FStar_Common.mk_thunk
                                      (fun uu____7616  ->
                                         let uu____7617 =
                                           let uu____7622 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____7622 args
                                            in
                                         uu____7617
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____7607  in
                                let uu____7668 =
                                  let uu____7671 =
                                    let uu____7674 = unembed ea x  in
                                    uu____7674 true norm1  in
                                  FStar_Util.bind_opt uu____7671
                                    (fun x1  ->
                                       let uu____7690 =
                                         let uu____7693 = unembed eb y  in
                                         uu____7693 true norm1  in
                                       FStar_Util.bind_opt uu____7690
                                         (fun y1  ->
                                            let uu____7709 =
                                              let uu____7710 =
                                                let uu____7717 = f x1 y1  in
                                                embed ec uu____7717  in
                                              uu____7710 rng shadow_app norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____7709))
                                   in
                                (match uu____7668 with
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
                    let uu____7863 = FStar_List.splitAt n_tvars args  in
                    match uu____7863 with
                    | (_tvar_args,rest_args) ->
                        let uu____7926 = FStar_List.hd rest_args  in
                        (match uu____7926 with
                         | (x,uu____7942) ->
                             let uu____7947 =
                               let uu____7954 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____7954  in
                             (match uu____7947 with
                              | (y,uu____7978) ->
                                  let uu____7983 =
                                    let uu____7990 =
                                      let uu____7999 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____7999  in
                                    FStar_List.hd uu____7990  in
                                  (match uu____7983 with
                                   | (z,uu____8029) ->
                                       let shadow_app =
                                         let uu____8039 =
                                           FStar_Common.mk_thunk
                                             (fun uu____8048  ->
                                                let uu____8049 =
                                                  let uu____8054 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____8054 args
                                                   in
                                                uu____8049
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____8039
                                          in
                                       let uu____8100 =
                                         let uu____8103 =
                                           let uu____8106 = unembed ea x  in
                                           uu____8106 true norm1  in
                                         FStar_Util.bind_opt uu____8103
                                           (fun x1  ->
                                              let uu____8122 =
                                                let uu____8125 = unembed eb y
                                                   in
                                                uu____8125 true norm1  in
                                              FStar_Util.bind_opt uu____8122
                                                (fun y1  ->
                                                   let uu____8141 =
                                                     let uu____8144 =
                                                       unembed ec z  in
                                                     uu____8144 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____8141
                                                     (fun z1  ->
                                                        let uu____8160 =
                                                          let uu____8161 =
                                                            let uu____8168 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____8168
                                                             in
                                                          uu____8161 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____8160)))
                                          in
                                       (match uu____8100 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____8220 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____8220 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____8243 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____8243 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  