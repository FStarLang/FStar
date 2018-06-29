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
let lazy_embed :
  'Auu____1473 'a .
    'a printer ->
      FStar_Syntax_Syntax.emb_typ ->
        FStar_Range.range ->
          'Auu____1473 ->
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
              let uu____1522 = FStar_Options.eager_embedding ()  in
              if uu____1522
              then f ()
              else
                (let thunk = FStar_Common.mk_thunk f  in
                 let uu____1533 =
                   let uu____1540 =
                     let uu____1541 =
                       let uu____1542 = FStar_Dyn.mkdyn x  in
                       {
                         FStar_Syntax_Syntax.blob = uu____1542;
                         FStar_Syntax_Syntax.lkind =
                           (FStar_Syntax_Syntax.Lazy_embedding (et, thunk));
                         FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                         FStar_Syntax_Syntax.rng = rng
                       }  in
                     FStar_Syntax_Syntax.Tm_lazy uu____1541  in
                   FStar_Syntax_Syntax.mk uu____1540  in
                 uu____1533 FStar_Pervasives_Native.None rng)
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___205_1594  ->
    match uu___205_1594 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____1604 =
          let uu____1605 =
            let uu____1606 =
              let uu____1607 = FStar_List.map emb_typ_to_string args  in
              FStar_All.pipe_right uu____1607 (FStar_String.concat " ")  in
            Prims.strcat uu____1606 ")"  in
          Prims.strcat h uu____1605  in
        Prims.strcat "(" uu____1604
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____1614 =
          let uu____1615 = emb_typ_to_string a  in
          let uu____1616 =
            let uu____1617 = emb_typ_to_string b  in
            Prims.strcat "-> " uu____1617  in
          Prims.strcat uu____1615 uu____1616  in
        Prims.strcat "(" uu____1614
  
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
                  FStar_Syntax_Syntax.ltyp = uu____1685;
                  FStar_Syntax_Syntax.rng = uu____1686;_}
                ->
                let uu____1697 =
                  (FStar_Options.eager_embedding ()) || (et <> et')  in
                if uu____1697
                then
                  let uu____1700 = FStar_Common.force_thunk t  in
                  f uu____1700
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____1746 = FStar_Options.debug_any ()  in
                    if uu____1746
                    then
                      let uu____1747 = emb_typ_to_string et  in
                      FStar_Util.print1 "Unembed cancelled for %s\n"
                        uu____1747
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____1749 -> f x1
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm = t  in
    let un t _w _n = FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____1929 =
    let uu____1930 =
      let uu____1937 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____1937, [])  in
    FStar_Syntax_Syntax.ET_app uu____1930  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____1929
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___207_2005 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___207_2005.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___207_2005.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____2033 ->
        (if w
         then
           (let uu____2035 =
              let uu____2040 =
                let uu____2041 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____2041  in
              (FStar_Errors.Warning_NotEmbedded, uu____2040)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2035)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2043 =
    let uu____2044 =
      let uu____2051 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____2051, [])  in
    FStar_Syntax_Syntax.ET_app uu____2044  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____2055  -> "()")
    uu____2043
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___208_2127 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___208_2127.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___208_2127.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____2158 ->
        (if w
         then
           (let uu____2160 =
              let uu____2165 =
                let uu____2166 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____2166  in
              (FStar_Errors.Warning_NotEmbedded, uu____2165)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2160)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2168 =
    let uu____2169 =
      let uu____2176 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____2176, [])  in
    FStar_Syntax_Syntax.ET_app uu____2169  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____2168
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___209_2248 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___209_2248.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___209_2248.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____2282 ->
        (if w
         then
           (let uu____2284 =
              let uu____2289 =
                let uu____2290 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____2290  in
              (FStar_Errors.Warning_NotEmbedded, uu____2289)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2284)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2293 =
    let uu____2294 =
      let uu____2301 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____2301, [])  in
    FStar_Syntax_Syntax.ET_app uu____2294  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____2293
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____2309 =
      let uu____2316 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____2316, [])  in
    FStar_Syntax_Syntax.ET_app uu____2309  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____2384  ->
         let uu____2385 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____2385)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____2419)) ->
             let uu____2432 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____2432
         | uu____2433 ->
             (if w
              then
                (let uu____2435 =
                   let uu____2440 =
                     let uu____2441 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____2441
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2440)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2435)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____2446 =
      let uu____2453 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____2453, [])  in
    FStar_Syntax_Syntax.ET_app uu____2446  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____2547)) -> FStar_Pervasives_Native.Some s
    | uu____2548 ->
        (if w
         then
           (let uu____2550 =
              let uu____2555 =
                let uu____2556 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____2556
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2555)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2550)
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
      let uu____2582 =
        let uu____2587 =
          let uu____2588 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____2588]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____2587  in
      uu____2582 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____2616 =
        let uu____2623 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____2623, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____2616  in
    let printer uu___206_2633 =
      match uu___206_2633 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____2637 =
            let uu____2638 = ea.print x  in Prims.strcat uu____2638 ")"  in
          Prims.strcat "(Some " uu____2637
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____2714  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____2715 =
                 let uu____2720 =
                   let uu____2721 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2721
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2722 =
                   let uu____2723 =
                     let uu____2732 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2732  in
                   [uu____2723]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2720 uu____2722  in
               uu____2715 FStar_Pervasives_Native.None rng
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
                        let uu____2821 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____2821  in
                      let uu____2822 =
                        let uu____2827 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____2828 =
                          let uu____2829 =
                            let uu____2838 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____2838  in
                          let uu____2839 =
                            let uu____2850 = FStar_Syntax_Syntax.as_arg t  in
                            [uu____2850]  in
                          uu____2829 :: uu____2839  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____2827 uu____2828
                         in
                      uu____2822 FStar_Pervasives_Native.None rng)
                  in
               let uu____2885 =
                 let uu____2890 =
                   let uu____2891 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2891
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2892 =
                   let uu____2893 =
                     let uu____2902 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2902  in
                   let uu____2903 =
                     let uu____2914 =
                       let uu____2923 =
                         let uu____2924 = embed ea a  in
                         uu____2924 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____2923  in
                     [uu____2914]  in
                   uu____2893 :: uu____2903  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2890 uu____2892  in
               uu____2885 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____3059 = FStar_Syntax_Util.head_and_args t1  in
           match uu____3059 with
           | (hd1,args) ->
               let uu____3106 =
                 let uu____3121 =
                   let uu____3122 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____3122.FStar_Syntax_Syntax.n  in
                 (uu____3121, args)  in
               (match uu____3106 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3140) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____3164::(a,uu____3166)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____3217 =
                      let uu____3220 = unembed ea a  in uu____3220 w norm1
                       in
                    FStar_Util.bind_opt uu____3217
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____3239 ->
                    (if w
                     then
                       (let uu____3255 =
                          let uu____3260 =
                            let uu____3261 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____3261
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____3260)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____3255)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____3265 =
      let uu____3266 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____3266  in
    mk_emb_full em un uu____3265 printer emb_t_option_a
  
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
        let uu____3307 =
          let uu____3312 =
            let uu____3313 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____3322 =
              let uu____3333 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____3333]  in
            uu____3313 :: uu____3322  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____3312  in
        uu____3307 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____3369 =
          let uu____3376 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____3376, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____3369  in
      let printer uu____3388 =
        match uu____3388 with
        | (x,y) ->
            let uu____3395 = ea.print x  in
            let uu____3396 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____3395 uu____3396
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____3481  ->
             let proj i ab =
               let uu____3495 =
                 let uu____3500 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____3501 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____3500
                   uu____3501 i
                  in
               match uu____3495 with
               | (proj_1,uu____3505) ->
                   let proj_1_tm =
                     let uu____3507 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____3507  in
                   let uu____3508 =
                     let uu____3513 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____3514 =
                       let uu____3515 =
                         let uu____3524 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____3524  in
                       let uu____3525 =
                         let uu____3536 =
                           let uu____3545 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____3545  in
                         let uu____3546 =
                           let uu____3557 = FStar_Syntax_Syntax.as_arg ab  in
                           [uu____3557]  in
                         uu____3536 :: uu____3546  in
                       uu____3515 :: uu____3525  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3513 uu____3514  in
                   uu____3508 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____3716 =
               let uu____3721 =
                 let uu____3722 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3722
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____3723 =
                 let uu____3724 =
                   let uu____3733 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____3733  in
                 let uu____3734 =
                   let uu____3745 =
                     let uu____3754 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____3754  in
                   let uu____3755 =
                     let uu____3766 =
                       let uu____3775 =
                         let uu____3776 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____3776 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3775  in
                     let uu____3846 =
                       let uu____3857 =
                         let uu____3866 =
                           let uu____3867 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____3867 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____3866  in
                       [uu____3857]  in
                     uu____3766 :: uu____3846  in
                   uu____3745 :: uu____3755  in
                 uu____3724 :: uu____3734  in
               FStar_Syntax_Syntax.mk_Tm_app uu____3721 uu____3723  in
             uu____3716 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____4030 = FStar_Syntax_Util.head_and_args t1  in
             match uu____4030 with
             | (hd1,args) ->
                 let uu____4079 =
                   let uu____4092 =
                     let uu____4093 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____4093.FStar_Syntax_Syntax.n  in
                   (uu____4092, args)  in
                 (match uu____4079 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____4111::uu____4112::(a,uu____4114)::(b,uu____4116)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____4175 =
                        let uu____4178 = unembed ea a  in uu____4178 w norm1
                         in
                      FStar_Util.bind_opt uu____4175
                        (fun a1  ->
                           let uu____4198 =
                             let uu____4201 = unembed eb b  in
                             uu____4201 w norm1  in
                           FStar_Util.bind_opt uu____4198
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____4224 ->
                      (if w
                       then
                         (let uu____4238 =
                            let uu____4243 =
                              let uu____4244 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____4244
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____4243)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____4238)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____4250 =
        let uu____4251 = type_of ea  in
        let uu____4252 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____4251 uu____4252  in
      mk_emb_full em un uu____4250 printer emb_t_pair_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____4279 =
        let uu____4284 =
          let uu____4285 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____4285]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____4284  in
      uu____4279 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____4313 =
        let uu____4320 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____4320, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4313  in
    let printer l =
      let uu____4333 =
        let uu____4334 =
          let uu____4335 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____4335 (FStar_String.concat "; ")  in
        Prims.strcat uu____4334 "]"  in
      Prims.strcat "[" uu____4333  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____4416  ->
           let t =
             let uu____4418 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____4418  in
           match l with
           | [] ->
               let uu____4419 =
                 let uu____4424 =
                   let uu____4425 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____4425
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____4424 [t]  in
               uu____4419 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____4449 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4449
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____4466 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____4466  in
                 let uu____4467 =
                   let uu____4472 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____4473 =
                     let uu____4474 =
                       let uu____4483 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____4483  in
                     let uu____4484 =
                       let uu____4495 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____4495]  in
                     uu____4474 :: uu____4484  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4472 uu____4473  in
                 uu____4467 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____4646 =
                 let uu____4651 =
                   let uu____4652 =
                     let uu____4663 =
                       let uu____4672 =
                         let uu____4673 = embed ea hd1  in
                         uu____4673 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____4672  in
                     let uu____4743 =
                       let uu____4754 =
                         let uu____4763 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4763  in
                       [uu____4754]  in
                     uu____4663 :: uu____4743  in
                   t :: uu____4652  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____4651  in
               uu____4646 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____4877 = FStar_Syntax_Util.head_and_args t1  in
           match uu____4877 with
           | (hd1,args) ->
               let uu____4924 =
                 let uu____4937 =
                   let uu____4938 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____4938.FStar_Syntax_Syntax.n  in
                 (uu____4937, args)  in
               (match uu____4924 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4954) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____4974,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____4975))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____5016 =
                      let uu____5019 = unembed ea hd2  in uu____5019 w norm1
                       in
                    FStar_Util.bind_opt uu____5016
                      (fun hd3  ->
                         let uu____5037 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____5037
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____5087 =
                      let uu____5090 = unembed ea hd2  in uu____5090 w norm1
                       in
                    FStar_Util.bind_opt uu____5087
                      (fun hd3  ->
                         let uu____5108 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____5108
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____5125 ->
                    (if w
                     then
                       (let uu____5139 =
                          let uu____5144 =
                            let uu____5145 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____5145
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____5144)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____5139)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____5149 =
      let uu____5150 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____5150  in
    mk_emb_full em un uu____5149 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____5181 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____5187 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____5193 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____5199 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____5205 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____5211 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____5217 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____5226 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____5248 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____5268 -> false
  
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
    let uu____5279 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____5279  in
  let emb_t_norm_step =
    let uu____5281 =
      let uu____5288 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____5288, [])  in
    FStar_Syntax_Syntax.ET_app uu____5281  in
  let printer uu____5296 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____5361  ->
         match n1 with
         | Simpl  -> steps_Simpl
         | Weak  -> steps_Weak
         | HNF  -> steps_HNF
         | Primops  -> steps_Primops
         | Delta  -> steps_Delta
         | Zeta  -> steps_Zeta
         | Iota  -> steps_Iota
         | UnfoldOnly l ->
             let uu____5365 =
               let uu____5370 =
                 let uu____5371 =
                   let uu____5380 =
                     let uu____5381 =
                       let uu____5388 = e_list e_string  in
                       embed uu____5388 l  in
                     uu____5381 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5380  in
                 [uu____5371]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____5370  in
             uu____5365 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
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
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____5448  in
             uu____5443 FStar_Pervasives_Native.None rng
         | UnfoldAttr a ->
             let uu____5519 =
               let uu____5524 =
                 let uu____5525 = FStar_Syntax_Syntax.as_arg a  in
                 [uu____5525]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____5524  in
             uu____5519 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____5584 = FStar_Syntax_Util.head_and_args t1  in
         match uu____5584 with
         | (hd1,args) ->
             let uu____5629 =
               let uu____5644 =
                 let uu____5645 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____5645.FStar_Syntax_Syntax.n  in
               (uu____5644, args)  in
             (match uu____5629 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5795)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____5830 =
                    let uu____5835 =
                      let uu____5844 = e_list e_string  in
                      unembed uu____5844 l  in
                    uu____5835 w norm1  in
                  FStar_Util.bind_opt uu____5830
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5867)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____5902 =
                    let uu____5907 =
                      let uu____5916 = e_list e_string  in
                      unembed uu____5916 l  in
                    uu____5907 w norm1  in
                  FStar_Util.bind_opt uu____5902
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5938::(a,uu____5940)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  -> FStar_Pervasives_Native.Some (UnfoldAttr a)
              | uu____5991 ->
                  (if w
                   then
                     (let uu____6007 =
                        let uu____6012 =
                          let uu____6013 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____6013
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____6012)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____6007)
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
    | uu____6108 ->
        (if w
         then
           (let uu____6110 =
              let uu____6115 =
                let uu____6116 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____6116  in
              (FStar_Errors.Warning_NotEmbedded, uu____6115)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____6110)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____6118 =
    let uu____6119 =
      let uu____6126 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____6126, [])  in
    FStar_Syntax_Syntax.ET_app uu____6119  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____6118
  
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
        let uu____6192 =
          let uu____6199 =
            let uu____6200 =
              let uu____6215 =
                let uu____6224 =
                  let uu____6231 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____6231, FStar_Pervasives_Native.None)  in
                [uu____6224]  in
              let uu____6246 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____6215, uu____6246)  in
            FStar_Syntax_Syntax.Tm_arrow uu____6200  in
          FStar_Syntax_Syntax.mk uu____6199  in
        uu____6192 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        let f_wrapped x =
          let shadow_app =
            map_shadow shadow_f
              (fun f1  ->
                 let uu____6413 =
                   let uu____6418 =
                     let uu____6419 = FStar_Syntax_Syntax.as_arg x  in
                     [uu____6419]  in
                   FStar_Syntax_Syntax.mk_Tm_app f1 uu____6418  in
                 uu____6413 FStar_Pervasives_Native.None rng)
             in
          let uu____6446 =
            let uu____6449 =
              let uu____6452 = unembed ea x  in uu____6452 true norm1  in
            FStar_Util.map_opt uu____6449
              (fun x1  ->
                 let uu____6491 =
                   let uu____6498 = f x1  in embed eb uu____6498  in
                 uu____6491 rng shadow_app norm1)
             in
          or_else uu____6446
            (fun uu____6564  ->
               let uu____6565 = force_shadow shadow_app  in
               match uu____6565 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise Embedding_failure
               | FStar_Pervasives_Native.Some app ->
                   norm1 (FStar_Util.Inr app))
           in
        lazy_embed (fun uu____6633  -> "<fun>") emb_t_arr_a_b rng t_arrow
          f_wrapped
          (fun uu____6638  ->
             let uu____6639 = force_shadow shadow_f  in
             match uu____6639 with
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
                 let uu____6753 = embed ea a  in
                 uu____6753 f1.FStar_Syntax_Syntax.pos
                   FStar_Pervasives_Native.None norm1
                  in
               let b_tm =
                 let uu____6786 =
                   let uu____6791 =
                     let uu____6792 =
                       let uu____6797 =
                         let uu____6798 = FStar_Syntax_Syntax.as_arg a_tm  in
                         [uu____6798]  in
                       FStar_Syntax_Syntax.mk_Tm_app f1 uu____6797  in
                     uu____6792 FStar_Pervasives_Native.None
                       f1.FStar_Syntax_Syntax.pos
                      in
                   FStar_Util.Inr uu____6791  in
                 norm1 uu____6786  in
               let uu____6825 =
                 let uu____6828 = unembed eb b_tm  in uu____6828 w norm1  in
               match uu____6825 with
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
                let uu____6925 = FStar_List.splitAt n_tvars args  in
                match uu____6925 with
                | (_tvar_args,rest_args) ->
                    let uu____7002 = FStar_List.hd rest_args  in
                    (match uu____7002 with
                     | (x,uu____7022) ->
                         let shadow_app =
                           let uu____7036 =
                             FStar_Common.mk_thunk
                               (fun uu____7045  ->
                                  let uu____7046 =
                                    let uu____7051 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____7051
                                      args
                                     in
                                  uu____7046 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____7036  in
                         let uu____7097 =
                           let uu____7100 =
                             let uu____7103 = unembed ea x  in
                             uu____7103 true norm1  in
                           FStar_Util.map_opt uu____7100
                             (fun x1  ->
                                let uu____7142 =
                                  let uu____7149 = f x1  in
                                  embed eb uu____7149  in
                                uu____7142 rng shadow_app norm1)
                            in
                         (match uu____7097 with
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
                  let uu____7276 = FStar_List.splitAt n_tvars args  in
                  match uu____7276 with
                  | (_tvar_args,rest_args) ->
                      let uu____7339 = FStar_List.hd rest_args  in
                      (match uu____7339 with
                       | (x,uu____7355) ->
                           let uu____7360 =
                             let uu____7367 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____7367  in
                           (match uu____7360 with
                            | (y,uu____7391) ->
                                let shadow_app =
                                  let uu____7401 =
                                    FStar_Common.mk_thunk
                                      (fun uu____7410  ->
                                         let uu____7411 =
                                           let uu____7416 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____7416 args
                                            in
                                         uu____7411
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____7401  in
                                let uu____7462 =
                                  let uu____7465 =
                                    let uu____7468 = unembed ea x  in
                                    uu____7468 true norm1  in
                                  FStar_Util.bind_opt uu____7465
                                    (fun x1  ->
                                       let uu____7484 =
                                         let uu____7487 = unembed eb y  in
                                         uu____7487 true norm1  in
                                       FStar_Util.bind_opt uu____7484
                                         (fun y1  ->
                                            let uu____7503 =
                                              let uu____7504 =
                                                let uu____7511 = f x1 y1  in
                                                embed ec uu____7511  in
                                              uu____7504 rng shadow_app norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____7503))
                                   in
                                (match uu____7462 with
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
                    let uu____7657 = FStar_List.splitAt n_tvars args  in
                    match uu____7657 with
                    | (_tvar_args,rest_args) ->
                        let uu____7720 = FStar_List.hd rest_args  in
                        (match uu____7720 with
                         | (x,uu____7736) ->
                             let uu____7741 =
                               let uu____7748 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____7748  in
                             (match uu____7741 with
                              | (y,uu____7772) ->
                                  let uu____7777 =
                                    let uu____7784 =
                                      let uu____7793 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____7793  in
                                    FStar_List.hd uu____7784  in
                                  (match uu____7777 with
                                   | (z,uu____7823) ->
                                       let shadow_app =
                                         let uu____7833 =
                                           FStar_Common.mk_thunk
                                             (fun uu____7842  ->
                                                let uu____7843 =
                                                  let uu____7848 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____7848 args
                                                   in
                                                uu____7843
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____7833
                                          in
                                       let uu____7894 =
                                         let uu____7897 =
                                           let uu____7900 = unembed ea x  in
                                           uu____7900 true norm1  in
                                         FStar_Util.bind_opt uu____7897
                                           (fun x1  ->
                                              let uu____7916 =
                                                let uu____7919 = unembed eb y
                                                   in
                                                uu____7919 true norm1  in
                                              FStar_Util.bind_opt uu____7916
                                                (fun y1  ->
                                                   let uu____7935 =
                                                     let uu____7938 =
                                                       unembed ec z  in
                                                     uu____7938 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____7935
                                                     (fun z1  ->
                                                        let uu____7954 =
                                                          let uu____7955 =
                                                            let uu____7962 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____7962
                                                             in
                                                          uu____7955 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____7954)))
                                          in
                                       (match uu____7894 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  