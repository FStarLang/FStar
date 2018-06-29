open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___203_13  ->
    match uu___203_13 with
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
              (let uu____1520 = FStar_Syntax_Print.term_to_string ta  in
               let uu____1521 = pa x  in
               let uu____1524 =
                 let uu____1525 = f ()  in
                 FStar_Syntax_Print.term_to_string uu____1525  in
               FStar_Util.print3
                 "Embedding a %s\n\tvalue is %s\nthunked as a %s\n"
                 uu____1520 uu____1521 uu____1524);
              (let uu____1526 = FStar_Options.eager_embedding ()  in
               if uu____1526
               then f ()
               else
                 (let thunk = FStar_Common.mk_thunk f  in
                  let uu____1537 =
                    let uu____1544 =
                      let uu____1545 =
                        let uu____1546 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____1546;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____1545  in
                    FStar_Syntax_Syntax.mk uu____1544  in
                  uu____1537 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____1661;
                  FStar_Syntax_Syntax.rng = uu____1662;_}
                ->
                let uu____1673 =
                  (FStar_Options.eager_embedding ()) || (et <> et')  in
                if uu____1673
                then
                  let uu____1676 = FStar_Common.force_thunk t  in
                  f uu____1676
                else
                  (let a = FStar_Dyn.undyn b  in
                   FStar_Pervasives_Native.Some a)
            | uu____1721 -> f x1
  
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
  let uu____1901 =
    let uu____1902 =
      let uu____1909 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____1909, [])  in
    FStar_Syntax_Syntax.ET_app uu____1902  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____1901
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___205_1977 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___205_1977.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___205_1977.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____2005 ->
        (if w
         then
           (let uu____2007 =
              let uu____2012 =
                let uu____2013 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____2013  in
              (FStar_Errors.Warning_NotEmbedded, uu____2012)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2007)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2015 =
    let uu____2016 =
      let uu____2023 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____2023, [])  in
    FStar_Syntax_Syntax.ET_app uu____2016  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____2027  -> "()")
    uu____2015
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___206_2099 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___206_2099.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___206_2099.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____2130 ->
        (if w
         then
           (let uu____2132 =
              let uu____2137 =
                let uu____2138 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____2138  in
              (FStar_Errors.Warning_NotEmbedded, uu____2137)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2132)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2140 =
    let uu____2141 =
      let uu____2148 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____2148, [])  in
    FStar_Syntax_Syntax.ET_app uu____2141  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____2140
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___207_2220 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___207_2220.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___207_2220.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____2254 ->
        (if w
         then
           (let uu____2256 =
              let uu____2261 =
                let uu____2262 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____2262  in
              (FStar_Errors.Warning_NotEmbedded, uu____2261)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2256)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2265 =
    let uu____2266 =
      let uu____2273 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____2273, [])  in
    FStar_Syntax_Syntax.ET_app uu____2266  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____2265
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____2281 =
      let uu____2288 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____2288, [])  in
    FStar_Syntax_Syntax.ET_app uu____2281  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____2356  ->
         let uu____2357 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____2357)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____2391)) ->
             let uu____2404 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____2404
         | uu____2405 ->
             (if w
              then
                (let uu____2407 =
                   let uu____2412 =
                     let uu____2413 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____2413
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2412)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2407)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____2418 =
      let uu____2425 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____2425, [])  in
    FStar_Syntax_Syntax.ET_app uu____2418  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____2519)) -> FStar_Pervasives_Native.Some s
    | uu____2520 ->
        (if w
         then
           (let uu____2522 =
              let uu____2527 =
                let uu____2528 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____2528
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2527)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2522)
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
      let uu____2554 =
        let uu____2559 =
          let uu____2560 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____2560]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____2559  in
      uu____2554 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____2588 =
        let uu____2595 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____2595, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____2588  in
    let printer uu___204_2605 =
      match uu___204_2605 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____2609 =
            let uu____2610 = ea.print x  in Prims.strcat uu____2610 ")"  in
          Prims.strcat "(Some " uu____2609
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____2684  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____2685 =
                 let uu____2690 =
                   let uu____2691 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2691
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2692 =
                   let uu____2693 =
                     let uu____2702 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2702  in
                   [uu____2693]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2690 uu____2692  in
               uu____2685 FStar_Pervasives_Native.None rng
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
                        let uu____2791 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____2791  in
                      let uu____2792 =
                        let uu____2797 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____2798 =
                          let uu____2799 =
                            let uu____2808 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____2808  in
                          let uu____2809 =
                            let uu____2820 = FStar_Syntax_Syntax.as_arg t  in
                            [uu____2820]  in
                          uu____2799 :: uu____2809  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____2797 uu____2798
                         in
                      uu____2792 FStar_Pervasives_Native.None rng)
                  in
               let uu____2855 =
                 let uu____2860 =
                   let uu____2861 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2861
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2862 =
                   let uu____2863 =
                     let uu____2872 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2872  in
                   let uu____2873 =
                     let uu____2884 =
                       let uu____2893 =
                         let uu____2894 = embed ea a  in
                         uu____2894 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____2893  in
                     [uu____2884]  in
                   uu____2863 :: uu____2873  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2860 uu____2862  in
               uu____2855 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____3029 = FStar_Syntax_Util.head_and_args t1  in
           match uu____3029 with
           | (hd1,args) ->
               let uu____3076 =
                 let uu____3091 =
                   let uu____3092 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____3092.FStar_Syntax_Syntax.n  in
                 (uu____3091, args)  in
               (match uu____3076 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3110) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____3134::(a,uu____3136)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____3187 =
                      let uu____3190 = unembed ea a  in uu____3190 w norm1
                       in
                    FStar_Util.bind_opt uu____3187
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____3209 ->
                    (if w
                     then
                       (let uu____3225 =
                          let uu____3230 =
                            let uu____3231 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____3231
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____3230)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____3225)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____3235 =
      let uu____3236 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____3236  in
    mk_emb_full em un uu____3235 printer emb_t_option_a
  
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
        let uu____3277 =
          let uu____3282 =
            let uu____3283 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____3292 =
              let uu____3303 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____3303]  in
            uu____3283 :: uu____3292  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____3282  in
        uu____3277 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____3339 =
          let uu____3346 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____3346, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____3339  in
      let printer uu____3358 =
        match uu____3358 with
        | (x,y) ->
            let uu____3365 = ea.print x  in
            let uu____3366 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____3365 uu____3366
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____3449  ->
             let proj i ab =
               let uu____3463 =
                 let uu____3468 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____3469 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____3468
                   uu____3469 i
                  in
               match uu____3463 with
               | (proj_1,uu____3473) ->
                   let proj_1_tm =
                     let uu____3475 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____3475  in
                   let uu____3476 =
                     let uu____3481 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____3482 =
                       let uu____3483 =
                         let uu____3492 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____3492  in
                       let uu____3493 =
                         let uu____3504 =
                           let uu____3513 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____3513  in
                         let uu____3514 =
                           let uu____3525 = FStar_Syntax_Syntax.as_arg ab  in
                           [uu____3525]  in
                         uu____3504 :: uu____3514  in
                       uu____3483 :: uu____3493  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3481 uu____3482  in
                   uu____3476 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____3684 =
               let uu____3689 =
                 let uu____3690 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3690
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____3691 =
                 let uu____3692 =
                   let uu____3701 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____3701  in
                 let uu____3702 =
                   let uu____3713 =
                     let uu____3722 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____3722  in
                   let uu____3723 =
                     let uu____3734 =
                       let uu____3743 =
                         let uu____3744 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____3744 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3743  in
                     let uu____3814 =
                       let uu____3825 =
                         let uu____3834 =
                           let uu____3835 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____3835 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____3834  in
                       [uu____3825]  in
                     uu____3734 :: uu____3814  in
                   uu____3713 :: uu____3723  in
                 uu____3692 :: uu____3702  in
               FStar_Syntax_Syntax.mk_Tm_app uu____3689 uu____3691  in
             uu____3684 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____3998 = FStar_Syntax_Util.head_and_args t1  in
             match uu____3998 with
             | (hd1,args) ->
                 let uu____4047 =
                   let uu____4060 =
                     let uu____4061 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____4061.FStar_Syntax_Syntax.n  in
                   (uu____4060, args)  in
                 (match uu____4047 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____4079::uu____4080::(a,uu____4082)::(b,uu____4084)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____4143 =
                        let uu____4146 = unembed ea a  in uu____4146 w norm1
                         in
                      FStar_Util.bind_opt uu____4143
                        (fun a1  ->
                           let uu____4166 =
                             let uu____4169 = unembed eb b  in
                             uu____4169 w norm1  in
                           FStar_Util.bind_opt uu____4166
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____4192 ->
                      (if w
                       then
                         (let uu____4206 =
                            let uu____4211 =
                              let uu____4212 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____4212
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____4211)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____4206)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____4218 =
        let uu____4219 = type_of ea  in
        let uu____4220 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____4219 uu____4220  in
      mk_emb_full em un uu____4218 printer emb_t_pair_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____4247 =
        let uu____4252 =
          let uu____4253 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____4253]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____4252  in
      uu____4247 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____4281 =
        let uu____4288 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____4288, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4281  in
    let printer l =
      let uu____4301 =
        let uu____4302 =
          let uu____4303 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____4303 (FStar_String.concat "; ")  in
        Prims.strcat uu____4302 "]"  in
      Prims.strcat "[" uu____4301  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____4382  ->
           let t =
             let uu____4384 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____4384  in
           match l with
           | [] ->
               let uu____4385 =
                 let uu____4390 =
                   let uu____4391 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____4391
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____4390 [t]  in
               uu____4385 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____4415 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4415
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____4432 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____4432  in
                 let uu____4433 =
                   let uu____4438 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____4439 =
                     let uu____4440 =
                       let uu____4449 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____4449  in
                     let uu____4450 =
                       let uu____4461 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____4461]  in
                     uu____4440 :: uu____4450  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4438 uu____4439  in
                 uu____4433 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____4612 =
                 let uu____4617 =
                   let uu____4618 =
                     let uu____4629 =
                       let uu____4638 =
                         let uu____4639 = embed ea hd1  in
                         uu____4639 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____4638  in
                     let uu____4709 =
                       let uu____4720 =
                         let uu____4729 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4729  in
                       [uu____4720]  in
                     uu____4629 :: uu____4709  in
                   t :: uu____4618  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____4617  in
               uu____4612 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____4843 = FStar_Syntax_Util.head_and_args t1  in
           match uu____4843 with
           | (hd1,args) ->
               let uu____4890 =
                 let uu____4903 =
                   let uu____4904 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____4904.FStar_Syntax_Syntax.n  in
                 (uu____4903, args)  in
               (match uu____4890 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4920) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____4940,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____4941))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4982 =
                      let uu____4985 = unembed ea hd2  in uu____4985 w norm1
                       in
                    FStar_Util.bind_opt uu____4982
                      (fun hd3  ->
                         let uu____5003 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____5003
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____5053 =
                      let uu____5056 = unembed ea hd2  in uu____5056 w norm1
                       in
                    FStar_Util.bind_opt uu____5053
                      (fun hd3  ->
                         let uu____5074 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____5074
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____5091 ->
                    (if w
                     then
                       (let uu____5105 =
                          let uu____5110 =
                            let uu____5111 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____5111
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____5110)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____5105)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____5115 =
      let uu____5116 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____5116  in
    mk_emb_full em un uu____5115 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____5147 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____5153 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____5159 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____5165 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____5171 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____5177 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____5183 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____5192 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____5214 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____5234 -> false
  
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
    let uu____5245 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____5245  in
  let emb_t_norm_step =
    let uu____5247 =
      let uu____5254 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____5254, [])  in
    FStar_Syntax_Syntax.ET_app uu____5247  in
  let printer uu____5262 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____5327  ->
         match n1 with
         | Simpl  -> steps_Simpl
         | Weak  -> steps_Weak
         | HNF  -> steps_HNF
         | Primops  -> steps_Primops
         | Delta  -> steps_Delta
         | Zeta  -> steps_Zeta
         | Iota  -> steps_Iota
         | UnfoldOnly l ->
             let uu____5331 =
               let uu____5336 =
                 let uu____5337 =
                   let uu____5346 =
                     let uu____5347 =
                       let uu____5354 = e_list e_string  in
                       embed uu____5354 l  in
                     uu____5347 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5346  in
                 [uu____5337]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____5336  in
             uu____5331 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____5409 =
               let uu____5414 =
                 let uu____5415 =
                   let uu____5424 =
                     let uu____5425 =
                       let uu____5432 = e_list e_string  in
                       embed uu____5432 l  in
                     uu____5425 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5424  in
                 [uu____5415]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____5414  in
             uu____5409 FStar_Pervasives_Native.None rng
         | UnfoldAttr a ->
             let uu____5485 =
               let uu____5490 =
                 let uu____5491 = FStar_Syntax_Syntax.as_arg a  in
                 [uu____5491]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____5490  in
             uu____5485 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____5550 = FStar_Syntax_Util.head_and_args t1  in
         match uu____5550 with
         | (hd1,args) ->
             let uu____5595 =
               let uu____5610 =
                 let uu____5611 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____5611.FStar_Syntax_Syntax.n  in
               (uu____5610, args)  in
             (match uu____5595 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5761)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____5796 =
                    let uu____5801 =
                      let uu____5810 = e_list e_string  in
                      unembed uu____5810 l  in
                    uu____5801 w norm1  in
                  FStar_Util.bind_opt uu____5796
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5833)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____5868 =
                    let uu____5873 =
                      let uu____5882 = e_list e_string  in
                      unembed uu____5882 l  in
                    uu____5873 w norm1  in
                  FStar_Util.bind_opt uu____5868
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5904::(a,uu____5906)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  -> FStar_Pervasives_Native.Some (UnfoldAttr a)
              | uu____5957 ->
                  (if w
                   then
                     (let uu____5973 =
                        let uu____5978 =
                          let uu____5979 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____5979
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____5978)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____5973)
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
    | uu____6074 ->
        (if w
         then
           (let uu____6076 =
              let uu____6081 =
                let uu____6082 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____6082  in
              (FStar_Errors.Warning_NotEmbedded, uu____6081)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____6076)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____6084 =
    let uu____6085 =
      let uu____6092 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____6092, [])  in
    FStar_Syntax_Syntax.ET_app uu____6085  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____6084
  
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
        let uu____6158 =
          let uu____6165 =
            let uu____6166 =
              let uu____6181 =
                let uu____6190 =
                  let uu____6197 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____6197, FStar_Pervasives_Native.None)  in
                [uu____6190]  in
              let uu____6212 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____6181, uu____6212)  in
            FStar_Syntax_Syntax.Tm_arrow uu____6166  in
          FStar_Syntax_Syntax.mk uu____6165  in
        uu____6158 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        let f_wrapped x =
          let shadow_app =
            map_shadow shadow_f
              (fun f1  ->
                 let uu____6379 =
                   let uu____6384 =
                     let uu____6385 = FStar_Syntax_Syntax.as_arg x  in
                     [uu____6385]  in
                   FStar_Syntax_Syntax.mk_Tm_app f1 uu____6384  in
                 uu____6379 FStar_Pervasives_Native.None rng)
             in
          let uu____6412 =
            let uu____6415 =
              let uu____6418 = unembed ea x  in uu____6418 true norm1  in
            FStar_Util.map_opt uu____6415
              (fun x1  ->
                 let uu____6457 =
                   let uu____6464 = f x1  in embed eb uu____6464  in
                 uu____6457 rng shadow_app norm1)
             in
          or_else uu____6412
            (fun uu____6530  ->
               let uu____6531 = force_shadow shadow_app  in
               match uu____6531 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise Embedding_failure
               | FStar_Pervasives_Native.Some app ->
                   norm1 (FStar_Util.Inr app))
           in
        lazy_embed (fun uu____6597  -> "<fun>") emb_t_arr_a_b rng t_arrow
          f_wrapped
          (fun uu____6602  ->
             let uu____6603 = force_shadow shadow_f  in
             match uu____6603 with
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
                 let uu____6717 = embed ea a  in
                 uu____6717 f1.FStar_Syntax_Syntax.pos
                   FStar_Pervasives_Native.None norm1
                  in
               let b_tm =
                 let uu____6750 =
                   let uu____6755 =
                     let uu____6756 =
                       let uu____6761 =
                         let uu____6762 = FStar_Syntax_Syntax.as_arg a_tm  in
                         [uu____6762]  in
                       FStar_Syntax_Syntax.mk_Tm_app f1 uu____6761  in
                     uu____6756 FStar_Pervasives_Native.None
                       f1.FStar_Syntax_Syntax.pos
                      in
                   FStar_Util.Inr uu____6755  in
                 norm1 uu____6750  in
               let uu____6789 =
                 let uu____6792 = unembed eb b_tm  in uu____6792 w norm1  in
               match uu____6789 with
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
                let uu____6889 = FStar_List.splitAt n_tvars args  in
                match uu____6889 with
                | (_tvar_args,rest_args) ->
                    let uu____6966 = FStar_List.hd rest_args  in
                    (match uu____6966 with
                     | (x,uu____6986) ->
                         let shadow_app =
                           let uu____7000 =
                             FStar_Common.mk_thunk
                               (fun uu____7009  ->
                                  let uu____7010 =
                                    let uu____7015 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____7015
                                      args
                                     in
                                  uu____7010 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____7000  in
                         let uu____7061 =
                           let uu____7064 =
                             let uu____7067 = unembed ea x  in
                             uu____7067 true norm1  in
                           FStar_Util.map_opt uu____7064
                             (fun x1  ->
                                let uu____7106 =
                                  let uu____7113 = f x1  in
                                  embed eb uu____7113  in
                                uu____7106 rng shadow_app norm1)
                            in
                         (match uu____7061 with
                          | FStar_Pervasives_Native.Some x1 ->
                              FStar_Pervasives_Native.Some x1
                          | FStar_Pervasives_Native.None  ->
                              let uu____7142 = force_shadow shadow_app  in
                              (match uu____7142 with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some app ->
                                   let uu____7148 =
                                     norm1 (FStar_Util.Inr app)  in
                                   FStar_Pervasives_Native.Some uu____7148)))
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
                  let uu____7248 = FStar_List.splitAt n_tvars args  in
                  match uu____7248 with
                  | (_tvar_args,rest_args) ->
                      let uu____7311 = FStar_List.hd rest_args  in
                      (match uu____7311 with
                       | (x,uu____7327) ->
                           let uu____7332 =
                             let uu____7339 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____7339  in
                           (match uu____7332 with
                            | (y,uu____7363) ->
                                let shadow_app =
                                  let uu____7373 =
                                    FStar_Common.mk_thunk
                                      (fun uu____7382  ->
                                         let uu____7383 =
                                           let uu____7388 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____7388 args
                                            in
                                         uu____7383
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____7373  in
                                let uu____7434 =
                                  let uu____7437 =
                                    let uu____7440 = unembed ea x  in
                                    uu____7440 true norm1  in
                                  FStar_Util.bind_opt uu____7437
                                    (fun x1  ->
                                       let uu____7456 =
                                         let uu____7459 = unembed eb y  in
                                         uu____7459 true norm1  in
                                       FStar_Util.bind_opt uu____7456
                                         (fun y1  ->
                                            let uu____7475 =
                                              let uu____7476 =
                                                let uu____7483 = f x1 y1  in
                                                embed ec uu____7483  in
                                              uu____7476 rng shadow_app norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____7475))
                                   in
                                (match uu____7434 with
                                 | FStar_Pervasives_Native.Some x1 ->
                                     FStar_Pervasives_Native.Some x1
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____7512 = force_shadow shadow_app
                                        in
                                     (match uu____7512 with
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some app ->
                                          let uu____7518 =
                                            norm1 (FStar_Util.Inr app)  in
                                          FStar_Pervasives_Native.Some
                                            uu____7518))))
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
                    let uu____7637 = FStar_List.splitAt n_tvars args  in
                    match uu____7637 with
                    | (_tvar_args,rest_args) ->
                        let uu____7700 = FStar_List.hd rest_args  in
                        (match uu____7700 with
                         | (x,uu____7716) ->
                             let uu____7721 =
                               let uu____7728 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____7728  in
                             (match uu____7721 with
                              | (y,uu____7752) ->
                                  let uu____7757 =
                                    let uu____7764 =
                                      let uu____7773 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____7773  in
                                    FStar_List.hd uu____7764  in
                                  (match uu____7757 with
                                   | (z,uu____7803) ->
                                       let shadow_app =
                                         let uu____7813 =
                                           FStar_Common.mk_thunk
                                             (fun uu____7822  ->
                                                let uu____7823 =
                                                  let uu____7828 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____7828 args
                                                   in
                                                uu____7823
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____7813
                                          in
                                       let uu____7874 =
                                         let uu____7877 =
                                           let uu____7880 = unembed ea x  in
                                           uu____7880 true norm1  in
                                         FStar_Util.bind_opt uu____7877
                                           (fun x1  ->
                                              let uu____7896 =
                                                let uu____7899 = unembed eb y
                                                   in
                                                uu____7899 true norm1  in
                                              FStar_Util.bind_opt uu____7896
                                                (fun y1  ->
                                                   let uu____7915 =
                                                     let uu____7918 =
                                                       unembed ec z  in
                                                     uu____7918 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____7915
                                                     (fun z1  ->
                                                        let uu____7934 =
                                                          let uu____7935 =
                                                            let uu____7942 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____7942
                                                             in
                                                          uu____7935 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____7934)))
                                          in
                                       (match uu____7874 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7971 =
                                              force_shadow shadow_app  in
                                            (match uu____7971 with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some
                                                 app ->
                                                 let uu____7977 =
                                                   norm1 (FStar_Util.Inr app)
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____7977)))))
                     in
                  f_wrapped
  