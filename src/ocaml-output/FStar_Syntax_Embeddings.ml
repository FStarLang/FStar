open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___202_13  ->
    match uu___202_13 with
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
type 'a embedding =
  {
  em: 'a -> embed_t ;
  un: FStar_Syntax_Syntax.term -> 'a unembed_t ;
  typ: FStar_Syntax_Syntax.typ }
let __proj__Mkembedding__item__em : 'a . 'a embedding -> 'a -> embed_t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__em
  
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__un
  
let __proj__Mkembedding__item__typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__typ
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.typ -> 'a embedding
  = fun em  -> fun un  -> fun typ  -> { em; un; typ } 
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
    fun t  -> fun n1  -> let uu____1002 = unembed e t  in uu____1002 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  -> fun n1  -> let uu____1049 = unembed e t  in uu____1049 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let lazy_embed :
  'a .
    FStar_Range.range ->
      'a ->
        (unit -> FStar_Syntax_Syntax.term) ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun rng  ->
    fun x  ->
      fun f  ->
        let uu____1107 =
          let uu____1114 =
            let uu____1115 =
              let uu____1116 = FStar_Dyn.mkdyn x  in
              let uu____1117 =
                let uu____1118 = FStar_Common.mk_thunk f  in
                FStar_Syntax_Syntax.Lazy_embedding uu____1118  in
              {
                FStar_Syntax_Syntax.blob = uu____1116;
                FStar_Syntax_Syntax.lkind = uu____1117;
                FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                FStar_Syntax_Syntax.rng = rng
              }  in
            FStar_Syntax_Syntax.Tm_lazy uu____1115  in
          FStar_Syntax_Syntax.mk uu____1114  in
        uu____1107 FStar_Pervasives_Native.None rng
  
let lazy_unembed :
  'a .
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option) ->
        'a FStar_Pervasives_Native.option
  =
  fun x  ->
    fun f  ->
      let x1 = FStar_Syntax_Subst.compress x  in
      match x1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = b;
            FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
              uu____1220;
            FStar_Syntax_Syntax.ltyp = uu____1221;
            FStar_Syntax_Syntax.rng = uu____1222;_}
          ->
          let uu____1229 = FStar_Dyn.undyn b  in
          FStar_Pervasives_Native.Some uu____1229
      | uu____1230 -> f x1
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let typ = FStar_Syntax_Syntax.t_term  in mk_emb em un typ 
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  -> { em = (e_any.em); un = (e_any.un); typ } 
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___203_1391 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___203_1391.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___203_1391.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____1419 ->
        (if w
         then
           (let uu____1421 =
              let uu____1426 =
                let uu____1427 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____1427  in
              (FStar_Errors.Warning_NotEmbedded, uu____1426)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1421)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_unit 
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___204_1500 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___204_1500.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___204_1500.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____1531 ->
        (if w
         then
           (let uu____1533 =
              let uu____1538 =
                let uu____1539 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____1539  in
              (FStar_Errors.Warning_NotEmbedded, uu____1538)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1533)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_bool 
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___205_1610 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___205_1610.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___205_1610.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____1644 ->
        (if w
         then
           (let uu____1646 =
              let uu____1651 =
                let uu____1652 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____1652  in
              (FStar_Errors.Warning_NotEmbedded, uu____1651)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1646)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_char 
let (e_int : FStar_BigInt.t embedding) =
  let em i rng _topt _norm =
    lazy_embed rng i
      (fun uu____1723  ->
         let uu____1724 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____1724)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed t
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____1758)) ->
             let uu____1771 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____1771
         | uu____1772 ->
             (if w
              then
                (let uu____1774 =
                   let uu____1779 =
                     let uu____1780 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____1780
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1779)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1774)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb em un FStar_Syntax_Syntax.t_int 
let (e_string : Prims.string embedding) =
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____1875)) -> FStar_Pervasives_Native.Some s
    | uu____1876 ->
        (if w
         then
           (let uu____1878 =
              let uu____1883 =
                let uu____1884 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____1884
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1883)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1878)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_string 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let em o rng topt norm1 =
      lazy_embed rng o
        (fun uu____1977  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____1978 =
                 let uu____1983 =
                   let uu____1984 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____1984
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____1985 =
                   let uu____1986 =
                     let uu____1995 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____1995  in
                   [uu____1986]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____1983 uu____1985  in
               uu____1978 FStar_Pervasives_Native.None rng
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
                        let uu____2084 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____2084  in
                      let uu____2085 =
                        let uu____2090 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____2091 =
                          let uu____2092 =
                            let uu____2101 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____2101  in
                          let uu____2102 =
                            let uu____2113 = FStar_Syntax_Syntax.as_arg t  in
                            [uu____2113]  in
                          uu____2092 :: uu____2102  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____2090 uu____2091
                         in
                      uu____2085 FStar_Pervasives_Native.None rng)
                  in
               let uu____2148 =
                 let uu____2153 =
                   let uu____2154 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2154
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2155 =
                   let uu____2156 =
                     let uu____2165 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2165  in
                   let uu____2166 =
                     let uu____2177 =
                       let uu____2186 =
                         let uu____2187 = embed ea a  in
                         uu____2187 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____2186  in
                     [uu____2177]  in
                   uu____2156 :: uu____2166  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2153 uu____2155  in
               uu____2148 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed t
        (fun t1  ->
           let uu____2322 = FStar_Syntax_Util.head_and_args t1  in
           match uu____2322 with
           | (hd1,args) ->
               let uu____2369 =
                 let uu____2384 =
                   let uu____2385 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____2385.FStar_Syntax_Syntax.n  in
                 (uu____2384, args)  in
               (match uu____2369 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2403) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____2427::(a,uu____2429)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____2480 =
                      let uu____2483 = unembed ea a  in uu____2483 w norm1
                       in
                    FStar_Util.bind_opt uu____2480
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____2502 ->
                    (if w
                     then
                       (let uu____2518 =
                          let uu____2523 =
                            let uu____2524 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____2524
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____2523)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____2518)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____2528 =
      let uu____2529 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____2529  in
    mk_emb em un uu____2528
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em x rng topt norm1 =
        lazy_embed rng x
          (fun uu____2648  ->
             let proj i ab =
               let uu____2662 =
                 let uu____2667 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____2668 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____2667
                   uu____2668 i
                  in
               match uu____2662 with
               | (proj_1,uu____2672) ->
                   let proj_1_tm =
                     let uu____2674 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____2674  in
                   let uu____2675 =
                     let uu____2680 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____2681 =
                       let uu____2682 =
                         let uu____2691 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____2691  in
                       let uu____2692 =
                         let uu____2703 =
                           let uu____2712 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____2712  in
                         let uu____2713 =
                           let uu____2724 = FStar_Syntax_Syntax.as_arg ab  in
                           [uu____2724]  in
                         uu____2703 :: uu____2713  in
                       uu____2682 :: uu____2692  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____2680 uu____2681  in
                   uu____2675 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____2883 =
               let uu____2888 =
                 let uu____2889 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____2889
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____2890 =
                 let uu____2891 =
                   let uu____2900 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____2900  in
                 let uu____2901 =
                   let uu____2912 =
                     let uu____2921 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____2921  in
                   let uu____2922 =
                     let uu____2933 =
                       let uu____2942 =
                         let uu____2943 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____2943 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____2942  in
                     let uu____3013 =
                       let uu____3024 =
                         let uu____3033 =
                           let uu____3034 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____3034 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____3033  in
                       [uu____3024]  in
                     uu____2933 :: uu____3013  in
                   uu____2912 :: uu____2922  in
                 uu____2891 :: uu____2901  in
               FStar_Syntax_Syntax.mk_Tm_app uu____2888 uu____2890  in
             uu____2883 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed t
          (fun t1  ->
             let uu____3197 = FStar_Syntax_Util.head_and_args t1  in
             match uu____3197 with
             | (hd1,args) ->
                 let uu____3246 =
                   let uu____3259 =
                     let uu____3260 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____3260.FStar_Syntax_Syntax.n  in
                   (uu____3259, args)  in
                 (match uu____3246 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____3278::uu____3279::(a,uu____3281)::(b,uu____3283)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____3342 =
                        let uu____3345 = unembed ea a  in uu____3345 w norm1
                         in
                      FStar_Util.bind_opt uu____3342
                        (fun a1  ->
                           let uu____3365 =
                             let uu____3368 = unembed eb b  in
                             uu____3368 w norm1  in
                           FStar_Util.bind_opt uu____3365
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____3391 ->
                      (if w
                       then
                         (let uu____3405 =
                            let uu____3410 =
                              let uu____3411 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____3411
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____3410)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____3405)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____3417 =
        let uu____3418 = type_of ea  in
        let uu____3419 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____3418 uu____3419  in
      mk_emb em un uu____3417
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let rec em l rng shadow_l norm1 =
      lazy_embed rng l
        (fun uu____3516  ->
           let t =
             let uu____3518 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____3518  in
           match l with
           | [] ->
               let uu____3519 =
                 let uu____3524 =
                   let uu____3525 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____3525
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3524 [t]  in
               uu____3519 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____3549 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3549
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____3566 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____3566  in
                 let uu____3567 =
                   let uu____3572 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____3573 =
                     let uu____3574 =
                       let uu____3583 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____3583  in
                     let uu____3584 =
                       let uu____3595 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____3595]  in
                     uu____3574 :: uu____3584  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____3572 uu____3573  in
                 uu____3567 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____3746 =
                 let uu____3751 =
                   let uu____3752 =
                     let uu____3763 =
                       let uu____3772 =
                         let uu____3773 = embed ea hd1  in
                         uu____3773 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3772  in
                     let uu____3843 =
                       let uu____3854 =
                         let uu____3863 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____3863  in
                       [uu____3854]  in
                     uu____3763 :: uu____3843  in
                   t :: uu____3752  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____3751  in
               uu____3746 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed t
        (fun t1  ->
           let uu____3977 = FStar_Syntax_Util.head_and_args t1  in
           match uu____3977 with
           | (hd1,args) ->
               let uu____4024 =
                 let uu____4037 =
                   let uu____4038 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____4038.FStar_Syntax_Syntax.n  in
                 (uu____4037, args)  in
               (match uu____4024 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4054) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____4074,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____4075))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4116 =
                      let uu____4119 = unembed ea hd2  in uu____4119 w norm1
                       in
                    FStar_Util.bind_opt uu____4116
                      (fun hd3  ->
                         let uu____4137 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____4137
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4187 =
                      let uu____4190 = unembed ea hd2  in uu____4190 w norm1
                       in
                    FStar_Util.bind_opt uu____4187
                      (fun hd3  ->
                         let uu____4208 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____4208
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____4225 ->
                    (if w
                     then
                       (let uu____4239 =
                          let uu____4244 =
                            let uu____4245 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____4245
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____4244)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____4239)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____4249 =
      let uu____4250 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____4250  in
    mk_emb em un uu____4249
  
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
    match projectee with | Simpl  -> true | uu____4281 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____4287 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____4293 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____4299 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____4305 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____4311 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____4317 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____4326 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____4348 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____4368 -> false
  
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
  let em n1 rng _topt norm1 =
    lazy_embed rng n1
      (fun uu____4442  ->
         match n1 with
         | Simpl  -> steps_Simpl
         | Weak  -> steps_Weak
         | HNF  -> steps_HNF
         | Primops  -> steps_Primops
         | Delta  -> steps_Delta
         | Zeta  -> steps_Zeta
         | Iota  -> steps_Iota
         | UnfoldOnly l ->
             let uu____4446 =
               let uu____4451 =
                 let uu____4452 =
                   let uu____4461 =
                     let uu____4462 =
                       let uu____4469 = e_list e_string  in
                       embed uu____4469 l  in
                     uu____4462 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____4461  in
                 [uu____4452]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____4451  in
             uu____4446 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____4524 =
               let uu____4529 =
                 let uu____4530 =
                   let uu____4539 =
                     let uu____4540 =
                       let uu____4547 = e_list e_string  in
                       embed uu____4547 l  in
                     uu____4540 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____4539  in
                 [uu____4530]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____4529  in
             uu____4524 FStar_Pervasives_Native.None rng
         | UnfoldAttr a ->
             let uu____4600 =
               let uu____4605 =
                 let uu____4606 = FStar_Syntax_Syntax.as_arg a  in
                 [uu____4606]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____4605  in
             uu____4600 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed t
      (fun t1  ->
         let uu____4665 = FStar_Syntax_Util.head_and_args t1  in
         match uu____4665 with
         | (hd1,args) ->
             let uu____4710 =
               let uu____4725 =
                 let uu____4726 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____4726.FStar_Syntax_Syntax.n  in
               (uu____4725, args)  in
             (match uu____4710 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____4876)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____4911 =
                    let uu____4916 =
                      let uu____4925 = e_list e_string  in
                      unembed uu____4925 l  in
                    uu____4916 w norm1  in
                  FStar_Util.bind_opt uu____4911
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____4948)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____4983 =
                    let uu____4988 =
                      let uu____4997 = e_list e_string  in
                      unembed uu____4997 l  in
                    uu____4988 w norm1  in
                  FStar_Util.bind_opt uu____4983
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5019::(a,uu____5021)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  -> FStar_Pervasives_Native.Some (UnfoldAttr a)
              | uu____5072 ->
                  (if w
                   then
                     (let uu____5088 =
                        let uu____5093 =
                          let uu____5094 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____5094
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____5093)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____5088)
                   else ();
                   FStar_Pervasives_Native.None)))
     in
  mk_emb em un FStar_Syntax_Syntax.t_norm_step 
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
    | uu____5189 ->
        (if w
         then
           (let uu____5191 =
              let uu____5196 =
                let uu____5197 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____5197  in
              (FStar_Errors.Warning_NotEmbedded, uu____5196)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____5191)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_range 
let or_else : 'a . 'a FStar_Pervasives_Native.option -> (unit -> 'a) -> 'a =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Pervasives_Native.Some x -> x
      | FStar_Pervasives_Native.None  -> g ()
  
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let em f rng shadow_f norm1 =
        let f_wrapped x =
          let shadow_app =
            map_shadow shadow_f
              (fun f1  ->
                 let uu____5398 =
                   let uu____5403 =
                     let uu____5404 = FStar_Syntax_Syntax.as_arg x  in
                     [uu____5404]  in
                   FStar_Syntax_Syntax.mk_Tm_app f1 uu____5403  in
                 uu____5398 FStar_Pervasives_Native.None rng)
             in
          let uu____5431 =
            let uu____5434 =
              let uu____5437 = unembed ea x  in uu____5437 true norm1  in
            FStar_Util.map_opt uu____5434
              (fun x1  ->
                 let uu____5476 =
                   let uu____5483 = f x1  in embed eb uu____5483  in
                 uu____5476 rng shadow_app norm1)
             in
          or_else uu____5431
            (fun uu____5549  ->
               let uu____5550 = force_shadow shadow_app  in
               match uu____5550 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise Embedding_failure
               | FStar_Pervasives_Native.Some app ->
                   norm1 (FStar_Util.Inr app))
           in
        lazy_embed rng f_wrapped
          (fun uu____5617  ->
             let uu____5618 = force_shadow shadow_f  in
             match uu____5618 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 norm1 (FStar_Util.Inr repr_f))
         in
      let un f w norm1 =
        let f_wrapped a =
          let a_tm =
            let uu____5726 = embed ea a  in
            uu____5726 f.FStar_Syntax_Syntax.pos FStar_Pervasives_Native.None
              norm1
             in
          let b_tm =
            let uu____5759 =
              let uu____5764 =
                let uu____5765 =
                  let uu____5770 =
                    let uu____5771 = FStar_Syntax_Syntax.as_arg a_tm  in
                    [uu____5771]  in
                  FStar_Syntax_Syntax.mk_Tm_app f uu____5770  in
                uu____5765 FStar_Pervasives_Native.None
                  f.FStar_Syntax_Syntax.pos
                 in
              FStar_Util.Inr uu____5764  in
            norm1 uu____5759  in
          let uu____5798 =
            let uu____5801 = unembed eb b_tm  in uu____5801 w norm1  in
          match uu____5798 with
          | FStar_Pervasives_Native.None  ->
              FStar_Exn.raise Unembedding_failure
          | FStar_Pervasives_Native.Some b -> b  in
        FStar_Pervasives_Native.Some f_wrapped  in
      let tarr =
        let uu____5819 =
          let uu____5826 =
            let uu____5827 =
              let uu____5842 =
                let uu____5851 =
                  let uu____5858 =
                    let uu____5859 = type_of ea  in
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      uu____5859
                     in
                  FStar_Syntax_Syntax.mk_binder uu____5858  in
                [uu____5851]  in
              let uu____5872 =
                let uu____5875 = type_of eb  in
                FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____5875
                 in
              (uu____5842, uu____5872)  in
            FStar_Syntax_Syntax.Tm_arrow uu____5827  in
          FStar_Syntax_Syntax.mk uu____5826  in
        uu____5819 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      mk_emb em un tarr
  
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
                let uu____5973 = FStar_List.splitAt n_tvars args  in
                match uu____5973 with
                | (_tvar_args,rest_args) ->
                    let uu____6050 = FStar_List.hd rest_args  in
                    (match uu____6050 with
                     | (x,uu____6070) ->
                         let shadow_app =
                           let uu____6084 =
                             FStar_Common.mk_thunk
                               (fun uu____6093  ->
                                  let uu____6094 =
                                    let uu____6099 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6099
                                      args
                                     in
                                  uu____6094 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____6084  in
                         let uu____6145 =
                           let uu____6148 =
                             let uu____6151 = unembed ea x  in
                             uu____6151 true norm1  in
                           FStar_Util.map_opt uu____6148
                             (fun x1  ->
                                let uu____6190 =
                                  let uu____6197 = f x1  in
                                  embed eb uu____6197  in
                                uu____6190 rng shadow_app norm1)
                            in
                         (match uu____6145 with
                          | FStar_Pervasives_Native.Some x1 ->
                              FStar_Pervasives_Native.Some x1
                          | FStar_Pervasives_Native.None  ->
                              let uu____6226 = force_shadow shadow_app  in
                              (match uu____6226 with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some app ->
                                   let uu____6232 =
                                     norm1 (FStar_Util.Inr app)  in
                                   FStar_Pervasives_Native.Some uu____6232)))
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
                  let uu____6332 = FStar_List.splitAt n_tvars args  in
                  match uu____6332 with
                  | (_tvar_args,rest_args) ->
                      let uu____6395 = FStar_List.hd rest_args  in
                      (match uu____6395 with
                       | (x,uu____6411) ->
                           let uu____6416 =
                             let uu____6423 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____6423  in
                           (match uu____6416 with
                            | (y,uu____6447) ->
                                let shadow_app =
                                  let uu____6457 =
                                    FStar_Common.mk_thunk
                                      (fun uu____6466  ->
                                         let uu____6467 =
                                           let uu____6472 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6472 args
                                            in
                                         uu____6467
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____6457  in
                                let uu____6518 =
                                  let uu____6521 =
                                    let uu____6524 = unembed ea x  in
                                    uu____6524 true norm1  in
                                  FStar_Util.bind_opt uu____6521
                                    (fun x1  ->
                                       let uu____6540 =
                                         let uu____6543 = unembed eb y  in
                                         uu____6543 true norm1  in
                                       FStar_Util.bind_opt uu____6540
                                         (fun y1  ->
                                            let uu____6559 =
                                              let uu____6560 =
                                                let uu____6567 = f x1 y1  in
                                                embed ec uu____6567  in
                                              uu____6560 rng shadow_app norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____6559))
                                   in
                                (match uu____6518 with
                                 | FStar_Pervasives_Native.Some x1 ->
                                     FStar_Pervasives_Native.Some x1
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____6596 = force_shadow shadow_app
                                        in
                                     (match uu____6596 with
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some app ->
                                          let uu____6602 =
                                            norm1 (FStar_Util.Inr app)  in
                                          FStar_Pervasives_Native.Some
                                            uu____6602))))
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
                    let uu____6721 = FStar_List.splitAt n_tvars args  in
                    match uu____6721 with
                    | (_tvar_args,rest_args) ->
                        let uu____6784 = FStar_List.hd rest_args  in
                        (match uu____6784 with
                         | (x,uu____6800) ->
                             let uu____6805 =
                               let uu____6812 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____6812  in
                             (match uu____6805 with
                              | (y,uu____6836) ->
                                  let uu____6841 =
                                    let uu____6848 =
                                      let uu____6857 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____6857  in
                                    FStar_List.hd uu____6848  in
                                  (match uu____6841 with
                                   | (z,uu____6887) ->
                                       let shadow_app =
                                         let uu____6897 =
                                           FStar_Common.mk_thunk
                                             (fun uu____6906  ->
                                                let uu____6907 =
                                                  let uu____6912 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____6912 args
                                                   in
                                                uu____6907
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6897
                                          in
                                       let uu____6958 =
                                         let uu____6961 =
                                           let uu____6964 = unembed ea x  in
                                           uu____6964 true norm1  in
                                         FStar_Util.bind_opt uu____6961
                                           (fun x1  ->
                                              let uu____6980 =
                                                let uu____6983 = unembed eb y
                                                   in
                                                uu____6983 true norm1  in
                                              FStar_Util.bind_opt uu____6980
                                                (fun y1  ->
                                                   let uu____6999 =
                                                     let uu____7002 =
                                                       unembed ec z  in
                                                     uu____7002 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____6999
                                                     (fun z1  ->
                                                        let uu____7018 =
                                                          let uu____7019 =
                                                            let uu____7026 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____7026
                                                             in
                                                          uu____7019 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____7018)))
                                          in
                                       (match uu____6958 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7055 =
                                              force_shadow shadow_app  in
                                            (match uu____7055 with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some
                                                 app ->
                                                 let uu____7061 =
                                                   norm1 (FStar_Util.Inr app)
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____7061)))))
                     in
                  f_wrapped
  