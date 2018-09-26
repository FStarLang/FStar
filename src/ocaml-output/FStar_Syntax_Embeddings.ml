open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___214_13  ->
    match uu___214_13 with
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
    match projectee with | { em; un; typ; print = print7; emb_typ;_} -> em
  
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun projectee  ->
    match projectee with | { em; un; typ; print = print7; emb_typ;_} -> un
  
let __proj__Mkembedding__item__typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with | { em; un; typ; print = print7; emb_typ;_} -> typ
  
let __proj__Mkembedding__item__print : 'a . 'a embedding -> 'a printer =
  fun projectee  ->
    match projectee with
    | { em; un; typ; print = print7; emb_typ;_} -> print7
  
let __proj__Mkembedding__item__emb_typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun projectee  ->
    match projectee with
    | { em; un; typ; print = print7; emb_typ;_} -> emb_typ
  
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
      let uu___216_1478 = e  in
      {
        em = (uu___216_1478.em);
        un = (uu___216_1478.un);
        typ = ty;
        print = (uu___216_1478.print);
        emb_typ = (uu___216_1478.emb_typ)
      }
  
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
              (let uu____1546 =
                 FStar_ST.op_Bang FStar_Options.debug_embedding  in
               if uu____1546
               then
                 let uu____1566 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____1567 = FStar_Syntax_Print.emb_typ_to_string et  in
                 let uu____1568 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu____1566
                   uu____1567 uu____1568
               else ());
              (let uu____1572 =
                 FStar_ST.op_Bang FStar_Options.eager_embedding  in
               if uu____1572
               then f ()
               else
                 (let thunk = FStar_Common.mk_thunk f  in
                  let uu____1602 =
                    let uu____1609 =
                      let uu____1610 =
                        let uu____1611 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____1611;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____1610  in
                    FStar_Syntax_Syntax.mk uu____1609  in
                  uu____1602 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____1726;
                  FStar_Syntax_Syntax.rng = uu____1727;_}
                ->
                let uu____1738 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____1738
                then
                  let res =
                    let uu____1763 = FStar_Common.force_thunk t  in
                    f uu____1763  in
                  ((let uu____1807 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1807
                    then
                      let uu____1827 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____1828 =
                        FStar_Syntax_Print.emb_typ_to_string et'  in
                      let uu____1829 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____1831 = pa x2  in
                            Prims.strcat "Some " uu____1831
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____1827 uu____1828 uu____1829
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____1838 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1838
                    then
                      let uu____1858 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____1859 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____1858 uu____1859
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____1863 ->
                let aopt = f x1  in
                ((let uu____1868 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____1868
                  then
                    let uu____1888 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____1889 = FStar_Syntax_Print.term_to_string x1  in
                    let uu____1890 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____1892 = pa a  in
                          Prims.strcat "Some " uu____1892
                       in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____1888 uu____1889 uu____1890
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____1967 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____1967
       then
         let uu____1987 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____1987
       else ());
      t  in
    let un t _w _n =
      (let uu____2012 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____2012
       then
         let uu____2032 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____2032
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____2121 =
    let uu____2122 =
      let uu____2129 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____2129, [])  in
    FStar_Syntax_Syntax.ET_app uu____2122  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____2121
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___217_2197 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___217_2197.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___217_2197.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____2225 ->
        (if w
         then
           (let uu____2227 =
              let uu____2232 =
                let uu____2233 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____2233  in
              (FStar_Errors.Warning_NotEmbedded, uu____2232)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2227)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2235 =
    let uu____2236 =
      let uu____2243 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____2243, [])  in
    FStar_Syntax_Syntax.ET_app uu____2236  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____2247  -> "()")
    uu____2235
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___218_2319 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___218_2319.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___218_2319.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____2350 ->
        (if w
         then
           (let uu____2352 =
              let uu____2357 =
                let uu____2358 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____2358  in
              (FStar_Errors.Warning_NotEmbedded, uu____2357)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2352)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2360 =
    let uu____2361 =
      let uu____2368 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____2368, [])  in
    FStar_Syntax_Syntax.ET_app uu____2361  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____2360
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___219_2440 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___219_2440.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___219_2440.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____2474 ->
        (if w
         then
           (let uu____2476 =
              let uu____2481 =
                let uu____2482 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____2482  in
              (FStar_Errors.Warning_NotEmbedded, uu____2481)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2476)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2485 =
    let uu____2486 =
      let uu____2493 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____2493, [])  in
    FStar_Syntax_Syntax.ET_app uu____2486  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____2485
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____2501 =
      let uu____2508 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____2508, [])  in
    FStar_Syntax_Syntax.ET_app uu____2501  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____2576  ->
         let uu____2577 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____2577)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____2611)) ->
             let uu____2624 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____2624
         | uu____2625 ->
             (if w
              then
                (let uu____2627 =
                   let uu____2632 =
                     let uu____2633 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____2633
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2632)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2627)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____2638 =
      let uu____2645 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____2645, [])  in
    FStar_Syntax_Syntax.ET_app uu____2638  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____2739)) -> FStar_Pervasives_Native.Some s
    | uu____2740 ->
        (if w
         then
           (let uu____2742 =
              let uu____2747 =
                let uu____2748 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____2748
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2747)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2742)
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
      let uu____2774 =
        let uu____2779 =
          let uu____2780 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____2780]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____2779  in
      uu____2774 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____2808 =
        let uu____2815 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____2815, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____2808  in
    let printer uu___215_2825 =
      match uu___215_2825 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____2829 =
            let uu____2830 = ea.print x  in Prims.strcat uu____2830 ")"  in
          Prims.strcat "(Some " uu____2829
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____2904  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____2905 =
                 let uu____2910 =
                   let uu____2911 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2911
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2912 =
                   let uu____2913 =
                     let uu____2922 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2922  in
                   [uu____2913]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2910 uu____2912  in
               uu____2905 FStar_Pervasives_Native.None rng
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
                        let uu____3011 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____3011  in
                      let uu____3012 =
                        let uu____3017 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____3018 =
                          let uu____3019 =
                            let uu____3028 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____3028  in
                          let uu____3029 =
                            let uu____3040 = FStar_Syntax_Syntax.as_arg t  in
                            [uu____3040]  in
                          uu____3019 :: uu____3029  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3017 uu____3018
                         in
                      uu____3012 FStar_Pervasives_Native.None rng)
                  in
               let uu____3075 =
                 let uu____3080 =
                   let uu____3081 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____3081
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____3082 =
                   let uu____3083 =
                     let uu____3092 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____3092  in
                   let uu____3093 =
                     let uu____3104 =
                       let uu____3113 =
                         let uu____3114 = embed ea a  in
                         uu____3114 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3113  in
                     [uu____3104]  in
                   uu____3083 :: uu____3093  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3080 uu____3082  in
               uu____3075 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____3249 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____3249 with
           | (hd1,args) ->
               let uu____3290 =
                 let uu____3305 =
                   let uu____3306 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____3306.FStar_Syntax_Syntax.n  in
                 (uu____3305, args)  in
               (match uu____3290 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3324) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____3348::(a,uu____3350)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____3401 =
                      let uu____3404 = unembed ea a  in uu____3404 w norm1
                       in
                    FStar_Util.bind_opt uu____3401
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____3423 ->
                    (if w
                     then
                       (let uu____3439 =
                          let uu____3444 =
                            let uu____3445 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____3445
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____3444)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____3439)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____3449 =
      let uu____3450 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____3450  in
    mk_emb_full em un uu____3449 printer emb_t_option_a
  
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
        let uu____3491 =
          let uu____3496 =
            let uu____3497 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____3506 =
              let uu____3517 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____3517]  in
            uu____3497 :: uu____3506  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____3496  in
        uu____3491 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____3553 =
          let uu____3560 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____3560, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____3553  in
      let printer uu____3572 =
        match uu____3572 with
        | (x,y) ->
            let uu____3579 = ea.print x  in
            let uu____3580 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____3579 uu____3580
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____3663  ->
             let proj i ab =
               let uu____3677 =
                 let uu____3682 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____3683 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____3682
                   uu____3683 i
                  in
               match uu____3677 with
               | (proj_1,uu____3687) ->
                   let proj_1_tm =
                     let uu____3689 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____3689  in
                   let uu____3690 =
                     let uu____3695 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____3696 =
                       let uu____3697 =
                         let uu____3706 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____3706  in
                       let uu____3707 =
                         let uu____3718 =
                           let uu____3727 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____3727  in
                         let uu____3728 =
                           let uu____3739 = FStar_Syntax_Syntax.as_arg ab  in
                           [uu____3739]  in
                         uu____3718 :: uu____3728  in
                       uu____3697 :: uu____3707  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3695 uu____3696  in
                   uu____3690 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____3898 =
               let uu____3903 =
                 let uu____3904 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3904
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____3905 =
                 let uu____3906 =
                   let uu____3915 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____3915  in
                 let uu____3916 =
                   let uu____3927 =
                     let uu____3936 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____3936  in
                   let uu____3937 =
                     let uu____3948 =
                       let uu____3957 =
                         let uu____3958 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____3958 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3957  in
                     let uu____4028 =
                       let uu____4039 =
                         let uu____4048 =
                           let uu____4049 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____4049 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4048  in
                       [uu____4039]  in
                     uu____3948 :: uu____4028  in
                   uu____3927 :: uu____3937  in
                 uu____3906 :: uu____3916  in
               FStar_Syntax_Syntax.mk_Tm_app uu____3903 uu____3905  in
             uu____3898 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____4212 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____4212 with
             | (hd1,args) ->
                 let uu____4255 =
                   let uu____4268 =
                     let uu____4269 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____4269.FStar_Syntax_Syntax.n  in
                   (uu____4268, args)  in
                 (match uu____4255 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____4287::uu____4288::(a,uu____4290)::(b,uu____4292)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____4351 =
                        let uu____4354 = unembed ea a  in uu____4354 w norm1
                         in
                      FStar_Util.bind_opt uu____4351
                        (fun a1  ->
                           let uu____4374 =
                             let uu____4377 = unembed eb b  in
                             uu____4377 w norm1  in
                           FStar_Util.bind_opt uu____4374
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____4400 ->
                      (if w
                       then
                         (let uu____4414 =
                            let uu____4419 =
                              let uu____4420 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____4420
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____4419)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____4414)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____4426 =
        let uu____4427 = type_of ea  in
        let uu____4428 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____4427 uu____4428  in
      mk_emb_full em un uu____4426 printer emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____4471 =
          let uu____4476 =
            let uu____4477 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____4486 =
              let uu____4497 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____4497]  in
            uu____4477 :: uu____4486  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____4476  in
        uu____4471 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____4533 =
          let uu____4540 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____4540, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4533  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____4558 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____4558
        | FStar_Util.Inr b ->
            let uu____4560 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____4560
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____4646  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____4716 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____4716  in
                         let uu____4717 =
                           let uu____4722 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____4723 =
                             let uu____4724 =
                               let uu____4733 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____4733  in
                             let uu____4734 =
                               let uu____4745 =
                                 let uu____4754 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____4754  in
                               let uu____4755 =
                                 let uu____4766 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____4766]  in
                               uu____4745 :: uu____4755  in
                             uu____4724 :: uu____4734  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____4722
                             uu____4723
                            in
                         uu____4717 FStar_Pervasives_Native.None rng)
                     in
                  let uu____4809 =
                    let uu____4814 =
                      let uu____4815 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____4815
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____4816 =
                      let uu____4817 =
                        let uu____4826 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____4826  in
                      let uu____4827 =
                        let uu____4838 =
                          let uu____4847 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____4847  in
                        let uu____4848 =
                          let uu____4859 =
                            let uu____4868 =
                              let uu____4869 = embed ea a  in
                              uu____4869 rng shadow_a norm1  in
                            FStar_Syntax_Syntax.as_arg uu____4868  in
                          [uu____4859]  in
                        uu____4838 :: uu____4848  in
                      uu____4817 :: uu____4827  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____4814 uu____4816  in
                  uu____4809 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____4974  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____5044 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____5044  in
                         let uu____5045 =
                           let uu____5050 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____5051 =
                             let uu____5052 =
                               let uu____5061 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____5061  in
                             let uu____5062 =
                               let uu____5073 =
                                 let uu____5082 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____5082  in
                               let uu____5083 =
                                 let uu____5094 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____5094]  in
                               uu____5073 :: uu____5083  in
                             uu____5052 :: uu____5062  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____5050
                             uu____5051
                            in
                         uu____5045 FStar_Pervasives_Native.None rng)
                     in
                  let uu____5137 =
                    let uu____5142 =
                      let uu____5143 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____5143
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____5144 =
                      let uu____5145 =
                        let uu____5154 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____5154  in
                      let uu____5155 =
                        let uu____5166 =
                          let uu____5175 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____5175  in
                        let uu____5176 =
                          let uu____5187 =
                            let uu____5196 =
                              let uu____5197 = embed eb b  in
                              uu____5197 rng shadow_b norm1  in
                            FStar_Syntax_Syntax.as_arg uu____5196  in
                          [uu____5187]  in
                        uu____5166 :: uu____5176  in
                      uu____5145 :: uu____5155  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____5142 uu____5144  in
                  uu____5137 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____5350 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____5350 with
             | (hd1,args) ->
                 let uu____5393 =
                   let uu____5408 =
                     let uu____5409 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____5409.FStar_Syntax_Syntax.n  in
                   (uu____5408, args)  in
                 (match uu____5393 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____5429::uu____5430::(a,uu____5432)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____5499 =
                        let uu____5502 = unembed ea a  in uu____5502 w norm1
                         in
                      FStar_Util.bind_opt uu____5499
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____5526::uu____5527::(b,uu____5529)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____5596 =
                        let uu____5599 = unembed eb b  in uu____5599 w norm1
                         in
                      FStar_Util.bind_opt uu____5596
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____5622 ->
                      (if w
                       then
                         (let uu____5638 =
                            let uu____5643 =
                              let uu____5644 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____5644
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____5643)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____5638)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____5650 =
        let uu____5651 = type_of ea  in
        let uu____5652 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____5651 uu____5652  in
      mk_emb_full em un uu____5650 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____5679 =
        let uu____5684 =
          let uu____5685 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____5685]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____5684  in
      uu____5679 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____5713 =
        let uu____5720 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____5720, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____5713  in
    let printer l =
      let uu____5733 =
        let uu____5734 =
          let uu____5735 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____5735 (FStar_String.concat "; ")  in
        Prims.strcat uu____5734 "]"  in
      Prims.strcat "[" uu____5733  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____5814  ->
           let t =
             let uu____5816 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____5816  in
           match l with
           | [] ->
               let uu____5817 =
                 let uu____5822 =
                   let uu____5823 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____5823
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____5822 [t]  in
               uu____5817 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____5847 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____5847
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____5864 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____5864  in
                 let uu____5865 =
                   let uu____5870 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____5871 =
                     let uu____5872 =
                       let uu____5881 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____5881  in
                     let uu____5882 =
                       let uu____5893 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____5893]  in
                     uu____5872 :: uu____5882  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____5870 uu____5871  in
                 uu____5865 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____6044 =
                 let uu____6049 =
                   let uu____6050 =
                     let uu____6061 =
                       let uu____6070 =
                         let uu____6071 = embed ea hd1  in
                         uu____6071 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____6070  in
                     let uu____6141 =
                       let uu____6152 =
                         let uu____6161 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____6161  in
                       [uu____6152]  in
                     uu____6061 :: uu____6141  in
                   t :: uu____6050  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____6049  in
               uu____6044 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____6275 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____6275 with
           | (hd1,args) ->
               let uu____6316 =
                 let uu____6329 =
                   let uu____6330 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____6330.FStar_Syntax_Syntax.n  in
                 (uu____6329, args)  in
               (match uu____6316 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6346) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____6366,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____6367))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____6408 =
                      let uu____6411 = unembed ea hd2  in uu____6411 w norm1
                       in
                    FStar_Util.bind_opt uu____6408
                      (fun hd3  ->
                         let uu____6429 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____6429
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____6479 =
                      let uu____6482 = unembed ea hd2  in uu____6482 w norm1
                       in
                    FStar_Util.bind_opt uu____6479
                      (fun hd3  ->
                         let uu____6500 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____6500
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____6517 ->
                    (if w
                     then
                       (let uu____6531 =
                          let uu____6536 =
                            let uu____6537 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____6537
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____6536)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____6531)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____6541 =
      let uu____6542 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____6542  in
    mk_emb_full em un uu____6541 printer emb_t_list_a
  
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
  | UnfoldAttr of Prims.string Prims.list 
  | NBE 
let (uu___is_Simpl : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____6575 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____6581 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____6587 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____6593 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____6599 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____6605 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____6611 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____6617 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____6626 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____6648 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____6670 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____6689 -> false 
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
    let uu____6693 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____6693  in
  let emb_t_norm_step =
    let uu____6695 =
      let uu____6702 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____6702, [])  in
    FStar_Syntax_Syntax.ET_app uu____6695  in
  let printer uu____6710 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____6775  ->
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
             let uu____6779 =
               let uu____6784 =
                 let uu____6785 =
                   let uu____6794 =
                     let uu____6795 =
                       let uu____6802 = e_list e_string  in
                       embed uu____6802 l  in
                     uu____6795 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____6794  in
                 [uu____6785]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____6784  in
             uu____6779 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____6857 =
               let uu____6862 =
                 let uu____6863 =
                   let uu____6872 =
                     let uu____6873 =
                       let uu____6880 = e_list e_string  in
                       embed uu____6880 l  in
                     uu____6873 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____6872  in
                 [uu____6863]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____6862  in
             uu____6857 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____6935 =
               let uu____6940 =
                 let uu____6941 =
                   let uu____6950 =
                     let uu____6951 =
                       let uu____6958 = e_list e_string  in
                       embed uu____6958 l  in
                     uu____6951 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____6950  in
                 [uu____6941]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____6940  in
             uu____6935 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____7042 = FStar_Syntax_Util.head_and_args t1  in
         match uu____7042 with
         | (hd1,args) ->
             let uu____7087 =
               let uu____7102 =
                 let uu____7103 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____7103.FStar_Syntax_Syntax.n  in
               (uu____7102, args)  in
             (match uu____7087 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7291)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____7326 =
                    let uu____7331 =
                      let uu____7340 = e_list e_string  in
                      unembed uu____7340 l  in
                    uu____7331 w norm1  in
                  FStar_Util.bind_opt uu____7326
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_1  -> FStar_Pervasives_Native.Some _0_1)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7363)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____7398 =
                    let uu____7403 =
                      let uu____7412 = e_list e_string  in
                      unembed uu____7412 l  in
                    uu____7403 w norm1  in
                  FStar_Util.bind_opt uu____7398
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_2  -> FStar_Pervasives_Native.Some _0_2)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7435)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____7470 =
                    let uu____7475 =
                      let uu____7484 = e_list e_string  in
                      unembed uu____7484 l  in
                    uu____7475 w norm1  in
                  FStar_Util.bind_opt uu____7470
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_3  -> FStar_Pervasives_Native.Some _0_3)
                         (UnfoldAttr ss))
              | uu____7505 ->
                  (if w
                   then
                     (let uu____7521 =
                        let uu____7526 =
                          let uu____7527 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____7527
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____7526)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____7521)
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
    | uu____7622 ->
        (if w
         then
           (let uu____7624 =
              let uu____7629 =
                let uu____7630 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____7630  in
              (FStar_Errors.Warning_NotEmbedded, uu____7629)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____7624)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____7632 =
    let uu____7633 =
      let uu____7640 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____7640, [])  in
    FStar_Syntax_Syntax.ET_app uu____7633  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____7632
  
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
        let uu____7706 =
          let uu____7713 =
            let uu____7714 =
              let uu____7729 =
                let uu____7738 =
                  let uu____7745 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____7745, FStar_Pervasives_Native.None)  in
                [uu____7738]  in
              let uu____7760 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____7729, uu____7760)  in
            FStar_Syntax_Syntax.Tm_arrow uu____7714  in
          FStar_Syntax_Syntax.mk uu____7713  in
        uu____7706 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____7871  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____7876  ->
             let uu____7877 = force_shadow shadow_f  in
             match uu____7877 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____7939 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____7939
                   then
                     let uu____7959 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____7960 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____7959 uu____7960
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f)  in
                   (let uu____7964 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____7964
                    then
                      let uu____7984 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____7985 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____7986 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____7984 uu____7985 uu____7986
                    else ());
                   res)))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               (let uu____8040 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____8040
                then
                  let uu____8060 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____8061 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____8060
                    uu____8061
                else ());
               (let a_tm =
                  let uu____8064 = embed ea a  in
                  uu____8064 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1
                   in
                let b_tm =
                  let uu____8097 =
                    let uu____8102 =
                      let uu____8103 =
                        let uu____8108 =
                          let uu____8109 = FStar_Syntax_Syntax.as_arg a_tm
                             in
                          [uu____8109]  in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____8108  in
                      uu____8103 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____8102  in
                  norm1 uu____8097  in
                let uu____8136 =
                  let uu____8139 = unembed eb b_tm  in uu____8139 w norm1  in
                match uu____8136 with
                | FStar_Pervasives_Native.None  ->
                    FStar_Exn.raise Unembedding_failure
                | FStar_Pervasives_Native.Some b -> b)
                in
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
                let uu____8236 = FStar_List.splitAt n_tvars args  in
                match uu____8236 with
                | (_tvar_args,rest_args) ->
                    let uu____8313 = FStar_List.hd rest_args  in
                    (match uu____8313 with
                     | (x,uu____8333) ->
                         let shadow_app =
                           let uu____8347 =
                             FStar_Common.mk_thunk
                               (fun uu____8356  ->
                                  let uu____8357 =
                                    let uu____8362 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____8362
                                      args
                                     in
                                  uu____8357 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____8347  in
                         let uu____8408 =
                           let uu____8411 =
                             let uu____8414 = unembed ea x  in
                             uu____8414 true norm1  in
                           FStar_Util.map_opt uu____8411
                             (fun x1  ->
                                let uu____8453 =
                                  let uu____8460 = f x1  in
                                  embed eb uu____8460  in
                                uu____8453 rng shadow_app norm1)
                            in
                         (match uu____8408 with
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
                  let uu____8587 = FStar_List.splitAt n_tvars args  in
                  match uu____8587 with
                  | (_tvar_args,rest_args) ->
                      let uu____8650 = FStar_List.hd rest_args  in
                      (match uu____8650 with
                       | (x,uu____8666) ->
                           let uu____8671 =
                             let uu____8678 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____8678  in
                           (match uu____8671 with
                            | (y,uu____8702) ->
                                let shadow_app =
                                  let uu____8712 =
                                    FStar_Common.mk_thunk
                                      (fun uu____8721  ->
                                         let uu____8722 =
                                           let uu____8727 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____8727 args
                                            in
                                         uu____8722
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____8712  in
                                let uu____8773 =
                                  let uu____8776 =
                                    let uu____8779 = unembed ea x  in
                                    uu____8779 true norm1  in
                                  FStar_Util.bind_opt uu____8776
                                    (fun x1  ->
                                       let uu____8795 =
                                         let uu____8798 = unembed eb y  in
                                         uu____8798 true norm1  in
                                       FStar_Util.bind_opt uu____8795
                                         (fun y1  ->
                                            let uu____8814 =
                                              let uu____8815 =
                                                let uu____8822 = f x1 y1  in
                                                embed ec uu____8822  in
                                              uu____8815 rng shadow_app norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____8814))
                                   in
                                (match uu____8773 with
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
                    let uu____8968 = FStar_List.splitAt n_tvars args  in
                    match uu____8968 with
                    | (_tvar_args,rest_args) ->
                        let uu____9031 = FStar_List.hd rest_args  in
                        (match uu____9031 with
                         | (x,uu____9047) ->
                             let uu____9052 =
                               let uu____9059 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____9059  in
                             (match uu____9052 with
                              | (y,uu____9083) ->
                                  let uu____9088 =
                                    let uu____9095 =
                                      let uu____9104 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____9104  in
                                    FStar_List.hd uu____9095  in
                                  (match uu____9088 with
                                   | (z,uu____9134) ->
                                       let shadow_app =
                                         let uu____9144 =
                                           FStar_Common.mk_thunk
                                             (fun uu____9153  ->
                                                let uu____9154 =
                                                  let uu____9159 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____9159 args
                                                   in
                                                uu____9154
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____9144
                                          in
                                       let uu____9205 =
                                         let uu____9208 =
                                           let uu____9211 = unembed ea x  in
                                           uu____9211 true norm1  in
                                         FStar_Util.bind_opt uu____9208
                                           (fun x1  ->
                                              let uu____9227 =
                                                let uu____9230 = unembed eb y
                                                   in
                                                uu____9230 true norm1  in
                                              FStar_Util.bind_opt uu____9227
                                                (fun y1  ->
                                                   let uu____9246 =
                                                     let uu____9249 =
                                                       unembed ec z  in
                                                     uu____9249 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____9246
                                                     (fun z1  ->
                                                        let uu____9265 =
                                                          let uu____9266 =
                                                            let uu____9273 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____9273
                                                             in
                                                          uu____9266 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____9265)))
                                          in
                                       (match uu____9205 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____9325 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____9325 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____9348 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____9348 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  