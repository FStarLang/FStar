open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___429_50688  ->
    match uu___429_50688 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____50695 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____50695
  
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embedding_failure  -> true | uu____50705 -> false
  
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unembedding_failure  -> true
    | uu____50716 -> false
  
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
             (fun uu____50748  ->
                let uu____50749 = FStar_Common.force_thunk s1  in
                f uu____50749))
  
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
  'Auu____51111 . FStar_Syntax_Syntax.term -> 'Auu____51111 -> Prims.string =
  fun typ  ->
    fun uu____51122  ->
      let uu____51123 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____51123
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____51132 =
      let uu____51133 = FStar_Syntax_Subst.compress t  in
      uu____51133.FStar_Syntax_Syntax.n  in
    match uu____51132 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____51137 ->
        let uu____51138 =
          let uu____51140 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____51140
           in
        failwith uu____51138
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____51183 =
          let uu____51184 =
            let uu____51192 =
              let uu____51194 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____51194 FStar_Ident.string_of_lid  in
            (uu____51192, [])  in
          FStar_Syntax_Syntax.ET_app uu____51184  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____51183 }
  
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
    fun t  ->
      fun n1  -> let uu____51343 = unembed e t  in uu____51343 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      fun n1  -> let uu____51384 = unembed e t  in uu____51384 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___508_51431 = e  in
      {
        em = (uu___508_51431.em);
        un = (uu___508_51431.un);
        typ = ty;
        print = (uu___508_51431.print);
        emb_typ = (uu___508_51431.emb_typ)
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
              (let uu____51494 =
                 FStar_ST.op_Bang FStar_Options.debug_embedding  in
               if uu____51494
               then
                 let uu____51518 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____51520 = FStar_Syntax_Print.emb_typ_to_string et
                    in
                 let uu____51522 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n"
                   uu____51518 uu____51520 uu____51522
               else ());
              (let uu____51527 =
                 FStar_ST.op_Bang FStar_Options.eager_embedding  in
               if uu____51527
               then f ()
               else
                 (let thunk1 = FStar_Common.mk_thunk f  in
                  let uu____51562 =
                    let uu____51569 =
                      let uu____51570 =
                        let uu____51571 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____51571;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk1));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____51570  in
                    FStar_Syntax_Syntax.mk uu____51569  in
                  uu____51562 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____51638;
                  FStar_Syntax_Syntax.rng = uu____51639;_}
                ->
                let uu____51650 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____51650
                then
                  let res =
                    let uu____51679 = FStar_Common.force_thunk t  in
                    f uu____51679  in
                  ((let uu____51683 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____51683
                    then
                      let uu____51707 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____51709 =
                        FStar_Syntax_Print.emb_typ_to_string et'  in
                      let uu____51711 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____51716 = pa x2  in
                            Prims.op_Hat "Some " uu____51716
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____51707 uu____51709 uu____51711
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____51726 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____51726
                    then
                      let uu____51750 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____51752 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____51750 uu____51752
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____51757 ->
                let aopt = f x1  in
                ((let uu____51762 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____51762
                  then
                    let uu____51786 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____51788 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____51790 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____51795 = pa a  in
                          Prims.op_Hat "Some " uu____51795
                       in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____51786 uu____51788 uu____51790
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____51833 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____51833
       then
         let uu____51857 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____51857
       else ());
      t  in
    let un t _w _n =
      (let uu____51885 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____51885
       then
         let uu____51909 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____51909
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____51962 =
    let uu____51963 =
      let uu____51971 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____51971, [])  in
    FStar_Syntax_Syntax.ET_app uu____51963  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____51962
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___582_52003 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___582_52003.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___582_52003.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____52031 ->
        (if w
         then
           (let uu____52034 =
              let uu____52040 =
                let uu____52042 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____52042  in
              (FStar_Errors.Warning_NotEmbedded, uu____52040)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52034)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____52048 =
    let uu____52049 =
      let uu____52057 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____52057, [])  in
    FStar_Syntax_Syntax.ET_app uu____52049  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____52064  -> "()")
    uu____52048
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___602_52103 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___602_52103.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___602_52103.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____52139 ->
        (if w
         then
           (let uu____52142 =
              let uu____52148 =
                let uu____52150 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____52150  in
              (FStar_Errors.Warning_NotEmbedded, uu____52148)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52142)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____52157 =
    let uu____52158 =
      let uu____52166 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____52166, [])  in
    FStar_Syntax_Syntax.ET_app uu____52158  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____52157
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___621_52203 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___621_52203.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___621_52203.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____52237 ->
        (if w
         then
           (let uu____52240 =
              let uu____52246 =
                let uu____52248 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____52248  in
              (FStar_Errors.Warning_NotEmbedded, uu____52246)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52240)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____52255 =
    let uu____52256 =
      let uu____52264 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____52264, [])  in
    FStar_Syntax_Syntax.ET_app uu____52256  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____52255
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____52276 =
      let uu____52284 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____52284, [])  in
    FStar_Syntax_Syntax.ET_app uu____52276  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____52315  ->
         let uu____52316 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____52316)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____52351)) ->
             let uu____52366 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____52366
         | uu____52367 ->
             (if w
              then
                (let uu____52370 =
                   let uu____52376 =
                     let uu____52378 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____52378
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____52376)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                   uu____52370)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____52389 =
      let uu____52397 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____52397, [])  in
    FStar_Syntax_Syntax.ET_app uu____52389  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____52460)) -> FStar_Pervasives_Native.Some s
    | uu____52464 ->
        (if w
         then
           (let uu____52467 =
              let uu____52473 =
                let uu____52475 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____52475
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____52473)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52467)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_string
    (fun x  -> Prims.op_Hat "\"" (Prims.op_Hat x "\"")) emb_t_string
  
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let t_option_a =
      let t_opt = FStar_Syntax_Util.fvar_const FStar_Parser_Const.option_lid
         in
      let uu____52511 =
        let uu____52516 =
          let uu____52517 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____52517]  in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____52516  in
      uu____52511 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____52543 =
        let uu____52551 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____52551, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____52543  in
    let printer uu___430_52565 =
      match uu___430_52565 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____52571 =
            let uu____52573 = ea.print x  in Prims.op_Hat uu____52573 ")"  in
          Prims.op_Hat "(Some " uu____52571
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____52608  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____52609 =
                 let uu____52614 =
                   let uu____52615 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____52615
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____52616 =
                   let uu____52617 =
                     let uu____52626 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____52626  in
                   [uu____52617]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____52614 uu____52616  in
               uu____52609 FStar_Pervasives_Native.None rng
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
                        let uu____52656 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____52656  in
                      let uu____52657 =
                        let uu____52662 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____52663 =
                          let uu____52664 =
                            let uu____52673 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____52673  in
                          let uu____52674 =
                            let uu____52685 = FStar_Syntax_Syntax.as_arg t
                               in
                            [uu____52685]  in
                          uu____52664 :: uu____52674  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____52662 uu____52663
                         in
                      uu____52657 FStar_Pervasives_Native.None rng)
                  in
               let uu____52718 =
                 let uu____52723 =
                   let uu____52724 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____52724
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____52725 =
                   let uu____52726 =
                     let uu____52735 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____52735  in
                   let uu____52736 =
                     let uu____52747 =
                       let uu____52756 =
                         let uu____52757 = embed ea a  in
                         uu____52757 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____52756  in
                     [uu____52747]  in
                   uu____52726 :: uu____52736  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____52723 uu____52725  in
               uu____52718 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____52827 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____52827 with
           | (hd1,args) ->
               let uu____52868 =
                 let uu____52883 =
                   let uu____52884 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____52884.FStar_Syntax_Syntax.n  in
                 (uu____52883, args)  in
               (match uu____52868 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____52902) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____52926::(a,uu____52928)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____52979 =
                      let uu____52982 = unembed ea a  in uu____52982 w norm1
                       in
                    FStar_Util.bind_opt uu____52979
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____52995 ->
                    (if w
                     then
                       (let uu____53012 =
                          let uu____53018 =
                            let uu____53020 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____53020
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____53018)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____53012)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____53028 =
      let uu____53029 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____53029  in
    mk_emb_full em un uu____53028 printer emb_t_option_a
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2  in
        let uu____53071 =
          let uu____53076 =
            let uu____53077 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____53086 =
              let uu____53097 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____53097]  in
            uu____53077 :: uu____53086  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____53076  in
        uu____53071 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____53131 =
          let uu____53139 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____53139, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____53131  in
      let printer uu____53155 =
        match uu____53155 with
        | (x,y) ->
            let uu____53163 = ea.print x  in
            let uu____53165 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____53163 uu____53165
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____53208  ->
             let proj i ab =
               let uu____53224 =
                 let uu____53229 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____53231 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____53229
                   uu____53231 i
                  in
               match uu____53224 with
               | (proj_1,uu____53235) ->
                   let proj_1_tm =
                     let uu____53237 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____53237  in
                   let uu____53238 =
                     let uu____53243 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____53244 =
                       let uu____53245 =
                         let uu____53254 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____53254  in
                       let uu____53255 =
                         let uu____53266 =
                           let uu____53275 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____53275  in
                         let uu____53276 =
                           let uu____53287 = FStar_Syntax_Syntax.as_arg ab
                              in
                           [uu____53287]  in
                         uu____53266 :: uu____53276  in
                       uu____53245 :: uu____53255  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____53243 uu____53244
                      in
                   uu____53238 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____53332 =
               let uu____53337 =
                 let uu____53338 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____53338
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____53339 =
                 let uu____53340 =
                   let uu____53349 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____53349  in
                 let uu____53350 =
                   let uu____53361 =
                     let uu____53370 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____53370  in
                   let uu____53371 =
                     let uu____53382 =
                       let uu____53391 =
                         let uu____53392 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____53392 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____53391  in
                     let uu____53399 =
                       let uu____53410 =
                         let uu____53419 =
                           let uu____53420 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____53420 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____53419  in
                       [uu____53410]  in
                     uu____53382 :: uu____53399  in
                   uu____53361 :: uu____53371  in
                 uu____53340 :: uu____53350  in
               FStar_Syntax_Syntax.mk_Tm_app uu____53337 uu____53339  in
             uu____53332 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____53518 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____53518 with
             | (hd1,args) ->
                 let uu____53561 =
                   let uu____53574 =
                     let uu____53575 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____53575.FStar_Syntax_Syntax.n  in
                   (uu____53574, args)  in
                 (match uu____53561 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____53593::uu____53594::(a,uu____53596)::(b,uu____53598)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____53657 =
                        let uu____53660 = unembed ea a  in
                        uu____53660 w norm1  in
                      FStar_Util.bind_opt uu____53657
                        (fun a1  ->
                           let uu____53674 =
                             let uu____53677 = unembed eb b  in
                             uu____53677 w norm1  in
                           FStar_Util.bind_opt uu____53674
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____53694 ->
                      (if w
                       then
                         (let uu____53709 =
                            let uu____53715 =
                              let uu____53717 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____53717
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____53715)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____53709)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____53727 =
        let uu____53728 = type_of ea  in
        let uu____53729 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____53728 uu____53729  in
      mk_emb_full em un uu____53727 printer emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____53773 =
          let uu____53778 =
            let uu____53779 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____53788 =
              let uu____53799 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____53799]  in
            uu____53779 :: uu____53788  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____53778  in
        uu____53773 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____53833 =
          let uu____53841 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____53841, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____53833  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____53864 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____53864
        | FStar_Util.Inr b ->
            let uu____53868 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____53868
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____53914  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____53927 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____53927  in
                         let uu____53928 =
                           let uu____53933 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____53934 =
                             let uu____53935 =
                               let uu____53944 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____53944  in
                             let uu____53945 =
                               let uu____53956 =
                                 let uu____53965 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____53965  in
                               let uu____53966 =
                                 let uu____53977 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____53977]  in
                               uu____53956 :: uu____53966  in
                             uu____53935 :: uu____53945  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____53933
                             uu____53934
                            in
                         uu____53928 FStar_Pervasives_Native.None rng)
                     in
                  let uu____54018 =
                    let uu____54023 =
                      let uu____54024 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____54024
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____54025 =
                      let uu____54026 =
                        let uu____54035 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____54035  in
                      let uu____54036 =
                        let uu____54047 =
                          let uu____54056 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____54056  in
                        let uu____54057 =
                          let uu____54068 =
                            let uu____54077 =
                              let uu____54078 = embed ea a  in
                              uu____54078 rng shadow_a norm1  in
                            FStar_Syntax_Syntax.as_arg uu____54077  in
                          [uu____54068]  in
                        uu____54047 :: uu____54057  in
                      uu____54026 :: uu____54036  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____54023 uu____54025  in
                  uu____54018 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____54118  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____54131 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____54131  in
                         let uu____54132 =
                           let uu____54137 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____54138 =
                             let uu____54139 =
                               let uu____54148 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____54148  in
                             let uu____54149 =
                               let uu____54160 =
                                 let uu____54169 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____54169  in
                               let uu____54170 =
                                 let uu____54181 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____54181]  in
                               uu____54160 :: uu____54170  in
                             uu____54139 :: uu____54149  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____54137
                             uu____54138
                            in
                         uu____54132 FStar_Pervasives_Native.None rng)
                     in
                  let uu____54222 =
                    let uu____54227 =
                      let uu____54228 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____54228
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____54229 =
                      let uu____54230 =
                        let uu____54239 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____54239  in
                      let uu____54240 =
                        let uu____54251 =
                          let uu____54260 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____54260  in
                        let uu____54261 =
                          let uu____54272 =
                            let uu____54281 =
                              let uu____54282 = embed eb b  in
                              uu____54282 rng shadow_b norm1  in
                            FStar_Syntax_Syntax.as_arg uu____54281  in
                          [uu____54272]  in
                        uu____54251 :: uu____54261  in
                      uu____54230 :: uu____54240  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____54227 uu____54229  in
                  uu____54222 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____54370 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____54370 with
             | (hd1,args) ->
                 let uu____54413 =
                   let uu____54428 =
                     let uu____54429 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____54429.FStar_Syntax_Syntax.n  in
                   (uu____54428, args)  in
                 (match uu____54413 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____54449::uu____54450::(a,uu____54452)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____54519 =
                        let uu____54522 = unembed ea a  in
                        uu____54522 w norm1  in
                      FStar_Util.bind_opt uu____54519
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____54540::uu____54541::(b,uu____54543)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____54610 =
                        let uu____54613 = unembed eb b  in
                        uu____54613 w norm1  in
                      FStar_Util.bind_opt uu____54610
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____54630 ->
                      (if w
                       then
                         (let uu____54647 =
                            let uu____54653 =
                              let uu____54655 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____54655
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____54653)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____54647)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____54665 =
        let uu____54666 = type_of ea  in
        let uu____54667 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____54666 uu____54667  in
      mk_emb_full em un uu____54665 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____54695 =
        let uu____54700 =
          let uu____54701 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____54701]  in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____54700  in
      uu____54695 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____54727 =
        let uu____54735 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____54735, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____54727  in
    let printer l =
      let uu____54752 =
        let uu____54754 =
          let uu____54756 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____54756 (FStar_String.concat "; ")  in
        Prims.op_Hat uu____54754 "]"  in
      Prims.op_Hat "[" uu____54752  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____54800  ->
           let t =
             let uu____54802 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____54802  in
           match l with
           | [] ->
               let uu____54803 =
                 let uu____54808 =
                   let uu____54809 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____54809
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____54808 [t]  in
               uu____54803 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____54831 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____54831
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____54851 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____54851  in
                 let uu____54852 =
                   let uu____54857 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____54858 =
                     let uu____54859 =
                       let uu____54868 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____54868  in
                     let uu____54869 =
                       let uu____54880 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____54880]  in
                     uu____54859 :: uu____54869  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____54857 uu____54858  in
                 uu____54852 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____54917 =
                 let uu____54922 =
                   let uu____54923 =
                     let uu____54934 =
                       let uu____54943 =
                         let uu____54944 = embed ea hd1  in
                         uu____54944 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____54943  in
                     let uu____54951 =
                       let uu____54962 =
                         let uu____54971 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____54971  in
                       [uu____54962]  in
                     uu____54934 :: uu____54951  in
                   t :: uu____54923  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____54922  in
               uu____54917 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____55043 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____55043 with
           | (hd1,args) ->
               let uu____55084 =
                 let uu____55097 =
                   let uu____55098 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____55098.FStar_Syntax_Syntax.n  in
                 (uu____55097, args)  in
               (match uu____55084 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____55114) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____55134,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____55135))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____55177 =
                      let uu____55180 = unembed ea hd2  in
                      uu____55180 w norm1  in
                    FStar_Util.bind_opt uu____55177
                      (fun hd3  ->
                         let uu____55192 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____55192
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____55240 =
                      let uu____55243 = unembed ea hd2  in
                      uu____55243 w norm1  in
                    FStar_Util.bind_opt uu____55240
                      (fun hd3  ->
                         let uu____55255 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____55255
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____55270 ->
                    (if w
                     then
                       (let uu____55285 =
                          let uu____55291 =
                            let uu____55293 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____55293
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____55291)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____55285)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____55301 =
      let uu____55302 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____55302  in
    mk_emb_full em un uu____55301 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____55345 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____55356 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____55367 -> false
  
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____55378 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____55389 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____55400 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____55411 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____55422 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____55437 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____55468 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____55499 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____55526 -> false
  
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
    let uu____55544 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____55544  in
  let emb_t_norm_step =
    let uu____55547 =
      let uu____55555 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____55555, [])  in
    FStar_Syntax_Syntax.ET_app uu____55547  in
  let printer uu____55567 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____55593  ->
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
             let uu____55598 =
               let uu____55603 =
                 let uu____55604 =
                   let uu____55613 =
                     let uu____55614 =
                       let uu____55621 = e_list e_string  in
                       embed uu____55621 l  in
                     uu____55614 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____55613  in
                 [uu____55604]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____55603  in
             uu____55598 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____55653 =
               let uu____55658 =
                 let uu____55659 =
                   let uu____55668 =
                     let uu____55669 =
                       let uu____55676 = e_list e_string  in
                       embed uu____55676 l  in
                     uu____55669 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____55668  in
                 [uu____55659]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____55658
                in
             uu____55653 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____55708 =
               let uu____55713 =
                 let uu____55714 =
                   let uu____55723 =
                     let uu____55724 =
                       let uu____55731 = e_list e_string  in
                       embed uu____55731 l  in
                     uu____55724 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____55723  in
                 [uu____55714]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____55713  in
             uu____55708 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____55791 = FStar_Syntax_Util.head_and_args t1  in
         match uu____55791 with
         | (hd1,args) ->
             let uu____55836 =
               let uu____55851 =
                 let uu____55852 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____55852.FStar_Syntax_Syntax.n  in
               (uu____55851, args)  in
             (match uu____55836 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____56040)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____56075 =
                    let uu____56081 =
                      let uu____56091 = e_list e_string  in
                      unembed uu____56091 l  in
                    uu____56081 w norm1  in
                  FStar_Util.bind_opt uu____56075
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _56111  -> FStar_Pervasives_Native.Some _56111)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____56114)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____56149 =
                    let uu____56155 =
                      let uu____56165 = e_list e_string  in
                      unembed uu____56165 l  in
                    uu____56155 w norm1  in
                  FStar_Util.bind_opt uu____56149
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _56185  -> FStar_Pervasives_Native.Some _56185)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____56188)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____56223 =
                    let uu____56229 =
                      let uu____56239 = e_list e_string  in
                      unembed uu____56239 l  in
                    uu____56229 w norm1  in
                  FStar_Util.bind_opt uu____56223
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _56259  -> FStar_Pervasives_Native.Some _56259)
                         (UnfoldAttr ss))
              | uu____56260 ->
                  (if w
                   then
                     (let uu____56277 =
                        let uu____56283 =
                          let uu____56285 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____56285
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____56283)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____56277)
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
    | uu____56345 ->
        (if w
         then
           (let uu____56348 =
              let uu____56354 =
                let uu____56356 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____56356
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____56354)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____56348)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____56362 =
    let uu____56363 =
      let uu____56371 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____56371, [])  in
    FStar_Syntax_Syntax.ET_app uu____56363  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____56362
  
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
        let uu____56442 =
          let uu____56449 =
            let uu____56450 =
              let uu____56465 =
                let uu____56474 =
                  let uu____56481 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____56481, FStar_Pervasives_Native.None)  in
                [uu____56474]  in
              let uu____56496 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____56465, uu____56496)  in
            FStar_Syntax_Syntax.Tm_arrow uu____56450  in
          FStar_Syntax_Syntax.mk uu____56449  in
        uu____56442 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____56568  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____56574  ->
             let uu____56575 = force_shadow shadow_f  in
             match uu____56575 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____56580 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____56580
                   then
                     let uu____56604 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____56606 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____56604 uu____56606
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f)  in
                   (let uu____56613 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____56613
                    then
                      let uu____56637 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____56639 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____56641 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____56637 uu____56639 uu____56641
                    else ());
                   res)))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               (let uu____56700 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____56700
                then
                  let uu____56724 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____56726 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____56724
                    uu____56726
                else ());
               (let a_tm =
                  let uu____56732 = embed ea a  in
                  uu____56732 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1
                   in
                let b_tm =
                  let uu____56742 =
                    let uu____56747 =
                      let uu____56748 =
                        let uu____56753 =
                          let uu____56754 = FStar_Syntax_Syntax.as_arg a_tm
                             in
                          [uu____56754]  in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____56753  in
                      uu____56748 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____56747  in
                  norm1 uu____56742  in
                let uu____56779 =
                  let uu____56782 = unembed eb b_tm  in uu____56782 w norm1
                   in
                match uu____56779 with
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
                let uu____56876 = FStar_List.splitAt n_tvars args  in
                match uu____56876 with
                | (_tvar_args,rest_args) ->
                    let uu____56953 = FStar_List.hd rest_args  in
                    (match uu____56953 with
                     | (x,uu____56973) ->
                         let shadow_app =
                           let uu____56987 =
                             FStar_Common.mk_thunk
                               (fun uu____56994  ->
                                  let uu____56995 =
                                    let uu____57000 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____57000
                                      args
                                     in
                                  uu____56995 FStar_Pervasives_Native.None
                                    rng)
                              in
                           FStar_Pervasives_Native.Some uu____56987  in
                         let uu____57003 =
                           let uu____57006 =
                             let uu____57009 = unembed ea x  in
                             uu____57009 true norm1  in
                           FStar_Util.map_opt uu____57006
                             (fun x1  ->
                                let uu____57020 =
                                  let uu____57027 = f x1  in
                                  embed eb uu____57027  in
                                uu____57020 rng shadow_app norm1)
                            in
                         (match uu____57003 with
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
                  let uu____57130 = FStar_List.splitAt n_tvars args  in
                  match uu____57130 with
                  | (_tvar_args,rest_args) ->
                      let uu____57193 = FStar_List.hd rest_args  in
                      (match uu____57193 with
                       | (x,uu____57209) ->
                           let uu____57214 =
                             let uu____57221 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____57221  in
                           (match uu____57214 with
                            | (y,uu____57245) ->
                                let shadow_app =
                                  let uu____57255 =
                                    FStar_Common.mk_thunk
                                      (fun uu____57262  ->
                                         let uu____57263 =
                                           let uu____57268 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____57268 args
                                            in
                                         uu____57263
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____57255
                                   in
                                let uu____57271 =
                                  let uu____57274 =
                                    let uu____57277 = unembed ea x  in
                                    uu____57277 true norm1  in
                                  FStar_Util.bind_opt uu____57274
                                    (fun x1  ->
                                       let uu____57288 =
                                         let uu____57291 = unembed eb y  in
                                         uu____57291 true norm1  in
                                       FStar_Util.bind_opt uu____57288
                                         (fun y1  ->
                                            let uu____57302 =
                                              let uu____57303 =
                                                let uu____57310 = f x1 y1  in
                                                embed ec uu____57310  in
                                              uu____57303 rng shadow_app
                                                norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____57302))
                                   in
                                (match uu____57271 with
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
                    let uu____57432 = FStar_List.splitAt n_tvars args  in
                    match uu____57432 with
                    | (_tvar_args,rest_args) ->
                        let uu____57495 = FStar_List.hd rest_args  in
                        (match uu____57495 with
                         | (x,uu____57511) ->
                             let uu____57516 =
                               let uu____57523 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____57523  in
                             (match uu____57516 with
                              | (y,uu____57547) ->
                                  let uu____57552 =
                                    let uu____57559 =
                                      let uu____57568 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____57568  in
                                    FStar_List.hd uu____57559  in
                                  (match uu____57552 with
                                   | (z,uu____57598) ->
                                       let shadow_app =
                                         let uu____57608 =
                                           FStar_Common.mk_thunk
                                             (fun uu____57615  ->
                                                let uu____57616 =
                                                  let uu____57621 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____57621 args
                                                   in
                                                uu____57616
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____57608
                                          in
                                       let uu____57624 =
                                         let uu____57627 =
                                           let uu____57630 = unembed ea x  in
                                           uu____57630 true norm1  in
                                         FStar_Util.bind_opt uu____57627
                                           (fun x1  ->
                                              let uu____57641 =
                                                let uu____57644 =
                                                  unembed eb y  in
                                                uu____57644 true norm1  in
                                              FStar_Util.bind_opt uu____57641
                                                (fun y1  ->
                                                   let uu____57655 =
                                                     let uu____57658 =
                                                       unembed ec z  in
                                                     uu____57658 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____57655
                                                     (fun z1  ->
                                                        let uu____57669 =
                                                          let uu____57670 =
                                                            let uu____57677 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____57677
                                                             in
                                                          uu____57670 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____57669)))
                                          in
                                       (match uu____57624 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____57707 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____57707 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____57736 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____57736 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  