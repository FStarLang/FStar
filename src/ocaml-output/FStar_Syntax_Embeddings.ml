open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___429_50707  ->
    match uu___429_50707 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____50714 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____50714
  
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embedding_failure  -> true | uu____50724 -> false
  
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unembedding_failure  -> true
    | uu____50735 -> false
  
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
             (fun uu____50767  ->
                let uu____50768 = FStar_Common.force_thunk s1  in
                f uu____50768))
  
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
  'Auu____51130 . FStar_Syntax_Syntax.term -> 'Auu____51130 -> Prims.string =
  fun typ  ->
    fun uu____51141  ->
      let uu____51142 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____51142
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____51151 =
      let uu____51152 = FStar_Syntax_Subst.compress t  in
      uu____51152.FStar_Syntax_Syntax.n  in
    match uu____51151 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____51156 ->
        let uu____51157 =
          let uu____51159 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____51159
           in
        failwith uu____51157
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____51202 =
          let uu____51203 =
            let uu____51211 =
              let uu____51213 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____51213 FStar_Ident.string_of_lid  in
            (uu____51211, [])  in
          FStar_Syntax_Syntax.ET_app uu____51203  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____51202 }
  
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
      fun n1  -> let uu____51362 = unembed e t  in uu____51362 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      fun n1  -> let uu____51403 = unembed e t  in uu____51403 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___508_51450 = e  in
      {
        em = (uu___508_51450.em);
        un = (uu___508_51450.un);
        typ = ty;
        print = (uu___508_51450.print);
        emb_typ = (uu___508_51450.emb_typ)
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
              (let uu____51513 =
                 FStar_ST.op_Bang FStar_Options.debug_embedding  in
               if uu____51513
               then
                 let uu____51537 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____51539 = FStar_Syntax_Print.emb_typ_to_string et
                    in
                 let uu____51541 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n"
                   uu____51537 uu____51539 uu____51541
               else ());
              (let uu____51546 =
                 FStar_ST.op_Bang FStar_Options.eager_embedding  in
               if uu____51546
               then f ()
               else
                 (let thunk1 = FStar_Common.mk_thunk f  in
                  let uu____51581 =
                    let uu____51588 =
                      let uu____51589 =
                        let uu____51590 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____51590;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk1));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____51589  in
                    FStar_Syntax_Syntax.mk uu____51588  in
                  uu____51581 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____51657;
                  FStar_Syntax_Syntax.rng = uu____51658;_}
                ->
                let uu____51669 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____51669
                then
                  let res =
                    let uu____51698 = FStar_Common.force_thunk t  in
                    f uu____51698  in
                  ((let uu____51702 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____51702
                    then
                      let uu____51726 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____51728 =
                        FStar_Syntax_Print.emb_typ_to_string et'  in
                      let uu____51730 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____51735 = pa x2  in
                            Prims.op_Hat "Some " uu____51735
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____51726 uu____51728 uu____51730
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____51745 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____51745
                    then
                      let uu____51769 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____51771 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____51769 uu____51771
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____51776 ->
                let aopt = f x1  in
                ((let uu____51781 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____51781
                  then
                    let uu____51805 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____51807 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____51809 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____51814 = pa a  in
                          Prims.op_Hat "Some " uu____51814
                       in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____51805 uu____51807 uu____51809
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____51852 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____51852
       then
         let uu____51876 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____51876
       else ());
      t  in
    let un t _w _n =
      (let uu____51904 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____51904
       then
         let uu____51928 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____51928
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____51981 =
    let uu____51982 =
      let uu____51990 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____51990, [])  in
    FStar_Syntax_Syntax.ET_app uu____51982  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____51981
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___582_52022 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___582_52022.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___582_52022.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____52050 ->
        (if w
         then
           (let uu____52053 =
              let uu____52059 =
                let uu____52061 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____52061  in
              (FStar_Errors.Warning_NotEmbedded, uu____52059)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52053)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____52067 =
    let uu____52068 =
      let uu____52076 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____52076, [])  in
    FStar_Syntax_Syntax.ET_app uu____52068  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____52083  -> "()")
    uu____52067
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___602_52122 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___602_52122.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___602_52122.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____52158 ->
        (if w
         then
           (let uu____52161 =
              let uu____52167 =
                let uu____52169 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____52169  in
              (FStar_Errors.Warning_NotEmbedded, uu____52167)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52161)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____52176 =
    let uu____52177 =
      let uu____52185 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____52185, [])  in
    FStar_Syntax_Syntax.ET_app uu____52177  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____52176
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___621_52222 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___621_52222.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___621_52222.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____52256 ->
        (if w
         then
           (let uu____52259 =
              let uu____52265 =
                let uu____52267 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____52267  in
              (FStar_Errors.Warning_NotEmbedded, uu____52265)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52259)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____52274 =
    let uu____52275 =
      let uu____52283 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____52283, [])  in
    FStar_Syntax_Syntax.ET_app uu____52275  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____52274
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____52295 =
      let uu____52303 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____52303, [])  in
    FStar_Syntax_Syntax.ET_app uu____52295  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____52334  ->
         let uu____52335 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____52335)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____52370)) ->
             let uu____52385 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____52385
         | uu____52386 ->
             (if w
              then
                (let uu____52389 =
                   let uu____52395 =
                     let uu____52397 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____52397
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____52395)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                   uu____52389)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____52408 =
      let uu____52416 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____52416, [])  in
    FStar_Syntax_Syntax.ET_app uu____52408  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____52479)) -> FStar_Pervasives_Native.Some s
    | uu____52483 ->
        (if w
         then
           (let uu____52486 =
              let uu____52492 =
                let uu____52494 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____52494
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____52492)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52486)
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
      let uu____52530 =
        let uu____52535 =
          let uu____52536 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____52536]  in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____52535  in
      uu____52530 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____52562 =
        let uu____52570 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____52570, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____52562  in
    let printer uu___430_52584 =
      match uu___430_52584 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____52590 =
            let uu____52592 = ea.print x  in Prims.op_Hat uu____52592 ")"  in
          Prims.op_Hat "(Some " uu____52590
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____52627  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____52628 =
                 let uu____52633 =
                   let uu____52634 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____52634
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____52635 =
                   let uu____52636 =
                     let uu____52645 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____52645  in
                   [uu____52636]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____52633 uu____52635  in
               uu____52628 FStar_Pervasives_Native.None rng
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
                        let uu____52675 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____52675  in
                      let uu____52676 =
                        let uu____52681 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____52682 =
                          let uu____52683 =
                            let uu____52692 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____52692  in
                          let uu____52693 =
                            let uu____52704 = FStar_Syntax_Syntax.as_arg t
                               in
                            [uu____52704]  in
                          uu____52683 :: uu____52693  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____52681 uu____52682
                         in
                      uu____52676 FStar_Pervasives_Native.None rng)
                  in
               let uu____52737 =
                 let uu____52742 =
                   let uu____52743 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____52743
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____52744 =
                   let uu____52745 =
                     let uu____52754 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____52754  in
                   let uu____52755 =
                     let uu____52766 =
                       let uu____52775 =
                         let uu____52776 = embed ea a  in
                         uu____52776 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____52775  in
                     [uu____52766]  in
                   uu____52745 :: uu____52755  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____52742 uu____52744  in
               uu____52737 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____52846 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____52846 with
           | (hd1,args) ->
               let uu____52887 =
                 let uu____52902 =
                   let uu____52903 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____52903.FStar_Syntax_Syntax.n  in
                 (uu____52902, args)  in
               (match uu____52887 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____52921) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____52945::(a,uu____52947)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____52998 =
                      let uu____53001 = unembed ea a  in uu____53001 w norm1
                       in
                    FStar_Util.bind_opt uu____52998
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____53014 ->
                    (if w
                     then
                       (let uu____53031 =
                          let uu____53037 =
                            let uu____53039 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____53039
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____53037)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____53031)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____53047 =
      let uu____53048 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____53048  in
    mk_emb_full em un uu____53047 printer emb_t_option_a
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2  in
        let uu____53090 =
          let uu____53095 =
            let uu____53096 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____53105 =
              let uu____53116 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____53116]  in
            uu____53096 :: uu____53105  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____53095  in
        uu____53090 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____53150 =
          let uu____53158 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____53158, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____53150  in
      let printer uu____53174 =
        match uu____53174 with
        | (x,y) ->
            let uu____53182 = ea.print x  in
            let uu____53184 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____53182 uu____53184
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____53227  ->
             let proj i ab =
               let uu____53243 =
                 let uu____53248 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____53250 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____53248
                   uu____53250 i
                  in
               match uu____53243 with
               | (proj_1,uu____53254) ->
                   let proj_1_tm =
                     let uu____53256 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____53256  in
                   let uu____53257 =
                     let uu____53262 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____53263 =
                       let uu____53264 =
                         let uu____53273 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____53273  in
                       let uu____53274 =
                         let uu____53285 =
                           let uu____53294 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____53294  in
                         let uu____53295 =
                           let uu____53306 = FStar_Syntax_Syntax.as_arg ab
                              in
                           [uu____53306]  in
                         uu____53285 :: uu____53295  in
                       uu____53264 :: uu____53274  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____53262 uu____53263
                      in
                   uu____53257 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____53351 =
               let uu____53356 =
                 let uu____53357 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____53357
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____53358 =
                 let uu____53359 =
                   let uu____53368 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____53368  in
                 let uu____53369 =
                   let uu____53380 =
                     let uu____53389 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____53389  in
                   let uu____53390 =
                     let uu____53401 =
                       let uu____53410 =
                         let uu____53411 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____53411 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____53410  in
                     let uu____53418 =
                       let uu____53429 =
                         let uu____53438 =
                           let uu____53439 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____53439 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____53438  in
                       [uu____53429]  in
                     uu____53401 :: uu____53418  in
                   uu____53380 :: uu____53390  in
                 uu____53359 :: uu____53369  in
               FStar_Syntax_Syntax.mk_Tm_app uu____53356 uu____53358  in
             uu____53351 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____53537 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____53537 with
             | (hd1,args) ->
                 let uu____53580 =
                   let uu____53593 =
                     let uu____53594 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____53594.FStar_Syntax_Syntax.n  in
                   (uu____53593, args)  in
                 (match uu____53580 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____53612::uu____53613::(a,uu____53615)::(b,uu____53617)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____53676 =
                        let uu____53679 = unembed ea a  in
                        uu____53679 w norm1  in
                      FStar_Util.bind_opt uu____53676
                        (fun a1  ->
                           let uu____53693 =
                             let uu____53696 = unembed eb b  in
                             uu____53696 w norm1  in
                           FStar_Util.bind_opt uu____53693
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____53713 ->
                      (if w
                       then
                         (let uu____53728 =
                            let uu____53734 =
                              let uu____53736 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____53736
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____53734)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____53728)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____53746 =
        let uu____53747 = type_of ea  in
        let uu____53748 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____53747 uu____53748  in
      mk_emb_full em un uu____53746 printer emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____53792 =
          let uu____53797 =
            let uu____53798 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____53807 =
              let uu____53818 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____53818]  in
            uu____53798 :: uu____53807  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____53797  in
        uu____53792 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____53852 =
          let uu____53860 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____53860, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____53852  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____53883 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____53883
        | FStar_Util.Inr b ->
            let uu____53887 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____53887
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____53933  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____53946 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____53946  in
                         let uu____53947 =
                           let uu____53952 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____53953 =
                             let uu____53954 =
                               let uu____53963 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____53963  in
                             let uu____53964 =
                               let uu____53975 =
                                 let uu____53984 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____53984  in
                               let uu____53985 =
                                 let uu____53996 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____53996]  in
                               uu____53975 :: uu____53985  in
                             uu____53954 :: uu____53964  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____53952
                             uu____53953
                            in
                         uu____53947 FStar_Pervasives_Native.None rng)
                     in
                  let uu____54037 =
                    let uu____54042 =
                      let uu____54043 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____54043
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____54044 =
                      let uu____54045 =
                        let uu____54054 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____54054  in
                      let uu____54055 =
                        let uu____54066 =
                          let uu____54075 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____54075  in
                        let uu____54076 =
                          let uu____54087 =
                            let uu____54096 =
                              let uu____54097 = embed ea a  in
                              uu____54097 rng shadow_a norm1  in
                            FStar_Syntax_Syntax.as_arg uu____54096  in
                          [uu____54087]  in
                        uu____54066 :: uu____54076  in
                      uu____54045 :: uu____54055  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____54042 uu____54044  in
                  uu____54037 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____54137  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____54150 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____54150  in
                         let uu____54151 =
                           let uu____54156 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____54157 =
                             let uu____54158 =
                               let uu____54167 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____54167  in
                             let uu____54168 =
                               let uu____54179 =
                                 let uu____54188 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____54188  in
                               let uu____54189 =
                                 let uu____54200 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____54200]  in
                               uu____54179 :: uu____54189  in
                             uu____54158 :: uu____54168  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____54156
                             uu____54157
                            in
                         uu____54151 FStar_Pervasives_Native.None rng)
                     in
                  let uu____54241 =
                    let uu____54246 =
                      let uu____54247 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____54247
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____54248 =
                      let uu____54249 =
                        let uu____54258 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____54258  in
                      let uu____54259 =
                        let uu____54270 =
                          let uu____54279 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____54279  in
                        let uu____54280 =
                          let uu____54291 =
                            let uu____54300 =
                              let uu____54301 = embed eb b  in
                              uu____54301 rng shadow_b norm1  in
                            FStar_Syntax_Syntax.as_arg uu____54300  in
                          [uu____54291]  in
                        uu____54270 :: uu____54280  in
                      uu____54249 :: uu____54259  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____54246 uu____54248  in
                  uu____54241 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____54389 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____54389 with
             | (hd1,args) ->
                 let uu____54432 =
                   let uu____54447 =
                     let uu____54448 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____54448.FStar_Syntax_Syntax.n  in
                   (uu____54447, args)  in
                 (match uu____54432 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____54468::uu____54469::(a,uu____54471)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____54538 =
                        let uu____54541 = unembed ea a  in
                        uu____54541 w norm1  in
                      FStar_Util.bind_opt uu____54538
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____54559::uu____54560::(b,uu____54562)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____54629 =
                        let uu____54632 = unembed eb b  in
                        uu____54632 w norm1  in
                      FStar_Util.bind_opt uu____54629
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____54649 ->
                      (if w
                       then
                         (let uu____54666 =
                            let uu____54672 =
                              let uu____54674 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____54674
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____54672)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____54666)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____54684 =
        let uu____54685 = type_of ea  in
        let uu____54686 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____54685 uu____54686  in
      mk_emb_full em un uu____54684 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____54714 =
        let uu____54719 =
          let uu____54720 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____54720]  in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____54719  in
      uu____54714 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____54746 =
        let uu____54754 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____54754, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____54746  in
    let printer l =
      let uu____54771 =
        let uu____54773 =
          let uu____54775 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____54775 (FStar_String.concat "; ")  in
        Prims.op_Hat uu____54773 "]"  in
      Prims.op_Hat "[" uu____54771  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____54819  ->
           let t =
             let uu____54821 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____54821  in
           match l with
           | [] ->
               let uu____54822 =
                 let uu____54827 =
                   let uu____54828 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____54828
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____54827 [t]  in
               uu____54822 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____54850 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____54850
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____54870 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____54870  in
                 let uu____54871 =
                   let uu____54876 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____54877 =
                     let uu____54878 =
                       let uu____54887 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____54887  in
                     let uu____54888 =
                       let uu____54899 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____54899]  in
                     uu____54878 :: uu____54888  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____54876 uu____54877  in
                 uu____54871 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____54936 =
                 let uu____54941 =
                   let uu____54942 =
                     let uu____54953 =
                       let uu____54962 =
                         let uu____54963 = embed ea hd1  in
                         uu____54963 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____54962  in
                     let uu____54970 =
                       let uu____54981 =
                         let uu____54990 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____54990  in
                       [uu____54981]  in
                     uu____54953 :: uu____54970  in
                   t :: uu____54942  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____54941  in
               uu____54936 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____55062 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____55062 with
           | (hd1,args) ->
               let uu____55103 =
                 let uu____55116 =
                   let uu____55117 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____55117.FStar_Syntax_Syntax.n  in
                 (uu____55116, args)  in
               (match uu____55103 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____55133) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____55153,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____55154))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____55196 =
                      let uu____55199 = unembed ea hd2  in
                      uu____55199 w norm1  in
                    FStar_Util.bind_opt uu____55196
                      (fun hd3  ->
                         let uu____55211 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____55211
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____55259 =
                      let uu____55262 = unembed ea hd2  in
                      uu____55262 w norm1  in
                    FStar_Util.bind_opt uu____55259
                      (fun hd3  ->
                         let uu____55274 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____55274
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____55289 ->
                    (if w
                     then
                       (let uu____55304 =
                          let uu____55310 =
                            let uu____55312 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____55312
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____55310)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____55304)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____55320 =
      let uu____55321 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____55321  in
    mk_emb_full em un uu____55320 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____55364 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____55375 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____55386 -> false
  
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____55397 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____55408 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____55419 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____55430 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____55441 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____55456 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____55487 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____55518 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____55545 -> false
  
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
    let uu____55563 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____55563  in
  let emb_t_norm_step =
    let uu____55566 =
      let uu____55574 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____55574, [])  in
    FStar_Syntax_Syntax.ET_app uu____55566  in
  let printer uu____55586 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____55612  ->
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
             let uu____55617 =
               let uu____55622 =
                 let uu____55623 =
                   let uu____55632 =
                     let uu____55633 =
                       let uu____55640 = e_list e_string  in
                       embed uu____55640 l  in
                     uu____55633 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____55632  in
                 [uu____55623]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____55622  in
             uu____55617 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____55672 =
               let uu____55677 =
                 let uu____55678 =
                   let uu____55687 =
                     let uu____55688 =
                       let uu____55695 = e_list e_string  in
                       embed uu____55695 l  in
                     uu____55688 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____55687  in
                 [uu____55678]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____55677
                in
             uu____55672 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____55727 =
               let uu____55732 =
                 let uu____55733 =
                   let uu____55742 =
                     let uu____55743 =
                       let uu____55750 = e_list e_string  in
                       embed uu____55750 l  in
                     uu____55743 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____55742  in
                 [uu____55733]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____55732  in
             uu____55727 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____55810 = FStar_Syntax_Util.head_and_args t1  in
         match uu____55810 with
         | (hd1,args) ->
             let uu____55855 =
               let uu____55870 =
                 let uu____55871 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____55871.FStar_Syntax_Syntax.n  in
               (uu____55870, args)  in
             (match uu____55855 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____56059)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____56094 =
                    let uu____56100 =
                      let uu____56110 = e_list e_string  in
                      unembed uu____56110 l  in
                    uu____56100 w norm1  in
                  FStar_Util.bind_opt uu____56094
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _56130  -> FStar_Pervasives_Native.Some _56130)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____56133)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____56168 =
                    let uu____56174 =
                      let uu____56184 = e_list e_string  in
                      unembed uu____56184 l  in
                    uu____56174 w norm1  in
                  FStar_Util.bind_opt uu____56168
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _56204  -> FStar_Pervasives_Native.Some _56204)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____56207)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____56242 =
                    let uu____56248 =
                      let uu____56258 = e_list e_string  in
                      unembed uu____56258 l  in
                    uu____56248 w norm1  in
                  FStar_Util.bind_opt uu____56242
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _56278  -> FStar_Pervasives_Native.Some _56278)
                         (UnfoldAttr ss))
              | uu____56279 ->
                  (if w
                   then
                     (let uu____56296 =
                        let uu____56302 =
                          let uu____56304 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____56304
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____56302)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____56296)
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
    | uu____56364 ->
        (if w
         then
           (let uu____56367 =
              let uu____56373 =
                let uu____56375 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____56375
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____56373)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____56367)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____56381 =
    let uu____56382 =
      let uu____56390 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____56390, [])  in
    FStar_Syntax_Syntax.ET_app uu____56382  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____56381
  
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
        let uu____56461 =
          let uu____56468 =
            let uu____56469 =
              let uu____56484 =
                let uu____56493 =
                  let uu____56500 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____56500, FStar_Pervasives_Native.None)  in
                [uu____56493]  in
              let uu____56515 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____56484, uu____56515)  in
            FStar_Syntax_Syntax.Tm_arrow uu____56469  in
          FStar_Syntax_Syntax.mk uu____56468  in
        uu____56461 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____56587  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____56593  ->
             let uu____56594 = force_shadow shadow_f  in
             match uu____56594 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____56599 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____56599
                   then
                     let uu____56623 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____56625 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____56623 uu____56625
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f)  in
                   (let uu____56632 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____56632
                    then
                      let uu____56656 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____56658 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____56660 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____56656 uu____56658 uu____56660
                    else ());
                   res)))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               (let uu____56719 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____56719
                then
                  let uu____56743 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____56745 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____56743
                    uu____56745
                else ());
               (let a_tm =
                  let uu____56751 = embed ea a  in
                  uu____56751 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1
                   in
                let b_tm =
                  let uu____56761 =
                    let uu____56766 =
                      let uu____56767 =
                        let uu____56772 =
                          let uu____56773 = FStar_Syntax_Syntax.as_arg a_tm
                             in
                          [uu____56773]  in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____56772  in
                      uu____56767 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____56766  in
                  norm1 uu____56761  in
                let uu____56798 =
                  let uu____56801 = unembed eb b_tm  in uu____56801 w norm1
                   in
                match uu____56798 with
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
                let uu____56895 = FStar_List.splitAt n_tvars args  in
                match uu____56895 with
                | (_tvar_args,rest_args) ->
                    let uu____56972 = FStar_List.hd rest_args  in
                    (match uu____56972 with
                     | (x,uu____56992) ->
                         let shadow_app =
                           let uu____57006 =
                             FStar_Common.mk_thunk
                               (fun uu____57013  ->
                                  let uu____57014 =
                                    let uu____57019 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____57019
                                      args
                                     in
                                  uu____57014 FStar_Pervasives_Native.None
                                    rng)
                              in
                           FStar_Pervasives_Native.Some uu____57006  in
                         let uu____57022 =
                           let uu____57025 =
                             let uu____57028 = unembed ea x  in
                             uu____57028 true norm1  in
                           FStar_Util.map_opt uu____57025
                             (fun x1  ->
                                let uu____57039 =
                                  let uu____57046 = f x1  in
                                  embed eb uu____57046  in
                                uu____57039 rng shadow_app norm1)
                            in
                         (match uu____57022 with
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
                  let uu____57149 = FStar_List.splitAt n_tvars args  in
                  match uu____57149 with
                  | (_tvar_args,rest_args) ->
                      let uu____57212 = FStar_List.hd rest_args  in
                      (match uu____57212 with
                       | (x,uu____57228) ->
                           let uu____57233 =
                             let uu____57240 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____57240  in
                           (match uu____57233 with
                            | (y,uu____57264) ->
                                let shadow_app =
                                  let uu____57274 =
                                    FStar_Common.mk_thunk
                                      (fun uu____57281  ->
                                         let uu____57282 =
                                           let uu____57287 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____57287 args
                                            in
                                         uu____57282
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____57274
                                   in
                                let uu____57290 =
                                  let uu____57293 =
                                    let uu____57296 = unembed ea x  in
                                    uu____57296 true norm1  in
                                  FStar_Util.bind_opt uu____57293
                                    (fun x1  ->
                                       let uu____57307 =
                                         let uu____57310 = unembed eb y  in
                                         uu____57310 true norm1  in
                                       FStar_Util.bind_opt uu____57307
                                         (fun y1  ->
                                            let uu____57321 =
                                              let uu____57322 =
                                                let uu____57329 = f x1 y1  in
                                                embed ec uu____57329  in
                                              uu____57322 rng shadow_app
                                                norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____57321))
                                   in
                                (match uu____57290 with
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
                    let uu____57451 = FStar_List.splitAt n_tvars args  in
                    match uu____57451 with
                    | (_tvar_args,rest_args) ->
                        let uu____57514 = FStar_List.hd rest_args  in
                        (match uu____57514 with
                         | (x,uu____57530) ->
                             let uu____57535 =
                               let uu____57542 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____57542  in
                             (match uu____57535 with
                              | (y,uu____57566) ->
                                  let uu____57571 =
                                    let uu____57578 =
                                      let uu____57587 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____57587  in
                                    FStar_List.hd uu____57578  in
                                  (match uu____57571 with
                                   | (z,uu____57617) ->
                                       let shadow_app =
                                         let uu____57627 =
                                           FStar_Common.mk_thunk
                                             (fun uu____57634  ->
                                                let uu____57635 =
                                                  let uu____57640 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____57640 args
                                                   in
                                                uu____57635
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____57627
                                          in
                                       let uu____57643 =
                                         let uu____57646 =
                                           let uu____57649 = unembed ea x  in
                                           uu____57649 true norm1  in
                                         FStar_Util.bind_opt uu____57646
                                           (fun x1  ->
                                              let uu____57660 =
                                                let uu____57663 =
                                                  unembed eb y  in
                                                uu____57663 true norm1  in
                                              FStar_Util.bind_opt uu____57660
                                                (fun y1  ->
                                                   let uu____57674 =
                                                     let uu____57677 =
                                                       unembed ec z  in
                                                     uu____57677 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____57674
                                                     (fun z1  ->
                                                        let uu____57688 =
                                                          let uu____57689 =
                                                            let uu____57696 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____57696
                                                             in
                                                          uu____57689 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____57688)))
                                          in
                                       (match uu____57643 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____57726 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____57726 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____57755 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____57755 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  