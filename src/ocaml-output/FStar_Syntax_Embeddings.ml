open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___429_50675  ->
    match uu___429_50675 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____50682 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____50682
  
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embedding_failure  -> true | uu____50692 -> false
  
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unembedding_failure  -> true
    | uu____50703 -> false
  
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
             (fun uu____50735  ->
                let uu____50736 = FStar_Common.force_thunk s1  in
                f uu____50736))
  
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
  'Auu____51098 . FStar_Syntax_Syntax.term -> 'Auu____51098 -> Prims.string =
  fun typ  ->
    fun uu____51109  ->
      let uu____51110 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____51110
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____51119 =
      let uu____51120 = FStar_Syntax_Subst.compress t  in
      uu____51120.FStar_Syntax_Syntax.n  in
    match uu____51119 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____51124 ->
        let uu____51125 =
          let uu____51127 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____51127
           in
        failwith uu____51125
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____51170 =
          let uu____51171 =
            let uu____51179 =
              let uu____51181 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____51181 FStar_Ident.string_of_lid  in
            (uu____51179, [])  in
          FStar_Syntax_Syntax.ET_app uu____51171  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____51170 }
  
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
      fun n1  -> let uu____51330 = unembed e t  in uu____51330 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      fun n1  -> let uu____51371 = unembed e t  in uu____51371 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___508_51418 = e  in
      {
        em = (uu___508_51418.em);
        un = (uu___508_51418.un);
        typ = ty;
        print = (uu___508_51418.print);
        emb_typ = (uu___508_51418.emb_typ)
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
              (let uu____51481 =
                 FStar_ST.op_Bang FStar_Options.debug_embedding  in
               if uu____51481
               then
                 let uu____51505 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____51507 = FStar_Syntax_Print.emb_typ_to_string et
                    in
                 let uu____51509 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n"
                   uu____51505 uu____51507 uu____51509
               else ());
              (let uu____51514 =
                 FStar_ST.op_Bang FStar_Options.eager_embedding  in
               if uu____51514
               then f ()
               else
                 (let thunk1 = FStar_Common.mk_thunk f  in
                  let uu____51549 =
                    let uu____51556 =
                      let uu____51557 =
                        let uu____51558 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____51558;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk1));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____51557  in
                    FStar_Syntax_Syntax.mk uu____51556  in
                  uu____51549 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____51625;
                  FStar_Syntax_Syntax.rng = uu____51626;_}
                ->
                let uu____51637 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____51637
                then
                  let res =
                    let uu____51666 = FStar_Common.force_thunk t  in
                    f uu____51666  in
                  ((let uu____51670 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____51670
                    then
                      let uu____51694 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____51696 =
                        FStar_Syntax_Print.emb_typ_to_string et'  in
                      let uu____51698 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____51703 = pa x2  in
                            Prims.op_Hat "Some " uu____51703
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____51694 uu____51696 uu____51698
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____51713 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____51713
                    then
                      let uu____51737 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____51739 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____51737 uu____51739
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____51744 ->
                let aopt = f x1  in
                ((let uu____51749 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____51749
                  then
                    let uu____51773 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____51775 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____51777 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____51782 = pa a  in
                          Prims.op_Hat "Some " uu____51782
                       in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____51773 uu____51775 uu____51777
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____51820 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____51820
       then
         let uu____51844 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____51844
       else ());
      t  in
    let un t _w _n =
      (let uu____51872 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____51872
       then
         let uu____51896 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____51896
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____51949 =
    let uu____51950 =
      let uu____51958 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____51958, [])  in
    FStar_Syntax_Syntax.ET_app uu____51950  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____51949
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___582_51990 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___582_51990.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___582_51990.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____52018 ->
        (if w
         then
           (let uu____52021 =
              let uu____52027 =
                let uu____52029 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____52029  in
              (FStar_Errors.Warning_NotEmbedded, uu____52027)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52021)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____52035 =
    let uu____52036 =
      let uu____52044 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____52044, [])  in
    FStar_Syntax_Syntax.ET_app uu____52036  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____52051  -> "()")
    uu____52035
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___602_52090 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___602_52090.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___602_52090.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____52126 ->
        (if w
         then
           (let uu____52129 =
              let uu____52135 =
                let uu____52137 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____52137  in
              (FStar_Errors.Warning_NotEmbedded, uu____52135)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52129)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____52144 =
    let uu____52145 =
      let uu____52153 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____52153, [])  in
    FStar_Syntax_Syntax.ET_app uu____52145  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____52144
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___621_52190 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___621_52190.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___621_52190.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____52224 ->
        (if w
         then
           (let uu____52227 =
              let uu____52233 =
                let uu____52235 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____52235  in
              (FStar_Errors.Warning_NotEmbedded, uu____52233)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52227)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____52242 =
    let uu____52243 =
      let uu____52251 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____52251, [])  in
    FStar_Syntax_Syntax.ET_app uu____52243  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____52242
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____52263 =
      let uu____52271 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____52271, [])  in
    FStar_Syntax_Syntax.ET_app uu____52263  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____52302  ->
         let uu____52303 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____52303)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____52338)) ->
             let uu____52353 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____52353
         | uu____52354 ->
             (if w
              then
                (let uu____52357 =
                   let uu____52363 =
                     let uu____52365 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____52365
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____52363)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                   uu____52357)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____52376 =
      let uu____52384 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____52384, [])  in
    FStar_Syntax_Syntax.ET_app uu____52376  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____52447)) -> FStar_Pervasives_Native.Some s
    | uu____52451 ->
        (if w
         then
           (let uu____52454 =
              let uu____52460 =
                let uu____52462 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____52462
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____52460)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52454)
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
      let uu____52498 =
        let uu____52503 =
          let uu____52504 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____52504]  in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____52503  in
      uu____52498 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____52530 =
        let uu____52538 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____52538, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____52530  in
    let printer uu___430_52552 =
      match uu___430_52552 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____52558 =
            let uu____52560 = ea.print x  in Prims.op_Hat uu____52560 ")"  in
          Prims.op_Hat "(Some " uu____52558
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____52595  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____52596 =
                 let uu____52601 =
                   let uu____52602 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____52602
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____52603 =
                   let uu____52604 =
                     let uu____52613 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____52613  in
                   [uu____52604]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____52601 uu____52603  in
               uu____52596 FStar_Pervasives_Native.None rng
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
                        let uu____52643 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____52643  in
                      let uu____52644 =
                        let uu____52649 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____52650 =
                          let uu____52651 =
                            let uu____52660 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____52660  in
                          let uu____52661 =
                            let uu____52672 = FStar_Syntax_Syntax.as_arg t
                               in
                            [uu____52672]  in
                          uu____52651 :: uu____52661  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____52649 uu____52650
                         in
                      uu____52644 FStar_Pervasives_Native.None rng)
                  in
               let uu____52705 =
                 let uu____52710 =
                   let uu____52711 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____52711
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____52712 =
                   let uu____52713 =
                     let uu____52722 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____52722  in
                   let uu____52723 =
                     let uu____52734 =
                       let uu____52743 =
                         let uu____52744 = embed ea a  in
                         uu____52744 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____52743  in
                     [uu____52734]  in
                   uu____52713 :: uu____52723  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____52710 uu____52712  in
               uu____52705 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____52814 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____52814 with
           | (hd1,args) ->
               let uu____52855 =
                 let uu____52870 =
                   let uu____52871 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____52871.FStar_Syntax_Syntax.n  in
                 (uu____52870, args)  in
               (match uu____52855 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____52889) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____52913::(a,uu____52915)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____52966 =
                      let uu____52969 = unembed ea a  in uu____52969 w norm1
                       in
                    FStar_Util.bind_opt uu____52966
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____52982 ->
                    (if w
                     then
                       (let uu____52999 =
                          let uu____53005 =
                            let uu____53007 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____53007
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____53005)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____52999)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____53015 =
      let uu____53016 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____53016  in
    mk_emb_full em un uu____53015 printer emb_t_option_a
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2  in
        let uu____53058 =
          let uu____53063 =
            let uu____53064 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____53073 =
              let uu____53084 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____53084]  in
            uu____53064 :: uu____53073  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____53063  in
        uu____53058 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____53118 =
          let uu____53126 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____53126, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____53118  in
      let printer uu____53142 =
        match uu____53142 with
        | (x,y) ->
            let uu____53150 = ea.print x  in
            let uu____53152 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____53150 uu____53152
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____53195  ->
             let proj i ab =
               let uu____53211 =
                 let uu____53216 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____53218 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____53216
                   uu____53218 i
                  in
               match uu____53211 with
               | (proj_1,uu____53222) ->
                   let proj_1_tm =
                     let uu____53224 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____53224  in
                   let uu____53225 =
                     let uu____53230 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____53231 =
                       let uu____53232 =
                         let uu____53241 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____53241  in
                       let uu____53242 =
                         let uu____53253 =
                           let uu____53262 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____53262  in
                         let uu____53263 =
                           let uu____53274 = FStar_Syntax_Syntax.as_arg ab
                              in
                           [uu____53274]  in
                         uu____53253 :: uu____53263  in
                       uu____53232 :: uu____53242  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____53230 uu____53231
                      in
                   uu____53225 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____53319 =
               let uu____53324 =
                 let uu____53325 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____53325
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____53326 =
                 let uu____53327 =
                   let uu____53336 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____53336  in
                 let uu____53337 =
                   let uu____53348 =
                     let uu____53357 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____53357  in
                   let uu____53358 =
                     let uu____53369 =
                       let uu____53378 =
                         let uu____53379 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____53379 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____53378  in
                     let uu____53386 =
                       let uu____53397 =
                         let uu____53406 =
                           let uu____53407 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____53407 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____53406  in
                       [uu____53397]  in
                     uu____53369 :: uu____53386  in
                   uu____53348 :: uu____53358  in
                 uu____53327 :: uu____53337  in
               FStar_Syntax_Syntax.mk_Tm_app uu____53324 uu____53326  in
             uu____53319 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____53505 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____53505 with
             | (hd1,args) ->
                 let uu____53548 =
                   let uu____53561 =
                     let uu____53562 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____53562.FStar_Syntax_Syntax.n  in
                   (uu____53561, args)  in
                 (match uu____53548 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____53580::uu____53581::(a,uu____53583)::(b,uu____53585)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____53644 =
                        let uu____53647 = unembed ea a  in
                        uu____53647 w norm1  in
                      FStar_Util.bind_opt uu____53644
                        (fun a1  ->
                           let uu____53661 =
                             let uu____53664 = unembed eb b  in
                             uu____53664 w norm1  in
                           FStar_Util.bind_opt uu____53661
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____53681 ->
                      (if w
                       then
                         (let uu____53696 =
                            let uu____53702 =
                              let uu____53704 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____53704
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____53702)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____53696)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____53714 =
        let uu____53715 = type_of ea  in
        let uu____53716 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____53715 uu____53716  in
      mk_emb_full em un uu____53714 printer emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____53760 =
          let uu____53765 =
            let uu____53766 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____53775 =
              let uu____53786 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____53786]  in
            uu____53766 :: uu____53775  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____53765  in
        uu____53760 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____53820 =
          let uu____53828 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____53828, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____53820  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____53851 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____53851
        | FStar_Util.Inr b ->
            let uu____53855 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____53855
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____53901  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____53914 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____53914  in
                         let uu____53915 =
                           let uu____53920 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____53921 =
                             let uu____53922 =
                               let uu____53931 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____53931  in
                             let uu____53932 =
                               let uu____53943 =
                                 let uu____53952 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____53952  in
                               let uu____53953 =
                                 let uu____53964 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____53964]  in
                               uu____53943 :: uu____53953  in
                             uu____53922 :: uu____53932  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____53920
                             uu____53921
                            in
                         uu____53915 FStar_Pervasives_Native.None rng)
                     in
                  let uu____54005 =
                    let uu____54010 =
                      let uu____54011 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____54011
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____54012 =
                      let uu____54013 =
                        let uu____54022 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____54022  in
                      let uu____54023 =
                        let uu____54034 =
                          let uu____54043 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____54043  in
                        let uu____54044 =
                          let uu____54055 =
                            let uu____54064 =
                              let uu____54065 = embed ea a  in
                              uu____54065 rng shadow_a norm1  in
                            FStar_Syntax_Syntax.as_arg uu____54064  in
                          [uu____54055]  in
                        uu____54034 :: uu____54044  in
                      uu____54013 :: uu____54023  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____54010 uu____54012  in
                  uu____54005 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____54105  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____54118 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____54118  in
                         let uu____54119 =
                           let uu____54124 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____54125 =
                             let uu____54126 =
                               let uu____54135 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____54135  in
                             let uu____54136 =
                               let uu____54147 =
                                 let uu____54156 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____54156  in
                               let uu____54157 =
                                 let uu____54168 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____54168]  in
                               uu____54147 :: uu____54157  in
                             uu____54126 :: uu____54136  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____54124
                             uu____54125
                            in
                         uu____54119 FStar_Pervasives_Native.None rng)
                     in
                  let uu____54209 =
                    let uu____54214 =
                      let uu____54215 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____54215
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____54216 =
                      let uu____54217 =
                        let uu____54226 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____54226  in
                      let uu____54227 =
                        let uu____54238 =
                          let uu____54247 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____54247  in
                        let uu____54248 =
                          let uu____54259 =
                            let uu____54268 =
                              let uu____54269 = embed eb b  in
                              uu____54269 rng shadow_b norm1  in
                            FStar_Syntax_Syntax.as_arg uu____54268  in
                          [uu____54259]  in
                        uu____54238 :: uu____54248  in
                      uu____54217 :: uu____54227  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____54214 uu____54216  in
                  uu____54209 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____54357 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____54357 with
             | (hd1,args) ->
                 let uu____54400 =
                   let uu____54415 =
                     let uu____54416 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____54416.FStar_Syntax_Syntax.n  in
                   (uu____54415, args)  in
                 (match uu____54400 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____54436::uu____54437::(a,uu____54439)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____54506 =
                        let uu____54509 = unembed ea a  in
                        uu____54509 w norm1  in
                      FStar_Util.bind_opt uu____54506
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____54527::uu____54528::(b,uu____54530)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____54597 =
                        let uu____54600 = unembed eb b  in
                        uu____54600 w norm1  in
                      FStar_Util.bind_opt uu____54597
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____54617 ->
                      (if w
                       then
                         (let uu____54634 =
                            let uu____54640 =
                              let uu____54642 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____54642
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____54640)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____54634)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____54652 =
        let uu____54653 = type_of ea  in
        let uu____54654 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____54653 uu____54654  in
      mk_emb_full em un uu____54652 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____54682 =
        let uu____54687 =
          let uu____54688 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____54688]  in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____54687  in
      uu____54682 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____54714 =
        let uu____54722 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____54722, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____54714  in
    let printer l =
      let uu____54739 =
        let uu____54741 =
          let uu____54743 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____54743 (FStar_String.concat "; ")  in
        Prims.op_Hat uu____54741 "]"  in
      Prims.op_Hat "[" uu____54739  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____54787  ->
           let t =
             let uu____54789 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____54789  in
           match l with
           | [] ->
               let uu____54790 =
                 let uu____54795 =
                   let uu____54796 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____54796
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____54795 [t]  in
               uu____54790 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____54818 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____54818
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____54838 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____54838  in
                 let uu____54839 =
                   let uu____54844 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____54845 =
                     let uu____54846 =
                       let uu____54855 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____54855  in
                     let uu____54856 =
                       let uu____54867 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____54867]  in
                     uu____54846 :: uu____54856  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____54844 uu____54845  in
                 uu____54839 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____54904 =
                 let uu____54909 =
                   let uu____54910 =
                     let uu____54921 =
                       let uu____54930 =
                         let uu____54931 = embed ea hd1  in
                         uu____54931 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____54930  in
                     let uu____54938 =
                       let uu____54949 =
                         let uu____54958 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____54958  in
                       [uu____54949]  in
                     uu____54921 :: uu____54938  in
                   t :: uu____54910  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____54909  in
               uu____54904 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____55030 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____55030 with
           | (hd1,args) ->
               let uu____55071 =
                 let uu____55084 =
                   let uu____55085 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____55085.FStar_Syntax_Syntax.n  in
                 (uu____55084, args)  in
               (match uu____55071 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____55101) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____55121,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____55122))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____55164 =
                      let uu____55167 = unembed ea hd2  in
                      uu____55167 w norm1  in
                    FStar_Util.bind_opt uu____55164
                      (fun hd3  ->
                         let uu____55179 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____55179
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____55227 =
                      let uu____55230 = unembed ea hd2  in
                      uu____55230 w norm1  in
                    FStar_Util.bind_opt uu____55227
                      (fun hd3  ->
                         let uu____55242 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____55242
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____55257 ->
                    (if w
                     then
                       (let uu____55272 =
                          let uu____55278 =
                            let uu____55280 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____55280
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____55278)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____55272)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____55288 =
      let uu____55289 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____55289  in
    mk_emb_full em un uu____55288 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____55332 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____55343 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____55354 -> false
  
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____55365 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____55376 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____55387 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____55398 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____55409 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____55424 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____55455 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____55486 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____55513 -> false
  
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
    let uu____55531 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____55531  in
  let emb_t_norm_step =
    let uu____55534 =
      let uu____55542 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____55542, [])  in
    FStar_Syntax_Syntax.ET_app uu____55534  in
  let printer uu____55554 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____55580  ->
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
             let uu____55585 =
               let uu____55590 =
                 let uu____55591 =
                   let uu____55600 =
                     let uu____55601 =
                       let uu____55608 = e_list e_string  in
                       embed uu____55608 l  in
                     uu____55601 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____55600  in
                 [uu____55591]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____55590  in
             uu____55585 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____55640 =
               let uu____55645 =
                 let uu____55646 =
                   let uu____55655 =
                     let uu____55656 =
                       let uu____55663 = e_list e_string  in
                       embed uu____55663 l  in
                     uu____55656 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____55655  in
                 [uu____55646]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____55645
                in
             uu____55640 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____55695 =
               let uu____55700 =
                 let uu____55701 =
                   let uu____55710 =
                     let uu____55711 =
                       let uu____55718 = e_list e_string  in
                       embed uu____55718 l  in
                     uu____55711 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____55710  in
                 [uu____55701]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____55700  in
             uu____55695 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____55778 = FStar_Syntax_Util.head_and_args t1  in
         match uu____55778 with
         | (hd1,args) ->
             let uu____55823 =
               let uu____55838 =
                 let uu____55839 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____55839.FStar_Syntax_Syntax.n  in
               (uu____55838, args)  in
             (match uu____55823 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____56027)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____56062 =
                    let uu____56068 =
                      let uu____56078 = e_list e_string  in
                      unembed uu____56078 l  in
                    uu____56068 w norm1  in
                  FStar_Util.bind_opt uu____56062
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _56098  -> FStar_Pervasives_Native.Some _56098)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____56101)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____56136 =
                    let uu____56142 =
                      let uu____56152 = e_list e_string  in
                      unembed uu____56152 l  in
                    uu____56142 w norm1  in
                  FStar_Util.bind_opt uu____56136
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _56172  -> FStar_Pervasives_Native.Some _56172)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____56175)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____56210 =
                    let uu____56216 =
                      let uu____56226 = e_list e_string  in
                      unembed uu____56226 l  in
                    uu____56216 w norm1  in
                  FStar_Util.bind_opt uu____56210
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _56246  -> FStar_Pervasives_Native.Some _56246)
                         (UnfoldAttr ss))
              | uu____56247 ->
                  (if w
                   then
                     (let uu____56264 =
                        let uu____56270 =
                          let uu____56272 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____56272
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____56270)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____56264)
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
    | uu____56332 ->
        (if w
         then
           (let uu____56335 =
              let uu____56341 =
                let uu____56343 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____56343
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____56341)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____56335)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____56349 =
    let uu____56350 =
      let uu____56358 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____56358, [])  in
    FStar_Syntax_Syntax.ET_app uu____56350  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____56349
  
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
        let uu____56429 =
          let uu____56436 =
            let uu____56437 =
              let uu____56452 =
                let uu____56461 =
                  let uu____56468 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____56468, FStar_Pervasives_Native.None)  in
                [uu____56461]  in
              let uu____56483 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____56452, uu____56483)  in
            FStar_Syntax_Syntax.Tm_arrow uu____56437  in
          FStar_Syntax_Syntax.mk uu____56436  in
        uu____56429 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____56555  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____56561  ->
             let uu____56562 = force_shadow shadow_f  in
             match uu____56562 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____56567 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____56567
                   then
                     let uu____56591 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____56593 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____56591 uu____56593
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f)  in
                   (let uu____56600 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____56600
                    then
                      let uu____56624 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____56626 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____56628 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____56624 uu____56626 uu____56628
                    else ());
                   res)))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               (let uu____56687 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____56687
                then
                  let uu____56711 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____56713 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____56711
                    uu____56713
                else ());
               (let a_tm =
                  let uu____56719 = embed ea a  in
                  uu____56719 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1
                   in
                let b_tm =
                  let uu____56729 =
                    let uu____56734 =
                      let uu____56735 =
                        let uu____56740 =
                          let uu____56741 = FStar_Syntax_Syntax.as_arg a_tm
                             in
                          [uu____56741]  in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____56740  in
                      uu____56735 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____56734  in
                  norm1 uu____56729  in
                let uu____56766 =
                  let uu____56769 = unembed eb b_tm  in uu____56769 w norm1
                   in
                match uu____56766 with
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
                let uu____56863 = FStar_List.splitAt n_tvars args  in
                match uu____56863 with
                | (_tvar_args,rest_args) ->
                    let uu____56940 = FStar_List.hd rest_args  in
                    (match uu____56940 with
                     | (x,uu____56960) ->
                         let shadow_app =
                           let uu____56974 =
                             FStar_Common.mk_thunk
                               (fun uu____56981  ->
                                  let uu____56982 =
                                    let uu____56987 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____56987
                                      args
                                     in
                                  uu____56982 FStar_Pervasives_Native.None
                                    rng)
                              in
                           FStar_Pervasives_Native.Some uu____56974  in
                         let uu____56990 =
                           let uu____56993 =
                             let uu____56996 = unembed ea x  in
                             uu____56996 true norm1  in
                           FStar_Util.map_opt uu____56993
                             (fun x1  ->
                                let uu____57007 =
                                  let uu____57014 = f x1  in
                                  embed eb uu____57014  in
                                uu____57007 rng shadow_app norm1)
                            in
                         (match uu____56990 with
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
                  let uu____57117 = FStar_List.splitAt n_tvars args  in
                  match uu____57117 with
                  | (_tvar_args,rest_args) ->
                      let uu____57180 = FStar_List.hd rest_args  in
                      (match uu____57180 with
                       | (x,uu____57196) ->
                           let uu____57201 =
                             let uu____57208 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____57208  in
                           (match uu____57201 with
                            | (y,uu____57232) ->
                                let shadow_app =
                                  let uu____57242 =
                                    FStar_Common.mk_thunk
                                      (fun uu____57249  ->
                                         let uu____57250 =
                                           let uu____57255 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____57255 args
                                            in
                                         uu____57250
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____57242
                                   in
                                let uu____57258 =
                                  let uu____57261 =
                                    let uu____57264 = unembed ea x  in
                                    uu____57264 true norm1  in
                                  FStar_Util.bind_opt uu____57261
                                    (fun x1  ->
                                       let uu____57275 =
                                         let uu____57278 = unembed eb y  in
                                         uu____57278 true norm1  in
                                       FStar_Util.bind_opt uu____57275
                                         (fun y1  ->
                                            let uu____57289 =
                                              let uu____57290 =
                                                let uu____57297 = f x1 y1  in
                                                embed ec uu____57297  in
                                              uu____57290 rng shadow_app
                                                norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____57289))
                                   in
                                (match uu____57258 with
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
                    let uu____57419 = FStar_List.splitAt n_tvars args  in
                    match uu____57419 with
                    | (_tvar_args,rest_args) ->
                        let uu____57482 = FStar_List.hd rest_args  in
                        (match uu____57482 with
                         | (x,uu____57498) ->
                             let uu____57503 =
                               let uu____57510 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____57510  in
                             (match uu____57503 with
                              | (y,uu____57534) ->
                                  let uu____57539 =
                                    let uu____57546 =
                                      let uu____57555 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____57555  in
                                    FStar_List.hd uu____57546  in
                                  (match uu____57539 with
                                   | (z,uu____57585) ->
                                       let shadow_app =
                                         let uu____57595 =
                                           FStar_Common.mk_thunk
                                             (fun uu____57602  ->
                                                let uu____57603 =
                                                  let uu____57608 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____57608 args
                                                   in
                                                uu____57603
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____57595
                                          in
                                       let uu____57611 =
                                         let uu____57614 =
                                           let uu____57617 = unembed ea x  in
                                           uu____57617 true norm1  in
                                         FStar_Util.bind_opt uu____57614
                                           (fun x1  ->
                                              let uu____57628 =
                                                let uu____57631 =
                                                  unembed eb y  in
                                                uu____57631 true norm1  in
                                              FStar_Util.bind_opt uu____57628
                                                (fun y1  ->
                                                   let uu____57642 =
                                                     let uu____57645 =
                                                       unembed ec z  in
                                                     uu____57645 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____57642
                                                     (fun z1  ->
                                                        let uu____57656 =
                                                          let uu____57657 =
                                                            let uu____57664 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____57664
                                                             in
                                                          uu____57657 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____57656)))
                                          in
                                       (match uu____57611 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____57694 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____57694 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____57723 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____57723 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  