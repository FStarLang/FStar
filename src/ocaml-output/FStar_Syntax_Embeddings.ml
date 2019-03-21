open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___429_50708  ->
    match uu___429_50708 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____50715 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____50715
  
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embedding_failure  -> true | uu____50725 -> false
  
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unembedding_failure  -> true
    | uu____50736 -> false
  
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
             (fun uu____50768  ->
                let uu____50769 = FStar_Common.force_thunk s1  in
                f uu____50769))
  
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
  'Auu____51131 . FStar_Syntax_Syntax.term -> 'Auu____51131 -> Prims.string =
  fun typ  ->
    fun uu____51142  ->
      let uu____51143 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____51143
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____51152 =
      let uu____51153 = FStar_Syntax_Subst.compress t  in
      uu____51153.FStar_Syntax_Syntax.n  in
    match uu____51152 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____51157 ->
        let uu____51158 =
          let uu____51160 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____51160
           in
        failwith uu____51158
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____51203 =
          let uu____51204 =
            let uu____51212 =
              let uu____51214 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____51214 FStar_Ident.string_of_lid  in
            (uu____51212, [])  in
          FStar_Syntax_Syntax.ET_app uu____51204  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____51203 }
  
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
      fun n1  -> let uu____51363 = unembed e t  in uu____51363 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      fun n1  -> let uu____51404 = unembed e t  in uu____51404 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___508_51451 = e  in
      {
        em = (uu___508_51451.em);
        un = (uu___508_51451.un);
        typ = ty;
        print = (uu___508_51451.print);
        emb_typ = (uu___508_51451.emb_typ)
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
              (let uu____51514 =
                 FStar_ST.op_Bang FStar_Options.debug_embedding  in
               if uu____51514
               then
                 let uu____51538 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____51540 = FStar_Syntax_Print.emb_typ_to_string et
                    in
                 let uu____51542 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n"
                   uu____51538 uu____51540 uu____51542
               else ());
              (let uu____51547 =
                 FStar_ST.op_Bang FStar_Options.eager_embedding  in
               if uu____51547
               then f ()
               else
                 (let thunk1 = FStar_Common.mk_thunk f  in
                  let uu____51582 =
                    let uu____51589 =
                      let uu____51590 =
                        let uu____51591 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____51591;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk1));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____51590  in
                    FStar_Syntax_Syntax.mk uu____51589  in
                  uu____51582 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____51658;
                  FStar_Syntax_Syntax.rng = uu____51659;_}
                ->
                let uu____51670 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____51670
                then
                  let res =
                    let uu____51699 = FStar_Common.force_thunk t  in
                    f uu____51699  in
                  ((let uu____51703 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____51703
                    then
                      let uu____51727 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____51729 =
                        FStar_Syntax_Print.emb_typ_to_string et'  in
                      let uu____51731 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____51736 = pa x2  in
                            Prims.op_Hat "Some " uu____51736
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____51727 uu____51729 uu____51731
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____51746 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____51746
                    then
                      let uu____51770 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____51772 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____51770 uu____51772
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____51777 ->
                let aopt = f x1  in
                ((let uu____51782 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____51782
                  then
                    let uu____51806 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____51808 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____51810 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____51815 = pa a  in
                          Prims.op_Hat "Some " uu____51815
                       in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____51806 uu____51808 uu____51810
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____51853 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____51853
       then
         let uu____51877 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____51877
       else ());
      t  in
    let un t _w _n =
      (let uu____51905 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____51905
       then
         let uu____51929 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____51929
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____51982 =
    let uu____51983 =
      let uu____51991 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____51991, [])  in
    FStar_Syntax_Syntax.ET_app uu____51983  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____51982
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___582_52023 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___582_52023.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___582_52023.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____52051 ->
        (if w
         then
           (let uu____52054 =
              let uu____52060 =
                let uu____52062 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____52062  in
              (FStar_Errors.Warning_NotEmbedded, uu____52060)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52054)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____52068 =
    let uu____52069 =
      let uu____52077 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____52077, [])  in
    FStar_Syntax_Syntax.ET_app uu____52069  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____52084  -> "()")
    uu____52068
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___602_52123 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___602_52123.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___602_52123.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____52159 ->
        (if w
         then
           (let uu____52162 =
              let uu____52168 =
                let uu____52170 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____52170  in
              (FStar_Errors.Warning_NotEmbedded, uu____52168)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52162)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____52177 =
    let uu____52178 =
      let uu____52186 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____52186, [])  in
    FStar_Syntax_Syntax.ET_app uu____52178  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____52177
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___621_52223 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___621_52223.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___621_52223.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____52257 ->
        (if w
         then
           (let uu____52260 =
              let uu____52266 =
                let uu____52268 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____52268  in
              (FStar_Errors.Warning_NotEmbedded, uu____52266)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52260)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____52275 =
    let uu____52276 =
      let uu____52284 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____52284, [])  in
    FStar_Syntax_Syntax.ET_app uu____52276  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____52275
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____52296 =
      let uu____52304 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____52304, [])  in
    FStar_Syntax_Syntax.ET_app uu____52296  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____52335  ->
         let uu____52336 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____52336)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____52371)) ->
             let uu____52386 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____52386
         | uu____52387 ->
             (if w
              then
                (let uu____52390 =
                   let uu____52396 =
                     let uu____52398 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____52398
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____52396)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                   uu____52390)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____52409 =
      let uu____52417 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____52417, [])  in
    FStar_Syntax_Syntax.ET_app uu____52409  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____52480)) -> FStar_Pervasives_Native.Some s
    | uu____52484 ->
        (if w
         then
           (let uu____52487 =
              let uu____52493 =
                let uu____52495 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____52495
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____52493)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52487)
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
      let uu____52531 =
        let uu____52536 =
          let uu____52537 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____52537]  in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____52536  in
      uu____52531 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____52563 =
        let uu____52571 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____52571, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____52563  in
    let printer uu___430_52585 =
      match uu___430_52585 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____52591 =
            let uu____52593 = ea.print x  in Prims.op_Hat uu____52593 ")"  in
          Prims.op_Hat "(Some " uu____52591
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____52628  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____52629 =
                 let uu____52634 =
                   let uu____52635 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____52635
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____52636 =
                   let uu____52637 =
                     let uu____52646 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____52646  in
                   [uu____52637]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____52634 uu____52636  in
               uu____52629 FStar_Pervasives_Native.None rng
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
                        let uu____52676 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____52676  in
                      let uu____52677 =
                        let uu____52682 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____52683 =
                          let uu____52684 =
                            let uu____52693 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____52693  in
                          let uu____52694 =
                            let uu____52705 = FStar_Syntax_Syntax.as_arg t
                               in
                            [uu____52705]  in
                          uu____52684 :: uu____52694  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____52682 uu____52683
                         in
                      uu____52677 FStar_Pervasives_Native.None rng)
                  in
               let uu____52738 =
                 let uu____52743 =
                   let uu____52744 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____52744
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____52745 =
                   let uu____52746 =
                     let uu____52755 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____52755  in
                   let uu____52756 =
                     let uu____52767 =
                       let uu____52776 =
                         let uu____52777 = embed ea a  in
                         uu____52777 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____52776  in
                     [uu____52767]  in
                   uu____52746 :: uu____52756  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____52743 uu____52745  in
               uu____52738 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____52847 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____52847 with
           | (hd1,args) ->
               let uu____52888 =
                 let uu____52903 =
                   let uu____52904 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____52904.FStar_Syntax_Syntax.n  in
                 (uu____52903, args)  in
               (match uu____52888 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____52922) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____52946::(a,uu____52948)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____52999 =
                      let uu____53002 = unembed ea a  in uu____53002 w norm1
                       in
                    FStar_Util.bind_opt uu____52999
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____53015 ->
                    (if w
                     then
                       (let uu____53032 =
                          let uu____53038 =
                            let uu____53040 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____53040
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____53038)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____53032)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____53048 =
      let uu____53049 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____53049  in
    mk_emb_full em un uu____53048 printer emb_t_option_a
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2  in
        let uu____53091 =
          let uu____53096 =
            let uu____53097 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____53106 =
              let uu____53117 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____53117]  in
            uu____53097 :: uu____53106  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____53096  in
        uu____53091 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____53151 =
          let uu____53159 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____53159, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____53151  in
      let printer uu____53175 =
        match uu____53175 with
        | (x,y) ->
            let uu____53183 = ea.print x  in
            let uu____53185 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____53183 uu____53185
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____53228  ->
             let proj i ab =
               let uu____53244 =
                 let uu____53249 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____53251 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____53249
                   uu____53251 i
                  in
               match uu____53244 with
               | (proj_1,uu____53255) ->
                   let proj_1_tm =
                     let uu____53257 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____53257  in
                   let uu____53258 =
                     let uu____53263 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____53264 =
                       let uu____53265 =
                         let uu____53274 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____53274  in
                       let uu____53275 =
                         let uu____53286 =
                           let uu____53295 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____53295  in
                         let uu____53296 =
                           let uu____53307 = FStar_Syntax_Syntax.as_arg ab
                              in
                           [uu____53307]  in
                         uu____53286 :: uu____53296  in
                       uu____53265 :: uu____53275  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____53263 uu____53264
                      in
                   uu____53258 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____53352 =
               let uu____53357 =
                 let uu____53358 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____53358
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____53359 =
                 let uu____53360 =
                   let uu____53369 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____53369  in
                 let uu____53370 =
                   let uu____53381 =
                     let uu____53390 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____53390  in
                   let uu____53391 =
                     let uu____53402 =
                       let uu____53411 =
                         let uu____53412 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____53412 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____53411  in
                     let uu____53419 =
                       let uu____53430 =
                         let uu____53439 =
                           let uu____53440 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____53440 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____53439  in
                       [uu____53430]  in
                     uu____53402 :: uu____53419  in
                   uu____53381 :: uu____53391  in
                 uu____53360 :: uu____53370  in
               FStar_Syntax_Syntax.mk_Tm_app uu____53357 uu____53359  in
             uu____53352 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____53538 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____53538 with
             | (hd1,args) ->
                 let uu____53581 =
                   let uu____53594 =
                     let uu____53595 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____53595.FStar_Syntax_Syntax.n  in
                   (uu____53594, args)  in
                 (match uu____53581 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____53613::uu____53614::(a,uu____53616)::(b,uu____53618)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____53677 =
                        let uu____53680 = unembed ea a  in
                        uu____53680 w norm1  in
                      FStar_Util.bind_opt uu____53677
                        (fun a1  ->
                           let uu____53694 =
                             let uu____53697 = unembed eb b  in
                             uu____53697 w norm1  in
                           FStar_Util.bind_opt uu____53694
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____53714 ->
                      (if w
                       then
                         (let uu____53729 =
                            let uu____53735 =
                              let uu____53737 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____53737
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____53735)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____53729)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____53747 =
        let uu____53748 = type_of ea  in
        let uu____53749 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____53748 uu____53749  in
      mk_emb_full em un uu____53747 printer emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____53793 =
          let uu____53798 =
            let uu____53799 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____53808 =
              let uu____53819 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____53819]  in
            uu____53799 :: uu____53808  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____53798  in
        uu____53793 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____53853 =
          let uu____53861 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____53861, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____53853  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____53884 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____53884
        | FStar_Util.Inr b ->
            let uu____53888 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____53888
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____53934  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____53947 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____53947  in
                         let uu____53948 =
                           let uu____53953 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____53954 =
                             let uu____53955 =
                               let uu____53964 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____53964  in
                             let uu____53965 =
                               let uu____53976 =
                                 let uu____53985 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____53985  in
                               let uu____53986 =
                                 let uu____53997 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____53997]  in
                               uu____53976 :: uu____53986  in
                             uu____53955 :: uu____53965  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____53953
                             uu____53954
                            in
                         uu____53948 FStar_Pervasives_Native.None rng)
                     in
                  let uu____54038 =
                    let uu____54043 =
                      let uu____54044 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____54044
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____54045 =
                      let uu____54046 =
                        let uu____54055 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____54055  in
                      let uu____54056 =
                        let uu____54067 =
                          let uu____54076 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____54076  in
                        let uu____54077 =
                          let uu____54088 =
                            let uu____54097 =
                              let uu____54098 = embed ea a  in
                              uu____54098 rng shadow_a norm1  in
                            FStar_Syntax_Syntax.as_arg uu____54097  in
                          [uu____54088]  in
                        uu____54067 :: uu____54077  in
                      uu____54046 :: uu____54056  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____54043 uu____54045  in
                  uu____54038 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____54138  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____54151 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____54151  in
                         let uu____54152 =
                           let uu____54157 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____54158 =
                             let uu____54159 =
                               let uu____54168 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____54168  in
                             let uu____54169 =
                               let uu____54180 =
                                 let uu____54189 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____54189  in
                               let uu____54190 =
                                 let uu____54201 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____54201]  in
                               uu____54180 :: uu____54190  in
                             uu____54159 :: uu____54169  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____54157
                             uu____54158
                            in
                         uu____54152 FStar_Pervasives_Native.None rng)
                     in
                  let uu____54242 =
                    let uu____54247 =
                      let uu____54248 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____54248
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____54249 =
                      let uu____54250 =
                        let uu____54259 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____54259  in
                      let uu____54260 =
                        let uu____54271 =
                          let uu____54280 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____54280  in
                        let uu____54281 =
                          let uu____54292 =
                            let uu____54301 =
                              let uu____54302 = embed eb b  in
                              uu____54302 rng shadow_b norm1  in
                            FStar_Syntax_Syntax.as_arg uu____54301  in
                          [uu____54292]  in
                        uu____54271 :: uu____54281  in
                      uu____54250 :: uu____54260  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____54247 uu____54249  in
                  uu____54242 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____54390 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____54390 with
             | (hd1,args) ->
                 let uu____54433 =
                   let uu____54448 =
                     let uu____54449 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____54449.FStar_Syntax_Syntax.n  in
                   (uu____54448, args)  in
                 (match uu____54433 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____54469::uu____54470::(a,uu____54472)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____54539 =
                        let uu____54542 = unembed ea a  in
                        uu____54542 w norm1  in
                      FStar_Util.bind_opt uu____54539
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____54560::uu____54561::(b,uu____54563)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____54630 =
                        let uu____54633 = unembed eb b  in
                        uu____54633 w norm1  in
                      FStar_Util.bind_opt uu____54630
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____54650 ->
                      (if w
                       then
                         (let uu____54667 =
                            let uu____54673 =
                              let uu____54675 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____54675
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____54673)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____54667)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____54685 =
        let uu____54686 = type_of ea  in
        let uu____54687 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____54686 uu____54687  in
      mk_emb_full em un uu____54685 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____54715 =
        let uu____54720 =
          let uu____54721 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____54721]  in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____54720  in
      uu____54715 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____54747 =
        let uu____54755 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____54755, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____54747  in
    let printer l =
      let uu____54772 =
        let uu____54774 =
          let uu____54776 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____54776 (FStar_String.concat "; ")  in
        Prims.op_Hat uu____54774 "]"  in
      Prims.op_Hat "[" uu____54772  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____54820  ->
           let t =
             let uu____54822 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____54822  in
           match l with
           | [] ->
               let uu____54823 =
                 let uu____54828 =
                   let uu____54829 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____54829
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____54828 [t]  in
               uu____54823 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____54851 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____54851
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____54871 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____54871  in
                 let uu____54872 =
                   let uu____54877 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____54878 =
                     let uu____54879 =
                       let uu____54888 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____54888  in
                     let uu____54889 =
                       let uu____54900 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____54900]  in
                     uu____54879 :: uu____54889  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____54877 uu____54878  in
                 uu____54872 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____54937 =
                 let uu____54942 =
                   let uu____54943 =
                     let uu____54954 =
                       let uu____54963 =
                         let uu____54964 = embed ea hd1  in
                         uu____54964 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____54963  in
                     let uu____54971 =
                       let uu____54982 =
                         let uu____54991 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____54991  in
                       [uu____54982]  in
                     uu____54954 :: uu____54971  in
                   t :: uu____54943  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____54942  in
               uu____54937 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____55063 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____55063 with
           | (hd1,args) ->
               let uu____55104 =
                 let uu____55117 =
                   let uu____55118 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____55118.FStar_Syntax_Syntax.n  in
                 (uu____55117, args)  in
               (match uu____55104 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____55134) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____55154,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____55155))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____55197 =
                      let uu____55200 = unembed ea hd2  in
                      uu____55200 w norm1  in
                    FStar_Util.bind_opt uu____55197
                      (fun hd3  ->
                         let uu____55212 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____55212
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____55260 =
                      let uu____55263 = unembed ea hd2  in
                      uu____55263 w norm1  in
                    FStar_Util.bind_opt uu____55260
                      (fun hd3  ->
                         let uu____55275 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____55275
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____55290 ->
                    (if w
                     then
                       (let uu____55305 =
                          let uu____55311 =
                            let uu____55313 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____55313
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____55311)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____55305)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____55321 =
      let uu____55322 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____55322  in
    mk_emb_full em un uu____55321 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____55365 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____55376 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____55387 -> false
  
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____55398 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____55409 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____55420 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____55431 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____55442 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____55457 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____55488 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____55519 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____55546 -> false
  
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
    let uu____55564 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____55564  in
  let emb_t_norm_step =
    let uu____55567 =
      let uu____55575 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____55575, [])  in
    FStar_Syntax_Syntax.ET_app uu____55567  in
  let printer uu____55587 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____55613  ->
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
             let uu____55618 =
               let uu____55623 =
                 let uu____55624 =
                   let uu____55633 =
                     let uu____55634 =
                       let uu____55641 = e_list e_string  in
                       embed uu____55641 l  in
                     uu____55634 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____55633  in
                 [uu____55624]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____55623  in
             uu____55618 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____55673 =
               let uu____55678 =
                 let uu____55679 =
                   let uu____55688 =
                     let uu____55689 =
                       let uu____55696 = e_list e_string  in
                       embed uu____55696 l  in
                     uu____55689 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____55688  in
                 [uu____55679]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____55678
                in
             uu____55673 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____55728 =
               let uu____55733 =
                 let uu____55734 =
                   let uu____55743 =
                     let uu____55744 =
                       let uu____55751 = e_list e_string  in
                       embed uu____55751 l  in
                     uu____55744 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____55743  in
                 [uu____55734]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____55733  in
             uu____55728 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____55811 = FStar_Syntax_Util.head_and_args t1  in
         match uu____55811 with
         | (hd1,args) ->
             let uu____55856 =
               let uu____55871 =
                 let uu____55872 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____55872.FStar_Syntax_Syntax.n  in
               (uu____55871, args)  in
             (match uu____55856 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____56060)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____56095 =
                    let uu____56101 =
                      let uu____56111 = e_list e_string  in
                      unembed uu____56111 l  in
                    uu____56101 w norm1  in
                  FStar_Util.bind_opt uu____56095
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _56131  -> FStar_Pervasives_Native.Some _56131)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____56134)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____56169 =
                    let uu____56175 =
                      let uu____56185 = e_list e_string  in
                      unembed uu____56185 l  in
                    uu____56175 w norm1  in
                  FStar_Util.bind_opt uu____56169
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _56205  -> FStar_Pervasives_Native.Some _56205)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____56208)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____56243 =
                    let uu____56249 =
                      let uu____56259 = e_list e_string  in
                      unembed uu____56259 l  in
                    uu____56249 w norm1  in
                  FStar_Util.bind_opt uu____56243
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _56279  -> FStar_Pervasives_Native.Some _56279)
                         (UnfoldAttr ss))
              | uu____56280 ->
                  (if w
                   then
                     (let uu____56297 =
                        let uu____56303 =
                          let uu____56305 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____56305
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____56303)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____56297)
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
    | uu____56365 ->
        (if w
         then
           (let uu____56368 =
              let uu____56374 =
                let uu____56376 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____56376
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____56374)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____56368)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____56382 =
    let uu____56383 =
      let uu____56391 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____56391, [])  in
    FStar_Syntax_Syntax.ET_app uu____56383  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____56382
  
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
        let uu____56462 =
          let uu____56469 =
            let uu____56470 =
              let uu____56485 =
                let uu____56494 =
                  let uu____56501 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____56501, FStar_Pervasives_Native.None)  in
                [uu____56494]  in
              let uu____56516 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____56485, uu____56516)  in
            FStar_Syntax_Syntax.Tm_arrow uu____56470  in
          FStar_Syntax_Syntax.mk uu____56469  in
        uu____56462 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____56588  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____56594  ->
             let uu____56595 = force_shadow shadow_f  in
             match uu____56595 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____56600 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____56600
                   then
                     let uu____56624 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____56626 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____56624 uu____56626
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f)  in
                   (let uu____56633 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____56633
                    then
                      let uu____56657 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____56659 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____56661 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____56657 uu____56659 uu____56661
                    else ());
                   res)))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               (let uu____56720 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____56720
                then
                  let uu____56744 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____56746 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____56744
                    uu____56746
                else ());
               (let a_tm =
                  let uu____56752 = embed ea a  in
                  uu____56752 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1
                   in
                let b_tm =
                  let uu____56762 =
                    let uu____56767 =
                      let uu____56768 =
                        let uu____56773 =
                          let uu____56774 = FStar_Syntax_Syntax.as_arg a_tm
                             in
                          [uu____56774]  in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____56773  in
                      uu____56768 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____56767  in
                  norm1 uu____56762  in
                let uu____56799 =
                  let uu____56802 = unembed eb b_tm  in uu____56802 w norm1
                   in
                match uu____56799 with
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
                let uu____56896 = FStar_List.splitAt n_tvars args  in
                match uu____56896 with
                | (_tvar_args,rest_args) ->
                    let uu____56973 = FStar_List.hd rest_args  in
                    (match uu____56973 with
                     | (x,uu____56993) ->
                         let shadow_app =
                           let uu____57007 =
                             FStar_Common.mk_thunk
                               (fun uu____57014  ->
                                  let uu____57015 =
                                    let uu____57020 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____57020
                                      args
                                     in
                                  uu____57015 FStar_Pervasives_Native.None
                                    rng)
                              in
                           FStar_Pervasives_Native.Some uu____57007  in
                         let uu____57023 =
                           let uu____57026 =
                             let uu____57029 = unembed ea x  in
                             uu____57029 true norm1  in
                           FStar_Util.map_opt uu____57026
                             (fun x1  ->
                                let uu____57040 =
                                  let uu____57047 = f x1  in
                                  embed eb uu____57047  in
                                uu____57040 rng shadow_app norm1)
                            in
                         (match uu____57023 with
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
                  let uu____57150 = FStar_List.splitAt n_tvars args  in
                  match uu____57150 with
                  | (_tvar_args,rest_args) ->
                      let uu____57213 = FStar_List.hd rest_args  in
                      (match uu____57213 with
                       | (x,uu____57229) ->
                           let uu____57234 =
                             let uu____57241 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____57241  in
                           (match uu____57234 with
                            | (y,uu____57265) ->
                                let shadow_app =
                                  let uu____57275 =
                                    FStar_Common.mk_thunk
                                      (fun uu____57282  ->
                                         let uu____57283 =
                                           let uu____57288 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____57288 args
                                            in
                                         uu____57283
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____57275
                                   in
                                let uu____57291 =
                                  let uu____57294 =
                                    let uu____57297 = unembed ea x  in
                                    uu____57297 true norm1  in
                                  FStar_Util.bind_opt uu____57294
                                    (fun x1  ->
                                       let uu____57308 =
                                         let uu____57311 = unembed eb y  in
                                         uu____57311 true norm1  in
                                       FStar_Util.bind_opt uu____57308
                                         (fun y1  ->
                                            let uu____57322 =
                                              let uu____57323 =
                                                let uu____57330 = f x1 y1  in
                                                embed ec uu____57330  in
                                              uu____57323 rng shadow_app
                                                norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____57322))
                                   in
                                (match uu____57291 with
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
                    let uu____57452 = FStar_List.splitAt n_tvars args  in
                    match uu____57452 with
                    | (_tvar_args,rest_args) ->
                        let uu____57515 = FStar_List.hd rest_args  in
                        (match uu____57515 with
                         | (x,uu____57531) ->
                             let uu____57536 =
                               let uu____57543 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____57543  in
                             (match uu____57536 with
                              | (y,uu____57567) ->
                                  let uu____57572 =
                                    let uu____57579 =
                                      let uu____57588 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____57588  in
                                    FStar_List.hd uu____57579  in
                                  (match uu____57572 with
                                   | (z,uu____57618) ->
                                       let shadow_app =
                                         let uu____57628 =
                                           FStar_Common.mk_thunk
                                             (fun uu____57635  ->
                                                let uu____57636 =
                                                  let uu____57641 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____57641 args
                                                   in
                                                uu____57636
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____57628
                                          in
                                       let uu____57644 =
                                         let uu____57647 =
                                           let uu____57650 = unembed ea x  in
                                           uu____57650 true norm1  in
                                         FStar_Util.bind_opt uu____57647
                                           (fun x1  ->
                                              let uu____57661 =
                                                let uu____57664 =
                                                  unembed eb y  in
                                                uu____57664 true norm1  in
                                              FStar_Util.bind_opt uu____57661
                                                (fun y1  ->
                                                   let uu____57675 =
                                                     let uu____57678 =
                                                       unembed ec z  in
                                                     uu____57678 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____57675
                                                     (fun z1  ->
                                                        let uu____57689 =
                                                          let uu____57690 =
                                                            let uu____57697 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____57697
                                                             in
                                                          uu____57690 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____57689)))
                                          in
                                       (match uu____57644 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____57727 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____57727 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____57756 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____57756 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  