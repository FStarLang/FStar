open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___429_50674  ->
    match uu___429_50674 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____50681 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____50681
  
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embedding_failure  -> true | uu____50691 -> false
  
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unembedding_failure  -> true
    | uu____50702 -> false
  
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
             (fun uu____50734  ->
                let uu____50735 = FStar_Common.force_thunk s1  in
                f uu____50735))
  
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
  'Auu____51097 . FStar_Syntax_Syntax.term -> 'Auu____51097 -> Prims.string =
  fun typ  ->
    fun uu____51108  ->
      let uu____51109 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____51109
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____51118 =
      let uu____51119 = FStar_Syntax_Subst.compress t  in
      uu____51119.FStar_Syntax_Syntax.n  in
    match uu____51118 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____51123 ->
        let uu____51124 =
          let uu____51126 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____51126
           in
        failwith uu____51124
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____51169 =
          let uu____51170 =
            let uu____51178 =
              let uu____51180 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____51180 FStar_Ident.string_of_lid  in
            (uu____51178, [])  in
          FStar_Syntax_Syntax.ET_app uu____51170  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____51169 }
  
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
      fun n1  -> let uu____51329 = unembed e t  in uu____51329 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      fun n1  -> let uu____51370 = unembed e t  in uu____51370 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___508_51417 = e  in
      {
        em = (uu___508_51417.em);
        un = (uu___508_51417.un);
        typ = ty;
        print = (uu___508_51417.print);
        emb_typ = (uu___508_51417.emb_typ)
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
              (let uu____51480 =
                 FStar_ST.op_Bang FStar_Options.debug_embedding  in
               if uu____51480
               then
                 let uu____51504 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____51506 = FStar_Syntax_Print.emb_typ_to_string et
                    in
                 let uu____51508 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n"
                   uu____51504 uu____51506 uu____51508
               else ());
              (let uu____51513 =
                 FStar_ST.op_Bang FStar_Options.eager_embedding  in
               if uu____51513
               then f ()
               else
                 (let thunk1 = FStar_Common.mk_thunk f  in
                  let uu____51548 =
                    let uu____51555 =
                      let uu____51556 =
                        let uu____51557 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____51557;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk1));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____51556  in
                    FStar_Syntax_Syntax.mk uu____51555  in
                  uu____51548 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____51624;
                  FStar_Syntax_Syntax.rng = uu____51625;_}
                ->
                let uu____51636 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____51636
                then
                  let res =
                    let uu____51665 = FStar_Common.force_thunk t  in
                    f uu____51665  in
                  ((let uu____51669 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____51669
                    then
                      let uu____51693 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____51695 =
                        FStar_Syntax_Print.emb_typ_to_string et'  in
                      let uu____51697 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____51702 = pa x2  in
                            Prims.op_Hat "Some " uu____51702
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____51693 uu____51695 uu____51697
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____51712 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____51712
                    then
                      let uu____51736 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____51738 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____51736 uu____51738
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____51743 ->
                let aopt = f x1  in
                ((let uu____51748 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____51748
                  then
                    let uu____51772 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____51774 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____51776 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____51781 = pa a  in
                          Prims.op_Hat "Some " uu____51781
                       in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____51772 uu____51774 uu____51776
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____51819 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____51819
       then
         let uu____51843 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____51843
       else ());
      t  in
    let un t _w _n =
      (let uu____51871 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____51871
       then
         let uu____51895 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____51895
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____51948 =
    let uu____51949 =
      let uu____51957 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____51957, [])  in
    FStar_Syntax_Syntax.ET_app uu____51949  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____51948
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___582_51989 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___582_51989.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___582_51989.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____52017 ->
        (if w
         then
           (let uu____52020 =
              let uu____52026 =
                let uu____52028 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____52028  in
              (FStar_Errors.Warning_NotEmbedded, uu____52026)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52020)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____52034 =
    let uu____52035 =
      let uu____52043 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____52043, [])  in
    FStar_Syntax_Syntax.ET_app uu____52035  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____52050  -> "()")
    uu____52034
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___602_52089 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___602_52089.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___602_52089.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____52125 ->
        (if w
         then
           (let uu____52128 =
              let uu____52134 =
                let uu____52136 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____52136  in
              (FStar_Errors.Warning_NotEmbedded, uu____52134)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52128)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____52143 =
    let uu____52144 =
      let uu____52152 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____52152, [])  in
    FStar_Syntax_Syntax.ET_app uu____52144  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____52143
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___621_52189 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___621_52189.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___621_52189.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____52223 ->
        (if w
         then
           (let uu____52226 =
              let uu____52232 =
                let uu____52234 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____52234  in
              (FStar_Errors.Warning_NotEmbedded, uu____52232)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52226)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____52241 =
    let uu____52242 =
      let uu____52250 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____52250, [])  in
    FStar_Syntax_Syntax.ET_app uu____52242  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____52241
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____52262 =
      let uu____52270 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____52270, [])  in
    FStar_Syntax_Syntax.ET_app uu____52262  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____52301  ->
         let uu____52302 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____52302)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____52337)) ->
             let uu____52352 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____52352
         | uu____52353 ->
             (if w
              then
                (let uu____52356 =
                   let uu____52362 =
                     let uu____52364 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____52364
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____52362)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                   uu____52356)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____52375 =
      let uu____52383 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____52383, [])  in
    FStar_Syntax_Syntax.ET_app uu____52375  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____52446)) -> FStar_Pervasives_Native.Some s
    | uu____52450 ->
        (if w
         then
           (let uu____52453 =
              let uu____52459 =
                let uu____52461 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____52461
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____52459)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52453)
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
      let uu____52497 =
        let uu____52502 =
          let uu____52503 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____52503]  in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____52502  in
      uu____52497 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____52529 =
        let uu____52537 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____52537, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____52529  in
    let printer uu___430_52551 =
      match uu___430_52551 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____52557 =
            let uu____52559 = ea.print x  in Prims.op_Hat uu____52559 ")"  in
          Prims.op_Hat "(Some " uu____52557
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____52594  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____52595 =
                 let uu____52600 =
                   let uu____52601 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____52601
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____52602 =
                   let uu____52603 =
                     let uu____52612 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____52612  in
                   [uu____52603]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____52600 uu____52602  in
               uu____52595 FStar_Pervasives_Native.None rng
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
                        let uu____52642 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____52642  in
                      let uu____52643 =
                        let uu____52648 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____52649 =
                          let uu____52650 =
                            let uu____52659 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____52659  in
                          let uu____52660 =
                            let uu____52671 = FStar_Syntax_Syntax.as_arg t
                               in
                            [uu____52671]  in
                          uu____52650 :: uu____52660  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____52648 uu____52649
                         in
                      uu____52643 FStar_Pervasives_Native.None rng)
                  in
               let uu____52704 =
                 let uu____52709 =
                   let uu____52710 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____52710
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____52711 =
                   let uu____52712 =
                     let uu____52721 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____52721  in
                   let uu____52722 =
                     let uu____52733 =
                       let uu____52742 =
                         let uu____52743 = embed ea a  in
                         uu____52743 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____52742  in
                     [uu____52733]  in
                   uu____52712 :: uu____52722  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____52709 uu____52711  in
               uu____52704 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____52813 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____52813 with
           | (hd1,args) ->
               let uu____52854 =
                 let uu____52869 =
                   let uu____52870 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____52870.FStar_Syntax_Syntax.n  in
                 (uu____52869, args)  in
               (match uu____52854 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____52888) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____52912::(a,uu____52914)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____52965 =
                      let uu____52968 = unembed ea a  in uu____52968 w norm1
                       in
                    FStar_Util.bind_opt uu____52965
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____52981 ->
                    (if w
                     then
                       (let uu____52998 =
                          let uu____53004 =
                            let uu____53006 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____53006
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____53004)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____52998)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____53014 =
      let uu____53015 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____53015  in
    mk_emb_full em un uu____53014 printer emb_t_option_a
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2  in
        let uu____53057 =
          let uu____53062 =
            let uu____53063 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____53072 =
              let uu____53083 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____53083]  in
            uu____53063 :: uu____53072  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____53062  in
        uu____53057 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____53117 =
          let uu____53125 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____53125, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____53117  in
      let printer uu____53141 =
        match uu____53141 with
        | (x,y) ->
            let uu____53149 = ea.print x  in
            let uu____53151 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____53149 uu____53151
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____53194  ->
             let proj i ab =
               let uu____53210 =
                 let uu____53215 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____53217 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____53215
                   uu____53217 i
                  in
               match uu____53210 with
               | (proj_1,uu____53221) ->
                   let proj_1_tm =
                     let uu____53223 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____53223  in
                   let uu____53224 =
                     let uu____53229 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____53230 =
                       let uu____53231 =
                         let uu____53240 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____53240  in
                       let uu____53241 =
                         let uu____53252 =
                           let uu____53261 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____53261  in
                         let uu____53262 =
                           let uu____53273 = FStar_Syntax_Syntax.as_arg ab
                              in
                           [uu____53273]  in
                         uu____53252 :: uu____53262  in
                       uu____53231 :: uu____53241  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____53229 uu____53230
                      in
                   uu____53224 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____53318 =
               let uu____53323 =
                 let uu____53324 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____53324
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____53325 =
                 let uu____53326 =
                   let uu____53335 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____53335  in
                 let uu____53336 =
                   let uu____53347 =
                     let uu____53356 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____53356  in
                   let uu____53357 =
                     let uu____53368 =
                       let uu____53377 =
                         let uu____53378 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____53378 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____53377  in
                     let uu____53385 =
                       let uu____53396 =
                         let uu____53405 =
                           let uu____53406 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____53406 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____53405  in
                       [uu____53396]  in
                     uu____53368 :: uu____53385  in
                   uu____53347 :: uu____53357  in
                 uu____53326 :: uu____53336  in
               FStar_Syntax_Syntax.mk_Tm_app uu____53323 uu____53325  in
             uu____53318 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____53504 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____53504 with
             | (hd1,args) ->
                 let uu____53547 =
                   let uu____53560 =
                     let uu____53561 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____53561.FStar_Syntax_Syntax.n  in
                   (uu____53560, args)  in
                 (match uu____53547 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____53579::uu____53580::(a,uu____53582)::(b,uu____53584)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____53643 =
                        let uu____53646 = unembed ea a  in
                        uu____53646 w norm1  in
                      FStar_Util.bind_opt uu____53643
                        (fun a1  ->
                           let uu____53660 =
                             let uu____53663 = unembed eb b  in
                             uu____53663 w norm1  in
                           FStar_Util.bind_opt uu____53660
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____53680 ->
                      (if w
                       then
                         (let uu____53695 =
                            let uu____53701 =
                              let uu____53703 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____53703
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____53701)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____53695)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____53713 =
        let uu____53714 = type_of ea  in
        let uu____53715 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____53714 uu____53715  in
      mk_emb_full em un uu____53713 printer emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____53759 =
          let uu____53764 =
            let uu____53765 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____53774 =
              let uu____53785 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____53785]  in
            uu____53765 :: uu____53774  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____53764  in
        uu____53759 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____53819 =
          let uu____53827 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____53827, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____53819  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____53850 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____53850
        | FStar_Util.Inr b ->
            let uu____53854 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____53854
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____53900  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____53913 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____53913  in
                         let uu____53914 =
                           let uu____53919 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____53920 =
                             let uu____53921 =
                               let uu____53930 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____53930  in
                             let uu____53931 =
                               let uu____53942 =
                                 let uu____53951 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____53951  in
                               let uu____53952 =
                                 let uu____53963 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____53963]  in
                               uu____53942 :: uu____53952  in
                             uu____53921 :: uu____53931  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____53919
                             uu____53920
                            in
                         uu____53914 FStar_Pervasives_Native.None rng)
                     in
                  let uu____54004 =
                    let uu____54009 =
                      let uu____54010 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____54010
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____54011 =
                      let uu____54012 =
                        let uu____54021 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____54021  in
                      let uu____54022 =
                        let uu____54033 =
                          let uu____54042 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____54042  in
                        let uu____54043 =
                          let uu____54054 =
                            let uu____54063 =
                              let uu____54064 = embed ea a  in
                              uu____54064 rng shadow_a norm1  in
                            FStar_Syntax_Syntax.as_arg uu____54063  in
                          [uu____54054]  in
                        uu____54033 :: uu____54043  in
                      uu____54012 :: uu____54022  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____54009 uu____54011  in
                  uu____54004 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____54104  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____54117 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____54117  in
                         let uu____54118 =
                           let uu____54123 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____54124 =
                             let uu____54125 =
                               let uu____54134 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____54134  in
                             let uu____54135 =
                               let uu____54146 =
                                 let uu____54155 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____54155  in
                               let uu____54156 =
                                 let uu____54167 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____54167]  in
                               uu____54146 :: uu____54156  in
                             uu____54125 :: uu____54135  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____54123
                             uu____54124
                            in
                         uu____54118 FStar_Pervasives_Native.None rng)
                     in
                  let uu____54208 =
                    let uu____54213 =
                      let uu____54214 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____54214
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____54215 =
                      let uu____54216 =
                        let uu____54225 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____54225  in
                      let uu____54226 =
                        let uu____54237 =
                          let uu____54246 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____54246  in
                        let uu____54247 =
                          let uu____54258 =
                            let uu____54267 =
                              let uu____54268 = embed eb b  in
                              uu____54268 rng shadow_b norm1  in
                            FStar_Syntax_Syntax.as_arg uu____54267  in
                          [uu____54258]  in
                        uu____54237 :: uu____54247  in
                      uu____54216 :: uu____54226  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____54213 uu____54215  in
                  uu____54208 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____54356 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____54356 with
             | (hd1,args) ->
                 let uu____54399 =
                   let uu____54414 =
                     let uu____54415 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____54415.FStar_Syntax_Syntax.n  in
                   (uu____54414, args)  in
                 (match uu____54399 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____54435::uu____54436::(a,uu____54438)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____54505 =
                        let uu____54508 = unembed ea a  in
                        uu____54508 w norm1  in
                      FStar_Util.bind_opt uu____54505
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____54526::uu____54527::(b,uu____54529)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____54596 =
                        let uu____54599 = unembed eb b  in
                        uu____54599 w norm1  in
                      FStar_Util.bind_opt uu____54596
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____54616 ->
                      (if w
                       then
                         (let uu____54633 =
                            let uu____54639 =
                              let uu____54641 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____54641
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____54639)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____54633)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____54651 =
        let uu____54652 = type_of ea  in
        let uu____54653 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____54652 uu____54653  in
      mk_emb_full em un uu____54651 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____54681 =
        let uu____54686 =
          let uu____54687 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____54687]  in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____54686  in
      uu____54681 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____54713 =
        let uu____54721 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____54721, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____54713  in
    let printer l =
      let uu____54738 =
        let uu____54740 =
          let uu____54742 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____54742 (FStar_String.concat "; ")  in
        Prims.op_Hat uu____54740 "]"  in
      Prims.op_Hat "[" uu____54738  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____54786  ->
           let t =
             let uu____54788 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____54788  in
           match l with
           | [] ->
               let uu____54789 =
                 let uu____54794 =
                   let uu____54795 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____54795
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____54794 [t]  in
               uu____54789 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____54817 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____54817
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____54837 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____54837  in
                 let uu____54838 =
                   let uu____54843 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____54844 =
                     let uu____54845 =
                       let uu____54854 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____54854  in
                     let uu____54855 =
                       let uu____54866 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____54866]  in
                     uu____54845 :: uu____54855  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____54843 uu____54844  in
                 uu____54838 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____54903 =
                 let uu____54908 =
                   let uu____54909 =
                     let uu____54920 =
                       let uu____54929 =
                         let uu____54930 = embed ea hd1  in
                         uu____54930 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____54929  in
                     let uu____54937 =
                       let uu____54948 =
                         let uu____54957 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____54957  in
                       [uu____54948]  in
                     uu____54920 :: uu____54937  in
                   t :: uu____54909  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____54908  in
               uu____54903 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____55029 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____55029 with
           | (hd1,args) ->
               let uu____55070 =
                 let uu____55083 =
                   let uu____55084 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____55084.FStar_Syntax_Syntax.n  in
                 (uu____55083, args)  in
               (match uu____55070 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____55100) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____55120,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____55121))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____55163 =
                      let uu____55166 = unembed ea hd2  in
                      uu____55166 w norm1  in
                    FStar_Util.bind_opt uu____55163
                      (fun hd3  ->
                         let uu____55178 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____55178
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____55226 =
                      let uu____55229 = unembed ea hd2  in
                      uu____55229 w norm1  in
                    FStar_Util.bind_opt uu____55226
                      (fun hd3  ->
                         let uu____55241 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____55241
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____55256 ->
                    (if w
                     then
                       (let uu____55271 =
                          let uu____55277 =
                            let uu____55279 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____55279
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____55277)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____55271)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____55287 =
      let uu____55288 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____55288  in
    mk_emb_full em un uu____55287 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____55331 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____55342 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____55353 -> false
  
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____55364 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____55375 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____55386 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____55397 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____55408 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____55423 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____55454 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____55485 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____55512 -> false
  
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
    let uu____55530 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____55530  in
  let emb_t_norm_step =
    let uu____55533 =
      let uu____55541 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____55541, [])  in
    FStar_Syntax_Syntax.ET_app uu____55533  in
  let printer uu____55553 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____55579  ->
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
             let uu____55584 =
               let uu____55589 =
                 let uu____55590 =
                   let uu____55599 =
                     let uu____55600 =
                       let uu____55607 = e_list e_string  in
                       embed uu____55607 l  in
                     uu____55600 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____55599  in
                 [uu____55590]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____55589  in
             uu____55584 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____55639 =
               let uu____55644 =
                 let uu____55645 =
                   let uu____55654 =
                     let uu____55655 =
                       let uu____55662 = e_list e_string  in
                       embed uu____55662 l  in
                     uu____55655 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____55654  in
                 [uu____55645]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____55644
                in
             uu____55639 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____55694 =
               let uu____55699 =
                 let uu____55700 =
                   let uu____55709 =
                     let uu____55710 =
                       let uu____55717 = e_list e_string  in
                       embed uu____55717 l  in
                     uu____55710 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____55709  in
                 [uu____55700]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____55699  in
             uu____55694 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____55777 = FStar_Syntax_Util.head_and_args t1  in
         match uu____55777 with
         | (hd1,args) ->
             let uu____55822 =
               let uu____55837 =
                 let uu____55838 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____55838.FStar_Syntax_Syntax.n  in
               (uu____55837, args)  in
             (match uu____55822 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____56026)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____56061 =
                    let uu____56067 =
                      let uu____56077 = e_list e_string  in
                      unembed uu____56077 l  in
                    uu____56067 w norm1  in
                  FStar_Util.bind_opt uu____56061
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _56097  -> FStar_Pervasives_Native.Some _56097)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____56100)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____56135 =
                    let uu____56141 =
                      let uu____56151 = e_list e_string  in
                      unembed uu____56151 l  in
                    uu____56141 w norm1  in
                  FStar_Util.bind_opt uu____56135
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _56171  -> FStar_Pervasives_Native.Some _56171)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____56174)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____56209 =
                    let uu____56215 =
                      let uu____56225 = e_list e_string  in
                      unembed uu____56225 l  in
                    uu____56215 w norm1  in
                  FStar_Util.bind_opt uu____56209
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _56245  -> FStar_Pervasives_Native.Some _56245)
                         (UnfoldAttr ss))
              | uu____56246 ->
                  (if w
                   then
                     (let uu____56263 =
                        let uu____56269 =
                          let uu____56271 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____56271
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____56269)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____56263)
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
    | uu____56331 ->
        (if w
         then
           (let uu____56334 =
              let uu____56340 =
                let uu____56342 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____56342
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____56340)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____56334)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____56348 =
    let uu____56349 =
      let uu____56357 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____56357, [])  in
    FStar_Syntax_Syntax.ET_app uu____56349  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____56348
  
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
        let uu____56428 =
          let uu____56435 =
            let uu____56436 =
              let uu____56451 =
                let uu____56460 =
                  let uu____56467 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____56467, FStar_Pervasives_Native.None)  in
                [uu____56460]  in
              let uu____56482 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____56451, uu____56482)  in
            FStar_Syntax_Syntax.Tm_arrow uu____56436  in
          FStar_Syntax_Syntax.mk uu____56435  in
        uu____56428 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____56554  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____56560  ->
             let uu____56561 = force_shadow shadow_f  in
             match uu____56561 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____56566 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____56566
                   then
                     let uu____56590 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____56592 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____56590 uu____56592
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f)  in
                   (let uu____56599 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____56599
                    then
                      let uu____56623 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____56625 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____56627 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____56623 uu____56625 uu____56627
                    else ());
                   res)))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               (let uu____56686 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____56686
                then
                  let uu____56710 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____56712 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____56710
                    uu____56712
                else ());
               (let a_tm =
                  let uu____56718 = embed ea a  in
                  uu____56718 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1
                   in
                let b_tm =
                  let uu____56728 =
                    let uu____56733 =
                      let uu____56734 =
                        let uu____56739 =
                          let uu____56740 = FStar_Syntax_Syntax.as_arg a_tm
                             in
                          [uu____56740]  in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____56739  in
                      uu____56734 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____56733  in
                  norm1 uu____56728  in
                let uu____56765 =
                  let uu____56768 = unembed eb b_tm  in uu____56768 w norm1
                   in
                match uu____56765 with
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
                let uu____56862 = FStar_List.splitAt n_tvars args  in
                match uu____56862 with
                | (_tvar_args,rest_args) ->
                    let uu____56939 = FStar_List.hd rest_args  in
                    (match uu____56939 with
                     | (x,uu____56959) ->
                         let shadow_app =
                           let uu____56973 =
                             FStar_Common.mk_thunk
                               (fun uu____56980  ->
                                  let uu____56981 =
                                    let uu____56986 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____56986
                                      args
                                     in
                                  uu____56981 FStar_Pervasives_Native.None
                                    rng)
                              in
                           FStar_Pervasives_Native.Some uu____56973  in
                         let uu____56989 =
                           let uu____56992 =
                             let uu____56995 = unembed ea x  in
                             uu____56995 true norm1  in
                           FStar_Util.map_opt uu____56992
                             (fun x1  ->
                                let uu____57006 =
                                  let uu____57013 = f x1  in
                                  embed eb uu____57013  in
                                uu____57006 rng shadow_app norm1)
                            in
                         (match uu____56989 with
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
                  let uu____57116 = FStar_List.splitAt n_tvars args  in
                  match uu____57116 with
                  | (_tvar_args,rest_args) ->
                      let uu____57179 = FStar_List.hd rest_args  in
                      (match uu____57179 with
                       | (x,uu____57195) ->
                           let uu____57200 =
                             let uu____57207 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____57207  in
                           (match uu____57200 with
                            | (y,uu____57231) ->
                                let shadow_app =
                                  let uu____57241 =
                                    FStar_Common.mk_thunk
                                      (fun uu____57248  ->
                                         let uu____57249 =
                                           let uu____57254 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____57254 args
                                            in
                                         uu____57249
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____57241
                                   in
                                let uu____57257 =
                                  let uu____57260 =
                                    let uu____57263 = unembed ea x  in
                                    uu____57263 true norm1  in
                                  FStar_Util.bind_opt uu____57260
                                    (fun x1  ->
                                       let uu____57274 =
                                         let uu____57277 = unembed eb y  in
                                         uu____57277 true norm1  in
                                       FStar_Util.bind_opt uu____57274
                                         (fun y1  ->
                                            let uu____57288 =
                                              let uu____57289 =
                                                let uu____57296 = f x1 y1  in
                                                embed ec uu____57296  in
                                              uu____57289 rng shadow_app
                                                norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____57288))
                                   in
                                (match uu____57257 with
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
                    let uu____57418 = FStar_List.splitAt n_tvars args  in
                    match uu____57418 with
                    | (_tvar_args,rest_args) ->
                        let uu____57481 = FStar_List.hd rest_args  in
                        (match uu____57481 with
                         | (x,uu____57497) ->
                             let uu____57502 =
                               let uu____57509 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____57509  in
                             (match uu____57502 with
                              | (y,uu____57533) ->
                                  let uu____57538 =
                                    let uu____57545 =
                                      let uu____57554 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____57554  in
                                    FStar_List.hd uu____57545  in
                                  (match uu____57538 with
                                   | (z,uu____57584) ->
                                       let shadow_app =
                                         let uu____57594 =
                                           FStar_Common.mk_thunk
                                             (fun uu____57601  ->
                                                let uu____57602 =
                                                  let uu____57607 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____57607 args
                                                   in
                                                uu____57602
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____57594
                                          in
                                       let uu____57610 =
                                         let uu____57613 =
                                           let uu____57616 = unembed ea x  in
                                           uu____57616 true norm1  in
                                         FStar_Util.bind_opt uu____57613
                                           (fun x1  ->
                                              let uu____57627 =
                                                let uu____57630 =
                                                  unembed eb y  in
                                                uu____57630 true norm1  in
                                              FStar_Util.bind_opt uu____57627
                                                (fun y1  ->
                                                   let uu____57641 =
                                                     let uu____57644 =
                                                       unembed ec z  in
                                                     uu____57644 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____57641
                                                     (fun z1  ->
                                                        let uu____57655 =
                                                          let uu____57656 =
                                                            let uu____57663 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____57663
                                                             in
                                                          uu____57656 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____57655)))
                                          in
                                       (match uu____57610 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____57693 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____57693 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____57722 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____57722 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  