open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___429_55303  ->
    match uu___429_55303 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____55310 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____55310
  
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embedding_failure  -> true | uu____55320 -> false
  
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unembedding_failure  -> true
    | uu____55331 -> false
  
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
             (fun uu____55497  ->
                let uu____55498 = FStar_Common.force_thunk s1  in
                f uu____55498))
  
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
  'Auu____56132 . FStar_Syntax_Syntax.term -> 'Auu____56132 -> Prims.string =
  fun typ  ->
    fun uu____56143  ->
      let uu____56144 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____56144
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____56153 =
      let uu____56154 = FStar_Syntax_Subst.compress t  in
      uu____56154.FStar_Syntax_Syntax.n  in
    match uu____56153 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____56158 ->
        let uu____56159 =
          let uu____56161 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____56161
           in
        failwith uu____56159
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____56289 =
          let uu____56290 =
            let uu____56298 =
              let uu____56300 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____56300 FStar_Ident.string_of_lid  in
            (uu____56298, [])  in
          FStar_Syntax_Syntax.ET_app uu____56290  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____56289 }
  
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
      fun n1  -> let uu____56710 = unembed e t  in uu____56710 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      fun n1  -> let uu____56759 = unembed e t  in uu____56759 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___508_56812 = e  in
      {
        em = (uu___508_56812.em);
        un = (uu___508_56812.un);
        typ = ty;
        print = (uu___508_56812.print);
        emb_typ = (uu___508_56812.emb_typ)
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
              (let uu____56881 =
                 FStar_ST.op_Bang FStar_Options.debug_embedding  in
               if uu____56881
               then
                 let uu____56905 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____56907 = FStar_Syntax_Print.emb_typ_to_string et
                    in
                 let uu____56909 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n"
                   uu____56905 uu____56907 uu____56909
               else ());
              (let uu____56916 =
                 FStar_ST.op_Bang FStar_Options.eager_embedding  in
               if uu____56916
               then f ()
               else
                 (let thunk1 = FStar_Common.mk_thunk f  in
                  let uu____56951 =
                    let uu____56958 =
                      let uu____56959 =
                        let uu____56960 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____56960;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk1));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____56959  in
                    FStar_Syntax_Syntax.mk uu____56958  in
                  uu____56951 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____57076;
                  FStar_Syntax_Syntax.rng = uu____57077;_}
                ->
                let uu____57088 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____57088
                then
                  let res =
                    let uu____57117 = FStar_Common.force_thunk t  in
                    f uu____57117  in
                  ((let uu____57161 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____57161
                    then
                      let uu____57185 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____57187 =
                        FStar_Syntax_Print.emb_typ_to_string et'  in
                      let uu____57189 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____57194 = pa x2  in
                            Prims.op_Hat "Some " uu____57194
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____57185 uu____57187 uu____57189
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____57206 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____57206
                    then
                      let uu____57230 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____57232 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____57230 uu____57232
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____57239 ->
                let aopt = f x1  in
                ((let uu____57244 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____57244
                  then
                    let uu____57268 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____57270 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____57272 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____57277 = pa a  in
                          Prims.op_Hat "Some " uu____57277
                       in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____57268 uu____57270 uu____57272
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____57357 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____57357
       then
         let uu____57381 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____57381
       else ());
      t  in
    let un t _w _n =
      (let uu____57411 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____57411
       then
         let uu____57435 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____57435
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____57530 =
    let uu____57531 =
      let uu____57539 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____57539, [])  in
    FStar_Syntax_Syntax.ET_app uu____57531  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____57530
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___582_57611 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___582_57611.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___582_57611.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____57641 ->
        (if w
         then
           (let uu____57644 =
              let uu____57650 =
                let uu____57652 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____57652  in
              (FStar_Errors.Warning_NotEmbedded, uu____57650)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____57644)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____57658 =
    let uu____57659 =
      let uu____57667 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____57667, [])  in
    FStar_Syntax_Syntax.ET_app uu____57659  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____57674  -> "()")
    uu____57658
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___602_57753 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___602_57753.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___602_57753.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____57791 ->
        (if w
         then
           (let uu____57794 =
              let uu____57800 =
                let uu____57802 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____57802  in
              (FStar_Errors.Warning_NotEmbedded, uu____57800)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____57794)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____57809 =
    let uu____57810 =
      let uu____57818 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____57818, [])  in
    FStar_Syntax_Syntax.ET_app uu____57810  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____57809
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___621_57895 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___621_57895.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___621_57895.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____57931 ->
        (if w
         then
           (let uu____57934 =
              let uu____57940 =
                let uu____57942 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____57942  in
              (FStar_Errors.Warning_NotEmbedded, uu____57940)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____57934)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____57949 =
    let uu____57950 =
      let uu____57958 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____57958, [])  in
    FStar_Syntax_Syntax.ET_app uu____57950  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____57949
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____57970 =
      let uu____57978 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____57978, [])  in
    FStar_Syntax_Syntax.ET_app uu____57970  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____58049  ->
         let uu____58050 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____58050)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____58087)) ->
             let uu____58102 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____58102
         | uu____58103 ->
             (if w
              then
                (let uu____58106 =
                   let uu____58112 =
                     let uu____58114 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____58114
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____58112)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                   uu____58106)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____58125 =
      let uu____58133 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____58133, [])  in
    FStar_Syntax_Syntax.ET_app uu____58125  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____58238)) -> FStar_Pervasives_Native.Some s
    | uu____58242 ->
        (if w
         then
           (let uu____58245 =
              let uu____58251 =
                let uu____58253 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____58253
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____58251)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____58245)
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
      let uu____58289 =
        let uu____58294 =
          let uu____58295 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____58295]  in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____58294  in
      uu____58289 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____58323 =
        let uu____58331 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____58331, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____58323  in
    let printer uu___430_58345 =
      match uu___430_58345 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____58351 =
            let uu____58353 = ea.print x  in Prims.op_Hat uu____58353 ")"  in
          Prims.op_Hat "(Some " uu____58351
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____58430  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____58431 =
                 let uu____58436 =
                   let uu____58437 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____58437
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____58438 =
                   let uu____58439 =
                     let uu____58448 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____58448  in
                   [uu____58439]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____58436 uu____58438  in
               uu____58431 FStar_Pervasives_Native.None rng
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
                        let uu____58539 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____58539  in
                      let uu____58540 =
                        let uu____58545 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____58546 =
                          let uu____58547 =
                            let uu____58556 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____58556  in
                          let uu____58557 =
                            let uu____58568 = FStar_Syntax_Syntax.as_arg t
                               in
                            [uu____58568]  in
                          uu____58547 :: uu____58557  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____58545 uu____58546
                         in
                      uu____58540 FStar_Pervasives_Native.None rng)
                  in
               let uu____58603 =
                 let uu____58608 =
                   let uu____58609 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____58609
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____58610 =
                   let uu____58611 =
                     let uu____58620 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____58620  in
                   let uu____58621 =
                     let uu____58632 =
                       let uu____58641 =
                         let uu____58642 = embed ea a  in
                         uu____58642 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____58641  in
                     [uu____58632]  in
                   uu____58611 :: uu____58621  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____58608 uu____58610  in
               uu____58603 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____58779 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____58779 with
           | (hd1,args) ->
               let uu____58820 =
                 let uu____58835 =
                   let uu____58836 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____58836.FStar_Syntax_Syntax.n  in
                 (uu____58835, args)  in
               (match uu____58820 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____58854) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____58878::(a,uu____58880)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____58931 =
                      let uu____58934 = unembed ea a  in uu____58934 w norm1
                       in
                    FStar_Util.bind_opt uu____58931
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____58953 ->
                    (if w
                     then
                       (let uu____58970 =
                          let uu____58976 =
                            let uu____58978 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____58978
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____58976)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____58970)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____58986 =
      let uu____58987 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____58987  in
    mk_emb_full em un uu____58986 printer emb_t_option_a
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2  in
        let uu____59029 =
          let uu____59034 =
            let uu____59035 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____59044 =
              let uu____59055 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____59055]  in
            uu____59035 :: uu____59044  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____59034  in
        uu____59029 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____59091 =
          let uu____59099 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____59099, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____59091  in
      let printer uu____59115 =
        match uu____59115 with
        | (x,y) ->
            let uu____59123 = ea.print x  in
            let uu____59125 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____59123 uu____59125
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____59210  ->
             let proj i ab =
               let uu____59226 =
                 let uu____59231 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____59233 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____59231
                   uu____59233 i
                  in
               match uu____59226 with
               | (proj_1,uu____59237) ->
                   let proj_1_tm =
                     let uu____59239 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____59239  in
                   let uu____59240 =
                     let uu____59245 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____59246 =
                       let uu____59247 =
                         let uu____59256 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____59256  in
                       let uu____59257 =
                         let uu____59268 =
                           let uu____59277 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____59277  in
                         let uu____59278 =
                           let uu____59289 = FStar_Syntax_Syntax.as_arg ab
                              in
                           [uu____59289]  in
                         uu____59268 :: uu____59278  in
                       uu____59247 :: uu____59257  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____59245 uu____59246
                      in
                   uu____59240 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____59450 =
               let uu____59455 =
                 let uu____59456 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____59456
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____59457 =
                 let uu____59458 =
                   let uu____59467 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____59467  in
                 let uu____59468 =
                   let uu____59479 =
                     let uu____59488 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____59488  in
                   let uu____59489 =
                     let uu____59500 =
                       let uu____59509 =
                         let uu____59510 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____59510 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____59509  in
                     let uu____59580 =
                       let uu____59591 =
                         let uu____59600 =
                           let uu____59601 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____59601 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____59600  in
                       [uu____59591]  in
                     uu____59500 :: uu____59580  in
                   uu____59479 :: uu____59489  in
                 uu____59458 :: uu____59468  in
               FStar_Syntax_Syntax.mk_Tm_app uu____59455 uu____59457  in
             uu____59450 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____59766 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____59766 with
             | (hd1,args) ->
                 let uu____59809 =
                   let uu____59822 =
                     let uu____59823 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____59823.FStar_Syntax_Syntax.n  in
                   (uu____59822, args)  in
                 (match uu____59809 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____59841::uu____59842::(a,uu____59844)::(b,uu____59846)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____59905 =
                        let uu____59908 = unembed ea a  in
                        uu____59908 w norm1  in
                      FStar_Util.bind_opt uu____59905
                        (fun a1  ->
                           let uu____59928 =
                             let uu____59931 = unembed eb b  in
                             uu____59931 w norm1  in
                           FStar_Util.bind_opt uu____59928
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____59954 ->
                      (if w
                       then
                         (let uu____59969 =
                            let uu____59975 =
                              let uu____59977 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____59977
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____59975)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____59969)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____59987 =
        let uu____59988 = type_of ea  in
        let uu____59989 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____59988 uu____59989  in
      mk_emb_full em un uu____59987 printer emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____60033 =
          let uu____60038 =
            let uu____60039 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____60048 =
              let uu____60059 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____60059]  in
            uu____60039 :: uu____60048  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____60038  in
        uu____60033 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____60095 =
          let uu____60103 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____60103, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____60095  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____60126 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____60126
        | FStar_Util.Inr b ->
            let uu____60130 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____60130
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____60218  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____60290 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____60290  in
                         let uu____60291 =
                           let uu____60296 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____60297 =
                             let uu____60298 =
                               let uu____60307 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____60307  in
                             let uu____60308 =
                               let uu____60319 =
                                 let uu____60328 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____60328  in
                               let uu____60329 =
                                 let uu____60340 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____60340]  in
                               uu____60319 :: uu____60329  in
                             uu____60298 :: uu____60308  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____60296
                             uu____60297
                            in
                         uu____60291 FStar_Pervasives_Native.None rng)
                     in
                  let uu____60383 =
                    let uu____60388 =
                      let uu____60389 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____60389
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____60390 =
                      let uu____60391 =
                        let uu____60400 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____60400  in
                      let uu____60401 =
                        let uu____60412 =
                          let uu____60421 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____60421  in
                        let uu____60422 =
                          let uu____60433 =
                            let uu____60442 =
                              let uu____60443 = embed ea a  in
                              uu____60443 rng shadow_a norm1  in
                            FStar_Syntax_Syntax.as_arg uu____60442  in
                          [uu____60433]  in
                        uu____60412 :: uu____60422  in
                      uu____60391 :: uu____60401  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____60388 uu____60390  in
                  uu____60383 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____60548  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____60620 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____60620  in
                         let uu____60621 =
                           let uu____60626 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____60627 =
                             let uu____60628 =
                               let uu____60637 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____60637  in
                             let uu____60638 =
                               let uu____60649 =
                                 let uu____60658 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____60658  in
                               let uu____60659 =
                                 let uu____60670 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____60670]  in
                               uu____60649 :: uu____60659  in
                             uu____60628 :: uu____60638  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____60626
                             uu____60627
                            in
                         uu____60621 FStar_Pervasives_Native.None rng)
                     in
                  let uu____60713 =
                    let uu____60718 =
                      let uu____60719 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____60719
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____60720 =
                      let uu____60721 =
                        let uu____60730 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____60730  in
                      let uu____60731 =
                        let uu____60742 =
                          let uu____60751 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____60751  in
                        let uu____60752 =
                          let uu____60763 =
                            let uu____60772 =
                              let uu____60773 = embed eb b  in
                              uu____60773 rng shadow_b norm1  in
                            FStar_Syntax_Syntax.as_arg uu____60772  in
                          [uu____60763]  in
                        uu____60742 :: uu____60752  in
                      uu____60721 :: uu____60731  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____60718 uu____60720  in
                  uu____60713 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____60928 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____60928 with
             | (hd1,args) ->
                 let uu____60971 =
                   let uu____60986 =
                     let uu____60987 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____60987.FStar_Syntax_Syntax.n  in
                   (uu____60986, args)  in
                 (match uu____60971 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____61007::uu____61008::(a,uu____61010)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____61077 =
                        let uu____61080 = unembed ea a  in
                        uu____61080 w norm1  in
                      FStar_Util.bind_opt uu____61077
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____61104::uu____61105::(b,uu____61107)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____61174 =
                        let uu____61177 = unembed eb b  in
                        uu____61177 w norm1  in
                      FStar_Util.bind_opt uu____61174
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____61200 ->
                      (if w
                       then
                         (let uu____61217 =
                            let uu____61223 =
                              let uu____61225 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____61225
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____61223)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____61217)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____61235 =
        let uu____61236 = type_of ea  in
        let uu____61237 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____61236 uu____61237  in
      mk_emb_full em un uu____61235 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____61265 =
        let uu____61270 =
          let uu____61271 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____61271]  in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____61270  in
      uu____61265 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____61299 =
        let uu____61307 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____61307, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____61299  in
    let printer l =
      let uu____61324 =
        let uu____61326 =
          let uu____61328 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____61328 (FStar_String.concat "; ")  in
        Prims.op_Hat uu____61326 "]"  in
      Prims.op_Hat "[" uu____61324  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____61414  ->
           let t =
             let uu____61416 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____61416  in
           match l with
           | [] ->
               let uu____61417 =
                 let uu____61422 =
                   let uu____61423 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____61423
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____61422 [t]  in
               uu____61417 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____61447 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____61447
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____61467 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____61467  in
                 let uu____61468 =
                   let uu____61473 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____61474 =
                     let uu____61475 =
                       let uu____61484 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____61484  in
                     let uu____61485 =
                       let uu____61496 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____61496]  in
                     uu____61475 :: uu____61485  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____61473 uu____61474  in
                 uu____61468 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____61649 =
                 let uu____61654 =
                   let uu____61655 =
                     let uu____61666 =
                       let uu____61675 =
                         let uu____61676 = embed ea hd1  in
                         uu____61676 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____61675  in
                     let uu____61746 =
                       let uu____61757 =
                         let uu____61766 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____61766  in
                       [uu____61757]  in
                     uu____61666 :: uu____61746  in
                   t :: uu____61655  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____61654  in
               uu____61649 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____61882 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____61882 with
           | (hd1,args) ->
               let uu____61923 =
                 let uu____61936 =
                   let uu____61937 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____61937.FStar_Syntax_Syntax.n  in
                 (uu____61936, args)  in
               (match uu____61923 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____61953) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____61973,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____61974))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____62016 =
                      let uu____62019 = unembed ea hd2  in
                      uu____62019 w norm1  in
                    FStar_Util.bind_opt uu____62016
                      (fun hd3  ->
                         let uu____62037 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____62037
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____62087 =
                      let uu____62090 = unembed ea hd2  in
                      uu____62090 w norm1  in
                    FStar_Util.bind_opt uu____62087
                      (fun hd3  ->
                         let uu____62108 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____62108
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____62125 ->
                    (if w
                     then
                       (let uu____62140 =
                          let uu____62146 =
                            let uu____62148 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____62148
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____62146)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____62140)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____62156 =
      let uu____62157 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____62157  in
    mk_emb_full em un uu____62156 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____62200 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____62211 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____62222 -> false
  
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____62233 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____62244 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____62255 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____62266 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____62277 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____62292 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____62324 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____62356 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____62384 -> false
  
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
    let uu____62402 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____62402  in
  let emb_t_norm_step =
    let uu____62405 =
      let uu____62413 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____62413, [])  in
    FStar_Syntax_Syntax.ET_app uu____62405  in
  let printer uu____62425 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____62491  ->
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
             let uu____62496 =
               let uu____62501 =
                 let uu____62502 =
                   let uu____62511 =
                     let uu____62512 =
                       let uu____62519 = e_list e_string  in
                       embed uu____62519 l  in
                     uu____62512 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____62511  in
                 [uu____62502]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____62501  in
             uu____62496 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____62578 =
               let uu____62583 =
                 let uu____62584 =
                   let uu____62593 =
                     let uu____62594 =
                       let uu____62601 = e_list e_string  in
                       embed uu____62601 l  in
                     uu____62594 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____62593  in
                 [uu____62584]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____62583
                in
             uu____62578 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____62660 =
               let uu____62665 =
                 let uu____62666 =
                   let uu____62675 =
                     let uu____62676 =
                       let uu____62683 = e_list e_string  in
                       embed uu____62683 l  in
                     uu____62676 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____62675  in
                 [uu____62666]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____62665  in
             uu____62660 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____62772 = FStar_Syntax_Util.head_and_args t1  in
         match uu____62772 with
         | (hd1,args) ->
             let uu____62817 =
               let uu____62832 =
                 let uu____62833 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____62833.FStar_Syntax_Syntax.n  in
               (uu____62832, args)  in
             (match uu____62817 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____63021)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____63056 =
                    let uu____63062 =
                      let uu____63072 = e_list e_string  in
                      unembed uu____63072 l  in
                    uu____63062 w norm1  in
                  FStar_Util.bind_opt uu____63056
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _63098  -> FStar_Pervasives_Native.Some _63098)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____63101)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____63136 =
                    let uu____63142 =
                      let uu____63152 = e_list e_string  in
                      unembed uu____63152 l  in
                    uu____63142 w norm1  in
                  FStar_Util.bind_opt uu____63136
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _63178  -> FStar_Pervasives_Native.Some _63178)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____63181)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____63216 =
                    let uu____63222 =
                      let uu____63232 = e_list e_string  in
                      unembed uu____63232 l  in
                    uu____63222 w norm1  in
                  FStar_Util.bind_opt uu____63216
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _63258  -> FStar_Pervasives_Native.Some _63258)
                         (UnfoldAttr ss))
              | uu____63259 ->
                  (if w
                   then
                     (let uu____63276 =
                        let uu____63282 =
                          let uu____63284 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____63284
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____63282)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____63276)
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
    | uu____63386 ->
        (if w
         then
           (let uu____63389 =
              let uu____63395 =
                let uu____63397 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____63397
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____63395)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____63389)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____63403 =
    let uu____63404 =
      let uu____63412 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____63412, [])  in
    FStar_Syntax_Syntax.ET_app uu____63404  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____63403
  
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
        let uu____63483 =
          let uu____63490 =
            let uu____63491 =
              let uu____63506 =
                let uu____63515 =
                  let uu____63522 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____63522, FStar_Pervasives_Native.None)  in
                [uu____63515]  in
              let uu____63537 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____63506, uu____63537)  in
            FStar_Syntax_Syntax.Tm_arrow uu____63491  in
          FStar_Syntax_Syntax.mk uu____63490  in
        uu____63483 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____63650  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____63656  ->
             let uu____63657 = force_shadow shadow_f  in
             match uu____63657 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____63719 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____63719
                   then
                     let uu____63743 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____63745 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____63743 uu____63745
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f)  in
                   (let uu____63752 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____63752
                    then
                      let uu____63776 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____63778 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____63780 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____63776 uu____63778 uu____63780
                    else ());
                   res)))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               (let uu____63839 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____63839
                then
                  let uu____63863 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____63865 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____63863
                    uu____63865
                else ());
               (let a_tm =
                  let uu____63871 = embed ea a  in
                  uu____63871 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1
                   in
                let b_tm =
                  let uu____63904 =
                    let uu____63909 =
                      let uu____63910 =
                        let uu____63915 =
                          let uu____63916 = FStar_Syntax_Syntax.as_arg a_tm
                             in
                          [uu____63916]  in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____63915  in
                      uu____63910 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____63909  in
                  norm1 uu____63904  in
                let uu____63943 =
                  let uu____63946 = unembed eb b_tm  in uu____63946 w norm1
                   in
                match uu____63943 with
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
                let uu____64046 = FStar_List.splitAt n_tvars args  in
                match uu____64046 with
                | (_tvar_args,rest_args) ->
                    let uu____64123 = FStar_List.hd rest_args  in
                    (match uu____64123 with
                     | (x,uu____64143) ->
                         let shadow_app =
                           let uu____64157 =
                             FStar_Common.mk_thunk
                               (fun uu____64166  ->
                                  let uu____64167 =
                                    let uu____64172 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____64172
                                      args
                                     in
                                  uu____64167 FStar_Pervasives_Native.None
                                    rng)
                              in
                           FStar_Pervasives_Native.Some uu____64157  in
                         let uu____64218 =
                           let uu____64221 =
                             let uu____64224 = unembed ea x  in
                             uu____64224 true norm1  in
                           FStar_Util.map_opt uu____64221
                             (fun x1  ->
                                let uu____64264 =
                                  let uu____64271 = f x1  in
                                  embed eb uu____64271  in
                                uu____64264 rng shadow_app norm1)
                            in
                         (match uu____64218 with
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
                  let uu____64401 = FStar_List.splitAt n_tvars args  in
                  match uu____64401 with
                  | (_tvar_args,rest_args) ->
                      let uu____64464 = FStar_List.hd rest_args  in
                      (match uu____64464 with
                       | (x,uu____64480) ->
                           let uu____64485 =
                             let uu____64492 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____64492  in
                           (match uu____64485 with
                            | (y,uu____64516) ->
                                let shadow_app =
                                  let uu____64526 =
                                    FStar_Common.mk_thunk
                                      (fun uu____64535  ->
                                         let uu____64536 =
                                           let uu____64541 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____64541 args
                                            in
                                         uu____64536
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____64526
                                   in
                                let uu____64587 =
                                  let uu____64590 =
                                    let uu____64593 = unembed ea x  in
                                    uu____64593 true norm1  in
                                  FStar_Util.bind_opt uu____64590
                                    (fun x1  ->
                                       let uu____64610 =
                                         let uu____64613 = unembed eb y  in
                                         uu____64613 true norm1  in
                                       FStar_Util.bind_opt uu____64610
                                         (fun y1  ->
                                            let uu____64630 =
                                              let uu____64631 =
                                                let uu____64638 = f x1 y1  in
                                                embed ec uu____64638  in
                                              uu____64631 rng shadow_app
                                                norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____64630))
                                   in
                                (match uu____64587 with
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
                    let uu____64787 = FStar_List.splitAt n_tvars args  in
                    match uu____64787 with
                    | (_tvar_args,rest_args) ->
                        let uu____64850 = FStar_List.hd rest_args  in
                        (match uu____64850 with
                         | (x,uu____64866) ->
                             let uu____64871 =
                               let uu____64878 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____64878  in
                             (match uu____64871 with
                              | (y,uu____64902) ->
                                  let uu____64907 =
                                    let uu____64914 =
                                      let uu____64923 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____64923  in
                                    FStar_List.hd uu____64914  in
                                  (match uu____64907 with
                                   | (z,uu____64953) ->
                                       let shadow_app =
                                         let uu____64963 =
                                           FStar_Common.mk_thunk
                                             (fun uu____64972  ->
                                                let uu____64973 =
                                                  let uu____64978 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____64978 args
                                                   in
                                                uu____64973
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____64963
                                          in
                                       let uu____65024 =
                                         let uu____65027 =
                                           let uu____65030 = unembed ea x  in
                                           uu____65030 true norm1  in
                                         FStar_Util.bind_opt uu____65027
                                           (fun x1  ->
                                              let uu____65047 =
                                                let uu____65050 =
                                                  unembed eb y  in
                                                uu____65050 true norm1  in
                                              FStar_Util.bind_opt uu____65047
                                                (fun y1  ->
                                                   let uu____65067 =
                                                     let uu____65070 =
                                                       unembed ec z  in
                                                     uu____65070 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____65067
                                                     (fun z1  ->
                                                        let uu____65087 =
                                                          let uu____65088 =
                                                            let uu____65095 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____65095
                                                             in
                                                          uu____65088 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____65087)))
                                          in
                                       (match uu____65024 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____65150 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____65150 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____65179 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____65179 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  