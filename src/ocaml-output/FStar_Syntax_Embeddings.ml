open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___0_16  ->
    match uu___0_16 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____23 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____23
  
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embedding_failure  -> true | uu____33 -> false
  
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unembedding_failure  -> true | uu____44 -> false
  
type shadow_term =
  FStar_Syntax_Syntax.term FStar_Thunk.t FStar_Pervasives_Native.option
let (map_shadow :
  shadow_term ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> shadow_term)
  = fun s  -> fun f  -> FStar_Util.map_opt s (FStar_Thunk.map f) 
let (force_shadow :
  shadow_term -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun s  -> FStar_Util.map_opt s FStar_Thunk.force 
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
    match projectee with | { em; un; typ; print; emb_typ;_} -> em
  
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun projectee  ->
    match projectee with | { em; un; typ; print; emb_typ;_} -> un
  
let __proj__Mkembedding__item__typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with | { em; un; typ; print; emb_typ;_} -> typ
  
let __proj__Mkembedding__item__print : 'a . 'a embedding -> 'a printer =
  fun projectee  ->
    match projectee with | { em; un; typ; print; emb_typ;_} -> print
  
let __proj__Mkembedding__item__emb_typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun projectee  ->
    match projectee with | { em; un; typ; print; emb_typ;_} -> emb_typ
  
let emb_typ_of : 'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun e  -> e.emb_typ 
let unknown_printer :
  'uuuuuu457 . FStar_Syntax_Syntax.term -> 'uuuuuu457 -> Prims.string =
  fun typ  ->
    fun uu____468  ->
      let uu____469 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____469
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____478 =
      let uu____479 = FStar_Syntax_Subst.compress t  in
      uu____479.FStar_Syntax_Syntax.n  in
    match uu____478 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____483 ->
        let uu____484 =
          let uu____486 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____486
           in
        failwith uu____484
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____529 =
          let uu____530 =
            let uu____538 =
              let uu____540 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____540 FStar_Ident.string_of_lid  in
            (uu____538, [])  in
          FStar_Syntax_Syntax.ET_app uu____530  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____529 }
  
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
        fun printer1  ->
          fun emb_typ  -> { em; un; typ; print = printer1; emb_typ }
  
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
    fun t  -> fun n  -> let uu____689 = unembed e t  in uu____689 true n
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  -> fun n  -> let uu____730 = unembed e t  in uu____730 false n
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___77_777 = e  in
      {
        em = (uu___77_777.em);
        un = (uu___77_777.un);
        typ = ty;
        print = (uu___77_777.print);
        emb_typ = (uu___77_777.emb_typ)
      }
  
let embed_as :
  'a 'b .
    'a embedding ->
      ('a -> 'b) ->
        ('b -> 'a) ->
          FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
            'b embedding
  =
  fun ea  ->
    fun ab  ->
      fun ba  ->
        fun o  ->
          let uu____835 =
            match o with
            | FStar_Pervasives_Native.Some t -> t
            | uu____837 -> type_of ea  in
          mk_emb_full (fun x  -> let uu____843 = ba x  in embed ea uu____843)
            (fun t  ->
               fun w  ->
                 fun cb  ->
                   let uu____853 =
                     let uu____856 = unembed ea t  in uu____856 w cb  in
                   FStar_Util.map_opt uu____853 ab) uu____835
            (fun x  ->
               let uu____866 = let uu____868 = ba x  in ea.print uu____868
                  in
               FStar_Util.format1 "(embed_as>> %s)\n" uu____866) ea.emb_typ
  
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
              (let uu____930 = FStar_ST.op_Bang FStar_Options.debug_embedding
                  in
               if uu____930
               then
                 let uu____954 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____956 = FStar_Syntax_Print.emb_typ_to_string et  in
                 let uu____958 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu____954
                   uu____956 uu____958
               else ());
              (let uu____963 = FStar_ST.op_Bang FStar_Options.eager_embedding
                  in
               if uu____963
               then f ()
               else
                 (let thunk = FStar_Thunk.mk f  in
                  let uu____998 =
                    let uu____1005 =
                      let uu____1006 =
                        let uu____1007 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____1007;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____1006  in
                    FStar_Syntax_Syntax.mk uu____1005  in
                  uu____998 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____1074;
                  FStar_Syntax_Syntax.rng = uu____1075;_}
                ->
                let uu____1086 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____1086
                then
                  let res =
                    let uu____1115 = FStar_Thunk.force t  in f uu____1115  in
                  ((let uu____1119 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1119
                    then
                      let uu____1143 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____1145 =
                        FStar_Syntax_Print.emb_typ_to_string et'  in
                      let uu____1147 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____1152 = pa x2  in
                            Prims.op_Hat "Some " uu____1152
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____1143 uu____1145 uu____1147
                    else ());
                   res)
                else
                  (let a1 = FStar_Dyn.undyn b  in
                   (let uu____1162 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1162
                    then
                      let uu____1186 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____1188 = pa a1  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____1186 uu____1188
                    else ());
                   FStar_Pervasives_Native.Some a1)
            | uu____1193 ->
                let aopt = f x1  in
                ((let uu____1198 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____1198
                  then
                    let uu____1222 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____1224 = FStar_Syntax_Print.term_to_string x1  in
                    let uu____1226 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a1 ->
                          let uu____1231 = pa a1  in
                          Prims.op_Hat "Some " uu____1231
                       in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____1222 uu____1224 uu____1226
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____1269 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____1269
       then
         let uu____1293 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____1293
       else ());
      t  in
    let un t _w _n =
      (let uu____1321 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____1321
       then
         let uu____1345 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____1345
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____1398 =
    let uu____1399 =
      let uu____1407 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____1407, [])  in
    FStar_Syntax_Syntax.ET_app uu____1399  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____1398
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___167_1439 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___167_1439.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___167_1439.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____1467 ->
        (if w
         then
           (let uu____1470 =
              let uu____1476 =
                let uu____1478 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____1478  in
              (FStar_Errors.Warning_NotEmbedded, uu____1476)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1470)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____1484 =
    let uu____1485 =
      let uu____1493 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____1493, [])  in
    FStar_Syntax_Syntax.ET_app uu____1485  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____1500  -> "()")
    uu____1484
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___187_1539 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___187_1539.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___187_1539.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____1575 ->
        (if w
         then
           (let uu____1578 =
              let uu____1584 =
                let uu____1586 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____1586  in
              (FStar_Errors.Warning_NotEmbedded, uu____1584)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1578)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____1593 =
    let uu____1594 =
      let uu____1602 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____1602, [])  in
    FStar_Syntax_Syntax.ET_app uu____1594  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____1593
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___206_1639 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___206_1639.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___206_1639.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____1673 ->
        (if w
         then
           (let uu____1676 =
              let uu____1682 =
                let uu____1684 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____1684  in
              (FStar_Errors.Warning_NotEmbedded, uu____1682)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1676)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____1691 =
    let uu____1692 =
      let uu____1700 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____1700, [])  in
    FStar_Syntax_Syntax.ET_app uu____1692  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____1691
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____1712 =
      let uu____1720 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____1720, [])  in
    FStar_Syntax_Syntax.ET_app uu____1712  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int i
      (fun uu____1751  ->
         let uu____1752 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____1752)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____1787)) ->
             let uu____1802 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____1802
         | uu____1803 ->
             (if w
              then
                (let uu____1806 =
                   let uu____1812 =
                     let uu____1814 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____1814
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1812)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1806)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____1825 =
      let uu____1833 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____1833, [])  in
    FStar_Syntax_Syntax.ET_app uu____1825  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____1896)) -> FStar_Pervasives_Native.Some s
    | uu____1900 ->
        (if w
         then
           (let uu____1903 =
              let uu____1909 =
                let uu____1911 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____1911
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1909)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1903)
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
      let uu____1947 =
        let uu____1952 =
          let uu____1953 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____1953]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____1952  in
      uu____1947 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____1979 =
        let uu____1987 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____1987, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____1979  in
    let printer1 uu___1_2001 =
      match uu___1_2001 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____2007 =
            let uu____2009 = ea.print x  in Prims.op_Hat uu____2009 ")"  in
          Prims.op_Hat "(Some " uu____2007
       in
    let em o rng topt norm =
      lazy_embed printer1 emb_t_option_a rng t_option_a o
        (fun uu____2044  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____2045 =
                 let uu____2050 =
                   let uu____2051 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2051
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2052 =
                   let uu____2053 =
                     let uu____2062 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2062  in
                   [uu____2053]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2050 uu____2052  in
               uu____2045 FStar_Pervasives_Native.None rng
           | FStar_Pervasives_Native.Some a1 ->
               let shadow_a =
                 map_shadow topt
                   (fun t  ->
                      let v = FStar_Ident.mk_ident ("v", rng)  in
                      let some_v =
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          FStar_Parser_Const.some_lid v
                         in
                      let some_v_tm =
                        let uu____2092 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____2092  in
                      let uu____2093 =
                        let uu____2098 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____2099 =
                          let uu____2100 =
                            let uu____2109 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____2109  in
                          let uu____2110 =
                            let uu____2121 = FStar_Syntax_Syntax.as_arg t  in
                            [uu____2121]  in
                          uu____2100 :: uu____2110  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____2098 uu____2099
                         in
                      uu____2093 FStar_Pervasives_Native.None rng)
                  in
               let uu____2154 =
                 let uu____2159 =
                   let uu____2160 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2160
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2161 =
                   let uu____2162 =
                     let uu____2171 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2171  in
                   let uu____2172 =
                     let uu____2183 =
                       let uu____2192 =
                         let uu____2193 = embed ea a1  in
                         uu____2193 rng shadow_a norm  in
                       FStar_Syntax_Syntax.as_arg uu____2192  in
                     [uu____2183]  in
                   uu____2162 :: uu____2172  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2159 uu____2161  in
               uu____2154 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer1 emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____2263 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____2263 with
           | (hd,args) ->
               let uu____2304 =
                 let uu____2319 =
                   let uu____2320 = FStar_Syntax_Util.un_uinst hd  in
                   uu____2320.FStar_Syntax_Syntax.n  in
                 (uu____2319, args)  in
               (match uu____2304 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2338) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____2362::(a1,uu____2364)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____2415 =
                      let uu____2418 = unembed ea a1  in uu____2418 w norm
                       in
                    FStar_Util.bind_opt uu____2415
                      (fun a2  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a2))
                | uu____2431 ->
                    (if w
                     then
                       (let uu____2448 =
                          let uu____2454 =
                            let uu____2456 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____2456
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____2454)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____2448)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____2464 =
      let uu____2465 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____2465  in
    mk_emb_full em un uu____2464 printer1 emb_t_option_a
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2  in
        let uu____2507 =
          let uu____2512 =
            let uu____2513 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____2522 =
              let uu____2533 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____2533]  in
            uu____2513 :: uu____2522  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____2512  in
        uu____2507 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____2567 =
          let uu____2575 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____2575, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____2567  in
      let printer1 uu____2591 =
        match uu____2591 with
        | (x,y) ->
            let uu____2599 = ea.print x  in
            let uu____2601 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____2599 uu____2601
         in
      let em x rng topt norm =
        lazy_embed printer1 emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____2644  ->
             let proj i ab =
               let proj_1 =
                 let uu____2661 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.of_int (2))
                     rng
                    in
                 let uu____2663 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____2661
                   uu____2663 i
                  in
               let proj_1_tm =
                 let uu____2665 =
                   FStar_Syntax_Syntax.lid_as_fv proj_1
                     FStar_Syntax_Syntax.delta_equational
                     FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____2665  in
               let uu____2666 =
                 let uu____2671 =
                   FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2672 =
                   let uu____2673 =
                     let uu____2682 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2682  in
                   let uu____2683 =
                     let uu____2694 =
                       let uu____2703 = type_of eb  in
                       FStar_Syntax_Syntax.iarg uu____2703  in
                     let uu____2704 =
                       let uu____2715 = FStar_Syntax_Syntax.as_arg ab  in
                       [uu____2715]  in
                     uu____2694 :: uu____2704  in
                   uu____2673 :: uu____2683  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2671 uu____2672  in
               uu____2666 FStar_Pervasives_Native.None rng  in
             let shadow_a = map_shadow topt (proj Prims.int_one)  in
             let shadow_b = map_shadow topt (proj (Prims.of_int (2)))  in
             let uu____2760 =
               let uu____2765 =
                 let uu____2766 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____2766
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____2767 =
                 let uu____2768 =
                   let uu____2777 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____2777  in
                 let uu____2778 =
                   let uu____2789 =
                     let uu____2798 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____2798  in
                   let uu____2799 =
                     let uu____2810 =
                       let uu____2819 =
                         let uu____2820 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____2820 rng shadow_a norm  in
                       FStar_Syntax_Syntax.as_arg uu____2819  in
                     let uu____2827 =
                       let uu____2838 =
                         let uu____2847 =
                           let uu____2848 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____2848 rng shadow_b norm  in
                         FStar_Syntax_Syntax.as_arg uu____2847  in
                       [uu____2838]  in
                     uu____2810 :: uu____2827  in
                   uu____2789 :: uu____2799  in
                 uu____2768 :: uu____2778  in
               FStar_Syntax_Syntax.mk_Tm_app uu____2765 uu____2767  in
             uu____2760 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer1 emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____2946 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____2946 with
             | (hd,args) ->
                 let uu____2989 =
                   let uu____3002 =
                     let uu____3003 = FStar_Syntax_Util.un_uinst hd  in
                     uu____3003.FStar_Syntax_Syntax.n  in
                   (uu____3002, args)  in
                 (match uu____2989 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____3021::uu____3022::(a1,uu____3024)::(b1,uu____3026)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____3085 =
                        let uu____3088 = unembed ea a1  in uu____3088 w norm
                         in
                      FStar_Util.bind_opt uu____3085
                        (fun a2  ->
                           let uu____3102 =
                             let uu____3105 = unembed eb b1  in
                             uu____3105 w norm  in
                           FStar_Util.bind_opt uu____3102
                             (fun b2  ->
                                FStar_Pervasives_Native.Some (a2, b2)))
                  | uu____3122 ->
                      (if w
                       then
                         (let uu____3137 =
                            let uu____3143 =
                              let uu____3145 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____3145
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____3143)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____3137)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____3155 =
        let uu____3156 = type_of ea  in
        let uu____3157 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____3156 uu____3157  in
      mk_emb_full em un uu____3155 printer1 emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____3201 =
          let uu____3206 =
            let uu____3207 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____3216 =
              let uu____3227 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____3227]  in
            uu____3207 :: uu____3216  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____3206  in
        uu____3201 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____3261 =
          let uu____3269 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____3269, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____3261  in
      let printer1 s =
        match s with
        | FStar_Util.Inl a1 ->
            let uu____3292 = ea.print a1  in
            FStar_Util.format1 "Inl %s" uu____3292
        | FStar_Util.Inr b1 ->
            let uu____3296 = eb.print b1  in
            FStar_Util.format1 "Inr %s" uu____3296
         in
      let em s rng topt norm =
        lazy_embed printer1 emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a1 ->
               (fun uu____3342  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v
                            in
                         let some_v_tm =
                           let uu____3355 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____3355  in
                         let uu____3356 =
                           let uu____3361 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____3362 =
                             let uu____3363 =
                               let uu____3372 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____3372  in
                             let uu____3373 =
                               let uu____3384 =
                                 let uu____3393 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____3393  in
                               let uu____3394 =
                                 let uu____3405 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____3405]  in
                               uu____3384 :: uu____3394  in
                             uu____3363 :: uu____3373  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3361
                             uu____3362
                            in
                         uu____3356 FStar_Pervasives_Native.None rng)
                     in
                  let uu____3446 =
                    let uu____3451 =
                      let uu____3452 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____3452
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____3453 =
                      let uu____3454 =
                        let uu____3463 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____3463  in
                      let uu____3464 =
                        let uu____3475 =
                          let uu____3484 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____3484  in
                        let uu____3485 =
                          let uu____3496 =
                            let uu____3505 =
                              let uu____3506 = embed ea a1  in
                              uu____3506 rng shadow_a norm  in
                            FStar_Syntax_Syntax.as_arg uu____3505  in
                          [uu____3496]  in
                        uu____3475 :: uu____3485  in
                      uu____3454 :: uu____3464  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____3451 uu____3453  in
                  uu____3446 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b1 ->
               (fun uu____3546  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v
                            in
                         let some_v_tm =
                           let uu____3559 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____3559  in
                         let uu____3560 =
                           let uu____3565 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____3566 =
                             let uu____3567 =
                               let uu____3576 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____3576  in
                             let uu____3577 =
                               let uu____3588 =
                                 let uu____3597 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____3597  in
                               let uu____3598 =
                                 let uu____3609 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____3609]  in
                               uu____3588 :: uu____3598  in
                             uu____3567 :: uu____3577  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3565
                             uu____3566
                            in
                         uu____3560 FStar_Pervasives_Native.None rng)
                     in
                  let uu____3650 =
                    let uu____3655 =
                      let uu____3656 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____3656
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____3657 =
                      let uu____3658 =
                        let uu____3667 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____3667  in
                      let uu____3668 =
                        let uu____3679 =
                          let uu____3688 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____3688  in
                        let uu____3689 =
                          let uu____3700 =
                            let uu____3709 =
                              let uu____3710 = embed eb b1  in
                              uu____3710 rng shadow_b norm  in
                            FStar_Syntax_Syntax.as_arg uu____3709  in
                          [uu____3700]  in
                        uu____3679 :: uu____3689  in
                      uu____3658 :: uu____3668  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____3655 uu____3657  in
                  uu____3650 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer1 emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____3798 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____3798 with
             | (hd,args) ->
                 let uu____3841 =
                   let uu____3856 =
                     let uu____3857 = FStar_Syntax_Util.un_uinst hd  in
                     uu____3857.FStar_Syntax_Syntax.n  in
                   (uu____3856, args)  in
                 (match uu____3841 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____3877::uu____3878::(a1,uu____3880)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____3947 =
                        let uu____3950 = unembed ea a1  in uu____3950 w norm
                         in
                      FStar_Util.bind_opt uu____3947
                        (fun a2  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a2))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____3968::uu____3969::(b1,uu____3971)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____4038 =
                        let uu____4041 = unembed eb b1  in uu____4041 w norm
                         in
                      FStar_Util.bind_opt uu____4038
                        (fun b2  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b2))
                  | uu____4058 ->
                      (if w
                       then
                         (let uu____4075 =
                            let uu____4081 =
                              let uu____4083 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____4083
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____4081)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____4075)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____4093 =
        let uu____4094 = type_of ea  in
        let uu____4095 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____4094 uu____4095  in
      mk_emb_full em un uu____4093 printer1 emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____4123 =
        let uu____4128 =
          let uu____4129 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____4129]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____4128  in
      uu____4123 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____4155 =
        let uu____4163 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____4163, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4155  in
    let printer1 l =
      let uu____4180 =
        let uu____4182 =
          let uu____4184 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____4184 (FStar_String.concat "; ")  in
        Prims.op_Hat uu____4182 "]"  in
      Prims.op_Hat "[" uu____4180  in
    let rec em l rng shadow_l norm =
      lazy_embed printer1 emb_t_list_a rng t_list_a l
        (fun uu____4228  ->
           let t =
             let uu____4230 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____4230  in
           match l with
           | [] ->
               let uu____4231 =
                 let uu____4236 =
                   let uu____4237 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____4237
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____4236 [t]  in
               uu____4231 FStar_Pervasives_Native.None rng
           | hd::tl ->
               let cons =
                 let uu____4259 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4259
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____4279 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____4279  in
                 let uu____4280 =
                   let uu____4285 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____4286 =
                     let uu____4287 =
                       let uu____4296 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____4296  in
                     let uu____4297 =
                       let uu____4308 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____4308]  in
                     uu____4287 :: uu____4297  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4285 uu____4286  in
                 uu____4280 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____4345 =
                 let uu____4350 =
                   let uu____4351 =
                     let uu____4362 =
                       let uu____4371 =
                         let uu____4372 = embed ea hd  in
                         uu____4372 rng shadow_hd norm  in
                       FStar_Syntax_Syntax.as_arg uu____4371  in
                     let uu____4379 =
                       let uu____4390 =
                         let uu____4399 = em tl rng shadow_tl norm  in
                         FStar_Syntax_Syntax.as_arg uu____4399  in
                       [uu____4390]  in
                     uu____4362 :: uu____4379  in
                   t :: uu____4351  in
                 FStar_Syntax_Syntax.mk_Tm_app cons uu____4350  in
               uu____4345 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer1 emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____4471 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____4471 with
           | (hd,args) ->
               let uu____4512 =
                 let uu____4525 =
                   let uu____4526 = FStar_Syntax_Util.un_uinst hd  in
                   uu____4526.FStar_Syntax_Syntax.n  in
                 (uu____4525, args)  in
               (match uu____4512 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4542) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____4562,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____4563))::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                   (tl,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4605 =
                      let uu____4608 = unembed ea hd1  in uu____4608 w norm
                       in
                    FStar_Util.bind_opt uu____4605
                      (fun hd2  ->
                         let uu____4620 = un tl w norm  in
                         FStar_Util.bind_opt uu____4620
                           (fun tl1  ->
                              FStar_Pervasives_Native.Some (hd2 :: tl1)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd1,FStar_Pervasives_Native.None )::(tl,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4668 =
                      let uu____4671 = unembed ea hd1  in uu____4671 w norm
                       in
                    FStar_Util.bind_opt uu____4668
                      (fun hd2  ->
                         let uu____4683 = un tl w norm  in
                         FStar_Util.bind_opt uu____4683
                           (fun tl1  ->
                              FStar_Pervasives_Native.Some (hd2 :: tl1)))
                | uu____4698 ->
                    (if w
                     then
                       (let uu____4713 =
                          let uu____4719 =
                            let uu____4721 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____4721
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____4719)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____4713)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____4729 =
      let uu____4730 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____4730  in
    mk_emb_full em un uu____4729 printer1 emb_t_list_a
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
type norm_step =
  | Simpl 
  | Weak 
  | HNF 
  | Primops 
  | Delta 
  | Zeta 
  | ZetaFull 
  | Iota 
  | Reify 
  | UnfoldOnly of Prims.string Prims.list 
  | UnfoldFully of Prims.string Prims.list 
  | UnfoldAttr of Prims.string Prims.list 
  | NBE 
let (uu___is_Simpl : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____4773 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____4784 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____4795 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____4806 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____4817 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____4828 -> false
  
let (uu___is_ZetaFull : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ZetaFull  -> true | uu____4839 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____4850 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____4861 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____4876 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____4907 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____4938 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____4965 -> false 
let (steps_Simpl : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_simpl 
let (steps_Weak : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_weak 
let (steps_HNF : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_hnf 
let (steps_Primops : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_primops 
let (steps_Delta : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_delta 
let (steps_Zeta : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_zeta 
let (steps_ZetaFull : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_zeta_full 
let (steps_Iota : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_iota 
let (steps_Reify : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_reify 
let (steps_UnfoldOnly : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_unfoldonly 
let (steps_UnfoldFully : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_unfoldonly 
let (steps_UnfoldAttr : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_unfoldattr 
let (steps_NBE : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_nbe 
let (e_norm_step : norm_step embedding) =
  let t_norm_step =
    let uu____4984 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____4984  in
  let emb_t_norm_step =
    let uu____4987 =
      let uu____4995 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____4995, [])  in
    FStar_Syntax_Syntax.ET_app uu____4987  in
  let printer1 uu____5007 = "norm_step"  in
  let em n rng _topt norm =
    lazy_embed printer1 emb_t_norm_step rng t_norm_step n
      (fun uu____5033  ->
         match n with
         | Simpl  -> steps_Simpl
         | Weak  -> steps_Weak
         | HNF  -> steps_HNF
         | Primops  -> steps_Primops
         | Delta  -> steps_Delta
         | Zeta  -> steps_Zeta
         | ZetaFull  -> steps_ZetaFull
         | Iota  -> steps_Iota
         | NBE  -> steps_NBE
         | Reify  -> steps_Reify
         | UnfoldOnly l ->
             let uu____5038 =
               let uu____5043 =
                 let uu____5044 =
                   let uu____5053 =
                     let uu____5054 =
                       let uu____5061 = e_list e_string  in
                       embed uu____5061 l  in
                     uu____5054 rng FStar_Pervasives_Native.None norm  in
                   FStar_Syntax_Syntax.as_arg uu____5053  in
                 [uu____5044]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____5043  in
             uu____5038 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____5093 =
               let uu____5098 =
                 let uu____5099 =
                   let uu____5108 =
                     let uu____5109 =
                       let uu____5116 = e_list e_string  in
                       embed uu____5116 l  in
                     uu____5109 rng FStar_Pervasives_Native.None norm  in
                   FStar_Syntax_Syntax.as_arg uu____5108  in
                 [uu____5099]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____5098  in
             uu____5093 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____5148 =
               let uu____5153 =
                 let uu____5154 =
                   let uu____5163 =
                     let uu____5164 =
                       let uu____5171 = e_list e_string  in
                       embed uu____5171 l  in
                     uu____5164 rng FStar_Pervasives_Native.None norm  in
                   FStar_Syntax_Syntax.as_arg uu____5163  in
                 [uu____5154]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____5153  in
             uu____5148 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer1 emb_t_norm_step t t_norm_step
      (fun t1  ->
         let uu____5231 = FStar_Syntax_Util.head_and_args t1  in
         match uu____5231 with
         | (hd,args) ->
             let uu____5276 =
               let uu____5291 =
                 let uu____5292 = FStar_Syntax_Util.un_uinst hd  in
                 uu____5292.FStar_Syntax_Syntax.n  in
               (uu____5291, args)  in
             (match uu____5276 with
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
                    FStar_Parser_Const.steps_zeta_full
                  -> FStar_Pervasives_Native.Some ZetaFull
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5499)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____5534 =
                    let uu____5540 =
                      let uu____5550 = e_list e_string  in
                      unembed uu____5550 l  in
                    uu____5540 w norm  in
                  FStar_Util.bind_opt uu____5534
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun uu____5570  ->
                            FStar_Pervasives_Native.Some uu____5570)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5573)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____5608 =
                    let uu____5614 =
                      let uu____5624 = e_list e_string  in
                      unembed uu____5624 l  in
                    uu____5614 w norm  in
                  FStar_Util.bind_opt uu____5608
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun uu____5644  ->
                            FStar_Pervasives_Native.Some uu____5644)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5647)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____5682 =
                    let uu____5688 =
                      let uu____5698 = e_list e_string  in
                      unembed uu____5698 l  in
                    uu____5688 w norm  in
                  FStar_Util.bind_opt uu____5682
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun uu____5718  ->
                            FStar_Pervasives_Native.Some uu____5718)
                         (UnfoldAttr ss))
              | uu____5719 ->
                  (if w
                   then
                     (let uu____5736 =
                        let uu____5742 =
                          let uu____5744 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____5744
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____5742)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____5736)
                   else ();
                   FStar_Pervasives_Native.None)))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_norm_step printer1 emb_t_norm_step 
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
    | uu____5804 ->
        (if w
         then
           (let uu____5807 =
              let uu____5813 =
                let uu____5815 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____5815  in
              (FStar_Errors.Warning_NotEmbedded, uu____5813)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____5807)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____5821 =
    let uu____5822 =
      let uu____5830 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____5830, [])  in
    FStar_Syntax_Syntax.ET_app uu____5822  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____5821
  
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
        let uu____5901 =
          let uu____5908 =
            let uu____5909 =
              let uu____5924 =
                let uu____5933 =
                  let uu____5940 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____5940, FStar_Pervasives_Native.None)  in
                [uu____5933]  in
              let uu____5955 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____5924, uu____5955)  in
            FStar_Syntax_Syntax.Tm_arrow uu____5909  in
          FStar_Syntax_Syntax.mk uu____5908  in
        uu____5901 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer1 f = "<fun>"  in
      let em f rng shadow_f norm =
        lazy_embed (fun uu____6027  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____6033  ->
             let uu____6034 = force_shadow shadow_f  in
             match uu____6034 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____6039 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____6039
                   then
                     let uu____6063 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____6065 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____6063 uu____6065
                   else ());
                  (let res = norm (FStar_Util.Inr repr_f)  in
                   (let uu____6072 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____6072
                    then
                      let uu____6096 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____6098 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____6100 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____6096 uu____6098 uu____6100
                    else ());
                   res)))
         in
      let un f w norm =
        lazy_unembed printer1 emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a1 =
               (let uu____6159 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____6159
                then
                  let uu____6183 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____6185 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____6183
                    uu____6185
                else ());
               (let a_tm =
                  let uu____6191 = embed ea a1  in
                  uu____6191 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm
                   in
                let b_tm =
                  let uu____6201 =
                    let uu____6206 =
                      let uu____6207 =
                        let uu____6212 =
                          let uu____6213 = FStar_Syntax_Syntax.as_arg a_tm
                             in
                          [uu____6213]  in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____6212  in
                      uu____6207 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____6206  in
                  norm uu____6201  in
                let uu____6238 =
                  let uu____6241 = unembed eb b_tm  in uu____6241 w norm  in
                match uu____6238 with
                | FStar_Pervasives_Native.None  ->
                    FStar_Exn.raise Unembedding_failure
                | FStar_Pervasives_Native.Some b1 -> b1)
                in
             FStar_Pervasives_Native.Some f_wrapped)
         in
      mk_emb_full em un t_arrow printer1 emb_t_arr_a_b
  
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
          fun fv_lid  ->
            fun norm  ->
              let rng = FStar_Ident.range_of_lid fv_lid  in
              let f_wrapped args =
                let uu____6335 = FStar_List.splitAt n_tvars args  in
                match uu____6335 with
                | (_tvar_args,rest_args) ->
                    let uu____6412 = FStar_List.hd rest_args  in
                    (match uu____6412 with
                     | (x,uu____6432) ->
                         let shadow_app =
                           let uu____6446 =
                             FStar_Thunk.mk
                               (fun uu____6453  ->
                                  let uu____6454 =
                                    let uu____6459 =
                                      norm (FStar_Util.Inl fv_lid)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6459
                                      args
                                     in
                                  uu____6454 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____6446  in
                         let uu____6462 =
                           let uu____6465 =
                             let uu____6468 = unembed ea x  in
                             uu____6468 true norm  in
                           FStar_Util.map_opt uu____6465
                             (fun x1  ->
                                let uu____6479 =
                                  let uu____6486 = f x1  in
                                  embed eb uu____6486  in
                                uu____6479 rng shadow_app norm)
                            in
                         (match uu____6462 with
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
            fun fv_lid  ->
              fun norm  ->
                let rng = FStar_Ident.range_of_lid fv_lid  in
                let f_wrapped args =
                  let uu____6589 = FStar_List.splitAt n_tvars args  in
                  match uu____6589 with
                  | (_tvar_args,rest_args) ->
                      let uu____6652 = FStar_List.hd rest_args  in
                      (match uu____6652 with
                       | (x,uu____6668) ->
                           let uu____6673 =
                             let uu____6680 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____6680  in
                           (match uu____6673 with
                            | (y,uu____6704) ->
                                let shadow_app =
                                  let uu____6714 =
                                    FStar_Thunk.mk
                                      (fun uu____6721  ->
                                         let uu____6722 =
                                           let uu____6727 =
                                             norm (FStar_Util.Inl fv_lid)  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6727 args
                                            in
                                         uu____6722
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____6714  in
                                let uu____6730 =
                                  let uu____6733 =
                                    let uu____6736 = unembed ea x  in
                                    uu____6736 true norm  in
                                  FStar_Util.bind_opt uu____6733
                                    (fun x1  ->
                                       let uu____6747 =
                                         let uu____6750 = unembed eb y  in
                                         uu____6750 true norm  in
                                       FStar_Util.bind_opt uu____6747
                                         (fun y1  ->
                                            let uu____6761 =
                                              let uu____6762 =
                                                let uu____6769 = f x1 y1  in
                                                embed ec uu____6769  in
                                              uu____6762 rng shadow_app norm
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____6761))
                                   in
                                (match uu____6730 with
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
              fun fv_lid  ->
                fun norm  ->
                  let rng = FStar_Ident.range_of_lid fv_lid  in
                  let f_wrapped args =
                    let uu____6891 = FStar_List.splitAt n_tvars args  in
                    match uu____6891 with
                    | (_tvar_args,rest_args) ->
                        let uu____6954 = FStar_List.hd rest_args  in
                        (match uu____6954 with
                         | (x,uu____6970) ->
                             let uu____6975 =
                               let uu____6982 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____6982  in
                             (match uu____6975 with
                              | (y,uu____7006) ->
                                  let uu____7011 =
                                    let uu____7018 =
                                      let uu____7027 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____7027  in
                                    FStar_List.hd uu____7018  in
                                  (match uu____7011 with
                                   | (z,uu____7057) ->
                                       let shadow_app =
                                         let uu____7067 =
                                           FStar_Thunk.mk
                                             (fun uu____7074  ->
                                                let uu____7075 =
                                                  let uu____7080 =
                                                    norm
                                                      (FStar_Util.Inl fv_lid)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____7080 args
                                                   in
                                                uu____7075
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____7067
                                          in
                                       let uu____7083 =
                                         let uu____7086 =
                                           let uu____7089 = unembed ea x  in
                                           uu____7089 true norm  in
                                         FStar_Util.bind_opt uu____7086
                                           (fun x1  ->
                                              let uu____7100 =
                                                let uu____7103 = unembed eb y
                                                   in
                                                uu____7103 true norm  in
                                              FStar_Util.bind_opt uu____7100
                                                (fun y1  ->
                                                   let uu____7114 =
                                                     let uu____7117 =
                                                       unembed ec z  in
                                                     uu____7117 true norm  in
                                                   FStar_Util.bind_opt
                                                     uu____7114
                                                     (fun z1  ->
                                                        let uu____7128 =
                                                          let uu____7129 =
                                                            let uu____7136 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____7136
                                                             in
                                                          uu____7129 rng
                                                            shadow_app norm
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____7128)))
                                          in
                                       (match uu____7083 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____7166 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____7166 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____7195 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____7195 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  