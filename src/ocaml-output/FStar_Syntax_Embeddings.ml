open Prims
type 'a embedding =
  {
  em: FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term ;
  un:
    Prims.bool ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
    ;
  typ: FStar_Syntax_Syntax.typ }[@@deriving show]
let __proj__Mkembedding__item__em :
  'a . 'a embedding -> FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__em
  
let __proj__Mkembedding__item__un :
  'a .
    'a embedding ->
      Prims.bool ->
        FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
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
  
let embed :
  'a . 'a embedding -> FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term =
  fun e  -> fun r  -> fun x  -> e.em r x 
let unembed' :
  'a .
    Prims.bool ->
      'a embedding ->
        FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  = fun b  -> fun e  -> fun t  -> e.un b t 
let unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  = fun e  -> fun t  -> e.un true t 
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  = fun e  -> fun t  -> e.un false t 
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
type 'a raw_embedder = FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
[@@deriving show]
type 'a raw_unembedder' =
  Prims.bool -> FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
[@@deriving show]
type 'a raw_unembedder =
  FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option[@@deriving
                                                                 show]
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder' -> FStar_Syntax_Syntax.typ -> 'a embedding
  = fun em  -> fun un  -> fun typ  -> { em; un; typ } 
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em r t = t  in
  let un b t = FStar_Pervasives_Native.Some t  in
  let typ = FStar_Syntax_Syntax.t_term  in mk_emb em un typ 
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  -> { em = (e_any.em); un = (e_any.un); typ } 
let (e_unit : unit embedding) =
  let em rng u =
    let uu___77_418 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___77_418.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___77_418.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____439 ->
        (if w
         then
           (let uu____441 =
              let uu____446 =
                let uu____447 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____447  in
              (FStar_Errors.Warning_NotEmbedded, uu____446)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____441)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_unit 
let (e_bool : Prims.bool embedding) =
  let em rng b =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___78_468 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___78_468.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___78_468.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____490 ->
        (if w
         then
           (let uu____492 =
              let uu____497 =
                let uu____498 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____498  in
              (FStar_Errors.Warning_NotEmbedded, uu____497)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____492)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_bool 
let (e_char : FStar_Char.char embedding) =
  let em rng c =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___79_517 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___79_517.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___79_517.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____541 ->
        (if w
         then
           (let uu____543 =
              let uu____548 =
                let uu____549 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____549  in
              (FStar_Errors.Warning_NotEmbedded, uu____548)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____543)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_char 
let (e_int : FStar_BigInt.t embedding) =
  let em rng i =
    let t =
      let uu____567 = FStar_BigInt.string_of_big_int i  in
      FStar_Syntax_Util.exp_int uu____567  in
    let uu___80_568 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___80_568.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___80_568.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____588))
        ->
        let uu____601 = FStar_BigInt.big_int_of_string s  in
        FStar_Pervasives_Native.Some uu____601
    | uu____602 ->
        (if w
         then
           (let uu____604 =
              let uu____609 =
                let uu____610 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded int: %s" uu____610  in
              (FStar_Errors.Warning_NotEmbedded, uu____609)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____604)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_int 
let (e_string : Prims.string embedding) =
  let em rng s =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____644)) -> FStar_Pervasives_Native.Some s
    | uu____645 ->
        (if w
         then
           (let uu____647 =
              let uu____652 =
                let uu____653 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____653  in
              (FStar_Errors.Warning_NotEmbedded, uu____652)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____647)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_string 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let em rng o =
      match o with
      | FStar_Pervasives_Native.None  ->
          let uu____688 =
            let uu____693 =
              let uu____694 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.none_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____694
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____695 =
              let uu____696 =
                let uu____703 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____703  in
              [uu____696]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____693 uu____695  in
          uu____688 FStar_Pervasives_Native.None rng
      | FStar_Pervasives_Native.Some a ->
          let uu____719 =
            let uu____724 =
              let uu____725 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.some_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____725
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____726 =
              let uu____727 =
                let uu____734 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____734  in
              let uu____735 =
                let uu____744 =
                  let uu____751 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____751  in
                [uu____744]  in
              uu____727 :: uu____735  in
            FStar_Syntax_Syntax.mk_Tm_app uu____724 uu____726  in
          uu____719 FStar_Pervasives_Native.None rng
       in
    let un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____792 = FStar_Syntax_Util.head_and_args t  in
      match uu____792 with
      | (hd1,args) ->
          let uu____833 =
            let uu____846 =
              let uu____847 = FStar_Syntax_Util.un_uinst hd1  in
              uu____847.FStar_Syntax_Syntax.n  in
            (uu____846, args)  in
          (match uu____833 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____863) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____883::(a,uu____885)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
               ->
               let uu____922 = unembed' w ea a  in
               FStar_Util.bind_opt uu____922
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____931 ->
               (if w
                then
                  (let uu____945 =
                     let uu____950 =
                       let uu____951 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded option: %s"
                         uu____951
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____950)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____945)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____955 =
      let uu____956 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____956  in
    mk_emb em un uu____955
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em rng x =
        let uu____1012 =
          let uu____1017 =
            let uu____1018 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.lid_Mktuple2
               in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1018
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
             in
          let uu____1019 =
            let uu____1020 =
              let uu____1027 = type_of ea  in
              FStar_Syntax_Syntax.iarg uu____1027  in
            let uu____1028 =
              let uu____1037 =
                let uu____1044 = type_of eb  in
                FStar_Syntax_Syntax.iarg uu____1044  in
              let uu____1045 =
                let uu____1054 =
                  let uu____1061 =
                    embed ea rng (FStar_Pervasives_Native.fst x)  in
                  FStar_Syntax_Syntax.as_arg uu____1061  in
                let uu____1062 =
                  let uu____1071 =
                    let uu____1078 =
                      embed eb rng (FStar_Pervasives_Native.snd x)  in
                    FStar_Syntax_Syntax.as_arg uu____1078  in
                  [uu____1071]  in
                uu____1054 :: uu____1062  in
              uu____1037 :: uu____1045  in
            uu____1020 :: uu____1028  in
          FStar_Syntax_Syntax.mk_Tm_app uu____1017 uu____1019  in
        uu____1012 FStar_Pervasives_Native.None rng  in
      let un w t0 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        let uu____1135 = FStar_Syntax_Util.head_and_args t  in
        match uu____1135 with
        | (hd1,args) ->
            let uu____1178 =
              let uu____1189 =
                let uu____1190 = FStar_Syntax_Util.un_uinst hd1  in
                uu____1190.FStar_Syntax_Syntax.n  in
              (uu____1189, args)  in
            (match uu____1178 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1206::uu____1207::(a,uu____1209)::(b,uu____1211)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____1246 = unembed' w ea a  in
                 FStar_Util.bind_opt uu____1246
                   (fun a1  ->
                      let uu____1256 = unembed' w eb b  in
                      FStar_Util.bind_opt uu____1256
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____1269 ->
                 (if w
                  then
                    (let uu____1281 =
                       let uu____1286 =
                         let uu____1287 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1 "Not an embedded pair: %s"
                           uu____1287
                          in
                       (FStar_Errors.Warning_NotEmbedded, uu____1286)  in
                     FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                       uu____1281)
                  else ();
                  FStar_Pervasives_Native.None))
         in
      let uu____1293 =
        let uu____1294 = type_of ea  in
        let uu____1295 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____1294 uu____1295  in
      mk_emb em un uu____1293
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em rng l =
      let t =
        let uu____1334 = type_of ea  in FStar_Syntax_Syntax.iarg uu____1334
         in
      let nil =
        let uu____1338 =
          let uu____1343 =
            let uu____1344 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid  in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1344
              [FStar_Syntax_Syntax.U_zero]
             in
          FStar_Syntax_Syntax.mk_Tm_app uu____1343 [t]  in
        uu____1338 FStar_Pervasives_Native.None rng  in
      let cons1 =
        let uu____1360 =
          FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.cons_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____1360
          [FStar_Syntax_Syntax.U_zero]
         in
      FStar_List.fold_right
        (fun hd1  ->
           fun tail1  ->
             let uu____1368 =
               let uu____1373 =
                 let uu____1374 =
                   let uu____1383 =
                     let uu____1390 = embed ea rng hd1  in
                     FStar_Syntax_Syntax.as_arg uu____1390  in
                   let uu____1391 =
                     let uu____1400 = FStar_Syntax_Syntax.as_arg tail1  in
                     [uu____1400]  in
                   uu____1383 :: uu____1391  in
                 t :: uu____1374  in
               FStar_Syntax_Syntax.mk_Tm_app cons1 uu____1373  in
             uu____1368 FStar_Pervasives_Native.None rng) l nil
       in
    let rec un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____1453 = FStar_Syntax_Util.head_and_args t  in
      match uu____1453 with
      | (hd1,args) ->
          let uu____1494 =
            let uu____1507 =
              let uu____1508 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1508.FStar_Syntax_Syntax.n  in
            (uu____1507, args)  in
          (match uu____1494 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1524) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(uu____1544,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit uu____1545))::(hd2,FStar_Pervasives_Native.None
                                                               )::(tl1,FStar_Pervasives_Native.None
                                                                   )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____1586 = unembed' w ea hd2  in
               FStar_Util.bind_opt uu____1586
                 (fun hd3  ->
                    let uu____1594 = un w tl1  in
                    FStar_Util.bind_opt uu____1594
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                       )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____1642 = unembed' w ea hd2  in
               FStar_Util.bind_opt uu____1642
                 (fun hd3  ->
                    let uu____1650 = un w tl1  in
                    FStar_Util.bind_opt uu____1650
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
           | uu____1665 ->
               (if w
                then
                  (let uu____1679 =
                     let uu____1684 =
                       let uu____1685 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded list: %s"
                         uu____1685
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1684)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____1679)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____1689 =
      let uu____1690 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____1690  in
    mk_emb em un uu____1689
  
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
  | UnfoldAttr of FStar_Syntax_Syntax.attribute [@@deriving show]
let (uu___is_Simpl : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____1721 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1727 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____1733 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1739 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1745 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1751 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1757 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____1766 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____1788 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____1808 -> false
  
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
  let em rng n1 =
    match n1 with
    | Simpl  -> steps_Simpl
    | Weak  -> steps_Weak
    | HNF  -> steps_HNF
    | Primops  -> steps_Primops
    | Delta  -> steps_Delta
    | Zeta  -> steps_Zeta
    | Iota  -> steps_Iota
    | UnfoldOnly l ->
        let uu____1832 =
          let uu____1837 =
            let uu____1838 =
              let uu____1845 =
                let uu____1846 = e_list e_string  in embed uu____1846 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1845  in
            [uu____1838]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____1837  in
        uu____1832 FStar_Pervasives_Native.None rng
    | UnfoldFully l ->
        let uu____1870 =
          let uu____1875 =
            let uu____1876 =
              let uu____1883 =
                let uu____1884 = e_list e_string  in embed uu____1884 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1883  in
            [uu____1876]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____1875  in
        uu____1870 FStar_Pervasives_Native.None rng
    | UnfoldAttr a ->
        let uu____1906 =
          let uu____1911 =
            let uu____1912 = FStar_Syntax_Syntax.as_arg a  in [uu____1912]
             in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____1911  in
        uu____1906 FStar_Pervasives_Native.None rng
     in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    let uu____1949 = FStar_Syntax_Util.head_and_args t  in
    match uu____1949 with
    | (hd1,args) ->
        let uu____1988 =
          let uu____2001 =
            let uu____2002 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2002.FStar_Syntax_Syntax.n  in
          (uu____2001, args)  in
        (match uu____1988 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl
             -> FStar_Pervasives_Native.Some Simpl
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak
             -> FStar_Pervasives_Native.Some Weak
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
             FStar_Pervasives_Native.Some HNF
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_primops
             -> FStar_Pervasives_Native.Some Primops
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta
             -> FStar_Pervasives_Native.Some Delta
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta
             -> FStar_Pervasives_Native.Some Zeta
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota
             -> FStar_Pervasives_Native.Some Iota
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____2122)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldonly
             ->
             let uu____2147 =
               let uu____2152 = e_list e_string  in unembed' w uu____2152 l
                in
             FStar_Util.bind_opt uu____2147
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (UnfoldOnly ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____2169)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldfully
             ->
             let uu____2194 =
               let uu____2199 = e_list e_string  in unembed' w uu____2199 l
                in
             FStar_Util.bind_opt uu____2194
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (UnfoldFully ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2215::(a,uu____2217)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldattr
             -> FStar_Pervasives_Native.Some (UnfoldAttr a)
         | uu____2254 ->
             (if w
              then
                (let uu____2268 =
                   let uu____2273 =
                     let uu____2274 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded norm_step: %s"
                       uu____2274
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2273)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2268)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb em un FStar_Syntax_Syntax.t_norm_step 
let (e_range : FStar_Range.range embedding) =
  let em rng r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None rng
     in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r) ->
        FStar_Pervasives_Native.Some r
    | uu____2308 ->
        (if w
         then
           (let uu____2310 =
              let uu____2315 =
                let uu____2316 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____2316  in
              (FStar_Errors.Warning_NotEmbedded, uu____2315)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2310)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_range 
let embed_arrow_1 :
  'a 'b .
    'a embedding ->
      'b embedding ->
        ('a -> 'b) ->
          FStar_Syntax_Syntax.args ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun f  ->
        fun args  ->
          let ua = unembed ea  in
          let eb1 = embed eb  in
          match args with
          | (x,uu____2386)::[] ->
              let uu____2403 = ua x  in
              FStar_Util.bind_opt uu____2403
                (fun a  ->
                   let uu____2409 =
                     let uu____2410 =
                       let uu____2411 =
                         let uu____2412 = ua x  in FStar_Util.must uu____2412
                          in
                       f uu____2411  in
                     eb1 FStar_Range.dummyRange uu____2410  in
                   FStar_Pervasives_Native.Some uu____2409)
          | uu____2415 -> FStar_Pervasives_Native.None
  
let embed_arrow_2 :
  'a 'b 'c .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          ('a -> 'b -> 'c) ->
            FStar_Syntax_Syntax.args ->
              FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun f  ->
          fun args  ->
            let ua = unembed ea  in
            let ub = unembed eb  in
            let ec1 = embed ec  in
            match args with
            | (x,uu____2510)::(y,uu____2512)::[] ->
                let uu____2539 = ua x  in
                FStar_Util.bind_opt uu____2539
                  (fun a  ->
                     let uu____2545 = ub y  in
                     FStar_Util.bind_opt uu____2545
                       (fun b  ->
                          let uu____2551 =
                            let uu____2552 = f a b  in
                            ec1 FStar_Range.dummyRange uu____2552  in
                          FStar_Pervasives_Native.Some uu____2551))
            | uu____2553 -> FStar_Pervasives_Native.None
  
let embed_arrow_3 :
  'a 'b 'c 'd .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          'd embedding ->
            ('a -> 'b -> 'c -> 'd) ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun f  ->
            fun args  ->
              let ua = unembed ea  in
              let ub = unembed eb  in
              let uc = unembed ec  in
              let ed1 = embed ed  in
              match args with
              | (x,uu____2674)::(y,uu____2676)::(z,uu____2678)::[] ->
                  let uu____2715 = ua x  in
                  FStar_Util.bind_opt uu____2715
                    (fun a  ->
                       let uu____2721 = ub y  in
                       FStar_Util.bind_opt uu____2721
                         (fun b  ->
                            let uu____2727 = uc z  in
                            FStar_Util.bind_opt uu____2727
                              (fun c  ->
                                 let uu____2733 =
                                   let uu____2734 = f a b c  in
                                   ed1 FStar_Range.dummyRange uu____2734  in
                                 FStar_Pervasives_Native.Some uu____2733)))
              | uu____2735 -> FStar_Pervasives_Native.None
  