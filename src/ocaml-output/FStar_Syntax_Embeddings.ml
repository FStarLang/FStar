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
    'a embedding ->
      Prims.bool ->
        FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  = fun e  -> fun b  -> fun t  -> e.un b t 
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
let e_any : FStar_Syntax_Syntax.term embedding =
  let em r t = t  in
  let un b t = FStar_Pervasives_Native.Some t  in
  let typ = FStar_Syntax_Syntax.t_term  in mk_emb em un typ 
let mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding =
  fun typ  -> { em = (e_any.em); un = (e_any.un); typ } 
let e_unit : unit embedding =
  let em rng u =
    let uu___50_418 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___50_418.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___50_418.FStar_Syntax_Syntax.vars)
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
let e_bool : Prims.bool embedding =
  let em rng b =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___51_468 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___51_468.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___51_468.FStar_Syntax_Syntax.vars)
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
let e_char : FStar_Char.char embedding =
  let em rng c =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___52_517 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___52_517.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___52_517.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____540 ->
        (if w
         then
           (let uu____542 =
              let uu____547 =
                let uu____548 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____548  in
              (FStar_Errors.Warning_NotEmbedded, uu____547)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____542)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_char 
let e_int : FStar_BigInt.t embedding =
  let em rng i =
    let t =
      let uu____566 = FStar_BigInt.string_of_big_int i  in
      FStar_Syntax_Util.exp_int uu____566  in
    let uu___53_567 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___53_567.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___53_567.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____587))
        ->
        let uu____600 = FStar_BigInt.big_int_of_string s  in
        FStar_Pervasives_Native.Some uu____600
    | uu____601 ->
        (if w
         then
           (let uu____603 =
              let uu____608 =
                let uu____609 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded int: %s" uu____609  in
              (FStar_Errors.Warning_NotEmbedded, uu____608)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____603)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_int 
let e_string : Prims.string embedding =
  let em rng s =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____643)) -> FStar_Pervasives_Native.Some s
    | uu____644 ->
        (if w
         then
           (let uu____646 =
              let uu____651 =
                let uu____652 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____652  in
              (FStar_Errors.Warning_NotEmbedded, uu____651)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____646)
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
          let uu____687 =
            let uu____692 =
              let uu____693 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.none_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____693
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____694 =
              let uu____695 =
                let uu____696 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____696  in
              [uu____695]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____692 uu____694  in
          uu____687 FStar_Pervasives_Native.None rng
      | FStar_Pervasives_Native.Some a ->
          let uu____700 =
            let uu____705 =
              let uu____706 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.some_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____706
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____707 =
              let uu____708 =
                let uu____709 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____709  in
              let uu____710 =
                let uu____713 =
                  let uu____714 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____714  in
                [uu____713]  in
              uu____708 :: uu____710  in
            FStar_Syntax_Syntax.mk_Tm_app uu____705 uu____707  in
          uu____700 FStar_Pervasives_Native.None rng
       in
    let un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____737 = FStar_Syntax_Util.head_and_args t  in
      match uu____737 with
      | (hd1,args) ->
          let uu____778 =
            let uu____791 =
              let uu____792 = FStar_Syntax_Util.un_uinst hd1  in
              uu____792.FStar_Syntax_Syntax.n  in
            (uu____791, args)  in
          (match uu____778 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____808) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____828::(a,uu____830)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
               ->
               let uu____867 = unembed ea a  in
               FStar_Util.bind_opt uu____867
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____876 ->
               (if w
                then
                  (let uu____890 =
                     let uu____895 =
                       let uu____896 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded option: %s"
                         uu____896
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____895)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____890)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____900 =
      let uu____901 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____901  in
    mk_emb em un uu____900
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em rng x =
        let uu____957 =
          let uu____962 =
            let uu____963 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.lid_Mktuple2
               in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____963
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
             in
          let uu____964 =
            let uu____965 =
              let uu____966 = type_of ea  in
              FStar_Syntax_Syntax.iarg uu____966  in
            let uu____967 =
              let uu____970 =
                let uu____971 = type_of eb  in
                FStar_Syntax_Syntax.iarg uu____971  in
              let uu____972 =
                let uu____975 =
                  let uu____976 =
                    embed ea rng (FStar_Pervasives_Native.fst x)  in
                  FStar_Syntax_Syntax.as_arg uu____976  in
                let uu____977 =
                  let uu____980 =
                    let uu____981 =
                      embed eb rng (FStar_Pervasives_Native.snd x)  in
                    FStar_Syntax_Syntax.as_arg uu____981  in
                  [uu____980]  in
                uu____975 :: uu____977  in
              uu____970 :: uu____972  in
            uu____965 :: uu____967  in
          FStar_Syntax_Syntax.mk_Tm_app uu____962 uu____964  in
        uu____957 FStar_Pervasives_Native.None rng  in
      let un w t0 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        let uu____1008 = FStar_Syntax_Util.head_and_args t  in
        match uu____1008 with
        | (hd1,args) ->
            let uu____1051 =
              let uu____1064 =
                let uu____1065 = FStar_Syntax_Util.un_uinst hd1  in
                uu____1065.FStar_Syntax_Syntax.n  in
              (uu____1064, args)  in
            (match uu____1051 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1083::uu____1084::(a,uu____1086)::(b,uu____1088)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____1147 = unembed ea a  in
                 FStar_Util.bind_opt uu____1147
                   (fun a1  ->
                      let uu____1157 = unembed eb b  in
                      FStar_Util.bind_opt uu____1157
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____1170 ->
                 (if w
                  then
                    (let uu____1184 =
                       let uu____1189 =
                         let uu____1190 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1 "Not an embedded pair: %s"
                           uu____1190
                          in
                       (FStar_Errors.Warning_NotEmbedded, uu____1189)  in
                     FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                       uu____1184)
                  else ();
                  FStar_Pervasives_Native.None))
         in
      let uu____1196 =
        let uu____1197 = type_of ea  in
        let uu____1198 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____1197 uu____1198  in
      mk_emb em un uu____1196
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em rng l =
      let t =
        let uu____1237 = type_of ea  in FStar_Syntax_Syntax.iarg uu____1237
         in
      let nil =
        let uu____1241 =
          let uu____1246 =
            let uu____1247 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid  in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1247
              [FStar_Syntax_Syntax.U_zero]
             in
          FStar_Syntax_Syntax.mk_Tm_app uu____1246 [t]  in
        uu____1241 FStar_Pervasives_Native.None rng  in
      let cons1 =
        let uu____1251 =
          FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.cons_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____1251
          [FStar_Syntax_Syntax.U_zero]
         in
      FStar_List.fold_right
        (fun hd1  ->
           fun tail1  ->
             let uu____1259 =
               let uu____1264 =
                 let uu____1265 =
                   let uu____1268 =
                     let uu____1269 = embed ea rng hd1  in
                     FStar_Syntax_Syntax.as_arg uu____1269  in
                   let uu____1270 =
                     let uu____1273 = FStar_Syntax_Syntax.as_arg tail1  in
                     [uu____1273]  in
                   uu____1268 :: uu____1270  in
                 t :: uu____1265  in
               FStar_Syntax_Syntax.mk_Tm_app cons1 uu____1264  in
             uu____1259 FStar_Pervasives_Native.None rng) l nil
       in
    let rec un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____1296 = FStar_Syntax_Util.head_and_args t  in
      match uu____1296 with
      | (hd1,args) ->
          let uu____1337 =
            let uu____1350 =
              let uu____1351 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1351.FStar_Syntax_Syntax.n  in
            (uu____1350, args)  in
          (match uu____1337 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1367) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(uu____1387,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit uu____1388))::(hd2,FStar_Pervasives_Native.None
                                                               )::(tl1,FStar_Pervasives_Native.None
                                                                   )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____1451 = unembed ea hd2  in
               FStar_Util.bind_opt uu____1451
                 (fun hd3  ->
                    let uu____1459 = un w tl1  in
                    FStar_Util.bind_opt uu____1459
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                       )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____1523 = unembed ea hd2  in
               FStar_Util.bind_opt uu____1523
                 (fun hd3  ->
                    let uu____1531 = un w tl1  in
                    FStar_Util.bind_opt uu____1531
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
           | uu____1546 ->
               (if w
                then
                  (let uu____1560 =
                     let uu____1565 =
                       let uu____1566 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded list: %s"
                         uu____1566
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1565)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____1560)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____1570 =
      let uu____1571 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____1571  in
    mk_emb em un uu____1570
  
let e_string_list : Prims.string Prims.list embedding = e_list e_string 
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
let uu___is_Simpl : norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____1602 -> false
  
let uu___is_Weak : norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1608 -> false
  
let uu___is_HNF : norm_step -> Prims.bool =
  fun projectee  -> match projectee with | HNF  -> true | uu____1614 -> false 
let uu___is_Primops : norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1620 -> false
  
let uu___is_Delta : norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1626 -> false
  
let uu___is_Zeta : norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1632 -> false
  
let uu___is_Iota : norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1638 -> false
  
let uu___is_UnfoldOnly : norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____1647 -> false
  
let __proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let uu___is_UnfoldFully : norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____1669 -> false
  
let __proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let uu___is_UnfoldAttr : norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____1689 -> false
  
let __proj__UnfoldAttr__item___0 : norm_step -> FStar_Syntax_Syntax.attribute
  = fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let steps_Simpl : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_simpl 
let steps_Weak : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_weak 
let steps_HNF : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_hnf 
let steps_Primops : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_primops 
let steps_Delta : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_delta 
let steps_Zeta : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_zeta 
let steps_Iota : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_iota 
let steps_UnfoldOnly : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldonly 
let steps_UnfoldFully : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldonly 
let steps_UnfoldAttr : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldattr 
let e_norm_step : norm_step embedding =
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
        let uu____1713 =
          let uu____1718 =
            let uu____1719 =
              let uu____1720 =
                let uu____1721 = e_list e_string  in embed uu____1721 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1720  in
            [uu____1719]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____1718  in
        uu____1713 FStar_Pervasives_Native.None rng
    | UnfoldFully l ->
        let uu____1733 =
          let uu____1738 =
            let uu____1739 =
              let uu____1740 =
                let uu____1741 = e_list e_string  in embed uu____1741 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1740  in
            [uu____1739]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____1738  in
        uu____1733 FStar_Pervasives_Native.None rng
    | UnfoldAttr a ->
        let uu____1751 =
          let uu____1756 =
            let uu____1757 = FStar_Syntax_Syntax.as_arg a  in [uu____1757]
             in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____1756  in
        uu____1751 FStar_Pervasives_Native.None rng
     in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    let uu____1776 = FStar_Syntax_Util.head_and_args t  in
    match uu____1776 with
    | (hd1,args) ->
        let uu____1815 =
          let uu____1828 =
            let uu____1829 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1829.FStar_Syntax_Syntax.n  in
          (uu____1828, args)  in
        (match uu____1815 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____1949)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldonly
             ->
             let uu____1974 =
               let uu____1979 = e_list e_string  in unembed uu____1979 l  in
             FStar_Util.bind_opt uu____1974
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (UnfoldOnly ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____1996)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldfully
             ->
             let uu____2021 =
               let uu____2026 = e_list e_string  in unembed uu____2026 l  in
             FStar_Util.bind_opt uu____2021
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (UnfoldFully ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2042::(a,uu____2044)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldattr
             -> FStar_Pervasives_Native.Some (UnfoldAttr a)
         | uu____2081 ->
             (if w
              then
                (let uu____2095 =
                   let uu____2100 =
                     let uu____2101 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded norm_step: %s"
                       uu____2101
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2100)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2095)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb em un FStar_Syntax_Syntax.t_norm_step 
let e_range : FStar_Range.range embedding =
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
    | uu____2135 ->
        (if w
         then
           (let uu____2137 =
              let uu____2142 =
                let uu____2143 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____2143  in
              (FStar_Errors.Warning_NotEmbedded, uu____2142)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2137)
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
          | (x,uu____2213)::[] ->
              let uu____2230 = ua x  in
              FStar_Util.bind_opt uu____2230
                (fun a  ->
                   let uu____2236 =
                     let uu____2237 =
                       let uu____2238 =
                         let uu____2239 = ua x  in FStar_Util.must uu____2239
                          in
                       f uu____2238  in
                     eb1 FStar_Range.dummyRange uu____2237  in
                   FStar_Pervasives_Native.Some uu____2236)
          | uu____2242 -> FStar_Pervasives_Native.None
  
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
            | (x,uu____2337)::(y,uu____2339)::[] ->
                let uu____2366 = ua x  in
                FStar_Util.bind_opt uu____2366
                  (fun a  ->
                     let uu____2372 = ub y  in
                     FStar_Util.bind_opt uu____2372
                       (fun b  ->
                          let uu____2378 =
                            let uu____2379 = f a b  in
                            ec1 FStar_Range.dummyRange uu____2379  in
                          FStar_Pervasives_Native.Some uu____2378))
            | uu____2380 -> FStar_Pervasives_Native.None
  
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
              | (x,uu____2501)::(y,uu____2503)::(z,uu____2505)::[] ->
                  let uu____2542 = ua x  in
                  FStar_Util.bind_opt uu____2542
                    (fun a  ->
                       let uu____2548 = ub y  in
                       FStar_Util.bind_opt uu____2548
                         (fun b  ->
                            let uu____2554 = uc z  in
                            FStar_Util.bind_opt uu____2554
                              (fun c  ->
                                 let uu____2560 =
                                   let uu____2561 = f a b c  in
                                   ed1 FStar_Range.dummyRange uu____2561  in
                                 FStar_Pervasives_Native.Some uu____2560)))
              | uu____2562 -> FStar_Pervasives_Native.None
  