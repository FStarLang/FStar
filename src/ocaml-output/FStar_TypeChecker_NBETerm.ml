open Prims
type var = FStar_Syntax_Syntax.bv
type sort = Prims.int
type constant =
  | Unit 
  | Bool of Prims.bool 
  | Int of FStar_BigInt.t 
  | String of (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
  
  | Char of FStar_Char.char 
  | Range of FStar_Range.range 
let (uu___is_Unit : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Unit  -> true | uu____36 -> false 
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____43 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Int _0 -> true | uu____57 -> false 
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____75 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____102 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____119 -> false
  
let (__proj__Range__item___0 : constant -> FStar_Range.range) =
  fun projectee  -> match projectee with | Range _0 -> _0 
type atom =
  | Var of var 
  | Match of
  (t,t -> t,(t -> FStar_Syntax_Syntax.term) ->
              FStar_Syntax_Syntax.branch Prims.list)
  FStar_Pervasives_Native.tuple3 
  | Rec of
  (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
  t Prims.list) FStar_Pervasives_Native.tuple3 
and t =
  | Lam of
  (t Prims.list -> t,(unit ->
                        (t,FStar_Syntax_Syntax.aqual)
                          FStar_Pervasives_Native.tuple2)
                       Prims.list,Prims.int)
  FStar_Pervasives_Native.tuple3 
  | Accu of
  (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
          Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Construct of
  (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
  FStar_Pervasives_Native.tuple3 
  | FV of
  (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
  FStar_Pervasives_Native.tuple3 
  | Constant of constant 
  | Type_t of FStar_Syntax_Syntax.universe 
  | Univ of FStar_Syntax_Syntax.universe 
  | Unknown 
  | Arrow of
  (t Prims.list -> t,(unit ->
                        (t,FStar_Syntax_Syntax.aqual)
                          FStar_Pervasives_Native.tuple2)
                       Prims.list)
  FStar_Pervasives_Native.tuple2 
let (uu___is_Var : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____298 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____329 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t,t -> t,(t -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.branch Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Rec : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____404 -> false
  
let (__proj__Rec__item___0 :
  atom ->
    (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
      t Prims.list) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____468 -> false
  
let (__proj__Lam__item___0 :
  t ->
    (t Prims.list -> t,(unit ->
                          (t,FStar_Syntax_Syntax.aqual)
                            FStar_Pervasives_Native.tuple2)
                         Prims.list,Prims.int)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____552 -> false
  
let (__proj__Accu__item___0 :
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____610 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____680 -> false 
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____736 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____750 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____764 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____777 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____802 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    (t Prims.list -> t,(unit ->
                          (t,FStar_Syntax_Syntax.aqual)
                            FStar_Pervasives_Native.tuple2)
                         Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
type arg = (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
type args =
  (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
type head = t
type annot = t FStar_Pervasives_Native.option
let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____887) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____889 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____889
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam uu____899 -> "Lam"
    | Accu (a,l) ->
        let uu____934 =
          let uu____935 = atom_to_string a  in
          let uu____936 =
            let uu____937 =
              let uu____938 =
                let uu____939 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____939  in
              Prims.strcat uu____938 ")"  in
            Prims.strcat ") (" uu____937  in
          Prims.strcat uu____935 uu____936  in
        Prims.strcat "Accu (" uu____934
    | Construct (fv,us,l) ->
        let uu____971 =
          let uu____972 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____973 =
            let uu____974 =
              let uu____975 =
                let uu____976 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____976  in
              let uu____979 =
                let uu____980 =
                  let uu____981 =
                    let uu____982 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____982  in
                  Prims.strcat uu____981 ")"  in
                Prims.strcat "] (" uu____980  in
              Prims.strcat uu____975 uu____979  in
            Prims.strcat ") [" uu____974  in
          Prims.strcat uu____972 uu____973  in
        Prims.strcat "Construct (" uu____971
    | FV (fv,us,l) ->
        let uu____1014 =
          let uu____1015 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____1016 =
            let uu____1017 =
              let uu____1018 =
                let uu____1019 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____1019  in
              let uu____1022 =
                let uu____1023 =
                  let uu____1024 =
                    let uu____1025 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____1025  in
                  Prims.strcat uu____1024 ")"  in
                Prims.strcat "] (" uu____1023  in
              Prims.strcat uu____1018 uu____1022  in
            Prims.strcat ") [" uu____1017  in
          Prims.strcat uu____1015 uu____1016  in
        Prims.strcat "FV (" uu____1014
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____1040 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____1040
    | Type_t u ->
        let uu____1042 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____1042
    | Arrow uu____1043 -> "Arrow"
    | Unknown  -> "Unknown"

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____1064 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____1064
    | Match (t,uu____1066,uu____1067) ->
        let uu____1090 = t_to_string t  in Prims.strcat "Match " uu____1090
    | Rec (uu____1091,uu____1092,l) ->
        let uu____1102 =
          let uu____1103 =
            let uu____1104 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____1104  in
          Prims.strcat uu____1103 ")"  in
        Prims.strcat "Rec (" uu____1102

let (isAccu : t -> Prims.bool) =
  fun trm  -> match trm with | Accu uu____1112 -> true | uu____1123 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____1129,uu____1130) -> false | uu____1143 -> true
  
let (mkConstruct :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  = fun i  -> fun us  -> fun ts  -> Construct (i, us, ts) 
let (mkFV :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  = fun i  -> fun us  -> fun ts  -> FV (i, us, ts) 
let (mkAccuVar : var -> t) = fun v1  -> Accu ((Var v1), []) 
let (mkAccuMatch :
  t ->
    (t -> t) ->
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)
        -> t)
  = fun s  -> fun cases  -> fun bs  -> Accu ((Match (s, cases, bs)), []) 
let (mkAccuRec :
  FStar_Syntax_Syntax.letbinding ->
    FStar_Syntax_Syntax.letbinding Prims.list -> t Prims.list -> t)
  = fun b  -> fun bs  -> fun env  -> Accu ((Rec (b, bs, env)), []) 
type 'a embedding =
  {
  em: 'a -> t ;
  un: t -> 'a FStar_Pervasives_Native.option ;
  typ: t }
let __proj__Mkembedding__item__em : 'a . 'a embedding -> 'a -> t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__em
  
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> t -> 'a FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__un
  
let __proj__Mkembedding__item__typ : 'a . 'a embedding -> t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__typ
  
let embed : 'a . 'a embedding -> 'a -> t = fun e  -> fun x  -> e.em x 
let unembed : 'a . 'a embedding -> t -> 'a FStar_Pervasives_Native.option =
  fun e  -> fun trm  -> e.un trm 
let type_of : 'a . 'a embedding -> t = fun e  -> e.typ 
let mk_emb :
  'Auu____1487 .
    ('Auu____1487 -> t) ->
      (t -> 'Auu____1487 FStar_Pervasives_Native.option) ->
        t -> 'Auu____1487 embedding
  = fun em  -> fun un  -> fun typ  -> { em; un; typ } 
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____1538 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____1538 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____1558 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkConstruct uu____1558 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  -> Arrow ((fun uu____1594  -> t1), [(fun uu____1605  -> a)])
  
let (e_any : t embedding) =
  let em a = a  in
  let un t = FStar_Pervasives_Native.Some t  in
  let uu____1629 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____1629 
let (e_unit : unit embedding) =
  let em a = Constant Unit  in
  let un t = FStar_Pervasives_Native.Some ()  in
  let uu____1650 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  mk_emb em un uu____1650 
let (e_bool : Prims.bool embedding) =
  let em a = Constant (Bool a)  in
  let un t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____1674 -> FStar_Pervasives_Native.None  in
  let uu____1675 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  mk_emb em un uu____1675 
let (e_char : FStar_Char.char embedding) =
  let em c = Constant (Char c)  in
  let un c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____1706 -> FStar_Pervasives_Native.None  in
  let uu____1708 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  mk_emb em un uu____1708 
let (e_string : Prims.string embedding) =
  let em s = Constant (String (s, FStar_Range.dummyRange))  in
  let un s =
    match s with
    | Constant (String (s1,uu____1733)) -> FStar_Pervasives_Native.Some s1
    | uu____1734 -> FStar_Pervasives_Native.None  in
  let uu____1735 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  mk_emb em un uu____1735 
let (e_int : FStar_BigInt.t embedding) =
  let em c = Constant (Int c)  in
  let un c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____1759 -> FStar_Pervasives_Native.None  in
  let uu____1760 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  mk_emb em un uu____1760 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let em o =
      match o with
      | FStar_Pervasives_Native.None  ->
          let uu____1793 =
            let uu____1794 =
              let uu____1799 = type_of ea  in as_iarg uu____1799  in
            [uu____1794]  in
          lid_as_constr FStar_Parser_Const.none_lid
            [FStar_Syntax_Syntax.U_zero] uu____1793
      | FStar_Pervasives_Native.Some x ->
          let uu____1809 =
            let uu____1810 =
              let uu____1815 = type_of ea  in as_iarg uu____1815  in
            let uu____1816 =
              let uu____1823 =
                let uu____1828 = embed ea x  in as_arg uu____1828  in
              [uu____1823]  in
            uu____1810 :: uu____1816  in
          lid_as_constr FStar_Parser_Const.some_lid
            [FStar_Syntax_Syntax.U_zero] uu____1809
       in
    let un trm =
      match trm with
      | Construct (fvar1,us,args) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.none_lid ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | Construct (fvar1,us,uu____1878::(a,uu____1880)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.some_lid ->
          let uu____1907 = unembed ea a  in
          FStar_Util.bind_opt uu____1907
            (fun a1  ->
               FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some a1))
      | uu____1916 -> FStar_Pervasives_Native.None  in
    let uu____1919 =
      let uu____1920 =
        let uu____1921 = let uu____1926 = type_of ea  in as_arg uu____1926
           in
        [uu____1921]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____1920
       in
    mk_emb em un uu____1919
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em x =
        let uu____1985 =
          let uu____1986 = let uu____1991 = type_of ea  in as_iarg uu____1991
             in
          let uu____1992 =
            let uu____1999 =
              let uu____2004 = type_of eb  in as_iarg uu____2004  in
            let uu____2005 =
              let uu____2012 =
                let uu____2017 = embed ea (FStar_Pervasives_Native.fst x)  in
                as_arg uu____2017  in
              let uu____2018 =
                let uu____2025 =
                  let uu____2030 = embed eb (FStar_Pervasives_Native.snd x)
                     in
                  as_arg uu____2030  in
                [uu____2025]  in
              uu____2012 :: uu____2018  in
            uu____1999 :: uu____2005  in
          uu____1986 :: uu____1992  in
        lid_as_constr FStar_Parser_Const.lid_Mktuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____1985
         in
      let un trm =
        match trm with
        | Construct
            (fvar1,us,uu____2071::uu____2072::(a,uu____2074)::(b,uu____2076)::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1
              FStar_Parser_Const.lid_Mktuple2
            ->
            let uu____2115 = unembed ea a  in
            FStar_Util.bind_opt uu____2115
              (fun a1  ->
                 let uu____2125 = unembed eb b  in
                 FStar_Util.bind_opt uu____2125
                   (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
        | uu____2138 -> FStar_Pervasives_Native.None  in
      let uu____2143 =
        let uu____2144 =
          let uu____2145 = let uu____2150 = type_of ea  in as_arg uu____2150
             in
          let uu____2151 =
            let uu____2158 =
              let uu____2163 = type_of eb  in as_arg uu____2163  in
            [uu____2158]  in
          uu____2145 :: uu____2151  in
        lid_as_typ FStar_Parser_Const.lid_tuple2 [FStar_Syntax_Syntax.U_zero]
          uu____2144
         in
      mk_emb em un uu____2143
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em l =
      let typ = let uu____2209 = type_of ea  in as_iarg uu____2209  in
      let nil =
        lid_as_constr FStar_Parser_Const.nil_lid [FStar_Syntax_Syntax.U_zero]
          [typ]
         in
      let cons1 hd1 tl1 =
        let uu____2230 =
          let uu____2231 =
            let uu____2238 =
              let uu____2243 = embed ea hd1  in as_arg uu____2243  in
            let uu____2244 = let uu____2251 = as_arg tl1  in [uu____2251]  in
            uu____2238 :: uu____2244  in
          typ :: uu____2231  in
        lid_as_constr FStar_Parser_Const.cons_lid
          [FStar_Syntax_Syntax.U_zero] uu____2230
         in
      FStar_List.fold_right cons1 l nil  in
    let rec un trm =
      match trm with
      | Construct (fv,uu____2287,uu____2288) when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
          FStar_Pervasives_Native.Some []
      | Construct
          (fv,uu____2308,(uu____2309,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____2310))::
           (hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                 )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____2339 = unembed ea hd1  in
          FStar_Util.bind_opt uu____2339
            (fun hd2  ->
               let uu____2347 = un tl1  in
               FStar_Util.bind_opt uu____2347
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | Construct
          (fv,uu____2363,(hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                               )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____2388 = unembed ea hd1  in
          FStar_Util.bind_opt uu____2388
            (fun hd2  ->
               let uu____2396 = un tl1  in
               FStar_Util.bind_opt uu____2396
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | uu____2411 -> FStar_Pervasives_Native.None  in
    let uu____2414 =
      let uu____2415 =
        let uu____2416 = let uu____2421 = type_of ea  in as_arg uu____2421
           in
        [uu____2416]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____2415
       in
    mk_emb em un uu____2414
  
let e_arrow1 : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let em f =
        Lam
          ((fun tas  ->
              let uu____2497 =
                let uu____2500 = FStar_List.hd tas  in unembed ea uu____2500
                 in
              match uu____2497 with
              | FStar_Pervasives_Native.Some a ->
                  let uu____2502 = f a  in embed eb uu____2502
              | FStar_Pervasives_Native.None  ->
                  failwith "Cannot unembed argument"),
            [(fun uu____2512  ->
                let uu____2513 = type_of eb  in as_arg uu____2513)],
            (Prims.parse_int "1"))
         in
      let un lam =
        match lam with
        | Lam (ft,uu____2543,uu____2544) ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____2580 =
                    let uu____2583 =
                      let uu____2584 =
                        let uu____2587 = embed ea x  in [uu____2587]  in
                      ft uu____2584  in
                    unembed eb uu____2583  in
                  match uu____2580 with
                  | FStar_Pervasives_Native.Some b -> b
                  | FStar_Pervasives_Native.None  ->
                      failwith "Cannot unembed function result"))
        | uu____2589 -> FStar_Pervasives_Native.None  in
      let uu____2593 =
        let uu____2594 = type_of ea  in
        let uu____2595 = let uu____2596 = type_of eb  in as_iarg uu____2596
           in
        make_arrow1 uu____2594 uu____2595  in
      mk_emb em un uu____2593
  
let (arg_as_int : arg -> FStar_BigInt.t FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_int)
  
let (arg_as_bool : arg -> Prims.bool FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_bool)
  
let (arg_as_char : arg -> FStar_Char.char FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_char)
  
let (arg_as_string : arg -> Prims.string FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_string)
  
let arg_as_list :
  'Auu____2647 'a .
    'a embedding ->
      (t,'Auu____2647) FStar_Pervasives_Native.tuple2 ->
        'a Prims.list FStar_Pervasives_Native.option
  =
  fun e  ->
    fun a  ->
      let uu____2675 = let uu____2684 = e_list e  in unembed uu____2684  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____2675
  
let arg_as_bounded_int :
  'Auu____2699 .
    (t,'Auu____2699) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun uu____2714  ->
    match uu____2714 with
    | (a,uu____2720) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____2735)::[]) when
             let uu____2752 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____2752 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____2757 -> FStar_Pervasives_Native.None)
  
let lift_unary :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option Prims.list ->
        'b FStar_Pervasives_Native.option
  =
  fun f  ->
    fun aopts  ->
      match aopts with
      | (FStar_Pervasives_Native.Some a)::[] ->
          let uu____2802 = f a  in FStar_Pervasives_Native.Some uu____2802
      | uu____2803 -> FStar_Pervasives_Native.None
  
let lift_binary :
  'a 'b .
    ('a -> 'a -> 'b) ->
      'a FStar_Pervasives_Native.option Prims.list ->
        'b FStar_Pervasives_Native.option
  =
  fun f  ->
    fun aopts  ->
      match aopts with
      | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
          a1)::[] ->
          let uu____2856 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____2856
      | uu____2857 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____2902 = FStar_List.map as_a args  in lift_unary f uu____2902
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____2958 = FStar_List.map as_a args  in
        lift_binary f uu____2958
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____2989 = f x  in embed e_int uu____2989)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  -> fun y  -> let uu____3017 = f x y  in embed e_int uu____3017)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____3038 = f x  in embed e_bool uu____3038)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  -> fun y  -> let uu____3066 = f x y  in embed e_bool uu____3066)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  -> let uu____3094 = f x y  in embed e_string uu____3094)
  
let mixed_binary_op :
  'a 'b 'c .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      (arg -> 'b FStar_Pervasives_Native.option) ->
        ('c -> t) ->
          ('a -> 'b -> 'c) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun as_b  ->
      fun embed_c  ->
        fun f  ->
          fun args  ->
            match args with
            | a::b::[] ->
                let uu____3196 =
                  let uu____3205 = as_a a  in
                  let uu____3208 = as_b b  in (uu____3205, uu____3208)  in
                (match uu____3196 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____3223 =
                       let uu____3224 = f a1 b1  in embed_c uu____3224  in
                     FStar_Pervasives_Native.Some uu____3223
                 | uu____3225 -> FStar_Pervasives_Native.None)
            | uu____3234 -> FStar_Pervasives_Native.None
  
let list_of_string' : 'Auu____3241 . 'Auu____3241 -> Prims.string -> t =
  fun rng  ->
    fun s  ->
      let uu____3252 = e_list e_char  in
      let uu____3259 = FStar_String.list_of_string s  in
      embed uu____3252 uu____3259
  
let (string_of_list' : FStar_Range.range -> FStar_Char.char Prims.list -> t)
  =
  fun rng  ->
    fun l  ->
      let s = FStar_String.string_of_list l  in Constant (String (s, rng))
  
let string_compare' :
  'Auu____3291 . 'Auu____3291 -> Prims.string -> Prims.string -> t =
  fun rng  ->
    fun s1  ->
      fun s2  ->
        let r = FStar_String.compare s1 s2  in
        let uu____3308 =
          let uu____3309 = FStar_Util.string_of_int r  in
          FStar_BigInt.big_int_of_string uu____3309  in
        embed e_int uu____3308
  
let (string_concat' :
  (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list ->
    t FStar_Pervasives_Native.option)
  =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____3353 = arg_as_string a1  in
        (match uu____3353 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____3359 = arg_as_list e_string a2  in
             (match uu____3359 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____3372 = embed e_string r  in
                  FStar_Pervasives_Native.Some uu____3372
              | uu____3373 -> FStar_Pervasives_Native.None)
         | uu____3378 -> FStar_Pervasives_Native.None)
    | uu____3381 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____3393 = FStar_BigInt.string_of_big_int i  in
    embed e_string uu____3393
  
let string_of_bool : 'Auu____3400 . 'Auu____3400 -> Prims.bool -> t =
  fun rng  -> fun b  -> embed e_string (if b then "true" else "false") 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      match args with
      | (_typ,uu____3427)::(a1,uu____3429)::(a2,uu____3431)::[] ->
          failwith "decidable_eq not yet implemented"
      | uu____3450 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____3467 =
        let uu____3468 = FStar_Ident.string_of_lid lid  in
        Prims.strcat "No interpretation for " uu____3468  in
      failwith uu____3467
  