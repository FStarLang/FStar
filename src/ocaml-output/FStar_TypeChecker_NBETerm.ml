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
  (t Prims.list -> comp,(unit ->
                           (t,FStar_Syntax_Syntax.aqual)
                             FStar_Pervasives_Native.tuple2)
                          Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Refinement of
  (t -> t,unit ->
            (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2)
  FStar_Pervasives_Native.tuple2 
  | Quote of (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.quoteinfo)
  FStar_Pervasives_Native.tuple2 
  | Lazy of FStar_Syntax_Syntax.lazyinfo 
and comp =
  | Tot of (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | GTot of (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | Comp of comp_typ 
and comp_typ =
  {
  comp_univs: FStar_Syntax_Syntax.universes ;
  effect_name: FStar_Ident.lident ;
  result_typ: t ;
  effect_args:
    (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list ;
  flags: FStar_Syntax_Syntax.cflags Prims.list }
let (uu___is_Var : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____393 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____424 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t,t -> t,(t -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.branch Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Rec : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____499 -> false
  
let (__proj__Rec__item___0 :
  atom ->
    (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
      t Prims.list) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____563 -> false
  
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
    match projectee with | Accu _0 -> true | uu____647 -> false
  
let (__proj__Accu__item___0 :
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____705 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____775 -> false 
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
    match projectee with | Constant _0 -> true | uu____831 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____845 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____859 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____872 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____897 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    (t Prims.list -> comp,(unit ->
                             (t,FStar_Syntax_Syntax.aqual)
                               FStar_Pervasives_Native.tuple2)
                            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____979 -> false
  
let (__proj__Refinement__item___0 :
  t ->
    (t -> t,unit ->
              (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1039 -> false
  
let (__proj__Quote__item___0 :
  t ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.quoteinfo)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1065 -> false
  
let (__proj__Lazy__item___0 : t -> FStar_Syntax_Syntax.lazyinfo) =
  fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____1085 -> false
  
let (__proj__Tot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1123 -> false
  
let (__proj__GTot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1155 -> false
  
let (__proj__Comp__item___0 : comp -> comp_typ) =
  fun projectee  -> match projectee with | Comp _0 -> _0 
let (__proj__Mkcomp_typ__item__comp_univs :
  comp_typ -> FStar_Syntax_Syntax.universes) =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__comp_univs
  
let (__proj__Mkcomp_typ__item__effect_name : comp_typ -> FStar_Ident.lident)
  =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__effect_name
  
let (__proj__Mkcomp_typ__item__result_typ : comp_typ -> t) =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__result_typ
  
let (__proj__Mkcomp_typ__item__effect_args :
  comp_typ ->
    (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__effect_args
  
let (__proj__Mkcomp_typ__item__flags :
  comp_typ -> FStar_Syntax_Syntax.cflags Prims.list) =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__flags
  
type arg = (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
type args =
  (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
type head = t
type annot = t FStar_Pervasives_Native.option
let (isAccu : t -> Prims.bool) =
  fun trm  -> match trm with | Accu uu____1286 -> true | uu____1297 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____1303,uu____1304) -> false | uu____1317 -> true
  
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
let (equal_if : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___222_1483  ->
    if uu___222_1483
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___223_1489  ->
    if uu___223_1489
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.NotEqual
  
let (eq_inj :
  FStar_Syntax_Util.eq_result ->
    FStar_Syntax_Util.eq_result -> FStar_Syntax_Util.eq_result)
  =
  fun r1  ->
    fun r2  ->
      match (r1, r2) with
      | (FStar_Syntax_Util.Equal ,FStar_Syntax_Util.Equal ) ->
          FStar_Syntax_Util.Equal
      | (FStar_Syntax_Util.NotEqual ,uu____1501) ->
          FStar_Syntax_Util.NotEqual
      | (uu____1502,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____1503) -> FStar_Syntax_Util.Unknown
      | (uu____1504,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____1520 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____1536),String (s2,uu____1538)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____1546,uu____1547) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____1582,Lam uu____1583) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____1652 = eq_atom a1 a2  in
          eq_and uu____1652 (fun uu____1654  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____1693 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1693
          then
            let uu____1694 =
              let uu____1695 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____1695  in
            eq_and uu____1694 (fun uu____1697  -> eq_args args1 args2)
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____1737 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1737
          then
            let uu____1738 =
              let uu____1739 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____1739  in
            eq_and uu____1738 (fun uu____1741  -> eq_args args1 args2)
          else FStar_Syntax_Util.NotEqual
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____1747 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1747
      | (Univ u1,Univ u2) ->
          let uu____1750 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1750
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____1796 =
            let uu____1797 =
              let uu____1798 = t11 ()  in
              FStar_Pervasives_Native.fst uu____1798  in
            let uu____1803 =
              let uu____1804 = t11 ()  in
              FStar_Pervasives_Native.fst uu____1804  in
            eq_t uu____1797 uu____1803  in
          eq_and uu____1796
            (fun uu____1812  ->
               let uu____1813 =
                 let uu____1814 = mkAccuVar x  in r1 uu____1814  in
               let uu____1815 =
                 let uu____1816 = mkAccuVar x  in r2 uu____1816  in
               eq_t uu____1813 uu____1815)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____1817,uu____1818) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____1823,uu____1824) -> FStar_Syntax_Util.Unknown

and (eq_arg : arg -> arg -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      eq_t (FStar_Pervasives_Native.fst a1) (FStar_Pervasives_Native.fst a2)

and (eq_args : args -> args -> FStar_Syntax_Util.eq_result) =
  fun as1  ->
    fun as2  ->
      match (as1, as2) with
      | ([],[]) -> FStar_Syntax_Util.Equal
      | (x::xs,y::ys) ->
          let uu____1905 = eq_arg x y  in
          eq_and uu____1905 (fun uu____1907  -> eq_args xs ys)
      | (uu____1908,uu____1909) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____1945) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____1947 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____1947
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity) ->
        let uu____1996 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____2004 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____1996 uu____2004
    | Accu (a,l) ->
        let uu____2019 =
          let uu____2020 = atom_to_string a  in
          let uu____2021 =
            let uu____2022 =
              let uu____2023 =
                let uu____2024 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____2024  in
              Prims.strcat uu____2023 ")"  in
            Prims.strcat ") (" uu____2022  in
          Prims.strcat uu____2020 uu____2021  in
        Prims.strcat "Accu (" uu____2019
    | Construct (fv,us,l) ->
        let uu____2056 =
          let uu____2057 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2058 =
            let uu____2059 =
              let uu____2060 =
                let uu____2061 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2061  in
              let uu____2064 =
                let uu____2065 =
                  let uu____2066 =
                    let uu____2067 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2067  in
                  Prims.strcat uu____2066 "]"  in
                Prims.strcat "] [" uu____2065  in
              Prims.strcat uu____2060 uu____2064  in
            Prims.strcat ") [" uu____2059  in
          Prims.strcat uu____2057 uu____2058  in
        Prims.strcat "Construct (" uu____2056
    | FV (fv,us,l) ->
        let uu____2099 =
          let uu____2100 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2101 =
            let uu____2102 =
              let uu____2103 =
                let uu____2104 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2104  in
              let uu____2107 =
                let uu____2108 =
                  let uu____2109 =
                    let uu____2110 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2110  in
                  Prims.strcat uu____2109 "]"  in
                Prims.strcat "] [" uu____2108  in
              Prims.strcat uu____2103 uu____2107  in
            Prims.strcat ") [" uu____2102  in
          Prims.strcat uu____2100 uu____2101  in
        Prims.strcat "FV (" uu____2099
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____2125 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____2125
    | Type_t u ->
        let uu____2127 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____2127
    | Arrow uu____2128 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____2171 = t ()  in FStar_Pervasives_Native.fst uu____2171
           in
        let uu____2176 =
          let uu____2177 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____2178 =
            let uu____2179 =
              let uu____2180 = t_to_string t1  in
              let uu____2181 =
                let uu____2182 =
                  let uu____2183 =
                    let uu____2184 =
                      let uu____2185 = mkAccuVar x1  in f uu____2185  in
                    t_to_string uu____2184  in
                  Prims.strcat uu____2183 "}"  in
                Prims.strcat "{" uu____2182  in
              Prims.strcat uu____2180 uu____2181  in
            Prims.strcat ":" uu____2179  in
          Prims.strcat uu____2177 uu____2178  in
        Prims.strcat "Refinement " uu____2176
    | Unknown  -> "Unknown"
    | Quote uu____2186 -> "Quote _"
    | Lazy uu____2191 -> "Lazy _"

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____2194 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____2194
    | Match (t,uu____2196,uu____2197) ->
        let uu____2220 = t_to_string t  in Prims.strcat "Match " uu____2220
    | Rec (uu____2221,uu____2222,l) ->
        let uu____2232 =
          let uu____2233 =
            let uu____2234 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____2234  in
          Prims.strcat uu____2233 ")"  in
        Prims.strcat "Rec (" uu____2232

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____2238 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____2238 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____2244 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____2244 (FStar_String.concat " ")

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
  'a .
    ('a -> t) ->
      (t -> 'a FStar_Pervasives_Native.option) -> t -> 'a embedding
  = fun em  -> fun un  -> fun typ  -> { em; un; typ } 
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2486 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____2486 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2506 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkConstruct uu____2506 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____2542  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____2555  -> a)])
  
let (e_any : t embedding) =
  let em a = a  in
  let un t = FStar_Pervasives_Native.Some t  in
  let uu____2581 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____2581 
let (e_unit : unit embedding) =
  let em a = Constant Unit  in
  let un t = FStar_Pervasives_Native.Some ()  in
  let uu____2604 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  mk_emb em un uu____2604 
let (e_bool : Prims.bool embedding) =
  let em a = Constant (Bool a)  in
  let un t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____2630 -> FStar_Pervasives_Native.None  in
  let uu____2631 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  mk_emb em un uu____2631 
let (e_char : FStar_Char.char embedding) =
  let em c = Constant (Char c)  in
  let un c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____2665 -> FStar_Pervasives_Native.None  in
  let uu____2667 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  mk_emb em un uu____2667 
let (e_string : Prims.string embedding) =
  let em s = Constant (String (s, FStar_Range.dummyRange))  in
  let un s =
    match s with
    | Constant (String (s1,uu____2694)) -> FStar_Pervasives_Native.Some s1
    | uu____2695 -> FStar_Pervasives_Native.None  in
  let uu____2696 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  mk_emb em un uu____2696 
let (e_int : FStar_BigInt.t embedding) =
  let em c = Constant (Int c)  in
  let un c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____2722 -> FStar_Pervasives_Native.None  in
  let uu____2723 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  mk_emb em un uu____2723 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let em o =
      match o with
      | FStar_Pervasives_Native.None  ->
          let uu____2756 =
            let uu____2757 =
              let uu____2762 = type_of ea  in as_iarg uu____2762  in
            [uu____2757]  in
          lid_as_constr FStar_Parser_Const.none_lid
            [FStar_Syntax_Syntax.U_zero] uu____2756
      | FStar_Pervasives_Native.Some x ->
          let uu____2772 =
            let uu____2773 =
              let uu____2778 = type_of ea  in as_iarg uu____2778  in
            let uu____2779 =
              let uu____2786 =
                let uu____2791 = embed ea x  in as_arg uu____2791  in
              [uu____2786]  in
            uu____2773 :: uu____2779  in
          lid_as_constr FStar_Parser_Const.some_lid
            [FStar_Syntax_Syntax.U_zero] uu____2772
       in
    let un trm =
      match trm with
      | Construct (fvar1,us,args) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.none_lid ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | Construct (fvar1,us,uu____2841::(a,uu____2843)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.some_lid ->
          let uu____2870 = unembed ea a  in
          FStar_Util.bind_opt uu____2870
            (fun a1  ->
               FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some a1))
      | uu____2879 -> FStar_Pervasives_Native.None  in
    let uu____2882 =
      let uu____2883 =
        let uu____2884 = let uu____2889 = type_of ea  in as_arg uu____2889
           in
        [uu____2884]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____2883
       in
    mk_emb em un uu____2882
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em x =
        let uu____2948 =
          let uu____2949 = let uu____2954 = type_of ea  in as_iarg uu____2954
             in
          let uu____2955 =
            let uu____2962 =
              let uu____2967 = type_of eb  in as_iarg uu____2967  in
            let uu____2968 =
              let uu____2975 =
                let uu____2980 = embed ea (FStar_Pervasives_Native.fst x)  in
                as_arg uu____2980  in
              let uu____2981 =
                let uu____2988 =
                  let uu____2993 = embed eb (FStar_Pervasives_Native.snd x)
                     in
                  as_arg uu____2993  in
                [uu____2988]  in
              uu____2975 :: uu____2981  in
            uu____2962 :: uu____2968  in
          uu____2949 :: uu____2955  in
        lid_as_constr FStar_Parser_Const.lid_Mktuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____2948
         in
      let un trm =
        match trm with
        | Construct
            (fvar1,us,uu____3034::uu____3035::(a,uu____3037)::(b,uu____3039)::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1
              FStar_Parser_Const.lid_Mktuple2
            ->
            let uu____3078 = unembed ea a  in
            FStar_Util.bind_opt uu____3078
              (fun a1  ->
                 let uu____3088 = unembed eb b  in
                 FStar_Util.bind_opt uu____3088
                   (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
        | uu____3101 -> FStar_Pervasives_Native.None  in
      let uu____3106 =
        let uu____3107 =
          let uu____3108 = let uu____3113 = type_of ea  in as_arg uu____3113
             in
          let uu____3114 =
            let uu____3121 =
              let uu____3126 = type_of eb  in as_arg uu____3126  in
            [uu____3121]  in
          uu____3108 :: uu____3114  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____3107
         in
      mk_emb em un uu____3106
  
let (e_range : FStar_Range.range embedding) =
  let em r = Constant (Range r)  in
  let un t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____3164 -> FStar_Pervasives_Native.None  in
  let uu____3165 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  mk_emb em un uu____3165 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em l =
      let typ = let uu____3199 = type_of ea  in as_iarg uu____3199  in
      let nil =
        lid_as_constr FStar_Parser_Const.nil_lid [FStar_Syntax_Syntax.U_zero]
          [typ]
         in
      let cons1 hd1 tl1 =
        let uu____3220 =
          let uu____3221 =
            let uu____3228 =
              let uu____3233 = embed ea hd1  in as_arg uu____3233  in
            let uu____3234 = let uu____3241 = as_arg tl1  in [uu____3241]  in
            uu____3228 :: uu____3234  in
          typ :: uu____3221  in
        lid_as_constr FStar_Parser_Const.cons_lid
          [FStar_Syntax_Syntax.U_zero] uu____3220
         in
      FStar_List.fold_right cons1 l nil  in
    let rec un trm =
      match trm with
      | Construct (fv,uu____3277,uu____3278) when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
          FStar_Pervasives_Native.Some []
      | Construct
          (fv,uu____3298,(uu____3299,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____3300))::
           (hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                 )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____3329 = unembed ea hd1  in
          FStar_Util.bind_opt uu____3329
            (fun hd2  ->
               let uu____3337 = un tl1  in
               FStar_Util.bind_opt uu____3337
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | Construct
          (fv,uu____3353,(hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                               )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____3378 = unembed ea hd1  in
          FStar_Util.bind_opt uu____3378
            (fun hd2  ->
               let uu____3386 = un tl1  in
               FStar_Util.bind_opt uu____3386
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | uu____3401 -> FStar_Pervasives_Native.None  in
    let uu____3404 =
      let uu____3405 =
        let uu____3406 = let uu____3411 = type_of ea  in as_arg uu____3411
           in
        [uu____3406]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____3405
       in
    mk_emb em un uu____3404
  
let e_arrow1 : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let em f =
        Lam
          ((fun tas  ->
              let uu____3487 =
                let uu____3490 = FStar_List.hd tas  in unembed ea uu____3490
                 in
              match uu____3487 with
              | FStar_Pervasives_Native.Some a ->
                  let uu____3492 = f a  in embed eb uu____3492
              | FStar_Pervasives_Native.None  ->
                  failwith "cannot unembed function argument"),
            [(fun uu____3502  ->
                let uu____3503 = type_of eb  in as_arg uu____3503)],
            (Prims.parse_int "1"))
         in
      let un lam =
        match lam with
        | Lam (ft,uu____3533,uu____3534) ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____3570 =
                    let uu____3573 =
                      let uu____3574 =
                        let uu____3577 = embed ea x  in [uu____3577]  in
                      ft uu____3574  in
                    unembed eb uu____3573  in
                  match uu____3570 with
                  | FStar_Pervasives_Native.Some x1 -> x1
                  | FStar_Pervasives_Native.None  ->
                      failwith "cannot unembed function result"))
        | uu____3579 -> FStar_Pervasives_Native.None  in
      let uu____3583 =
        let uu____3584 = type_of ea  in
        let uu____3585 = let uu____3586 = type_of eb  in as_iarg uu____3586
           in
        make_arrow1 uu____3584 uu____3585  in
      mk_emb em un uu____3583
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____3598 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3598 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____3603 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3603 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____3608 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3608 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____3613 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3613 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____3618 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3618 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____3623 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3623 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____3628 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3628 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____3633 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3633 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____3638 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3638 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____3646 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____3647 =
          let uu____3648 =
            let uu____3653 =
              let uu____3654 = e_list e_string  in embed uu____3654 l  in
            as_arg uu____3653  in
          [uu____3648]  in
        mkFV uu____3646 [] uu____3647
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____3672 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____3673 =
          let uu____3674 =
            let uu____3679 =
              let uu____3680 = e_list e_string  in embed uu____3680 l  in
            as_arg uu____3679  in
          [uu____3674]  in
        mkFV uu____3672 [] uu____3673
    | FStar_Syntax_Embeddings.UnfoldAttr a -> failwith "NBE UnfoldAttr..."
     in
  let un t0 =
    match t0 with
    | FV (fv,uu____3707,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____3723,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____3739,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____3755,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____3771,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____3787,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____3803,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____3819,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____3835,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____3851,(l,uu____3853)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____3872 =
          let uu____3877 = e_list e_string  in unembed uu____3877 l  in
        FStar_Util.bind_opt uu____3872
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____3893,(l,uu____3895)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____3914 =
          let uu____3919 = e_list e_string  in unembed uu____3919 l  in
        FStar_Util.bind_opt uu____3914
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | uu____3934 ->
        ((let uu____3936 =
            let uu____3941 =
              let uu____3942 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____3942
               in
            (FStar_Errors.Warning_NotEmbedded, uu____3941)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3936);
         FStar_Pervasives_Native.None)
     in
  let uu____3943 =
    let uu____3944 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____3944 [] []  in
  mk_emb em un uu____3943 
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
  'a . 'a embedding -> arg -> 'a Prims.list FStar_Pervasives_Native.option =
  fun e  ->
    fun a  ->
      let uu____4013 = let uu____4022 = e_list e  in unembed uu____4022  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4013
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____4043  ->
    match uu____4043 with
    | (a,uu____4051) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____4066)::[]) when
             let uu____4083 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____4083 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____4088 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____4130 = let uu____4137 = as_arg c  in [uu____4137]  in
      int_to_t2 uu____4130
  
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
          let uu____4190 = f a  in FStar_Pervasives_Native.Some uu____4190
      | uu____4191 -> FStar_Pervasives_Native.None
  
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
          let uu____4244 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____4244
      | uu____4245 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____4288 = FStar_List.map as_a args  in lift_unary f uu____4288
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____4342 = FStar_List.map as_a args  in
        lift_binary f uu____4342
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____4371 = f x  in embed e_int uu____4371)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  -> fun y  -> let uu____4397 = f x y  in embed e_int uu____4397)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____4416 = f x  in embed e_bool uu____4416)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  -> fun y  -> let uu____4442 = f x y  in embed e_bool uu____4442)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  -> let uu____4468 = f x y  in embed e_string uu____4468)
  
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
                let uu____4570 =
                  let uu____4579 = as_a a  in
                  let uu____4582 = as_b b  in (uu____4579, uu____4582)  in
                (match uu____4570 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____4597 =
                       let uu____4598 = f a1 b1  in embed_c uu____4598  in
                     FStar_Pervasives_Native.Some uu____4597
                 | uu____4599 -> FStar_Pervasives_Native.None)
            | uu____4608 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____4614 = e_list e_char  in
    let uu____4621 = FStar_String.list_of_string s  in
    embed uu____4614 uu____4621
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____4651 =
        let uu____4652 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____4652  in
      embed e_int uu____4651
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____4684 = arg_as_string a1  in
        (match uu____4684 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4690 = arg_as_list e_string a2  in
             (match uu____4690 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____4703 = embed e_string r  in
                  FStar_Pervasives_Native.Some uu____4703
              | uu____4704 -> FStar_Pervasives_Native.None)
         | uu____4709 -> FStar_Pervasives_Native.None)
    | uu____4712 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____4718 = FStar_BigInt.string_of_big_int i  in
    embed e_string uu____4718
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string (if b then "true" else "false") 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool true  in
      let fal = embed e_bool false  in
      match args with
      | (_univ,uu____4744)::(_typ,uu____4746)::(a1,uu____4748)::(a2,uu____4750)::[]
          ->
          let uu____4771 = eq_t a1 a2  in
          (match uu____4771 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____4776 -> FStar_Pervasives_Native.None)
      | uu____4777 -> failwith "Unexpected number of arguments"
  
let (interp_prop : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____4790)::(_typ,uu____4792)::(a1,uu____4794)::(a2,uu____4796)::[]
        ->
        let uu____4817 = eq_t a1 a2  in
        (match uu____4817 with
         | FStar_Syntax_Util.Equal  ->
             let uu____4820 = embed e_bool true  in
             FStar_Pervasives_Native.Some uu____4820
         | FStar_Syntax_Util.NotEqual  ->
             let uu____4821 = embed e_bool false  in
             FStar_Pervasives_Native.Some uu____4821
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____4822 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____4839 =
        let uu____4840 = FStar_Ident.string_of_lid lid  in
        Prims.strcat "No interpretation for " uu____4840  in
      failwith uu____4839
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____4853)::[] ->
        let uu____4862 = unembed e_range a1  in
        (match uu____4862 with
         | FStar_Pervasives_Native.Some r ->
             let uu____4868 = embed e_range r  in
             FStar_Pervasives_Native.Some uu____4868
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____4869 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____4903 = arg_as_list e_char a1  in
        (match uu____4903 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4919 = arg_as_string a2  in
             (match uu____4919 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____4928 =
                    let uu____4929 = e_list e_string  in embed uu____4929 r
                     in
                  FStar_Pervasives_Native.Some uu____4928
              | uu____4936 -> FStar_Pervasives_Native.None)
         | uu____4939 -> FStar_Pervasives_Native.None)
    | uu____4945 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____4986 =
          let uu____4999 = arg_as_string a1  in
          let uu____5002 = arg_as_int a2  in
          let uu____5005 = arg_as_int a3  in
          (uu____4999, uu____5002, uu____5005)  in
        (match uu____4986 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                let r = FStar_String.substring s1 n11 n21  in
                let uu____5036 = embed e_string r  in
                FStar_Pervasives_Native.Some uu____5036
              with | uu____5042 -> FStar_Pervasives_Native.None)
         | uu____5043 -> FStar_Pervasives_Native.None)
    | uu____5056 -> FStar_Pervasives_Native.None
  