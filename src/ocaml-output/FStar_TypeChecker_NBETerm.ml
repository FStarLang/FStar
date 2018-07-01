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
    | Lam uu____1965 -> "Lam"
    | Accu (a,l) ->
        let uu____2000 =
          let uu____2001 = atom_to_string a  in
          let uu____2002 =
            let uu____2003 =
              let uu____2004 =
                let uu____2005 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____2005  in
              Prims.strcat uu____2004 ")"  in
            Prims.strcat ") (" uu____2003  in
          Prims.strcat uu____2001 uu____2002  in
        Prims.strcat "Accu (" uu____2000
    | Construct (fv,us,l) ->
        let uu____2037 =
          let uu____2038 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2039 =
            let uu____2040 =
              let uu____2041 =
                let uu____2042 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2042  in
              let uu____2045 =
                let uu____2046 =
                  let uu____2047 =
                    let uu____2048 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2048  in
                  Prims.strcat uu____2047 "]"  in
                Prims.strcat "] [" uu____2046  in
              Prims.strcat uu____2041 uu____2045  in
            Prims.strcat ") [" uu____2040  in
          Prims.strcat uu____2038 uu____2039  in
        Prims.strcat "Construct (" uu____2037
    | FV (fv,us,l) ->
        let uu____2080 =
          let uu____2081 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2082 =
            let uu____2083 =
              let uu____2084 =
                let uu____2085 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2085  in
              let uu____2088 =
                let uu____2089 =
                  let uu____2090 =
                    let uu____2091 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2091  in
                  Prims.strcat uu____2090 "]"  in
                Prims.strcat "] [" uu____2089  in
              Prims.strcat uu____2084 uu____2088  in
            Prims.strcat ") [" uu____2083  in
          Prims.strcat uu____2081 uu____2082  in
        Prims.strcat "FV (" uu____2080
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____2106 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____2106
    | Type_t u ->
        let uu____2108 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____2108
    | Arrow uu____2109 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____2152 = t ()  in FStar_Pervasives_Native.fst uu____2152
           in
        let uu____2157 =
          let uu____2158 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____2159 =
            let uu____2160 =
              let uu____2161 = t_to_string t1  in
              let uu____2162 =
                let uu____2163 =
                  let uu____2164 =
                    let uu____2165 =
                      let uu____2166 = mkAccuVar x1  in f uu____2166  in
                    t_to_string uu____2165  in
                  Prims.strcat uu____2164 "}"  in
                Prims.strcat "{" uu____2163  in
              Prims.strcat uu____2161 uu____2162  in
            Prims.strcat ":" uu____2160  in
          Prims.strcat uu____2158 uu____2159  in
        Prims.strcat "Refinement " uu____2157
    | Unknown  -> "Unknown"
    | Quote uu____2167 -> "Quote _"
    | Lazy uu____2172 -> "Lazy _"

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____2175 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____2175
    | Match (t,uu____2177,uu____2178) ->
        let uu____2201 = t_to_string t  in Prims.strcat "Match " uu____2201
    | Rec (uu____2202,uu____2203,l) ->
        let uu____2213 =
          let uu____2214 =
            let uu____2215 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____2215  in
          Prims.strcat uu____2214 ")"  in
        Prims.strcat "Rec (" uu____2213

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____2219 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____2219 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____2225 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____2225 (FStar_String.concat " ")

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
        let uu____2467 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____2467 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2487 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkConstruct uu____2487 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____2523  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____2536  -> a)])
  
let (e_any : t embedding) =
  let em a = a  in
  let un t = FStar_Pervasives_Native.Some t  in
  let uu____2562 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____2562 
let (e_unit : unit embedding) =
  let em a = Constant Unit  in
  let un t = FStar_Pervasives_Native.Some ()  in
  let uu____2585 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  mk_emb em un uu____2585 
let (e_bool : Prims.bool embedding) =
  let em a = Constant (Bool a)  in
  let un t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____2611 -> FStar_Pervasives_Native.None  in
  let uu____2612 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  mk_emb em un uu____2612 
let (e_char : FStar_Char.char embedding) =
  let em c = Constant (Char c)  in
  let un c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____2646 -> FStar_Pervasives_Native.None  in
  let uu____2648 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  mk_emb em un uu____2648 
let (e_string : Prims.string embedding) =
  let em s = Constant (String (s, FStar_Range.dummyRange))  in
  let un s =
    match s with
    | Constant (String (s1,uu____2675)) -> FStar_Pervasives_Native.Some s1
    | uu____2676 -> FStar_Pervasives_Native.None  in
  let uu____2677 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  mk_emb em un uu____2677 
let (e_int : FStar_BigInt.t embedding) =
  let em c = Constant (Int c)  in
  let un c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____2703 -> FStar_Pervasives_Native.None  in
  let uu____2704 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  mk_emb em un uu____2704 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let em o =
      match o with
      | FStar_Pervasives_Native.None  ->
          let uu____2737 =
            let uu____2738 =
              let uu____2743 = type_of ea  in as_iarg uu____2743  in
            [uu____2738]  in
          lid_as_constr FStar_Parser_Const.none_lid
            [FStar_Syntax_Syntax.U_zero] uu____2737
      | FStar_Pervasives_Native.Some x ->
          let uu____2753 =
            let uu____2754 =
              let uu____2759 = type_of ea  in as_iarg uu____2759  in
            let uu____2760 =
              let uu____2767 =
                let uu____2772 = embed ea x  in as_arg uu____2772  in
              [uu____2767]  in
            uu____2754 :: uu____2760  in
          lid_as_constr FStar_Parser_Const.some_lid
            [FStar_Syntax_Syntax.U_zero] uu____2753
       in
    let un trm =
      match trm with
      | Construct (fvar1,us,args) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.none_lid ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | Construct (fvar1,us,uu____2822::(a,uu____2824)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.some_lid ->
          let uu____2851 = unembed ea a  in
          FStar_Util.bind_opt uu____2851
            (fun a1  ->
               FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some a1))
      | uu____2860 -> FStar_Pervasives_Native.None  in
    let uu____2863 =
      let uu____2864 =
        let uu____2865 = let uu____2870 = type_of ea  in as_arg uu____2870
           in
        [uu____2865]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____2864
       in
    mk_emb em un uu____2863
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em x =
        let uu____2929 =
          let uu____2930 = let uu____2935 = type_of ea  in as_iarg uu____2935
             in
          let uu____2936 =
            let uu____2943 =
              let uu____2948 = type_of eb  in as_iarg uu____2948  in
            let uu____2949 =
              let uu____2956 =
                let uu____2961 = embed ea (FStar_Pervasives_Native.fst x)  in
                as_arg uu____2961  in
              let uu____2962 =
                let uu____2969 =
                  let uu____2974 = embed eb (FStar_Pervasives_Native.snd x)
                     in
                  as_arg uu____2974  in
                [uu____2969]  in
              uu____2956 :: uu____2962  in
            uu____2943 :: uu____2949  in
          uu____2930 :: uu____2936  in
        lid_as_constr FStar_Parser_Const.lid_Mktuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____2929
         in
      let un trm =
        match trm with
        | Construct
            (fvar1,us,uu____3015::uu____3016::(a,uu____3018)::(b,uu____3020)::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1
              FStar_Parser_Const.lid_Mktuple2
            ->
            let uu____3059 = unembed ea a  in
            FStar_Util.bind_opt uu____3059
              (fun a1  ->
                 let uu____3069 = unembed eb b  in
                 FStar_Util.bind_opt uu____3069
                   (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
        | uu____3082 -> FStar_Pervasives_Native.None  in
      let uu____3087 =
        let uu____3088 =
          let uu____3089 = let uu____3094 = type_of ea  in as_arg uu____3094
             in
          let uu____3095 =
            let uu____3102 =
              let uu____3107 = type_of eb  in as_arg uu____3107  in
            [uu____3102]  in
          uu____3089 :: uu____3095  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____3088
         in
      mk_emb em un uu____3087
  
let (e_range : FStar_Range.range embedding) =
  let em r = Constant (Range r)  in
  let un t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____3145 -> FStar_Pervasives_Native.None  in
  let uu____3146 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  mk_emb em un uu____3146 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em l =
      let typ = let uu____3180 = type_of ea  in as_iarg uu____3180  in
      let nil =
        lid_as_constr FStar_Parser_Const.nil_lid [FStar_Syntax_Syntax.U_zero]
          [typ]
         in
      let cons1 hd1 tl1 =
        let uu____3201 =
          let uu____3202 =
            let uu____3209 =
              let uu____3214 = embed ea hd1  in as_arg uu____3214  in
            let uu____3215 = let uu____3222 = as_arg tl1  in [uu____3222]  in
            uu____3209 :: uu____3215  in
          typ :: uu____3202  in
        lid_as_constr FStar_Parser_Const.cons_lid
          [FStar_Syntax_Syntax.U_zero] uu____3201
         in
      FStar_List.fold_right cons1 l nil  in
    let rec un trm =
      match trm with
      | Construct (fv,uu____3258,uu____3259) when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
          FStar_Pervasives_Native.Some []
      | Construct
          (fv,uu____3279,(uu____3280,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____3281))::
           (hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                 )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____3310 = unembed ea hd1  in
          FStar_Util.bind_opt uu____3310
            (fun hd2  ->
               let uu____3318 = un tl1  in
               FStar_Util.bind_opt uu____3318
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | Construct
          (fv,uu____3334,(hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                               )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____3359 = unembed ea hd1  in
          FStar_Util.bind_opt uu____3359
            (fun hd2  ->
               let uu____3367 = un tl1  in
               FStar_Util.bind_opt uu____3367
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | uu____3382 -> FStar_Pervasives_Native.None  in
    let uu____3385 =
      let uu____3386 =
        let uu____3387 = let uu____3392 = type_of ea  in as_arg uu____3392
           in
        [uu____3387]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____3386
       in
    mk_emb em un uu____3385
  
let e_arrow1 : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let em f =
        Lam
          ((fun tas  ->
              let uu____3468 =
                let uu____3471 = FStar_List.hd tas  in unembed ea uu____3471
                 in
              match uu____3468 with
              | FStar_Pervasives_Native.Some a ->
                  let uu____3473 = f a  in embed eb uu____3473
              | FStar_Pervasives_Native.None  ->
                  failwith "cannot unembed function argument"),
            [(fun uu____3483  ->
                let uu____3484 = type_of eb  in as_arg uu____3484)],
            (Prims.parse_int "1"))
         in
      let un lam =
        match lam with
        | Lam (ft,uu____3514,uu____3515) ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____3551 =
                    let uu____3554 =
                      let uu____3555 =
                        let uu____3558 = embed ea x  in [uu____3558]  in
                      ft uu____3555  in
                    unembed eb uu____3554  in
                  match uu____3551 with
                  | FStar_Pervasives_Native.Some x1 -> x1
                  | FStar_Pervasives_Native.None  ->
                      failwith "cannot unembed function result"))
        | uu____3560 -> FStar_Pervasives_Native.None  in
      let uu____3564 =
        let uu____3565 = type_of ea  in
        let uu____3566 = let uu____3567 = type_of eb  in as_iarg uu____3567
           in
        make_arrow1 uu____3565 uu____3566  in
      mk_emb em un uu____3564
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____3579 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3579 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____3584 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3584 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____3589 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3589 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____3594 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3594 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____3599 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3599 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____3604 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3604 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____3609 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3609 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____3614 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3614 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____3619 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3619 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____3627 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____3628 =
          let uu____3629 =
            let uu____3634 =
              let uu____3635 = e_list e_string  in embed uu____3635 l  in
            as_arg uu____3634  in
          [uu____3629]  in
        mkFV uu____3627 [] uu____3628
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____3653 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____3654 =
          let uu____3655 =
            let uu____3660 =
              let uu____3661 = e_list e_string  in embed uu____3661 l  in
            as_arg uu____3660  in
          [uu____3655]  in
        mkFV uu____3653 [] uu____3654
    | FStar_Syntax_Embeddings.UnfoldAttr a -> failwith "NBE UnfoldAttr..."
     in
  let un t0 =
    match t0 with
    | FV (fv,uu____3688,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____3704,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____3720,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____3736,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____3752,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____3768,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____3784,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____3800,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____3816,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____3832,(l,uu____3834)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____3853 =
          let uu____3858 = e_list e_string  in unembed uu____3858 l  in
        FStar_Util.bind_opt uu____3853
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____3874,(l,uu____3876)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____3895 =
          let uu____3900 = e_list e_string  in unembed uu____3900 l  in
        FStar_Util.bind_opt uu____3895
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | uu____3915 ->
        ((let uu____3917 =
            let uu____3922 =
              let uu____3923 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____3923
               in
            (FStar_Errors.Warning_NotEmbedded, uu____3922)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3917);
         FStar_Pervasives_Native.None)
     in
  let uu____3924 =
    let uu____3925 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____3925 [] []  in
  mk_emb em un uu____3924 
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
      let uu____3994 = let uu____4003 = e_list e  in unembed uu____4003  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____3994
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____4024  ->
    match uu____4024 with
    | (a,uu____4032) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____4047)::[]) when
             let uu____4064 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____4064 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____4069 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____4111 = let uu____4118 = as_arg c  in [uu____4118]  in
      int_to_t2 uu____4111
  
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
          let uu____4171 = f a  in FStar_Pervasives_Native.Some uu____4171
      | uu____4172 -> FStar_Pervasives_Native.None
  
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
          let uu____4225 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____4225
      | uu____4226 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____4269 = FStar_List.map as_a args  in lift_unary f uu____4269
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____4323 = FStar_List.map as_a args  in
        lift_binary f uu____4323
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____4352 = f x  in embed e_int uu____4352)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  -> fun y  -> let uu____4378 = f x y  in embed e_int uu____4378)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____4397 = f x  in embed e_bool uu____4397)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  -> fun y  -> let uu____4423 = f x y  in embed e_bool uu____4423)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  -> let uu____4449 = f x y  in embed e_string uu____4449)
  
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
                let uu____4551 =
                  let uu____4560 = as_a a  in
                  let uu____4563 = as_b b  in (uu____4560, uu____4563)  in
                (match uu____4551 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____4578 =
                       let uu____4579 = f a1 b1  in embed_c uu____4579  in
                     FStar_Pervasives_Native.Some uu____4578
                 | uu____4580 -> FStar_Pervasives_Native.None)
            | uu____4589 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____4595 = e_list e_char  in
    let uu____4602 = FStar_String.list_of_string s  in
    embed uu____4595 uu____4602
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____4632 =
        let uu____4633 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____4633  in
      embed e_int uu____4632
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____4665 = arg_as_string a1  in
        (match uu____4665 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4671 = arg_as_list e_string a2  in
             (match uu____4671 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____4684 = embed e_string r  in
                  FStar_Pervasives_Native.Some uu____4684
              | uu____4685 -> FStar_Pervasives_Native.None)
         | uu____4690 -> FStar_Pervasives_Native.None)
    | uu____4693 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____4699 = FStar_BigInt.string_of_big_int i  in
    embed e_string uu____4699
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string (if b then "true" else "false") 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool true  in
      let fal = embed e_bool false  in
      match args with
      | (_univ,uu____4725)::(_typ,uu____4727)::(a1,uu____4729)::(a2,uu____4731)::[]
          ->
          let uu____4752 = eq_t a1 a2  in
          (match uu____4752 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____4757 -> FStar_Pervasives_Native.None)
      | uu____4758 -> failwith "Unexpected number of arguments"
  
let (interp_prop : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____4771)::(_typ,uu____4773)::(a1,uu____4775)::(a2,uu____4777)::[]
        ->
        let uu____4798 = eq_t a1 a2  in
        (match uu____4798 with
         | FStar_Syntax_Util.Equal  ->
             let uu____4801 = embed e_bool true  in
             FStar_Pervasives_Native.Some uu____4801
         | FStar_Syntax_Util.NotEqual  ->
             let uu____4802 = embed e_bool false  in
             FStar_Pervasives_Native.Some uu____4802
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____4803 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____4820 =
        let uu____4821 = FStar_Ident.string_of_lid lid  in
        Prims.strcat "No interpretation for " uu____4821  in
      failwith uu____4820
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____4834)::[] ->
        let uu____4843 = unembed e_range a1  in
        (match uu____4843 with
         | FStar_Pervasives_Native.Some r ->
             let uu____4849 = embed e_range r  in
             FStar_Pervasives_Native.Some uu____4849
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____4850 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____4884 = arg_as_list e_char a1  in
        (match uu____4884 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4900 = arg_as_string a2  in
             (match uu____4900 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____4909 =
                    let uu____4910 = e_list e_string  in embed uu____4910 r
                     in
                  FStar_Pervasives_Native.Some uu____4909
              | uu____4917 -> FStar_Pervasives_Native.None)
         | uu____4920 -> FStar_Pervasives_Native.None)
    | uu____4926 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____4967 =
          let uu____4980 = arg_as_string a1  in
          let uu____4983 = arg_as_int a2  in
          let uu____4986 = arg_as_int a3  in
          (uu____4980, uu____4983, uu____4986)  in
        (match uu____4967 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                let r = FStar_String.substring s1 n11 n21  in
                let uu____5017 = embed e_string r  in
                FStar_Pervasives_Native.Some uu____5017
              with | uu____5023 -> FStar_Pervasives_Native.None)
         | uu____5024 -> FStar_Pervasives_Native.None)
    | uu____5037 -> FStar_Pervasives_Native.None
  