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
  'Auu____2416 .
    ('Auu____2416 -> t) ->
      (t -> 'Auu____2416 FStar_Pervasives_Native.option) ->
        t -> 'Auu____2416 embedding
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
  let uu____2560 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____2560 
let (e_unit : unit embedding) =
  let em a = Constant Unit  in
  let un t = FStar_Pervasives_Native.Some ()  in
  let uu____2581 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  mk_emb em un uu____2581 
let (e_bool : Prims.bool embedding) =
  let em a = Constant (Bool a)  in
  let un t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____2607 -> FStar_Pervasives_Native.None  in
  let uu____2608 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  mk_emb em un uu____2608 
let (e_char : FStar_Char.char embedding) =
  let em c = Constant (Char c)  in
  let un c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____2642 -> FStar_Pervasives_Native.None  in
  let uu____2644 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  mk_emb em un uu____2644 
let (e_string : Prims.string embedding) =
  let em s = Constant (String (s, FStar_Range.dummyRange))  in
  let un s =
    match s with
    | Constant (String (s1,uu____2671)) -> FStar_Pervasives_Native.Some s1
    | uu____2672 -> FStar_Pervasives_Native.None  in
  let uu____2673 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  mk_emb em un uu____2673 
let (e_int : FStar_BigInt.t embedding) =
  let em c = Constant (Int c)  in
  let un c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____2699 -> FStar_Pervasives_Native.None  in
  let uu____2700 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  mk_emb em un uu____2700 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let em o =
      match o with
      | FStar_Pervasives_Native.None  ->
          let uu____2733 =
            let uu____2734 =
              let uu____2739 = type_of ea  in as_iarg uu____2739  in
            [uu____2734]  in
          lid_as_constr FStar_Parser_Const.none_lid
            [FStar_Syntax_Syntax.U_zero] uu____2733
      | FStar_Pervasives_Native.Some x ->
          let uu____2749 =
            let uu____2750 =
              let uu____2755 = type_of ea  in as_iarg uu____2755  in
            let uu____2756 =
              let uu____2763 =
                let uu____2768 = embed ea x  in as_arg uu____2768  in
              [uu____2763]  in
            uu____2750 :: uu____2756  in
          lid_as_constr FStar_Parser_Const.some_lid
            [FStar_Syntax_Syntax.U_zero] uu____2749
       in
    let un trm =
      match trm with
      | Construct (fvar1,us,args) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.none_lid ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | Construct (fvar1,us,uu____2818::(a,uu____2820)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.some_lid ->
          let uu____2847 = unembed ea a  in
          FStar_Util.bind_opt uu____2847
            (fun a1  ->
               FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some a1))
      | uu____2856 -> FStar_Pervasives_Native.None  in
    let uu____2859 =
      let uu____2860 =
        let uu____2861 = let uu____2866 = type_of ea  in as_arg uu____2866
           in
        [uu____2861]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____2860
       in
    mk_emb em un uu____2859
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em x =
        let uu____2925 =
          let uu____2926 = let uu____2931 = type_of ea  in as_iarg uu____2931
             in
          let uu____2932 =
            let uu____2939 =
              let uu____2944 = type_of eb  in as_iarg uu____2944  in
            let uu____2945 =
              let uu____2952 =
                let uu____2957 = embed ea (FStar_Pervasives_Native.fst x)  in
                as_arg uu____2957  in
              let uu____2958 =
                let uu____2965 =
                  let uu____2970 = embed eb (FStar_Pervasives_Native.snd x)
                     in
                  as_arg uu____2970  in
                [uu____2965]  in
              uu____2952 :: uu____2958  in
            uu____2939 :: uu____2945  in
          uu____2926 :: uu____2932  in
        lid_as_constr FStar_Parser_Const.lid_Mktuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____2925
         in
      let un trm =
        match trm with
        | Construct
            (fvar1,us,uu____3011::uu____3012::(a,uu____3014)::(b,uu____3016)::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1
              FStar_Parser_Const.lid_Mktuple2
            ->
            let uu____3055 = unembed ea a  in
            FStar_Util.bind_opt uu____3055
              (fun a1  ->
                 let uu____3065 = unembed eb b  in
                 FStar_Util.bind_opt uu____3065
                   (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
        | uu____3078 -> FStar_Pervasives_Native.None  in
      let uu____3083 =
        let uu____3084 =
          let uu____3085 = let uu____3090 = type_of ea  in as_arg uu____3090
             in
          let uu____3091 =
            let uu____3098 =
              let uu____3103 = type_of eb  in as_arg uu____3103  in
            [uu____3098]  in
          uu____3085 :: uu____3091  in
        lid_as_typ FStar_Parser_Const.lid_tuple2 [FStar_Syntax_Syntax.U_zero]
          uu____3084
         in
      mk_emb em un uu____3083
  
let (e_range : FStar_Range.range embedding) =
  let em r = Constant (Range r)  in
  let un t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____3141 -> FStar_Pervasives_Native.None  in
  let uu____3142 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  mk_emb em un uu____3142 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em l =
      let typ = let uu____3176 = type_of ea  in as_iarg uu____3176  in
      let nil =
        lid_as_constr FStar_Parser_Const.nil_lid [FStar_Syntax_Syntax.U_zero]
          [typ]
         in
      let cons1 hd1 tl1 =
        let uu____3197 =
          let uu____3198 =
            let uu____3205 =
              let uu____3210 = embed ea hd1  in as_arg uu____3210  in
            let uu____3211 = let uu____3218 = as_arg tl1  in [uu____3218]  in
            uu____3205 :: uu____3211  in
          typ :: uu____3198  in
        lid_as_constr FStar_Parser_Const.cons_lid
          [FStar_Syntax_Syntax.U_zero] uu____3197
         in
      FStar_List.fold_right cons1 l nil  in
    let rec un trm =
      match trm with
      | Construct (fv,uu____3254,uu____3255) when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
          FStar_Pervasives_Native.Some []
      | Construct
          (fv,uu____3275,(uu____3276,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____3277))::
           (hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                 )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____3306 = unembed ea hd1  in
          FStar_Util.bind_opt uu____3306
            (fun hd2  ->
               let uu____3314 = un tl1  in
               FStar_Util.bind_opt uu____3314
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | Construct
          (fv,uu____3330,(hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                               )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____3355 = unembed ea hd1  in
          FStar_Util.bind_opt uu____3355
            (fun hd2  ->
               let uu____3363 = un tl1  in
               FStar_Util.bind_opt uu____3363
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | uu____3378 -> FStar_Pervasives_Native.None  in
    let uu____3381 =
      let uu____3382 =
        let uu____3383 = let uu____3388 = type_of ea  in as_arg uu____3388
           in
        [uu____3383]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____3382
       in
    mk_emb em un uu____3381
  
let e_arrow1 : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let em f =
        Lam
          ((fun tas  ->
              let uu____3464 =
                let uu____3467 = FStar_List.hd tas  in unembed ea uu____3467
                 in
              match uu____3464 with
              | FStar_Pervasives_Native.Some a ->
                  let uu____3469 = f a  in embed eb uu____3469
              | FStar_Pervasives_Native.None  ->
                  failwith "cannot unembed function argument"),
            [(fun uu____3479  ->
                let uu____3480 = type_of eb  in as_arg uu____3480)],
            (Prims.parse_int "1"))
         in
      let un lam =
        match lam with
        | Lam (ft,uu____3510,uu____3511) ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____3547 =
                    let uu____3550 =
                      let uu____3551 =
                        let uu____3554 = embed ea x  in [uu____3554]  in
                      ft uu____3551  in
                    unembed eb uu____3550  in
                  match uu____3547 with
                  | FStar_Pervasives_Native.Some x1 -> x1
                  | FStar_Pervasives_Native.None  ->
                      failwith "cannot unembed function result"))
        | uu____3556 -> FStar_Pervasives_Native.None  in
      let uu____3560 =
        let uu____3561 = type_of ea  in
        let uu____3562 = let uu____3563 = type_of eb  in as_iarg uu____3563
           in
        make_arrow1 uu____3561 uu____3562  in
      mk_emb em un uu____3560
  
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
      let uu____3631 = let uu____3640 = e_list e  in unembed uu____3640  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____3631
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____3661  ->
    match uu____3661 with
    | (a,uu____3669) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____3684)::[]) when
             let uu____3701 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____3701 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____3706 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____3748 = let uu____3755 = as_arg c  in [uu____3755]  in
      int_to_t2 uu____3748
  
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
          let uu____3808 = f a  in FStar_Pervasives_Native.Some uu____3808
      | uu____3809 -> FStar_Pervasives_Native.None
  
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
          let uu____3862 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____3862
      | uu____3863 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____3906 = FStar_List.map as_a args  in lift_unary f uu____3906
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____3960 = FStar_List.map as_a args  in
        lift_binary f uu____3960
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____3989 = f x  in embed e_int uu____3989)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  -> fun y  -> let uu____4015 = f x y  in embed e_int uu____4015)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____4034 = f x  in embed e_bool uu____4034)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  -> fun y  -> let uu____4060 = f x y  in embed e_bool uu____4060)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  -> let uu____4086 = f x y  in embed e_string uu____4086)
  
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
                let uu____4188 =
                  let uu____4197 = as_a a  in
                  let uu____4200 = as_b b  in (uu____4197, uu____4200)  in
                (match uu____4188 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____4215 =
                       let uu____4216 = f a1 b1  in embed_c uu____4216  in
                     FStar_Pervasives_Native.Some uu____4215
                 | uu____4217 -> FStar_Pervasives_Native.None)
            | uu____4226 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____4232 = e_list e_char  in
    let uu____4239 = FStar_String.list_of_string s  in
    embed uu____4232 uu____4239
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____4269 =
        let uu____4270 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____4270  in
      embed e_int uu____4269
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____4302 = arg_as_string a1  in
        (match uu____4302 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4308 = arg_as_list e_string a2  in
             (match uu____4308 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____4321 = embed e_string r  in
                  FStar_Pervasives_Native.Some uu____4321
              | uu____4322 -> FStar_Pervasives_Native.None)
         | uu____4327 -> FStar_Pervasives_Native.None)
    | uu____4330 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____4336 = FStar_BigInt.string_of_big_int i  in
    embed e_string uu____4336
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string (if b then "true" else "false") 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool true  in
      let fal = embed e_bool false  in
      match args with
      | (_univ,uu____4362)::(_typ,uu____4364)::(a1,uu____4366)::(a2,uu____4368)::[]
          ->
          let uu____4389 = eq_t a1 a2  in
          (match uu____4389 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____4394 -> FStar_Pervasives_Native.None)
      | uu____4395 -> failwith "Unexpected number of arguments"
  
let (interp_prop : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____4408)::(_typ,uu____4410)::(a1,uu____4412)::(a2,uu____4414)::[]
        ->
        let uu____4435 = eq_t a1 a2  in
        (match uu____4435 with
         | FStar_Syntax_Util.Equal  ->
             let uu____4438 = embed e_bool true  in
             FStar_Pervasives_Native.Some uu____4438
         | FStar_Syntax_Util.NotEqual  ->
             let uu____4439 = embed e_bool false  in
             FStar_Pervasives_Native.Some uu____4439
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____4440 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____4457 =
        let uu____4458 = FStar_Ident.string_of_lid lid  in
        Prims.strcat "No interpretation for " uu____4458  in
      failwith uu____4457
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____4471)::[] ->
        let uu____4480 = unembed e_range a1  in
        (match uu____4480 with
         | FStar_Pervasives_Native.Some r ->
             let uu____4486 = embed e_range r  in
             FStar_Pervasives_Native.Some uu____4486
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____4487 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____4521 = arg_as_list e_char a1  in
        (match uu____4521 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4537 = arg_as_string a2  in
             (match uu____4537 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____4546 =
                    let uu____4547 = e_list e_string  in embed uu____4547 r
                     in
                  FStar_Pervasives_Native.Some uu____4546
              | uu____4554 -> FStar_Pervasives_Native.None)
         | uu____4557 -> FStar_Pervasives_Native.None)
    | uu____4563 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____4604 =
          let uu____4617 = arg_as_string a1  in
          let uu____4620 = arg_as_int a2  in
          let uu____4623 = arg_as_int a3  in
          (uu____4617, uu____4620, uu____4623)  in
        (match uu____4604 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                let r = FStar_String.substring s1 n11 n21  in
                let uu____4654 = embed e_string r  in
                FStar_Pervasives_Native.Some uu____4654
              with | uu____4660 -> FStar_Pervasives_Native.None)
         | uu____4661 -> FStar_Pervasives_Native.None)
    | uu____4674 -> FStar_Pervasives_Native.None
  