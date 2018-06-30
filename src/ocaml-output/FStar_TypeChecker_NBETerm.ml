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
    match projectee with | Var _0 -> true | uu____379 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____410 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t,t -> t,(t -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.branch Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Rec : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____485 -> false
  
let (__proj__Rec__item___0 :
  atom ->
    (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
      t Prims.list) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____549 -> false
  
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
    match projectee with | Accu _0 -> true | uu____633 -> false
  
let (__proj__Accu__item___0 :
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____691 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____761 -> false 
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
    match projectee with | Constant _0 -> true | uu____817 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____831 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____845 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____858 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____883 -> false
  
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
    match projectee with | Refinement _0 -> true | uu____965 -> false
  
let (__proj__Refinement__item___0 :
  t ->
    (t -> t,unit ->
              (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____1027 -> false
  
let (__proj__Tot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1065 -> false
  
let (__proj__GTot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1097 -> false
  
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
  fun trm  -> match trm with | Accu uu____1228 -> true | uu____1239 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____1245,uu____1246) -> false | uu____1259 -> true
  
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
  fun uu___222_1425  ->
    if uu___222_1425
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___223_1431  ->
    if uu___223_1431
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
      | (FStar_Syntax_Util.NotEqual ,uu____1443) ->
          FStar_Syntax_Util.NotEqual
      | (uu____1444,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____1445) -> FStar_Syntax_Util.Unknown
      | (uu____1446,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____1462 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____1478),String (s2,uu____1480)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____1488,uu____1489) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____1524,Lam uu____1525) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____1594 = eq_atom a1 a2  in
          eq_and uu____1594 (fun uu____1596  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____1635 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1635
          then
            let uu____1636 =
              let uu____1637 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____1637  in
            eq_and uu____1636 (fun uu____1639  -> eq_args args1 args2)
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____1679 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1679
          then
            let uu____1680 =
              let uu____1681 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____1681  in
            eq_and uu____1680 (fun uu____1683  -> eq_args args1 args2)
          else FStar_Syntax_Util.NotEqual
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____1689 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1689
      | (Univ u1,Univ u2) ->
          let uu____1692 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1692
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____1738 =
            let uu____1739 =
              let uu____1740 = t11 ()  in
              FStar_Pervasives_Native.fst uu____1740  in
            let uu____1745 =
              let uu____1746 = t11 ()  in
              FStar_Pervasives_Native.fst uu____1746  in
            eq_t uu____1739 uu____1745  in
          eq_and uu____1738
            (fun uu____1754  ->
               let uu____1755 =
                 let uu____1756 = mkAccuVar x  in r1 uu____1756  in
               let uu____1757 =
                 let uu____1758 = mkAccuVar x  in r2 uu____1758  in
               eq_t uu____1755 uu____1757)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____1759,uu____1760) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____1765,uu____1766) -> FStar_Syntax_Util.Unknown

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
          let uu____1847 = eq_arg x y  in
          eq_and uu____1847 (fun uu____1849  -> eq_args xs ys)
      | (uu____1850,uu____1851) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____1887) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____1889 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____1889
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam uu____1907 -> "Lam"
    | Accu (a,l) ->
        let uu____1942 =
          let uu____1943 = atom_to_string a  in
          let uu____1944 =
            let uu____1945 =
              let uu____1946 =
                let uu____1947 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____1947  in
              Prims.strcat uu____1946 ")"  in
            Prims.strcat ") (" uu____1945  in
          Prims.strcat uu____1943 uu____1944  in
        Prims.strcat "Accu (" uu____1942
    | Construct (fv,us,l) ->
        let uu____1979 =
          let uu____1980 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____1981 =
            let uu____1982 =
              let uu____1983 =
                let uu____1984 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____1984  in
              let uu____1987 =
                let uu____1988 =
                  let uu____1989 =
                    let uu____1990 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____1990  in
                  Prims.strcat uu____1989 "]"  in
                Prims.strcat "] [" uu____1988  in
              Prims.strcat uu____1983 uu____1987  in
            Prims.strcat ") [" uu____1982  in
          Prims.strcat uu____1980 uu____1981  in
        Prims.strcat "Construct (" uu____1979
    | FV (fv,us,l) ->
        let uu____2022 =
          let uu____2023 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2024 =
            let uu____2025 =
              let uu____2026 =
                let uu____2027 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2027  in
              let uu____2030 =
                let uu____2031 =
                  let uu____2032 =
                    let uu____2033 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2033  in
                  Prims.strcat uu____2032 "]"  in
                Prims.strcat "] [" uu____2031  in
              Prims.strcat uu____2026 uu____2030  in
            Prims.strcat ") [" uu____2025  in
          Prims.strcat uu____2023 uu____2024  in
        Prims.strcat "FV (" uu____2022
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____2048 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____2048
    | Type_t u ->
        let uu____2050 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____2050
    | Arrow uu____2051 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____2094 = t ()  in FStar_Pervasives_Native.fst uu____2094
           in
        let uu____2099 =
          let uu____2100 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____2101 =
            let uu____2102 =
              let uu____2103 = t_to_string t1  in
              let uu____2104 =
                let uu____2105 =
                  let uu____2106 =
                    let uu____2107 =
                      let uu____2108 = mkAccuVar x1  in f uu____2108  in
                    t_to_string uu____2107  in
                  Prims.strcat uu____2106 "}"  in
                Prims.strcat "{" uu____2105  in
              Prims.strcat uu____2103 uu____2104  in
            Prims.strcat ":" uu____2102  in
          Prims.strcat uu____2100 uu____2101  in
        Prims.strcat "Refinement " uu____2099
    | Unknown  -> "Unknown"

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____2111 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____2111
    | Match (t,uu____2113,uu____2114) ->
        let uu____2137 = t_to_string t  in Prims.strcat "Match " uu____2137
    | Rec (uu____2138,uu____2139,l) ->
        let uu____2149 =
          let uu____2150 =
            let uu____2151 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____2151  in
          Prims.strcat uu____2150 ")"  in
        Prims.strcat "Rec (" uu____2149

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____2155 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____2155 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____2161 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____2161 (FStar_String.concat " ")

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
  'Auu____2352 .
    ('Auu____2352 -> t) ->
      (t -> 'Auu____2352 FStar_Pervasives_Native.option) ->
        t -> 'Auu____2352 embedding
  = fun em  -> fun un  -> fun typ  -> { em; un; typ } 
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2403 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____2403 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2423 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkConstruct uu____2423 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____2459  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____2472  -> a)])
  
let (e_any : t embedding) =
  let em a = a  in
  let un t = FStar_Pervasives_Native.Some t  in
  let uu____2496 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____2496 
let (e_unit : unit embedding) =
  let em a = Constant Unit  in
  let un t = FStar_Pervasives_Native.Some ()  in
  let uu____2517 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  mk_emb em un uu____2517 
let (e_bool : Prims.bool embedding) =
  let em a = Constant (Bool a)  in
  let un t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____2543 -> FStar_Pervasives_Native.None  in
  let uu____2544 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  mk_emb em un uu____2544 
let (e_char : FStar_Char.char embedding) =
  let em c = Constant (Char c)  in
  let un c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____2578 -> FStar_Pervasives_Native.None  in
  let uu____2580 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  mk_emb em un uu____2580 
let (e_string : Prims.string embedding) =
  let em s = Constant (String (s, FStar_Range.dummyRange))  in
  let un s =
    match s with
    | Constant (String (s1,uu____2607)) -> FStar_Pervasives_Native.Some s1
    | uu____2608 -> FStar_Pervasives_Native.None  in
  let uu____2609 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  mk_emb em un uu____2609 
let (e_int : FStar_BigInt.t embedding) =
  let em c = Constant (Int c)  in
  let un c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____2635 -> FStar_Pervasives_Native.None  in
  let uu____2636 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  mk_emb em un uu____2636 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let em o =
      match o with
      | FStar_Pervasives_Native.None  ->
          let uu____2669 =
            let uu____2670 =
              let uu____2675 = type_of ea  in as_iarg uu____2675  in
            [uu____2670]  in
          lid_as_constr FStar_Parser_Const.none_lid
            [FStar_Syntax_Syntax.U_zero] uu____2669
      | FStar_Pervasives_Native.Some x ->
          let uu____2685 =
            let uu____2686 =
              let uu____2691 = type_of ea  in as_iarg uu____2691  in
            let uu____2692 =
              let uu____2699 =
                let uu____2704 = embed ea x  in as_arg uu____2704  in
              [uu____2699]  in
            uu____2686 :: uu____2692  in
          lid_as_constr FStar_Parser_Const.some_lid
            [FStar_Syntax_Syntax.U_zero] uu____2685
       in
    let un trm =
      match trm with
      | Construct (fvar1,us,args) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.none_lid ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | Construct (fvar1,us,uu____2754::(a,uu____2756)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.some_lid ->
          let uu____2783 = unembed ea a  in
          FStar_Util.bind_opt uu____2783
            (fun a1  ->
               FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some a1))
      | uu____2792 -> FStar_Pervasives_Native.None  in
    let uu____2795 =
      let uu____2796 =
        let uu____2797 = let uu____2802 = type_of ea  in as_arg uu____2802
           in
        [uu____2797]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____2796
       in
    mk_emb em un uu____2795
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em x =
        let uu____2861 =
          let uu____2862 = let uu____2867 = type_of ea  in as_iarg uu____2867
             in
          let uu____2868 =
            let uu____2875 =
              let uu____2880 = type_of eb  in as_iarg uu____2880  in
            let uu____2881 =
              let uu____2888 =
                let uu____2893 = embed ea (FStar_Pervasives_Native.fst x)  in
                as_arg uu____2893  in
              let uu____2894 =
                let uu____2901 =
                  let uu____2906 = embed eb (FStar_Pervasives_Native.snd x)
                     in
                  as_arg uu____2906  in
                [uu____2901]  in
              uu____2888 :: uu____2894  in
            uu____2875 :: uu____2881  in
          uu____2862 :: uu____2868  in
        lid_as_constr FStar_Parser_Const.lid_Mktuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____2861
         in
      let un trm =
        match trm with
        | Construct
            (fvar1,us,uu____2947::uu____2948::(a,uu____2950)::(b,uu____2952)::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1
              FStar_Parser_Const.lid_Mktuple2
            ->
            let uu____2991 = unembed ea a  in
            FStar_Util.bind_opt uu____2991
              (fun a1  ->
                 let uu____3001 = unembed eb b  in
                 FStar_Util.bind_opt uu____3001
                   (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
        | uu____3014 -> FStar_Pervasives_Native.None  in
      let uu____3019 =
        let uu____3020 =
          let uu____3021 = let uu____3026 = type_of ea  in as_arg uu____3026
             in
          let uu____3027 =
            let uu____3034 =
              let uu____3039 = type_of eb  in as_arg uu____3039  in
            [uu____3034]  in
          uu____3021 :: uu____3027  in
        lid_as_typ FStar_Parser_Const.lid_tuple2 [FStar_Syntax_Syntax.U_zero]
          uu____3020
         in
      mk_emb em un uu____3019
  
let (e_range : FStar_Range.range embedding) =
  let em r = Constant (Range r)  in
  let un t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____3077 -> FStar_Pervasives_Native.None  in
  let uu____3078 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  mk_emb em un uu____3078 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em l =
      let typ = let uu____3112 = type_of ea  in as_iarg uu____3112  in
      let nil =
        lid_as_constr FStar_Parser_Const.nil_lid [FStar_Syntax_Syntax.U_zero]
          [typ]
         in
      let cons1 hd1 tl1 =
        let uu____3133 =
          let uu____3134 =
            let uu____3141 =
              let uu____3146 = embed ea hd1  in as_arg uu____3146  in
            let uu____3147 = let uu____3154 = as_arg tl1  in [uu____3154]  in
            uu____3141 :: uu____3147  in
          typ :: uu____3134  in
        lid_as_constr FStar_Parser_Const.cons_lid
          [FStar_Syntax_Syntax.U_zero] uu____3133
         in
      FStar_List.fold_right cons1 l nil  in
    let rec un trm =
      match trm with
      | Construct (fv,uu____3190,uu____3191) when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
          FStar_Pervasives_Native.Some []
      | Construct
          (fv,uu____3211,(uu____3212,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____3213))::
           (hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                 )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____3242 = unembed ea hd1  in
          FStar_Util.bind_opt uu____3242
            (fun hd2  ->
               let uu____3250 = un tl1  in
               FStar_Util.bind_opt uu____3250
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | Construct
          (fv,uu____3266,(hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                               )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____3291 = unembed ea hd1  in
          FStar_Util.bind_opt uu____3291
            (fun hd2  ->
               let uu____3299 = un tl1  in
               FStar_Util.bind_opt uu____3299
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | uu____3314 -> FStar_Pervasives_Native.None  in
    let uu____3317 =
      let uu____3318 =
        let uu____3319 = let uu____3324 = type_of ea  in as_arg uu____3324
           in
        [uu____3319]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____3318
       in
    mk_emb em un uu____3317
  
let e_arrow1 : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let em f =
        Lam
          ((fun tas  ->
              let uu____3400 =
                let uu____3403 = FStar_List.hd tas  in unembed ea uu____3403
                 in
              match uu____3400 with
              | FStar_Pervasives_Native.Some a ->
                  let uu____3405 = f a  in embed eb uu____3405
              | FStar_Pervasives_Native.None  ->
                  failwith "cannot unembed function argument"),
            [(fun uu____3415  ->
                let uu____3416 = type_of eb  in as_arg uu____3416)],
            (Prims.parse_int "1"))
         in
      let un lam =
        match lam with
        | Lam (ft,uu____3446,uu____3447) ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____3483 =
                    let uu____3486 =
                      let uu____3487 =
                        let uu____3490 = embed ea x  in [uu____3490]  in
                      ft uu____3487  in
                    unembed eb uu____3486  in
                  match uu____3483 with
                  | FStar_Pervasives_Native.Some x1 -> x1
                  | FStar_Pervasives_Native.None  ->
                      failwith "cannot unembed function result"))
        | uu____3492 -> FStar_Pervasives_Native.None  in
      let uu____3496 =
        let uu____3497 = type_of ea  in
        let uu____3498 = let uu____3499 = type_of eb  in as_iarg uu____3499
           in
        make_arrow1 uu____3497 uu____3498  in
      mk_emb em un uu____3496
  
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
      let uu____3567 = let uu____3576 = e_list e  in unembed uu____3576  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____3567
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____3597  ->
    match uu____3597 with
    | (a,uu____3605) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____3620)::[]) when
             let uu____3637 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____3637 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____3642 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____3684 = let uu____3691 = as_arg c  in [uu____3691]  in
      int_to_t2 uu____3684
  
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
          let uu____3744 = f a  in FStar_Pervasives_Native.Some uu____3744
      | uu____3745 -> FStar_Pervasives_Native.None
  
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
          let uu____3798 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____3798
      | uu____3799 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____3842 = FStar_List.map as_a args  in lift_unary f uu____3842
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____3896 = FStar_List.map as_a args  in
        lift_binary f uu____3896
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____3925 = f x  in embed e_int uu____3925)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  -> fun y  -> let uu____3951 = f x y  in embed e_int uu____3951)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____3970 = f x  in embed e_bool uu____3970)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  -> fun y  -> let uu____3996 = f x y  in embed e_bool uu____3996)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  -> let uu____4022 = f x y  in embed e_string uu____4022)
  
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
                let uu____4124 =
                  let uu____4133 = as_a a  in
                  let uu____4136 = as_b b  in (uu____4133, uu____4136)  in
                (match uu____4124 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____4151 =
                       let uu____4152 = f a1 b1  in embed_c uu____4152  in
                     FStar_Pervasives_Native.Some uu____4151
                 | uu____4153 -> FStar_Pervasives_Native.None)
            | uu____4162 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____4168 = e_list e_char  in
    let uu____4175 = FStar_String.list_of_string s  in
    embed uu____4168 uu____4175
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____4205 =
        let uu____4206 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____4206  in
      embed e_int uu____4205
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____4238 = arg_as_string a1  in
        (match uu____4238 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4244 = arg_as_list e_string a2  in
             (match uu____4244 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____4257 = embed e_string r  in
                  FStar_Pervasives_Native.Some uu____4257
              | uu____4258 -> FStar_Pervasives_Native.None)
         | uu____4263 -> FStar_Pervasives_Native.None)
    | uu____4266 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____4272 = FStar_BigInt.string_of_big_int i  in
    embed e_string uu____4272
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string (if b then "true" else "false") 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool true  in
      let fal = embed e_bool false  in
      match args with
      | (_univ,uu____4298)::(_typ,uu____4300)::(a1,uu____4302)::(a2,uu____4304)::[]
          ->
          let uu____4325 = eq_t a1 a2  in
          (match uu____4325 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____4330 -> FStar_Pervasives_Native.None)
      | uu____4331 -> failwith "Unexpected number of arguments"
  
let (interp_prop : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____4344)::(_typ,uu____4346)::(a1,uu____4348)::(a2,uu____4350)::[]
        ->
        let uu____4371 = eq_t a1 a2  in
        (match uu____4371 with
         | FStar_Syntax_Util.Equal  ->
             let uu____4374 = embed e_bool true  in
             FStar_Pervasives_Native.Some uu____4374
         | FStar_Syntax_Util.NotEqual  ->
             let uu____4375 = embed e_bool false  in
             FStar_Pervasives_Native.Some uu____4375
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____4376 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____4393 =
        let uu____4394 = FStar_Ident.string_of_lid lid  in
        Prims.strcat "No interpretation for " uu____4394  in
      failwith uu____4393
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____4407)::[] ->
        let uu____4416 = unembed e_range a1  in
        (match uu____4416 with
         | FStar_Pervasives_Native.Some r ->
             let uu____4422 = embed e_range r  in
             FStar_Pervasives_Native.Some uu____4422
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____4423 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____4457 = arg_as_list e_char a1  in
        (match uu____4457 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4473 = arg_as_string a2  in
             (match uu____4473 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____4482 =
                    let uu____4483 = e_list e_string  in embed uu____4483 r
                     in
                  FStar_Pervasives_Native.Some uu____4482
              | uu____4490 -> FStar_Pervasives_Native.None)
         | uu____4493 -> FStar_Pervasives_Native.None)
    | uu____4499 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____4540 =
          let uu____4553 = arg_as_string a1  in
          let uu____4556 = arg_as_int a2  in
          let uu____4559 = arg_as_int a3  in
          (uu____4553, uu____4556, uu____4559)  in
        (match uu____4540 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                let r = FStar_String.substring s1 n11 n21  in
                let uu____4590 = embed e_string r  in
                FStar_Pervasives_Native.Some uu____4590
              with | uu____4596 -> FStar_Pervasives_Native.None)
         | uu____4597 -> FStar_Pervasives_Native.None)
    | uu____4610 -> FStar_Pervasives_Native.None
  