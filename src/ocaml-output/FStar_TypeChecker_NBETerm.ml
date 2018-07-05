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
and t =
  | Lam of
  (t Prims.list -> t,(t Prims.list ->
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
  (t Prims.list -> comp,(t Prims.list ->
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
  | Rec of
  (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
  t Prims.list,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
                 Prims.list,Prims.int,Prims.bool Prims.list,t Prims.list ->
                                                              FStar_Syntax_Syntax.letbinding
                                                                -> t)
  FStar_Pervasives_Native.tuple7 
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
    match projectee with | Var _0 -> true | uu____423 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____454 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t,t -> t,(t -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.branch Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____541 -> false
  
let (__proj__Lam__item___0 :
  t ->
    (t Prims.list -> t,(t Prims.list ->
                          (t,FStar_Syntax_Syntax.aqual)
                            FStar_Pervasives_Native.tuple2)
                         Prims.list,Prims.int)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____631 -> false
  
let (__proj__Accu__item___0 :
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____689 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____759 -> false 
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
    match projectee with | Constant _0 -> true | uu____815 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____829 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____843 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____856 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____883 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    (t Prims.list -> comp,(t Prims.list ->
                             (t,FStar_Syntax_Syntax.aqual)
                               FStar_Pervasives_Native.tuple2)
                            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____971 -> false
  
let (__proj__Refinement__item___0 :
  t ->
    (t -> t,unit ->
              (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1031 -> false
  
let (__proj__Quote__item___0 :
  t ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.quoteinfo)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1057 -> false
  
let (__proj__Lazy__item___0 : t -> FStar_Syntax_Syntax.lazyinfo) =
  fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____1105 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
      t Prims.list,(t,FStar_Syntax_Syntax.aqual)
                     FStar_Pervasives_Native.tuple2 Prims.list,Prims.int,
      Prims.bool Prims.list,t Prims.list ->
                              FStar_Syntax_Syntax.letbinding -> t)
      FStar_Pervasives_Native.tuple7)
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____1227 -> false
  
let (__proj__Tot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1265 -> false
  
let (__proj__GTot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1297 -> false
  
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
  fun trm  -> match trm with | Accu uu____1428 -> true | uu____1439 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____1445,uu____1446) -> false | uu____1459 -> true
  
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
let (equal_if : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___227_1588  ->
    if uu___227_1588
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___228_1594  ->
    if uu___228_1594
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
      | (FStar_Syntax_Util.NotEqual ,uu____1606) ->
          FStar_Syntax_Util.NotEqual
      | (uu____1607,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____1608) -> FStar_Syntax_Util.Unknown
      | (uu____1609,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____1625 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____1641),String (s2,uu____1643)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____1651,uu____1652) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____1687,Lam uu____1688) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____1761 = eq_atom a1 a2  in
          eq_and uu____1761 (fun uu____1763  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____1802 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1802
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____1813 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____1870  ->
                        match uu____1870 with
                        | ((a1,uu____1884),(a2,uu____1886)) ->
                            let uu____1895 = eq_t a1 a2  in
                            eq_inj acc uu____1895) FStar_Syntax_Util.Equal)
                uu____1813))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____1935 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1935
          then
            let uu____1936 =
              let uu____1937 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____1937  in
            eq_and uu____1936 (fun uu____1939  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____1945 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1945
      | (Univ u1,Univ u2) ->
          let uu____1948 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1948
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____1994 =
            let uu____1995 =
              let uu____1996 = t11 ()  in
              FStar_Pervasives_Native.fst uu____1996  in
            let uu____2001 =
              let uu____2002 = t21 ()  in
              FStar_Pervasives_Native.fst uu____2002  in
            eq_t uu____1995 uu____2001  in
          eq_and uu____1994
            (fun uu____2010  ->
               let uu____2011 =
                 let uu____2012 = mkAccuVar x  in r1 uu____2012  in
               let uu____2013 =
                 let uu____2014 = mkAccuVar x  in r2 uu____2014  in
               eq_t uu____2011 uu____2013)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____2015,uu____2016) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____2021,uu____2022) -> FStar_Syntax_Util.Unknown

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
          let uu____2103 = eq_arg x y  in
          eq_and uu____2103 (fun uu____2105  -> eq_args xs ys)
      | (uu____2106,uu____2107) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____2143) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____2145 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____2145
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity) ->
        let uu____2198 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____2208 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____2198 uu____2208
    | Accu (a,l) ->
        let uu____2223 =
          let uu____2224 = atom_to_string a  in
          let uu____2225 =
            let uu____2226 =
              let uu____2227 =
                let uu____2228 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____2228  in
              Prims.strcat uu____2227 ")"  in
            Prims.strcat ") (" uu____2226  in
          Prims.strcat uu____2224 uu____2225  in
        Prims.strcat "Accu (" uu____2223
    | Construct (fv,us,l) ->
        let uu____2260 =
          let uu____2261 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2262 =
            let uu____2263 =
              let uu____2264 =
                let uu____2265 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2265  in
              let uu____2268 =
                let uu____2269 =
                  let uu____2270 =
                    let uu____2271 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2271  in
                  Prims.strcat uu____2270 "]"  in
                Prims.strcat "] [" uu____2269  in
              Prims.strcat uu____2264 uu____2268  in
            Prims.strcat ") [" uu____2263  in
          Prims.strcat uu____2261 uu____2262  in
        Prims.strcat "Construct (" uu____2260
    | FV (fv,us,l) ->
        let uu____2303 =
          let uu____2304 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2305 =
            let uu____2306 =
              let uu____2307 =
                let uu____2308 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2308  in
              let uu____2311 =
                let uu____2312 =
                  let uu____2313 =
                    let uu____2314 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2314  in
                  Prims.strcat uu____2313 "]"  in
                Prims.strcat "] [" uu____2312  in
              Prims.strcat uu____2307 uu____2311  in
            Prims.strcat ") [" uu____2306  in
          Prims.strcat uu____2304 uu____2305  in
        Prims.strcat "FV (" uu____2303
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____2329 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____2329
    | Type_t u ->
        let uu____2331 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____2331
    | Arrow uu____2332 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____2377 = t ()  in FStar_Pervasives_Native.fst uu____2377
           in
        let uu____2382 =
          let uu____2383 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____2384 =
            let uu____2385 =
              let uu____2386 = t_to_string t1  in
              let uu____2387 =
                let uu____2388 =
                  let uu____2389 =
                    let uu____2390 =
                      let uu____2391 = mkAccuVar x1  in f uu____2391  in
                    t_to_string uu____2390  in
                  Prims.strcat uu____2389 "}"  in
                Prims.strcat "{" uu____2388  in
              Prims.strcat uu____2386 uu____2387  in
            Prims.strcat ":" uu____2385  in
          Prims.strcat uu____2383 uu____2384  in
        Prims.strcat "Refinement " uu____2382
    | Unknown  -> "Unknown"
    | Quote uu____2392 -> "Quote _"
    | Lazy uu____2397 -> "Lazy _"
    | Rec
        (uu____2398,uu____2399,l,uu____2401,uu____2402,uu____2403,uu____2404)
        ->
        let uu____2445 =
          let uu____2446 =
            let uu____2447 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____2447  in
          Prims.strcat uu____2446 ")"  in
        Prims.strcat "Rec (" uu____2445

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____2452 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____2452
    | Match (t,uu____2454,uu____2455) ->
        let uu____2478 = t_to_string t  in Prims.strcat "Match " uu____2478

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____2480 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____2480 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____2486 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____2486 (FStar_String.concat " ")

type iapp_cb = t -> args -> t
type 'a embedding =
  {
  em: iapp_cb -> 'a -> t ;
  un: iapp_cb -> t -> 'a FStar_Pervasives_Native.option ;
  typ: t }
let __proj__Mkembedding__item__em : 'a . 'a embedding -> iapp_cb -> 'a -> t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__em
  
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> iapp_cb -> t -> 'a FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__un
  
let __proj__Mkembedding__item__typ : 'a . 'a embedding -> t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__typ
  
let embed : 'a . 'a embedding -> iapp_cb -> 'a -> t =
  fun e  -> fun cb  -> fun x  -> e.em cb x 
let unembed :
  'a . 'a embedding -> iapp_cb -> t -> 'a FStar_Pervasives_Native.option =
  fun e  -> fun cb  -> fun trm  -> e.un cb trm 
let type_of : 'a . 'a embedding -> t = fun e  -> e.typ 
let mk_emb :
  'a .
    (iapp_cb -> 'a -> t) ->
      (iapp_cb -> t -> 'a FStar_Pervasives_Native.option) ->
        t -> 'a embedding
  = fun em  -> fun un  -> fun typ  -> { em; un; typ } 
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2878 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____2878 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2898 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____2898 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____2936  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____2951  -> a)])
  
let (e_any : t embedding) =
  let em _cb a = a  in
  let un _cb t = FStar_Pervasives_Native.Some t  in
  let uu____3011 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____3011 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____3064 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  mk_emb em un uu____3064 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____3120 -> FStar_Pervasives_Native.None  in
  let uu____3121 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  mk_emb em un uu____3121 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____3185 -> FStar_Pervasives_Native.None  in
  let uu____3187 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  mk_emb em un uu____3187 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____3244)) -> FStar_Pervasives_Native.Some s1
    | uu____3245 -> FStar_Pervasives_Native.None  in
  let uu____3246 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  mk_emb em un uu____3246 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____3302 -> FStar_Pervasives_Native.None  in
  let uu____3303 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  mk_emb em un uu____3303 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let em cb o =
      match o with
      | FStar_Pervasives_Native.None  ->
          let uu____3351 =
            let uu____3352 =
              let uu____3357 = type_of ea  in as_iarg uu____3357  in
            [uu____3352]  in
          lid_as_constr FStar_Parser_Const.none_lid
            [FStar_Syntax_Syntax.U_zero] uu____3351
      | FStar_Pervasives_Native.Some x ->
          let uu____3367 =
            let uu____3368 =
              let uu____3373 = embed ea cb x  in as_arg uu____3373  in
            let uu____3378 =
              let uu____3385 =
                let uu____3390 = type_of ea  in as_iarg uu____3390  in
              [uu____3385]  in
            uu____3368 :: uu____3378  in
          lid_as_constr FStar_Parser_Const.some_lid
            [FStar_Syntax_Syntax.U_zero] uu____3367
       in
    let un cb trm =
      match trm with
      | Construct (fvar1,us,args) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.none_lid ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | Construct (fvar1,us,(a,uu____3456)::uu____3457::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.some_lid ->
          let uu____3484 = unembed ea cb a  in
          FStar_Util.bind_opt uu____3484
            (fun a1  ->
               FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some a1))
      | uu____3497 -> FStar_Pervasives_Native.None  in
    let uu____3500 =
      let uu____3501 =
        let uu____3502 = let uu____3507 = type_of ea  in as_arg uu____3507
           in
        [uu____3502]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____3501
       in
    mk_emb em un uu____3500
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em cb x =
        let uu____3581 =
          let uu____3582 =
            let uu____3587 = embed eb cb (FStar_Pervasives_Native.snd x)  in
            as_arg uu____3587  in
          let uu____3592 =
            let uu____3599 =
              let uu____3604 = embed ea cb (FStar_Pervasives_Native.fst x)
                 in
              as_arg uu____3604  in
            let uu____3609 =
              let uu____3616 =
                let uu____3621 = type_of eb  in as_iarg uu____3621  in
              let uu____3622 =
                let uu____3629 =
                  let uu____3634 = type_of ea  in as_iarg uu____3634  in
                [uu____3629]  in
              uu____3616 :: uu____3622  in
            uu____3599 :: uu____3609  in
          uu____3582 :: uu____3592  in
        lid_as_constr FStar_Parser_Const.lid_Mktuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____3581
         in
      let un cb trm =
        match trm with
        | Construct
            (fvar1,us,(b,uu____3691)::(a,uu____3693)::uu____3694::uu____3695::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1
              FStar_Parser_Const.lid_Mktuple2
            ->
            let uu____3734 = unembed ea cb a  in
            FStar_Util.bind_opt uu____3734
              (fun a1  ->
                 let uu____3748 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____3748
                   (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
        | uu____3765 -> FStar_Pervasives_Native.None  in
      let uu____3770 =
        let uu____3771 =
          let uu____3772 = let uu____3777 = type_of eb  in as_arg uu____3777
             in
          let uu____3778 =
            let uu____3785 =
              let uu____3790 = type_of ea  in as_arg uu____3790  in
            [uu____3785]  in
          uu____3772 :: uu____3778  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____3771
         in
      mk_emb em un uu____3770
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let em cb s =
        match s with
        | FStar_Util.Inl a ->
            let uu____3871 =
              let uu____3872 =
                let uu____3877 = embed ea cb a  in as_arg uu____3877  in
              let uu____3882 =
                let uu____3889 =
                  let uu____3894 = type_of eb  in as_iarg uu____3894  in
                let uu____3895 =
                  let uu____3902 =
                    let uu____3907 = type_of ea  in as_iarg uu____3907  in
                  [uu____3902]  in
                uu____3889 :: uu____3895  in
              uu____3872 :: uu____3882  in
            lid_as_constr FStar_Parser_Const.inl_lid
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
              uu____3871
        | FStar_Util.Inr b ->
            let uu____3925 =
              let uu____3926 =
                let uu____3931 = embed eb cb b  in as_arg uu____3931  in
              let uu____3936 =
                let uu____3943 =
                  let uu____3948 = type_of eb  in as_iarg uu____3948  in
                let uu____3949 =
                  let uu____3956 =
                    let uu____3961 = type_of ea  in as_iarg uu____3961  in
                  [uu____3956]  in
                uu____3943 :: uu____3949  in
              uu____3926 :: uu____3936  in
            lid_as_constr FStar_Parser_Const.inr_lid
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
              uu____3925
         in
      let un cb trm =
        match trm with
        | Construct (fvar1,us,(a,uu____4014)::uu____4015::uu____4016::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.inl_lid ->
            let uu____4051 = unembed ea cb a  in
            FStar_Util.bind_opt uu____4051
              (fun a1  -> FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
        | Construct (fvar1,us,(b,uu____4071)::uu____4072::uu____4073::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.inr_lid ->
            let uu____4108 = unembed eb cb b  in
            FStar_Util.bind_opt uu____4108
              (fun b1  -> FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
        | uu____4125 -> FStar_Pervasives_Native.None  in
      let uu____4130 =
        let uu____4131 =
          let uu____4132 = let uu____4137 = type_of eb  in as_arg uu____4137
             in
          let uu____4138 =
            let uu____4145 =
              let uu____4150 = type_of ea  in as_arg uu____4150  in
            [uu____4145]  in
          uu____4132 :: uu____4138  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____4131
         in
      mk_emb em un uu____4130
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____4218 -> FStar_Pervasives_Native.None  in
  let uu____4219 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  mk_emb em un uu____4219 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em cb l =
      let typ = let uu____4268 = type_of ea  in as_iarg uu____4268  in
      let nil =
        lid_as_constr FStar_Parser_Const.nil_lid [FStar_Syntax_Syntax.U_zero]
          [typ]
         in
      let cons1 hd1 tl1 =
        let uu____4289 =
          let uu____4290 = as_arg tl1  in
          let uu____4295 =
            let uu____4302 =
              let uu____4307 = embed ea cb hd1  in as_arg uu____4307  in
            [uu____4302; typ]  in
          uu____4290 :: uu____4295  in
        lid_as_constr FStar_Parser_Const.cons_lid
          [FStar_Syntax_Syntax.U_zero] uu____4289
         in
      FStar_List.fold_right cons1 l nil  in
    let rec un cb trm =
      match trm with
      | Construct (fv,uu____4358,uu____4359) when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
          FStar_Pervasives_Native.Some []
      | Construct
          (fv,uu____4379,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                               )::(uu____4382,FStar_Pervasives_Native.Some
                                                                   (FStar_Syntax_Syntax.Implicit
                                                                   uu____4383))::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____4410 = unembed ea cb hd1  in
          FStar_Util.bind_opt uu____4410
            (fun hd2  ->
               let uu____4422 = un cb tl1  in
               FStar_Util.bind_opt uu____4422
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | Construct
          (fv,uu____4444,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                               )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____4469 = unembed ea cb hd1  in
          FStar_Util.bind_opt uu____4469
            (fun hd2  ->
               let uu____4481 = un cb tl1  in
               FStar_Util.bind_opt uu____4481
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | uu____4502 -> FStar_Pervasives_Native.None  in
    let uu____4505 =
      let uu____4506 =
        let uu____4507 = let uu____4512 = type_of ea  in as_arg uu____4512
           in
        [uu____4507]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____4506
       in
    mk_emb em un uu____4505
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow1 : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let em cb f =
        Lam
          ((fun tas  ->
              let uu____4609 =
                let uu____4612 = FStar_List.hd tas  in
                unembed ea cb uu____4612  in
              match uu____4609 with
              | FStar_Pervasives_Native.Some a ->
                  let uu____4618 = f a  in embed eb cb uu____4618
              | FStar_Pervasives_Native.None  ->
                  failwith "cannot unembed function argument"),
            [(fun uu____4634  ->
                let uu____4637 = type_of eb  in as_arg uu____4637)],
            (Prims.parse_int "1"))
         in
      let un cb lam =
        match lam with
        | Lam (ft,uu____4684,uu____4685) ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____4725 =
                    let uu____4728 =
                      let uu____4729 =
                        let uu____4732 = embed ea cb x  in [uu____4732]  in
                      ft uu____4729  in
                    unembed eb cb uu____4728  in
                  match uu____4725 with
                  | FStar_Pervasives_Native.Some x1 -> x1
                  | FStar_Pervasives_Native.None  ->
                      failwith "cannot unembed function result"))
        | uu____4742 -> FStar_Pervasives_Native.None  in
      let uu____4746 =
        let uu____4747 = type_of ea  in
        let uu____4748 = let uu____4749 = type_of eb  in as_iarg uu____4749
           in
        make_arrow1 uu____4747 uu____4748  in
      mk_emb em un uu____4746
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____4776 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4776 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____4781 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4781 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____4786 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4786 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____4791 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4791 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____4796 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4796 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____4801 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4801 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____4806 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4806 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____4811 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4811 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____4816 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4816 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____4824 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____4825 =
          let uu____4826 =
            let uu____4831 =
              let uu____4832 = e_list e_string  in embed uu____4832 cb l  in
            as_arg uu____4831  in
          [uu____4826]  in
        mkFV uu____4824 [] uu____4825
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____4854 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____4855 =
          let uu____4856 =
            let uu____4861 =
              let uu____4862 = e_list e_string  in embed uu____4862 cb l  in
            as_arg uu____4861  in
          [uu____4856]  in
        mkFV uu____4854 [] uu____4855
    | FStar_Syntax_Embeddings.UnfoldAttr a -> failwith "NBE UnfoldAttr..."
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____4908,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____4924,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____4940,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____4956,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____4972,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____4988,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____5004,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____5020,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____5036,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____5052,(l,uu____5054)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____5073 =
          let uu____5078 = e_list e_string  in unembed uu____5078 cb l  in
        FStar_Util.bind_opt uu____5073
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____5098,(l,uu____5100)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____5119 =
          let uu____5124 = e_list e_string  in unembed uu____5124 cb l  in
        FStar_Util.bind_opt uu____5119
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | uu____5143 ->
        ((let uu____5145 =
            let uu____5150 =
              let uu____5151 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____5151
               in
            (FStar_Errors.Warning_NotEmbedded, uu____5150)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____5145);
         FStar_Pervasives_Native.None)
     in
  let uu____5152 =
    let uu____5153 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____5153 [] []  in
  mk_emb em un uu____5152 
let bogus_cb :
  'Auu____5166 'Auu____5167 . 'Auu____5166 -> 'Auu____5167 -> 'Auu____5166 =
  fun h  -> fun _args  -> h 
let (arg_as_int : arg -> FStar_BigInt.t FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_int bogus_cb)
  
let (arg_as_bool : arg -> Prims.bool FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_bool bogus_cb)
  
let (arg_as_char : arg -> FStar_Char.char FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_char bogus_cb)
  
let (arg_as_string : arg -> Prims.string FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_string bogus_cb)
  
let arg_as_list :
  'a . 'a embedding -> arg -> 'a Prims.list FStar_Pervasives_Native.option =
  fun e  ->
    fun a  ->
      let uu____5242 =
        let uu____5251 = e_list e  in unembed uu____5251 bogus_cb  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5242
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____5272  ->
    match uu____5272 with
    | (a,uu____5280) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____5295)::[]) when
             let uu____5312 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____5312 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____5317 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cb n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____5359 = let uu____5366 = as_arg c  in [uu____5366]  in
      int_to_t2 uu____5359
  
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
          let uu____5419 = f a  in FStar_Pervasives_Native.Some uu____5419
      | uu____5420 -> FStar_Pervasives_Native.None
  
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
          let uu____5473 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____5473
      | uu____5474 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____5517 = FStar_List.map as_a args  in lift_unary f uu____5517
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____5571 = FStar_List.map as_a args  in
        lift_binary f uu____5571
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____5600 = f x  in embed e_int bogus_cb uu____5600)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  -> let uu____5626 = f x y  in embed e_int bogus_cb uu____5626)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____5645 = f x  in embed e_bool bogus_cb uu____5645)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____5671 = f x y  in embed e_bool bogus_cb uu____5671)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____5697 = f x y  in embed e_string bogus_cb uu____5697)
  
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
                let uu____5799 =
                  let uu____5808 = as_a a  in
                  let uu____5811 = as_b b  in (uu____5808, uu____5811)  in
                (match uu____5799 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____5826 =
                       let uu____5827 = f a1 b1  in embed_c uu____5827  in
                     FStar_Pervasives_Native.Some uu____5826
                 | uu____5828 -> FStar_Pervasives_Native.None)
            | uu____5837 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____5843 = e_list e_char  in
    let uu____5850 = FStar_String.list_of_string s  in
    embed uu____5843 bogus_cb uu____5850
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____5880 =
        let uu____5881 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____5881  in
      embed e_int bogus_cb uu____5880
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____5913 = arg_as_string a1  in
        (match uu____5913 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5919 = arg_as_list e_string a2  in
             (match uu____5919 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5932 = embed e_string bogus_cb r  in
                  FStar_Pervasives_Native.Some uu____5932
              | uu____5933 -> FStar_Pervasives_Native.None)
         | uu____5938 -> FStar_Pervasives_Native.None)
    | uu____5941 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____5947 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cb uu____5947
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string bogus_cb (if b then "true" else "false") 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool bogus_cb true  in
      let fal = embed e_bool bogus_cb false  in
      match args with
      | (_univ,uu____5973)::(_typ,uu____5975)::(a1,uu____5977)::(a2,uu____5979)::[]
          ->
          let uu____6000 = eq_t a1 a2  in
          (match uu____6000 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____6005 -> FStar_Pervasives_Native.None)
      | uu____6006 -> failwith "Unexpected number of arguments"
  
let (interp_prop : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____6019)::(_typ,uu____6021)::(a1,uu____6023)::(a2,uu____6025)::[]
        ->
        let uu____6046 = eq_t a1 a2  in
        (match uu____6046 with
         | FStar_Syntax_Util.Equal  ->
             let uu____6049 = embed e_bool bogus_cb true  in
             FStar_Pervasives_Native.Some uu____6049
         | FStar_Syntax_Util.NotEqual  ->
             let uu____6050 = embed e_bool bogus_cb false  in
             FStar_Pervasives_Native.Some uu____6050
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____6051 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____6068 =
        let uu____6069 = FStar_Ident.string_of_lid lid  in
        Prims.strcat "No interpretation for " uu____6069  in
      failwith uu____6068
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____6082)::[] ->
        let uu____6091 = unembed e_range bogus_cb a1  in
        (match uu____6091 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6097 = embed e_range bogus_cb r  in
             FStar_Pervasives_Native.Some uu____6097
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6098 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____6132 = arg_as_list e_char a1  in
        (match uu____6132 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6148 = arg_as_string a2  in
             (match uu____6148 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____6157 =
                    let uu____6158 = e_list e_string  in
                    embed uu____6158 bogus_cb r  in
                  FStar_Pervasives_Native.Some uu____6157
              | uu____6165 -> FStar_Pervasives_Native.None)
         | uu____6168 -> FStar_Pervasives_Native.None)
    | uu____6174 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____6215 =
          let uu____6228 = arg_as_string a1  in
          let uu____6231 = arg_as_int a2  in
          let uu____6234 = arg_as_int a3  in
          (uu____6228, uu____6231, uu____6234)  in
        (match uu____6215 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___230_6261  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____6265 = embed e_string bogus_cb r  in
                       FStar_Pervasives_Native.Some uu____6265) ()
              with | uu___229_6267 -> FStar_Pervasives_Native.None)
         | uu____6270 -> FStar_Pervasives_Native.None)
    | uu____6283 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____6342 =
          let uu____6363 = arg_as_string fn  in
          let uu____6366 = arg_as_int from_line  in
          let uu____6369 = arg_as_int from_col  in
          let uu____6372 = arg_as_int to_line  in
          let uu____6375 = arg_as_int to_col  in
          (uu____6363, uu____6366, uu____6369, uu____6372, uu____6375)  in
        (match uu____6342 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6406 =
                 let uu____6407 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6408 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6407 uu____6408  in
               let uu____6409 =
                 let uu____6410 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6411 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6410 uu____6411  in
               FStar_Range.mk_range fn1 uu____6406 uu____6409  in
             let uu____6412 = embed e_range bogus_cb r  in
             FStar_Pervasives_Native.Some uu____6412
         | uu____6413 -> FStar_Pervasives_Native.None)
    | uu____6434 -> FStar_Pervasives_Native.None
  