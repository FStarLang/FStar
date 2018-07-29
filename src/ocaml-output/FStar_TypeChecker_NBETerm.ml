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
  | Refinement of
  (t -> t,unit ->
            (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2)
  FStar_Pervasives_Native.tuple2 
let (uu___is_Var : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____319 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____350 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t,t -> t,(t -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.branch Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Rec : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____425 -> false
  
let (__proj__Rec__item___0 :
  atom ->
    (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
      t Prims.list) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____489 -> false
  
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
    match projectee with | Accu _0 -> true | uu____573 -> false
  
let (__proj__Accu__item___0 :
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____631 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____701 -> false 
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
    match projectee with | Constant _0 -> true | uu____757 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____771 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____785 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____798 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____823 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    (t Prims.list -> t,(unit ->
                          (t,FStar_Syntax_Syntax.aqual)
                            FStar_Pervasives_Native.tuple2)
                         Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____905 -> false
  
let (__proj__Refinement__item___0 :
  t ->
    (t -> t,unit ->
              (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Refinement _0 -> _0 
type arg = (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
type args =
  (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
type head = t
type annot = t FStar_Pervasives_Native.option
let (isAccu : t -> Prims.bool) =
  fun trm  -> match trm with | Accu uu____972 -> true | uu____983 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____989,uu____990) -> false | uu____1007 -> true
  
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
  fun uu___223_1173  ->
    if uu___223_1173
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___224_1179  ->
    if uu___224_1179
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
      | (FStar_Syntax_Util.NotEqual ,uu____1191) ->
          FStar_Syntax_Util.NotEqual
      | (uu____1192,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____1193) -> FStar_Syntax_Util.Unknown
      | (uu____1194,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____1210 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____1226),String (s2,uu____1228)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____1236,uu____1237) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____1272,Lam uu____1273) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____1350 = eq_atom a1 a2  in
          eq_and uu____1350 (fun uu____1352  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____1399 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1399
          then
            let uu____1400 =
              let uu____1401 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____1401  in
            eq_and uu____1400 (fun uu____1403  -> eq_args args1 args2)
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____1451 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1451
          then
            let uu____1452 =
              let uu____1453 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____1453  in
            eq_and uu____1452 (fun uu____1455  -> eq_args args1 args2)
          else FStar_Syntax_Util.NotEqual
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____1461 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1461
      | (Univ u1,Univ u2) ->
          let uu____1464 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1464
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____1518 =
            let uu____1519 =
              let uu____1520 = t11 ()  in
              FStar_Pervasives_Native.fst uu____1520  in
            let uu____1529 =
              let uu____1530 = t11 ()  in
              FStar_Pervasives_Native.fst uu____1530  in
            eq_t uu____1519 uu____1529  in
          eq_and uu____1518
            (fun uu____1542  ->
               let uu____1543 =
                 let uu____1544 = mkAccuVar x  in r1 uu____1544  in
               let uu____1545 =
                 let uu____1546 = mkAccuVar x  in r2 uu____1546  in
               eq_t uu____1543 uu____1545)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____1547,uu____1548) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____1553,uu____1554) -> FStar_Syntax_Util.Unknown

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
          let uu____1635 = eq_arg x y  in
          eq_and uu____1635 (fun uu____1637  -> eq_args xs ys)
      | (uu____1638,uu____1639) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____1683) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____1685 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____1685
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam uu____1703 -> "Lam"
    | Accu (a,l) ->
        let uu____1742 =
          let uu____1743 = atom_to_string a  in
          let uu____1744 =
            let uu____1745 =
              let uu____1746 =
                let uu____1747 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____1747  in
              Prims.strcat uu____1746 ")"  in
            Prims.strcat ") (" uu____1745  in
          Prims.strcat uu____1743 uu____1744  in
        Prims.strcat "Accu (" uu____1742
    | Construct (fv,us,l) ->
        let uu____1789 =
          let uu____1790 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____1791 =
            let uu____1792 =
              let uu____1793 =
                let uu____1794 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____1794  in
              let uu____1797 =
                let uu____1798 =
                  let uu____1799 =
                    let uu____1800 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____1800  in
                  Prims.strcat uu____1799 "]"  in
                Prims.strcat "] [" uu____1798  in
              Prims.strcat uu____1793 uu____1797  in
            Prims.strcat ") [" uu____1792  in
          Prims.strcat uu____1790 uu____1791  in
        Prims.strcat "Construct (" uu____1789
    | FV (fv,us,l) ->
        let uu____1842 =
          let uu____1843 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____1844 =
            let uu____1845 =
              let uu____1846 =
                let uu____1847 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____1847  in
              let uu____1850 =
                let uu____1851 =
                  let uu____1852 =
                    let uu____1853 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____1853  in
                  Prims.strcat uu____1852 "]"  in
                Prims.strcat "] [" uu____1851  in
              Prims.strcat uu____1846 uu____1850  in
            Prims.strcat ") [" uu____1845  in
          Prims.strcat uu____1843 uu____1844  in
        Prims.strcat "FV (" uu____1842
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____1874 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____1874
    | Type_t u ->
        let uu____1876 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____1876
    | Arrow uu____1877 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____1924 = t ()  in FStar_Pervasives_Native.fst uu____1924
           in
        let uu____1933 =
          let uu____1934 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____1935 =
            let uu____1936 =
              let uu____1937 = t_to_string t1  in
              let uu____1938 =
                let uu____1939 =
                  let uu____1940 =
                    let uu____1941 =
                      let uu____1942 = mkAccuVar x1  in f uu____1942  in
                    t_to_string uu____1941  in
                  Prims.strcat uu____1940 "}"  in
                Prims.strcat "{" uu____1939  in
              Prims.strcat uu____1937 uu____1938  in
            Prims.strcat ":" uu____1936  in
          Prims.strcat uu____1934 uu____1935  in
        Prims.strcat "Refinement " uu____1933
    | Unknown  -> "Unknown"

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____1945 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____1945
    | Match (t,uu____1947,uu____1948) ->
        let uu____2003 = t_to_string t  in Prims.strcat "Match " uu____2003
    | Rec (uu____2004,uu____2005,l) ->
        let uu____2015 =
          let uu____2016 =
            let uu____2017 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____2017  in
          Prims.strcat uu____2016 ")"  in
        Prims.strcat "Rec (" uu____2015

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____2021 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____2021 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____2027 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____2027 (FStar_String.concat " ")

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
  'Auu____2218 .
    ('Auu____2218 -> t) ->
      (t -> 'Auu____2218 FStar_Pervasives_Native.option) ->
        t -> 'Auu____2218 embedding
  = fun em  -> fun un  -> fun typ  -> { em; un; typ } 
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2269 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____2269 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2289 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkConstruct uu____2289 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  -> Arrow ((fun uu____2325  -> t1), [(fun uu____2336  -> a)])
  
let (e_any : t embedding) =
  let em a = a  in
  let un t = FStar_Pervasives_Native.Some t  in
  let uu____2360 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____2360 
let (e_unit : unit embedding) =
  let em a = Constant Unit  in
  let un t = FStar_Pervasives_Native.Some ()  in
  let uu____2381 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  mk_emb em un uu____2381 
let (e_bool : Prims.bool embedding) =
  let em a = Constant (Bool a)  in
  let un t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____2407 -> FStar_Pervasives_Native.None  in
  let uu____2408 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  mk_emb em un uu____2408 
let (e_char : FStar_Char.char embedding) =
  let em c = Constant (Char c)  in
  let un c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____2442 -> FStar_Pervasives_Native.None  in
  let uu____2444 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  mk_emb em un uu____2444 
let (e_string : Prims.string embedding) =
  let em s = Constant (String (s, FStar_Range.dummyRange))  in
  let un s =
    match s with
    | Constant (String (s1,uu____2471)) -> FStar_Pervasives_Native.Some s1
    | uu____2472 -> FStar_Pervasives_Native.None  in
  let uu____2473 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  mk_emb em un uu____2473 
let (e_int : FStar_BigInt.t embedding) =
  let em c = Constant (Int c)  in
  let un c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____2499 -> FStar_Pervasives_Native.None  in
  let uu____2500 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  mk_emb em un uu____2500 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let em o =
      match o with
      | FStar_Pervasives_Native.None  ->
          let uu____2533 =
            let uu____2534 =
              let uu____2539 = type_of ea  in as_iarg uu____2539  in
            [uu____2534]  in
          lid_as_constr FStar_Parser_Const.none_lid
            [FStar_Syntax_Syntax.U_zero] uu____2533
      | FStar_Pervasives_Native.Some x ->
          let uu____2549 =
            let uu____2550 =
              let uu____2555 = type_of ea  in as_iarg uu____2555  in
            let uu____2556 =
              let uu____2563 =
                let uu____2568 = embed ea x  in as_arg uu____2568  in
              [uu____2563]  in
            uu____2550 :: uu____2556  in
          lid_as_constr FStar_Parser_Const.some_lid
            [FStar_Syntax_Syntax.U_zero] uu____2549
       in
    let un trm =
      match trm with
      | Construct (fvar1,us,args) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.none_lid ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | Construct (fvar1,us,uu____2622::(a,uu____2624)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.some_lid ->
          let uu____2665 = unembed ea a  in
          FStar_Util.bind_opt uu____2665
            (fun a1  ->
               FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some a1))
      | uu____2674 -> FStar_Pervasives_Native.None  in
    let uu____2677 =
      let uu____2678 =
        let uu____2679 = let uu____2684 = type_of ea  in as_arg uu____2684
           in
        [uu____2679]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____2678
       in
    mk_emb em un uu____2677
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em x =
        let uu____2743 =
          let uu____2744 = let uu____2749 = type_of ea  in as_iarg uu____2749
             in
          let uu____2750 =
            let uu____2757 =
              let uu____2762 = type_of eb  in as_iarg uu____2762  in
            let uu____2763 =
              let uu____2770 =
                let uu____2775 = embed ea (FStar_Pervasives_Native.fst x)  in
                as_arg uu____2775  in
              let uu____2776 =
                let uu____2783 =
                  let uu____2788 = embed eb (FStar_Pervasives_Native.snd x)
                     in
                  as_arg uu____2788  in
                [uu____2783]  in
              uu____2770 :: uu____2776  in
            uu____2757 :: uu____2763  in
          uu____2744 :: uu____2750  in
        lid_as_constr FStar_Parser_Const.lid_Mktuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____2743
         in
      let un trm =
        match trm with
        | Construct
            (fvar1,us,uu____2829::uu____2830::(a,uu____2832)::(b,uu____2834)::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1
              FStar_Parser_Const.lid_Mktuple2
            ->
            let uu____2897 = unembed ea a  in
            FStar_Util.bind_opt uu____2897
              (fun a1  ->
                 let uu____2907 = unembed eb b  in
                 FStar_Util.bind_opt uu____2907
                   (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
        | uu____2920 -> FStar_Pervasives_Native.None  in
      let uu____2925 =
        let uu____2926 =
          let uu____2927 = let uu____2932 = type_of ea  in as_arg uu____2932
             in
          let uu____2933 =
            let uu____2940 =
              let uu____2945 = type_of eb  in as_arg uu____2945  in
            [uu____2940]  in
          uu____2927 :: uu____2933  in
        lid_as_typ FStar_Parser_Const.lid_tuple2 [FStar_Syntax_Syntax.U_zero]
          uu____2926
         in
      mk_emb em un uu____2925
  
let (e_range : FStar_Range.range embedding) =
  let em r = Constant (Range r)  in
  let un t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____2983 -> FStar_Pervasives_Native.None  in
  let uu____2984 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  mk_emb em un uu____2984 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em l =
      let typ = let uu____3018 = type_of ea  in as_iarg uu____3018  in
      let nil =
        lid_as_constr FStar_Parser_Const.nil_lid [FStar_Syntax_Syntax.U_zero]
          [typ]
         in
      let cons1 hd1 tl1 =
        let uu____3039 =
          let uu____3040 =
            let uu____3047 =
              let uu____3052 = embed ea hd1  in as_arg uu____3052  in
            let uu____3053 = let uu____3060 = as_arg tl1  in [uu____3060]  in
            uu____3047 :: uu____3053  in
          typ :: uu____3040  in
        lid_as_constr FStar_Parser_Const.cons_lid
          [FStar_Syntax_Syntax.U_zero] uu____3039
         in
      FStar_List.fold_right cons1 l nil  in
    let rec un trm =
      match trm with
      | Construct (fv,uu____3096,uu____3097) when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
          FStar_Pervasives_Native.Some []
      | Construct
          (fv,uu____3121,(uu____3122,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____3123))::
           (hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                 )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____3168 = unembed ea hd1  in
          FStar_Util.bind_opt uu____3168
            (fun hd2  ->
               let uu____3176 = un tl1  in
               FStar_Util.bind_opt uu____3176
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | Construct
          (fv,uu____3192,(hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                               )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____3229 = unembed ea hd1  in
          FStar_Util.bind_opt uu____3229
            (fun hd2  ->
               let uu____3237 = un tl1  in
               FStar_Util.bind_opt uu____3237
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | uu____3252 -> FStar_Pervasives_Native.None  in
    let uu____3255 =
      let uu____3256 =
        let uu____3257 = let uu____3262 = type_of ea  in as_arg uu____3262
           in
        [uu____3257]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____3256
       in
    mk_emb em un uu____3255
  
let e_arrow1 : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let em f =
        Lam
          ((fun tas  ->
              let uu____3338 =
                let uu____3341 = FStar_List.hd tas  in unembed ea uu____3341
                 in
              match uu____3338 with
              | FStar_Pervasives_Native.Some a ->
                  let uu____3343 = f a  in embed eb uu____3343
              | FStar_Pervasives_Native.None  ->
                  failwith "cannot unembed function argument"),
            [(fun uu____3353  ->
                let uu____3354 = type_of eb  in as_arg uu____3354)],
            (Prims.parse_int "1"))
         in
      let un lam =
        match lam with
        | Lam (ft,uu____3384,uu____3385) ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____3425 =
                    let uu____3428 =
                      let uu____3429 =
                        let uu____3432 = embed ea x  in [uu____3432]  in
                      ft uu____3429  in
                    unembed eb uu____3428  in
                  match uu____3425 with
                  | FStar_Pervasives_Native.Some x1 -> x1
                  | FStar_Pervasives_Native.None  ->
                      failwith "cannot unembed function result"))
        | uu____3434 -> FStar_Pervasives_Native.None  in
      let uu____3438 =
        let uu____3439 = type_of ea  in
        let uu____3440 = let uu____3441 = type_of eb  in as_iarg uu____3441
           in
        make_arrow1 uu____3439 uu____3440  in
      mk_emb em un uu____3438
  
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
      let uu____3509 = let uu____3518 = e_list e  in unembed uu____3518  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____3509
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____3539  ->
    match uu____3539 with
    | (a,uu____3547) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____3566)::[]) when
             let uu____3593 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____3593 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____3598 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____3640 = let uu____3647 = as_arg c  in [uu____3647]  in
      int_to_t2 uu____3640
  
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
          let uu____3700 = f a  in FStar_Pervasives_Native.Some uu____3700
      | uu____3701 -> FStar_Pervasives_Native.None
  
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
          let uu____3754 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____3754
      | uu____3755 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____3798 = FStar_List.map as_a args  in lift_unary f uu____3798
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____3852 = FStar_List.map as_a args  in
        lift_binary f uu____3852
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____3881 = f x  in embed e_int uu____3881)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  -> fun y  -> let uu____3907 = f x y  in embed e_int uu____3907)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____3926 = f x  in embed e_bool uu____3926)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  -> fun y  -> let uu____3952 = f x y  in embed e_bool uu____3952)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  -> let uu____3978 = f x y  in embed e_string uu____3978)
  
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
                let uu____4090 =
                  let uu____4099 = as_a a  in
                  let uu____4102 = as_b b  in (uu____4099, uu____4102)  in
                (match uu____4090 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____4117 =
                       let uu____4118 = f a1 b1  in embed_c uu____4118  in
                     FStar_Pervasives_Native.Some uu____4117
                 | uu____4119 -> FStar_Pervasives_Native.None)
            | uu____4128 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____4134 = e_list e_char  in
    let uu____4141 = FStar_String.list_of_string s  in
    embed uu____4134 uu____4141
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____4171 =
        let uu____4172 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____4172  in
      embed e_int uu____4171
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____4214 = arg_as_string a1  in
        (match uu____4214 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4220 = arg_as_list e_string a2  in
             (match uu____4220 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____4233 = embed e_string r  in
                  FStar_Pervasives_Native.Some uu____4233
              | uu____4234 -> FStar_Pervasives_Native.None)
         | uu____4239 -> FStar_Pervasives_Native.None)
    | uu____4242 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____4248 = FStar_BigInt.string_of_big_int i  in
    embed e_string uu____4248
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string (if b then "true" else "false") 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool true  in
      let fal = embed e_bool false  in
      match args with
      | (_univ,uu____4274)::(_typ,uu____4276)::(a1,uu____4278)::(a2,uu____4280)::[]
          ->
          let uu____4327 = eq_t a1 a2  in
          (match uu____4327 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____4332 -> FStar_Pervasives_Native.None)
      | uu____4333 -> failwith "Unexpected number of arguments"
  
let (interp_prop : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____4346)::(_typ,uu____4348)::(a1,uu____4350)::(a2,uu____4352)::[]
        ->
        let uu____4399 = eq_t a1 a2  in
        (match uu____4399 with
         | FStar_Syntax_Util.Equal  ->
             let uu____4402 = embed e_bool true  in
             FStar_Pervasives_Native.Some uu____4402
         | FStar_Syntax_Util.NotEqual  ->
             let uu____4403 = embed e_bool false  in
             FStar_Pervasives_Native.Some uu____4403
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____4404 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____4421 =
        let uu____4422 = FStar_Ident.string_of_lid lid  in
        Prims.strcat "No interpretation for " uu____4422  in
      failwith uu____4421
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____4435)::[] ->
        let uu____4452 = unembed e_range a1  in
        (match uu____4452 with
         | FStar_Pervasives_Native.Some r ->
             let uu____4458 = embed e_range r  in
             FStar_Pervasives_Native.Some uu____4458
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____4459 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____4503 = arg_as_list e_char a1  in
        (match uu____4503 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4519 = arg_as_string a2  in
             (match uu____4519 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____4528 =
                    let uu____4529 = e_list e_string  in embed uu____4529 r
                     in
                  FStar_Pervasives_Native.Some uu____4528
              | uu____4536 -> FStar_Pervasives_Native.None)
         | uu____4539 -> FStar_Pervasives_Native.None)
    | uu____4545 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____4600 =
          let uu____4613 = arg_as_string a1  in
          let uu____4616 = arg_as_int a2  in
          let uu____4619 = arg_as_int a3  in
          (uu____4613, uu____4616, uu____4619)  in
        (match uu____4600 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___226_4646  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____4650 = embed e_string r  in
                       FStar_Pervasives_Native.Some uu____4650) ()
              with | uu___225_4652 -> FStar_Pervasives_Native.None)
         | uu____4655 -> FStar_Pervasives_Native.None)
    | uu____4668 -> FStar_Pervasives_Native.None
  