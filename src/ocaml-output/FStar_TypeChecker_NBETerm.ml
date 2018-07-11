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
    match x with | Accu (uu____989,uu____990) -> false | uu____1003 -> true
  
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
  fun uu___223_1169  ->
    if uu___223_1169
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___224_1175  ->
    if uu___224_1175
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
      | (FStar_Syntax_Util.NotEqual ,uu____1187) ->
          FStar_Syntax_Util.NotEqual
      | (uu____1188,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____1189) -> FStar_Syntax_Util.Unknown
      | (uu____1190,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____1206 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____1222),String (s2,uu____1224)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____1232,uu____1233) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____1268,Lam uu____1269) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____1338 = eq_atom a1 a2  in
          eq_and uu____1338 (fun uu____1340  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____1379 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1379
          then
            let uu____1380 =
              let uu____1381 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____1381  in
            eq_and uu____1380 (fun uu____1383  -> eq_args args1 args2)
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____1423 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1423
          then
            let uu____1424 =
              let uu____1425 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____1425  in
            eq_and uu____1424 (fun uu____1427  -> eq_args args1 args2)
          else FStar_Syntax_Util.NotEqual
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____1433 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1433
      | (Univ u1,Univ u2) ->
          let uu____1436 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1436
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____1482 =
            let uu____1483 =
              let uu____1484 = t11 ()  in
              FStar_Pervasives_Native.fst uu____1484  in
            let uu____1489 =
              let uu____1490 = t11 ()  in
              FStar_Pervasives_Native.fst uu____1490  in
            eq_t uu____1483 uu____1489  in
          eq_and uu____1482
            (fun uu____1498  ->
               let uu____1499 =
                 let uu____1500 = mkAccuVar x  in r1 uu____1500  in
               let uu____1501 =
                 let uu____1502 = mkAccuVar x  in r2 uu____1502  in
               eq_t uu____1499 uu____1501)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____1503,uu____1504) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____1509,uu____1510) -> FStar_Syntax_Util.Unknown

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
          let uu____1591 = eq_arg x y  in
          eq_and uu____1591 (fun uu____1593  -> eq_args xs ys)
      | (uu____1594,uu____1595) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____1631) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____1633 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____1633
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam uu____1651 -> "Lam"
    | Accu (a,l) ->
        let uu____1686 =
          let uu____1687 = atom_to_string a  in
          let uu____1688 =
            let uu____1689 =
              let uu____1690 =
                let uu____1691 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____1691  in
              Prims.strcat uu____1690 ")"  in
            Prims.strcat ") (" uu____1689  in
          Prims.strcat uu____1687 uu____1688  in
        Prims.strcat "Accu (" uu____1686
    | Construct (fv,us,l) ->
        let uu____1723 =
          let uu____1724 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____1725 =
            let uu____1726 =
              let uu____1727 =
                let uu____1728 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____1728  in
              let uu____1731 =
                let uu____1732 =
                  let uu____1733 =
                    let uu____1734 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____1734  in
                  Prims.strcat uu____1733 "]"  in
                Prims.strcat "] [" uu____1732  in
              Prims.strcat uu____1727 uu____1731  in
            Prims.strcat ") [" uu____1726  in
          Prims.strcat uu____1724 uu____1725  in
        Prims.strcat "Construct (" uu____1723
    | FV (fv,us,l) ->
        let uu____1766 =
          let uu____1767 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____1768 =
            let uu____1769 =
              let uu____1770 =
                let uu____1771 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____1771  in
              let uu____1774 =
                let uu____1775 =
                  let uu____1776 =
                    let uu____1777 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____1777  in
                  Prims.strcat uu____1776 "]"  in
                Prims.strcat "] [" uu____1775  in
              Prims.strcat uu____1770 uu____1774  in
            Prims.strcat ") [" uu____1769  in
          Prims.strcat uu____1767 uu____1768  in
        Prims.strcat "FV (" uu____1766
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____1792 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____1792
    | Type_t u ->
        let uu____1794 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____1794
    | Arrow uu____1795 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____1838 = t ()  in FStar_Pervasives_Native.fst uu____1838
           in
        let uu____1843 =
          let uu____1844 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____1845 =
            let uu____1846 =
              let uu____1847 = t_to_string t1  in
              let uu____1848 =
                let uu____1849 =
                  let uu____1850 =
                    let uu____1851 =
                      let uu____1852 = mkAccuVar x1  in f uu____1852  in
                    t_to_string uu____1851  in
                  Prims.strcat uu____1850 "}"  in
                Prims.strcat "{" uu____1849  in
              Prims.strcat uu____1847 uu____1848  in
            Prims.strcat ":" uu____1846  in
          Prims.strcat uu____1844 uu____1845  in
        Prims.strcat "Refinement " uu____1843
    | Unknown  -> "Unknown"

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____1855 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____1855
    | Match (t,uu____1857,uu____1858) ->
        let uu____1881 = t_to_string t  in Prims.strcat "Match " uu____1881
    | Rec (uu____1882,uu____1883,l) ->
        let uu____1893 =
          let uu____1894 =
            let uu____1895 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____1895  in
          Prims.strcat uu____1894 ")"  in
        Prims.strcat "Rec (" uu____1893

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____1899 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____1899 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____1905 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____1905 (FStar_String.concat " ")

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
  'Auu____2096 .
    ('Auu____2096 -> t) ->
      (t -> 'Auu____2096 FStar_Pervasives_Native.option) ->
        t -> 'Auu____2096 embedding
  = fun em  -> fun un  -> fun typ  -> { em; un; typ } 
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2147 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____2147 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2167 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkConstruct uu____2167 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  -> Arrow ((fun uu____2203  -> t1), [(fun uu____2214  -> a)])
  
let (e_any : t embedding) =
  let em a = a  in
  let un t = FStar_Pervasives_Native.Some t  in
  let uu____2238 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____2238 
let (e_unit : unit embedding) =
  let em a = Constant Unit  in
  let un t = FStar_Pervasives_Native.Some ()  in
  let uu____2259 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  mk_emb em un uu____2259 
let (e_bool : Prims.bool embedding) =
  let em a = Constant (Bool a)  in
  let un t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____2285 -> FStar_Pervasives_Native.None  in
  let uu____2286 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  mk_emb em un uu____2286 
let (e_char : FStar_Char.char embedding) =
  let em c = Constant (Char c)  in
  let un c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____2320 -> FStar_Pervasives_Native.None  in
  let uu____2322 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  mk_emb em un uu____2322 
let (e_string : Prims.string embedding) =
  let em s = Constant (String (s, FStar_Range.dummyRange))  in
  let un s =
    match s with
    | Constant (String (s1,uu____2349)) -> FStar_Pervasives_Native.Some s1
    | uu____2350 -> FStar_Pervasives_Native.None  in
  let uu____2351 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  mk_emb em un uu____2351 
let (e_int : FStar_BigInt.t embedding) =
  let em c = Constant (Int c)  in
  let un c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____2377 -> FStar_Pervasives_Native.None  in
  let uu____2378 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  mk_emb em un uu____2378 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let em o =
      match o with
      | FStar_Pervasives_Native.None  ->
          let uu____2411 =
            let uu____2412 =
              let uu____2417 = type_of ea  in as_iarg uu____2417  in
            [uu____2412]  in
          lid_as_constr FStar_Parser_Const.none_lid
            [FStar_Syntax_Syntax.U_zero] uu____2411
      | FStar_Pervasives_Native.Some x ->
          let uu____2427 =
            let uu____2428 =
              let uu____2433 = type_of ea  in as_iarg uu____2433  in
            let uu____2434 =
              let uu____2441 =
                let uu____2446 = embed ea x  in as_arg uu____2446  in
              [uu____2441]  in
            uu____2428 :: uu____2434  in
          lid_as_constr FStar_Parser_Const.some_lid
            [FStar_Syntax_Syntax.U_zero] uu____2427
       in
    let un trm =
      match trm with
      | Construct (fvar1,us,args) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.none_lid ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | Construct (fvar1,us,uu____2496::(a,uu____2498)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.some_lid ->
          let uu____2525 = unembed ea a  in
          FStar_Util.bind_opt uu____2525
            (fun a1  ->
               FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some a1))
      | uu____2534 -> FStar_Pervasives_Native.None  in
    let uu____2537 =
      let uu____2538 =
        let uu____2539 = let uu____2544 = type_of ea  in as_arg uu____2544
           in
        [uu____2539]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____2538
       in
    mk_emb em un uu____2537
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em x =
        let uu____2603 =
          let uu____2604 = let uu____2609 = type_of ea  in as_iarg uu____2609
             in
          let uu____2610 =
            let uu____2617 =
              let uu____2622 = type_of eb  in as_iarg uu____2622  in
            let uu____2623 =
              let uu____2630 =
                let uu____2635 = embed ea (FStar_Pervasives_Native.fst x)  in
                as_arg uu____2635  in
              let uu____2636 =
                let uu____2643 =
                  let uu____2648 = embed eb (FStar_Pervasives_Native.snd x)
                     in
                  as_arg uu____2648  in
                [uu____2643]  in
              uu____2630 :: uu____2636  in
            uu____2617 :: uu____2623  in
          uu____2604 :: uu____2610  in
        lid_as_constr FStar_Parser_Const.lid_Mktuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____2603
         in
      let un trm =
        match trm with
        | Construct
            (fvar1,us,uu____2689::uu____2690::(a,uu____2692)::(b,uu____2694)::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1
              FStar_Parser_Const.lid_Mktuple2
            ->
            let uu____2733 = unembed ea a  in
            FStar_Util.bind_opt uu____2733
              (fun a1  ->
                 let uu____2743 = unembed eb b  in
                 FStar_Util.bind_opt uu____2743
                   (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
        | uu____2756 -> FStar_Pervasives_Native.None  in
      let uu____2761 =
        let uu____2762 =
          let uu____2763 = let uu____2768 = type_of ea  in as_arg uu____2768
             in
          let uu____2769 =
            let uu____2776 =
              let uu____2781 = type_of eb  in as_arg uu____2781  in
            [uu____2776]  in
          uu____2763 :: uu____2769  in
        lid_as_typ FStar_Parser_Const.lid_tuple2 [FStar_Syntax_Syntax.U_zero]
          uu____2762
         in
      mk_emb em un uu____2761
  
let (e_range : FStar_Range.range embedding) =
  let em r = Constant (Range r)  in
  let un t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____2819 -> FStar_Pervasives_Native.None  in
  let uu____2820 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  mk_emb em un uu____2820 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em l =
      let typ = let uu____2854 = type_of ea  in as_iarg uu____2854  in
      let nil =
        lid_as_constr FStar_Parser_Const.nil_lid [FStar_Syntax_Syntax.U_zero]
          [typ]
         in
      let cons1 hd1 tl1 =
        let uu____2875 =
          let uu____2876 =
            let uu____2883 =
              let uu____2888 = embed ea hd1  in as_arg uu____2888  in
            let uu____2889 = let uu____2896 = as_arg tl1  in [uu____2896]  in
            uu____2883 :: uu____2889  in
          typ :: uu____2876  in
        lid_as_constr FStar_Parser_Const.cons_lid
          [FStar_Syntax_Syntax.U_zero] uu____2875
         in
      FStar_List.fold_right cons1 l nil  in
    let rec un trm =
      match trm with
      | Construct (fv,uu____2932,uu____2933) when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
          FStar_Pervasives_Native.Some []
      | Construct
          (fv,uu____2953,(uu____2954,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____2955))::
           (hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                 )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____2984 = unembed ea hd1  in
          FStar_Util.bind_opt uu____2984
            (fun hd2  ->
               let uu____2992 = un tl1  in
               FStar_Util.bind_opt uu____2992
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | Construct
          (fv,uu____3008,(hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                               )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____3033 = unembed ea hd1  in
          FStar_Util.bind_opt uu____3033
            (fun hd2  ->
               let uu____3041 = un tl1  in
               FStar_Util.bind_opt uu____3041
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | uu____3056 -> FStar_Pervasives_Native.None  in
    let uu____3059 =
      let uu____3060 =
        let uu____3061 = let uu____3066 = type_of ea  in as_arg uu____3066
           in
        [uu____3061]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____3060
       in
    mk_emb em un uu____3059
  
let e_arrow1 : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let em f =
        Lam
          ((fun tas  ->
              let uu____3142 =
                let uu____3145 = FStar_List.hd tas  in unembed ea uu____3145
                 in
              match uu____3142 with
              | FStar_Pervasives_Native.Some a ->
                  let uu____3147 = f a  in embed eb uu____3147
              | FStar_Pervasives_Native.None  ->
                  failwith "cannot unembed function argument"),
            [(fun uu____3157  ->
                let uu____3158 = type_of eb  in as_arg uu____3158)],
            (Prims.parse_int "1"))
         in
      let un lam =
        match lam with
        | Lam (ft,uu____3188,uu____3189) ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____3225 =
                    let uu____3228 =
                      let uu____3229 =
                        let uu____3232 = embed ea x  in [uu____3232]  in
                      ft uu____3229  in
                    unembed eb uu____3228  in
                  match uu____3225 with
                  | FStar_Pervasives_Native.Some x1 -> x1
                  | FStar_Pervasives_Native.None  ->
                      failwith "cannot unembed function result"))
        | uu____3234 -> FStar_Pervasives_Native.None  in
      let uu____3238 =
        let uu____3239 = type_of ea  in
        let uu____3240 = let uu____3241 = type_of eb  in as_iarg uu____3241
           in
        make_arrow1 uu____3239 uu____3240  in
      mk_emb em un uu____3238
  
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
      let uu____3309 = let uu____3318 = e_list e  in unembed uu____3318  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____3309
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____3339  ->
    match uu____3339 with
    | (a,uu____3347) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____3362)::[]) when
             let uu____3379 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____3379 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____3384 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____3426 = let uu____3433 = as_arg c  in [uu____3433]  in
      int_to_t2 uu____3426
  
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
          let uu____3486 = f a  in FStar_Pervasives_Native.Some uu____3486
      | uu____3487 -> FStar_Pervasives_Native.None
  
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
          let uu____3540 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____3540
      | uu____3541 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____3584 = FStar_List.map as_a args  in lift_unary f uu____3584
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____3638 = FStar_List.map as_a args  in
        lift_binary f uu____3638
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____3667 = f x  in embed e_int uu____3667)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  -> fun y  -> let uu____3693 = f x y  in embed e_int uu____3693)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____3712 = f x  in embed e_bool uu____3712)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  -> fun y  -> let uu____3738 = f x y  in embed e_bool uu____3738)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  -> let uu____3764 = f x y  in embed e_string uu____3764)
  
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
                let uu____3866 =
                  let uu____3875 = as_a a  in
                  let uu____3878 = as_b b  in (uu____3875, uu____3878)  in
                (match uu____3866 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____3893 =
                       let uu____3894 = f a1 b1  in embed_c uu____3894  in
                     FStar_Pervasives_Native.Some uu____3893
                 | uu____3895 -> FStar_Pervasives_Native.None)
            | uu____3904 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____3910 = e_list e_char  in
    let uu____3917 = FStar_String.list_of_string s  in
    embed uu____3910 uu____3917
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____3947 =
        let uu____3948 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____3948  in
      embed e_int uu____3947
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____3980 = arg_as_string a1  in
        (match uu____3980 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____3986 = arg_as_list e_string a2  in
             (match uu____3986 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____3999 = embed e_string r  in
                  FStar_Pervasives_Native.Some uu____3999
              | uu____4000 -> FStar_Pervasives_Native.None)
         | uu____4005 -> FStar_Pervasives_Native.None)
    | uu____4008 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____4014 = FStar_BigInt.string_of_big_int i  in
    embed e_string uu____4014
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string (if b then "true" else "false") 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool true  in
      let fal = embed e_bool false  in
      match args with
      | (_univ,uu____4040)::(_typ,uu____4042)::(a1,uu____4044)::(a2,uu____4046)::[]
          ->
          let uu____4067 = eq_t a1 a2  in
          (match uu____4067 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____4072 -> FStar_Pervasives_Native.None)
      | uu____4073 -> failwith "Unexpected number of arguments"
  
let (interp_prop : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____4086)::(_typ,uu____4088)::(a1,uu____4090)::(a2,uu____4092)::[]
        ->
        let uu____4113 = eq_t a1 a2  in
        (match uu____4113 with
         | FStar_Syntax_Util.Equal  ->
             let uu____4116 = embed e_bool true  in
             FStar_Pervasives_Native.Some uu____4116
         | FStar_Syntax_Util.NotEqual  ->
             let uu____4117 = embed e_bool false  in
             FStar_Pervasives_Native.Some uu____4117
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____4118 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____4135 =
        let uu____4136 = FStar_Ident.string_of_lid lid  in
        Prims.strcat "No interpretation for " uu____4136  in
      failwith uu____4135
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____4149)::[] ->
        let uu____4158 = unembed e_range a1  in
        (match uu____4158 with
         | FStar_Pervasives_Native.Some r ->
             let uu____4164 = embed e_range r  in
             FStar_Pervasives_Native.Some uu____4164
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____4165 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____4199 = arg_as_list e_char a1  in
        (match uu____4199 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4215 = arg_as_string a2  in
             (match uu____4215 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____4224 =
                    let uu____4225 = e_list e_string  in embed uu____4225 r
                     in
                  FStar_Pervasives_Native.Some uu____4224
              | uu____4232 -> FStar_Pervasives_Native.None)
         | uu____4235 -> FStar_Pervasives_Native.None)
    | uu____4241 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____4282 =
          let uu____4295 = arg_as_string a1  in
          let uu____4298 = arg_as_int a2  in
          let uu____4301 = arg_as_int a3  in
          (uu____4295, uu____4298, uu____4301)  in
        (match uu____4282 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___226_4328  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____4332 = embed e_string r  in
                       FStar_Pervasives_Native.Some uu____4332) ()
              with | uu___225_4334 -> FStar_Pervasives_Native.None)
         | uu____4337 -> FStar_Pervasives_Native.None)
    | uu____4350 -> FStar_Pervasives_Native.None
  