open Prims
let (b : FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.binder) =
  FStar_Syntax_Syntax.mk_binder 
let (id : FStar_Syntax_Syntax.term) = FStar_Tests_Pars.pars "fun x -> x" 
let (apply : FStar_Syntax_Syntax.term) =
  FStar_Tests_Pars.pars "fun f x -> f x" 
let (twice : FStar_Syntax_Syntax.term) =
  FStar_Tests_Pars.pars "fun f x -> f (f x)" 
let (tt : FStar_Syntax_Syntax.term) = FStar_Tests_Pars.pars "fun x y -> x" 
let (ff : FStar_Syntax_Syntax.term) = FStar_Tests_Pars.pars "fun x y -> y" 
let (z : FStar_Syntax_Syntax.term) = FStar_Tests_Pars.pars "fun f x -> x" 
let (one : FStar_Syntax_Syntax.term) = FStar_Tests_Pars.pars "fun f x -> f x" 
let (two : FStar_Syntax_Syntax.term) =
  FStar_Tests_Pars.pars "fun f x -> f (f x)" 
let (succ : FStar_Syntax_Syntax.term) =
  FStar_Tests_Pars.pars "fun n f x -> f (n f x)" 
let (pred : FStar_Syntax_Syntax.term) =
  FStar_Tests_Pars.pars
    "fun n f x -> n (fun g h -> h (g f)) (fun y -> x) (fun y -> y)"
  
let (mul : FStar_Syntax_Syntax.term) =
  FStar_Tests_Pars.pars "fun m n f -> m (n f)" 
let rec (encode : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then z
    else
      (let uu____140 =
         let uu____147 = encode (n1 - (Prims.parse_int "1"))  in [uu____147]
          in
       FStar_Tests_Util.app succ uu____140)
  
let (minus :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun m1  -> fun n1  -> FStar_Tests_Util.app n1 [pred; m1] 
let (let_ :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term)
  =
  fun x1  ->
    fun e  ->
      fun e'  ->
        let uu____268 =
          let uu____279 = let uu____280 = b x1  in [uu____280]  in
          FStar_Syntax_Util.abs uu____279 e' FStar_Pervasives_Native.None  in
        FStar_Tests_Util.app uu____268 [e]
  
let (mk_let :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun x1  ->
    fun e  ->
      fun e'  ->
        let e'1 =
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))] e'
           in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_let
             ((false,
                [{
                   FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x1);
                   FStar_Syntax_Syntax.lbunivs = [];
                   FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
                   FStar_Syntax_Syntax.lbeff =
                     FStar_Parser_Const.effect_Tot_lid;
                   FStar_Syntax_Syntax.lbdef = e;
                   FStar_Syntax_Syntax.lbattrs = [];
                   FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
                 }]), e'1)) FStar_Pervasives_Native.None
          FStar_Range.dummyRange
  
let (lid : Prims.string -> FStar_Ident.lident) =
  fun x1  -> FStar_Ident.lid_of_path ["Test"; x1] FStar_Range.dummyRange 
let (znat_l : FStar_Syntax_Syntax.fv) =
  let uu____483 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____483 FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____500 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____500 FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (tm_fv :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun fv  ->
    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
      FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (znat : FStar_Syntax_Syntax.term) = tm_fv znat_l 
let (snat :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    let uu____557 =
      let uu____564 =
        let uu____565 =
          let uu____590 = tm_fv snat_l  in
          let uu____601 =
            let uu____616 = FStar_Syntax_Syntax.as_arg s  in [uu____616]  in
          (uu____590, uu____601)  in
        FStar_Syntax_Syntax.Tm_app uu____565  in
      FStar_Syntax_Syntax.mk uu____564  in
    uu____557 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____678 . 'Auu____678 -> 'Auu____678 FStar_Syntax_Syntax.withinfo_t =
  fun p  -> FStar_Syntax_Syntax.withinfo p FStar_Range.dummyRange 
let (mk_match :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun h1  ->
    fun branches  ->
      let branches1 =
        FStar_All.pipe_right branches
          (FStar_List.map FStar_Syntax_Util.branch)
         in
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (h1, branches1))
        FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (pred_nat :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    let zbranch =
      let uu____862 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____862, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____944 =
        let uu____950 =
          let uu____951 =
            let uu____971 =
              let uu____984 =
                let uu____995 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____995, false)  in
              [uu____984]  in
            (snat_l, uu____971)  in
          FStar_Syntax_Syntax.Pat_cons uu____951  in
        pat uu____950  in
      let uu____1043 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___21_1056 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___21_1056.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___21_1056.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____944, FStar_Pervasives_Native.None, uu____1043)  in
    mk_match s [zbranch; sbranch]
  
let (minus_nat :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let minus1 = FStar_Tests_Util.m  in
      let zbranch =
        let uu____1163 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____1194 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____1163, FStar_Pervasives_Native.None, uu____1194)  in
      let sbranch =
        let uu____1256 =
          let uu____1262 =
            let uu____1263 =
              let uu____1283 =
                let uu____1296 =
                  let uu____1307 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____1307, false)  in
                [uu____1296]  in
              (snat_l, uu____1283)  in
            FStar_Syntax_Syntax.Pat_cons uu____1263  in
          pat uu____1262  in
        let uu____1355 =
          let uu____1366 = FStar_Tests_Util.nm minus1  in
          let uu____1377 =
            let uu____1384 =
              let uu____1393 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____1393  in
            let uu____1404 =
              let uu____1411 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____1411]  in
            uu____1384 :: uu____1404  in
          FStar_Tests_Util.app uu____1366 uu____1377  in
        (uu____1256, FStar_Pervasives_Native.None, uu____1355)  in
      let lb =
        let uu____1472 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____1484 =
          let uu____1495 =
            let uu____1504 =
              let uu____1505 = b FStar_Tests_Util.x  in
              let uu____1517 =
                let uu____1531 = b FStar_Tests_Util.y  in [uu____1531]  in
              uu____1505 :: uu____1517  in
            let uu____1576 =
              let uu____1587 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____1587 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____1504 uu____1576
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____1495
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____1472;
          FStar_Syntax_Syntax.lbdef = uu____1484;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____1628 =
        let uu____1635 =
          let uu____1636 =
            let uu____1661 =
              let uu____1672 =
                let uu____1681 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____1681 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____1672
               in
            ((true, [lb]), uu____1661)  in
          FStar_Syntax_Syntax.Tm_let uu____1636  in
        FStar_Syntax_Syntax.mk uu____1635  in
      uu____1628 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____1802 = snat out  in
         aux uu____1802 (n2 - (Prims.parse_int "1")))
       in
    aux znat n1
  
let (tests :
  (Prims.int * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list)
  =
  FStar_Tests_Pars.pars_and_tc_fragment
    "let rec copy (x:list int) : Tot (list int) = match x with | [] -> []  | hd::tl -> hd::copy tl";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let recons (x:list 'a) : Tot (list 'a) = match x with | [] -> []  | hd::tl -> hd::tl";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let rev (x:list 'a) : Tot (list 'a) = let rec aux (x:list 'a) (out:list 'a) : Tot (list 'a) = match x with | [] -> out | hd::tl -> aux tl (hd::out) in aux x []";
  FStar_Tests_Pars.pars_and_tc_fragment
    "type t = | A : int -> int -> t | B : int -> int -> t let f = function | A x y | B y x -> y - x";
  FStar_Tests_Pars.pars_and_tc_fragment "type snat = | Z | S : snat -> snat";
  FStar_Tests_Pars.pars_and_tc_fragment "type tb = | T | F";
  FStar_Tests_Pars.pars_and_tc_fragment "type rb = | A1 | A2 | A3";
  FStar_Tests_Pars.pars_and_tc_fragment "type hb = | H : tb -> hb";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let select (i:tb) (x:'a) (y:'a) : Tot 'a = match i with | T -> x | F -> y";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let select_int3 (i:int) (x:'a) (y:'a) (z:'a) : Tot 'a = match i with | 0 -> x | 1 -> y | _ -> z";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let select_bool (b:bool) (x:'a) (y:'a) : Tot 'a = if b then x else y";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let select_string3 (s:string) (x:'a) (y:'a) (z:'a) : Tot 'a = match s with | \"abc\" -> x | \"def\" -> y | _ -> z";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let recons_m (x:list tb) = match x with | [] -> []  | hd::tl -> hd::tl";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let rec copy_tb_list_2 (x:list tb) : Tot (list tb) = match x with | [] -> []  | [hd] -> [hd]\n                                          | hd1::hd2::tl -> hd1::hd2::copy_tb_list_2 tl";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let rec copy_list_2 (x:list 'a) : Tot (list 'a) = match x with | [] -> []  | [hd] -> [hd]\n                                          | hd1::hd2::tl -> hd1::hd2::copy_list_2 tl";
  FStar_Tests_Pars.pars_and_tc_fragment "let (x1:int{x1>3}) = 6";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let (x2:int{x2+1>3 /\\ not (x2-5>0)}) = 2";
  FStar_Tests_Pars.pars_and_tc_fragment "let my_plus (x:int) (y:int) = x + y";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let (x3:int{forall (a:nat). a > x2}) = 7";
  FStar_Tests_Pars.pars_and_tc_fragment "let idd (x: 'a) = x";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let revtb (x: tb) = match x with | T -> F | F -> T";
  FStar_Tests_Pars.pars_and_tc_fragment "let id_tb (x: tb) = x";
  FStar_Tests_Pars.pars_and_tc_fragment "let fst_a (x: 'a) (y: 'a) = x";
  FStar_Tests_Pars.pars_and_tc_fragment "let id_list (x: list 'a) = x";
  FStar_Tests_Pars.pars_and_tc_fragment "let id_list_m (x: list tb) = x";
  (let uu____1884 =
     let uu____1904 =
       let uu____1915 =
         let uu____1922 =
           let uu____1929 =
             let uu____1936 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____1936]  in
           id :: uu____1929  in
         one :: uu____1922  in
       FStar_Tests_Util.app apply uu____1915  in
     let uu____1961 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____1904, uu____1961)  in
   let uu____1986 =
     let uu____2008 =
       let uu____2028 =
         let uu____2039 =
           let uu____2046 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____2046]  in
         FStar_Tests_Util.app id uu____2039  in
       let uu____2063 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____2028, uu____2063)  in
     let uu____2088 =
       let uu____2110 =
         let uu____2130 =
           let uu____2141 =
             let uu____2148 =
               let uu____2155 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____2164 =
                 let uu____2171 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____2171]  in
               uu____2155 :: uu____2164  in
             tt :: uu____2148  in
           FStar_Tests_Util.app apply uu____2141  in
         let uu____2196 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____2130, uu____2196)  in
       let uu____2221 =
         let uu____2243 =
           let uu____2263 =
             let uu____2274 =
               let uu____2281 =
                 let uu____2288 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____2297 =
                   let uu____2304 = FStar_Tests_Util.nm FStar_Tests_Util.m
                      in
                   [uu____2304]  in
                 uu____2288 :: uu____2297  in
               ff :: uu____2281  in
             FStar_Tests_Util.app apply uu____2274  in
           let uu____2329 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____2263, uu____2329)  in
         let uu____2354 =
           let uu____2376 =
             let uu____2396 =
               let uu____2407 =
                 let uu____2414 =
                   let uu____2421 =
                     let uu____2428 =
                       let uu____2435 =
                         let uu____2442 =
                           let uu____2449 =
                             let uu____2456 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____2465 =
                               let uu____2472 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____2472]  in
                             uu____2456 :: uu____2465  in
                           ff :: uu____2449  in
                         apply :: uu____2442  in
                       apply :: uu____2435  in
                     apply :: uu____2428  in
                   apply :: uu____2421  in
                 apply :: uu____2414  in
               FStar_Tests_Util.app apply uu____2407  in
             let uu____2517 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____2396, uu____2517)  in
           let uu____2542 =
             let uu____2564 =
               let uu____2584 =
                 let uu____2595 =
                   let uu____2602 =
                     let uu____2609 =
                       let uu____2616 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n  in
                       let uu____2625 =
                         let uu____2632 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____2632]  in
                       uu____2616 :: uu____2625  in
                     ff :: uu____2609  in
                   apply :: uu____2602  in
                 FStar_Tests_Util.app twice uu____2595  in
               let uu____2661 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____2584, uu____2661)  in
             let uu____2686 =
               let uu____2708 =
                 let uu____2728 = minus one z  in
                 ((Prims.parse_int "5"), uu____2728, one)  in
               let uu____2753 =
                 let uu____2775 =
                   let uu____2795 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____2795, z)  in
                 let uu____2828 =
                   let uu____2850 =
                     let uu____2870 = minus one one  in
                     ((Prims.parse_int "7"), uu____2870, z)  in
                   let uu____2895 =
                     let uu____2917 =
                       let uu____2937 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____2937, one)  in
                     let uu____2974 =
                       let uu____2996 =
                         let uu____3016 = FStar_Tests_Util.app mul [two; one]
                            in
                         ((Prims.parse_int "9"), uu____3016, two)  in
                       let uu____3053 =
                         let uu____3075 =
                           let uu____3095 =
                             let uu____3106 =
                               let uu____3113 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____3113; one]  in
                             FStar_Tests_Util.app mul uu____3106  in
                           ((Prims.parse_int "10"), uu____3095, two)  in
                         let uu____3156 =
                           let uu____3178 =
                             let uu____3198 =
                               let uu____3209 = encode (Prims.parse_int "10")
                                  in
                               let uu____3219 = encode (Prims.parse_int "10")
                                  in
                               minus uu____3209 uu____3219  in
                             ((Prims.parse_int "11"), uu____3198, z)  in
                           let uu____3245 =
                             let uu____3267 =
                               let uu____3287 =
                                 let uu____3298 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____3308 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____3298 uu____3308  in
                               ((Prims.parse_int "12"), uu____3287, z)  in
                             let uu____3334 =
                               let uu____3356 =
                                 let uu____3376 =
                                   let uu____3387 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____3397 =
                                     let uu____3408 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____3417 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____3408 uu____3417  in
                                   let_ FStar_Tests_Util.x uu____3387
                                     uu____3397
                                    in
                                 ((Prims.parse_int "13"), uu____3376, z)  in
                               let uu____3442 =
                                 let uu____3464 =
                                   let uu____3484 =
                                     let uu____3495 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____3512 =
                                       let uu____3523 =
                                         let uu____3532 =
                                           let uu____3539 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____3548 =
                                             let uu____3555 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____3555]  in
                                           uu____3539 :: uu____3548  in
                                         FStar_Tests_Util.app mul uu____3532
                                          in
                                       let uu____3576 =
                                         let uu____3587 =
                                           let uu____3596 =
                                             let uu____3603 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____3612 =
                                               let uu____3619 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____3619]  in
                                             uu____3603 :: uu____3612  in
                                           FStar_Tests_Util.app mul
                                             uu____3596
                                            in
                                         let uu____3640 =
                                           let uu____3651 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____3660 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____3651 uu____3660  in
                                         let_ FStar_Tests_Util.h uu____3587
                                           uu____3640
                                          in
                                       let_ FStar_Tests_Util.y uu____3523
                                         uu____3576
                                        in
                                     let_ FStar_Tests_Util.x uu____3495
                                       uu____3512
                                      in
                                   ((Prims.parse_int "15"), uu____3484, z)
                                    in
                                 let uu____3685 =
                                   let uu____3707 =
                                     let uu____3727 =
                                       let uu____3738 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____3757 =
                                         let uu____3766 =
                                           let uu____3777 =
                                             let uu____3784 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____3793 =
                                               let uu____3800 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____3800]  in
                                             uu____3784 :: uu____3793  in
                                           FStar_Tests_Util.app mul
                                             uu____3777
                                            in
                                         let uu____3821 =
                                           let uu____3830 =
                                             let uu____3841 =
                                               let uu____3848 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____3857 =
                                                 let uu____3864 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____3864]  in
                                               uu____3848 :: uu____3857  in
                                             FStar_Tests_Util.app mul
                                               uu____3841
                                              in
                                           let uu____3885 =
                                             let uu____3894 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____3903 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____3894 uu____3903  in
                                           mk_let FStar_Tests_Util.h
                                             uu____3830 uu____3885
                                            in
                                         mk_let FStar_Tests_Util.y uu____3766
                                           uu____3821
                                          in
                                       mk_let FStar_Tests_Util.x uu____3738
                                         uu____3757
                                        in
                                     ((Prims.parse_int "16"), uu____3727, z)
                                      in
                                   let uu____3928 =
                                     let uu____3950 =
                                       let uu____3970 =
                                         let uu____3981 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____3998 =
                                           let uu____4009 =
                                             let uu____4018 =
                                               let uu____4025 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____4034 =
                                                 let uu____4041 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____4041]  in
                                               uu____4025 :: uu____4034  in
                                             FStar_Tests_Util.app mul
                                               uu____4018
                                              in
                                           let uu____4062 =
                                             let uu____4073 =
                                               let uu____4082 =
                                                 let uu____4089 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____4098 =
                                                   let uu____4105 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____4105]  in
                                                 uu____4089 :: uu____4098  in
                                               FStar_Tests_Util.app mul
                                                 uu____4082
                                                in
                                             let uu____4126 =
                                               let uu____4137 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____4146 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____4137 uu____4146
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____4073 uu____4126
                                              in
                                           let_ FStar_Tests_Util.y uu____4009
                                             uu____4062
                                            in
                                         let_ FStar_Tests_Util.x uu____3981
                                           uu____3998
                                          in
                                       ((Prims.parse_int "17"), uu____3970,
                                         z)
                                        in
                                     let uu____4171 =
                                       let uu____4193 =
                                         let uu____4213 =
                                           let uu____4224 =
                                             let uu____4235 = snat znat  in
                                             snat uu____4235  in
                                           pred_nat uu____4224  in
                                         let uu____4244 = snat znat  in
                                         ((Prims.parse_int "18"), uu____4213,
                                           uu____4244)
                                          in
                                       let uu____4269 =
                                         let uu____4291 =
                                           let uu____4311 =
                                             let uu____4322 =
                                               let uu____4331 =
                                                 let uu____4340 = snat znat
                                                    in
                                                 snat uu____4340  in
                                               let uu____4349 = snat znat  in
                                               minus_nat uu____4331
                                                 uu____4349
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____4322
                                              in
                                           let uu____4358 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____4311, uu____4358)
                                            in
                                         let uu____4383 =
                                           let uu____4405 =
                                             let uu____4425 =
                                               let uu____4436 =
                                                 let uu____4445 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 let uu____4455 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 minus_nat uu____4445
                                                   uu____4455
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____4436
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____4425, znat)
                                              in
                                           let uu____4479 =
                                             let uu____4501 =
                                               let uu____4521 =
                                                 let uu____4532 =
                                                   let uu____4541 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   let uu____4551 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   minus_nat uu____4541
                                                     uu____4551
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____4532
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____4521, znat)
                                                in
                                             let uu____4575 =
                                               let uu____4597 =
                                                 let uu____4617 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____4629 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____4617, uu____4629)
                                                  in
                                               let uu____4655 =
                                                 let uu____4677 =
                                                   let uu____4697 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____4709 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____4697, uu____4709)
                                                    in
                                                 let uu____4735 =
                                                   let uu____4757 =
                                                     let uu____4777 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____4789 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____4777,
                                                       uu____4789)
                                                      in
                                                   let uu____4815 =
                                                     let uu____4837 =
                                                       let uu____4857 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____4869 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____4857,
                                                         uu____4869)
                                                        in
                                                     let uu____4895 =
                                                       let uu____4917 =
                                                         let uu____4937 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____4949 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____4937,
                                                           uu____4949)
                                                          in
                                                       let uu____4975 =
                                                         let uu____4997 =
                                                           let uu____5017 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____5029 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____5017,
                                                             uu____5029)
                                                            in
                                                         let uu____5055 =
                                                           let uu____5077 =
                                                             let uu____5097 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____5109 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____5097,
                                                               uu____5109)
                                                              in
                                                           let uu____5135 =
                                                             let uu____5157 =
                                                               let uu____5177
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____5189
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____5177,
                                                                 uu____5189)
                                                                in
                                                             let uu____5215 =
                                                               let uu____5237
                                                                 =
                                                                 let uu____5257
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____5269
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____5257,
                                                                   uu____5269)
                                                                  in
                                                               let uu____5295
                                                                 =
                                                                 let uu____5317
                                                                   =
                                                                   let uu____5337
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____5349
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____5337,
                                                                    uu____5349)
                                                                    in
                                                                 let uu____5375
                                                                   =
                                                                   let uu____5397
                                                                    =
                                                                    let uu____5417
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____5429
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____5417,
                                                                    uu____5429)
                                                                     in
                                                                   let uu____5455
                                                                    =
                                                                    let uu____5477
                                                                    =
                                                                    let uu____5497
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____5509
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____5497,
                                                                    uu____5509)
                                                                     in
                                                                    let uu____5535
                                                                    =
                                                                    let uu____5557
                                                                    =
                                                                    let uu____5577
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____5589
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____5577,
                                                                    uu____5589)
                                                                     in
                                                                    let uu____5615
                                                                    =
                                                                    let uu____5637
                                                                    =
                                                                    let uu____5657
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____5669
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____5657,
                                                                    uu____5669)
                                                                     in
                                                                    let uu____5695
                                                                    =
                                                                    let uu____5717
                                                                    =
                                                                    let uu____5737
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____5749
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____5737,
                                                                    uu____5749)
                                                                     in
                                                                    let uu____5775
                                                                    =
                                                                    let uu____5797
                                                                    =
                                                                    let uu____5817
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____5829
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____5817,
                                                                    uu____5829)
                                                                     in
                                                                    let uu____5855
                                                                    =
                                                                    let uu____5877
                                                                    =
                                                                    let uu____5897
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____5909
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____5897,
                                                                    uu____5909)
                                                                     in
                                                                    let uu____5935
                                                                    =
                                                                    let uu____5957
                                                                    =
                                                                    let uu____5977
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____5989
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____5977,
                                                                    uu____5989)
                                                                     in
                                                                    let uu____6015
                                                                    =
                                                                    let uu____6037
                                                                    =
                                                                    let uu____6057
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____6069
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____6057,
                                                                    uu____6069)
                                                                     in
                                                                    let uu____6095
                                                                    =
                                                                    let uu____6117
                                                                    =
                                                                    let uu____6137
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____6149
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____6137,
                                                                    uu____6149)
                                                                     in
                                                                    let uu____6175
                                                                    =
                                                                    let uu____6197
                                                                    =
                                                                    let uu____6217
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____6229
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____6217,
                                                                    uu____6229)
                                                                     in
                                                                    let uu____6255
                                                                    =
                                                                    let uu____6277
                                                                    =
                                                                    let uu____6297
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____6309
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____6297,
                                                                    uu____6309)
                                                                     in
                                                                    let uu____6335
                                                                    =
                                                                    let uu____6357
                                                                    =
                                                                    let uu____6377
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____6389
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____6377,
                                                                    uu____6389)
                                                                     in
                                                                    let uu____6415
                                                                    =
                                                                    let uu____6437
                                                                    =
                                                                    let uu____6457
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____6469
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____6457,
                                                                    uu____6469)
                                                                     in
                                                                    let uu____6495
                                                                    =
                                                                    let uu____6517
                                                                    =
                                                                    let uu____6537
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____6549
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____6537,
                                                                    uu____6549)
                                                                     in
                                                                    let uu____6575
                                                                    =
                                                                    let uu____6597
                                                                    =
                                                                    let uu____6617
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____6629
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____6617,
                                                                    uu____6629)
                                                                     in
                                                                    let uu____6655
                                                                    =
                                                                    let uu____6677
                                                                    =
                                                                    let uu____6697
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____6709
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____6697,
                                                                    uu____6709)
                                                                     in
                                                                    let uu____6735
                                                                    =
                                                                    let uu____6757
                                                                    =
                                                                    let uu____6777
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____6789
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____6777,
                                                                    uu____6789)
                                                                     in
                                                                    let uu____6815
                                                                    =
                                                                    let uu____6837
                                                                    =
                                                                    let uu____6857
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____6869
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____6857,
                                                                    uu____6869)
                                                                     in
                                                                    let uu____6895
                                                                    =
                                                                    let uu____6917
                                                                    =
                                                                    let uu____6937
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____6949
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____6937,
                                                                    uu____6949)
                                                                     in
                                                                    let uu____6975
                                                                    =
                                                                    let uu____6997
                                                                    =
                                                                    let uu____7017
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____7029
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____7017,
                                                                    uu____7029)
                                                                     in
                                                                    let uu____7055
                                                                    =
                                                                    let uu____7077
                                                                    =
                                                                    let uu____7097
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____7109
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____7097,
                                                                    uu____7109)
                                                                     in
                                                                    let uu____7135
                                                                    =
                                                                    let uu____7157
                                                                    =
                                                                    let uu____7177
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____7189
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____7177,
                                                                    uu____7189)
                                                                     in
                                                                    let uu____7215
                                                                    =
                                                                    let uu____7237
                                                                    =
                                                                    let uu____7257
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____7269
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____7257,
                                                                    uu____7269)
                                                                     in
                                                                    [uu____7237]
                                                                     in
                                                                    uu____7157
                                                                    ::
                                                                    uu____7215
                                                                     in
                                                                    uu____7077
                                                                    ::
                                                                    uu____7135
                                                                     in
                                                                    uu____6997
                                                                    ::
                                                                    uu____7055
                                                                     in
                                                                    uu____6917
                                                                    ::
                                                                    uu____6975
                                                                     in
                                                                    uu____6837
                                                                    ::
                                                                    uu____6895
                                                                     in
                                                                    uu____6757
                                                                    ::
                                                                    uu____6815
                                                                     in
                                                                    uu____6677
                                                                    ::
                                                                    uu____6735
                                                                     in
                                                                    uu____6597
                                                                    ::
                                                                    uu____6655
                                                                     in
                                                                    uu____6517
                                                                    ::
                                                                    uu____6575
                                                                     in
                                                                    uu____6437
                                                                    ::
                                                                    uu____6495
                                                                     in
                                                                    uu____6357
                                                                    ::
                                                                    uu____6415
                                                                     in
                                                                    uu____6277
                                                                    ::
                                                                    uu____6335
                                                                     in
                                                                    uu____6197
                                                                    ::
                                                                    uu____6255
                                                                     in
                                                                    uu____6117
                                                                    ::
                                                                    uu____6175
                                                                     in
                                                                    uu____6037
                                                                    ::
                                                                    uu____6095
                                                                     in
                                                                    uu____5957
                                                                    ::
                                                                    uu____6015
                                                                     in
                                                                    uu____5877
                                                                    ::
                                                                    uu____5935
                                                                     in
                                                                    uu____5797
                                                                    ::
                                                                    uu____5855
                                                                     in
                                                                    uu____5717
                                                                    ::
                                                                    uu____5775
                                                                     in
                                                                    uu____5637
                                                                    ::
                                                                    uu____5695
                                                                     in
                                                                    uu____5557
                                                                    ::
                                                                    uu____5615
                                                                     in
                                                                    uu____5477
                                                                    ::
                                                                    uu____5535
                                                                     in
                                                                   uu____5397
                                                                    ::
                                                                    uu____5455
                                                                    in
                                                                 uu____5317
                                                                   ::
                                                                   uu____5375
                                                                  in
                                                               uu____5237 ::
                                                                 uu____5295
                                                                in
                                                             uu____5157 ::
                                                               uu____5215
                                                              in
                                                           uu____5077 ::
                                                             uu____5135
                                                            in
                                                         uu____4997 ::
                                                           uu____5055
                                                          in
                                                       uu____4917 ::
                                                         uu____4975
                                                        in
                                                     uu____4837 :: uu____4895
                                                      in
                                                   uu____4757 :: uu____4815
                                                    in
                                                 uu____4677 :: uu____4735  in
                                               uu____4597 :: uu____4655  in
                                             uu____4501 :: uu____4575  in
                                           uu____4405 :: uu____4479  in
                                         uu____4291 :: uu____4383  in
                                       uu____4193 :: uu____4269  in
                                     uu____3950 :: uu____4171  in
                                   uu____3707 :: uu____3928  in
                                 uu____3464 :: uu____3685  in
                               uu____3356 :: uu____3442  in
                             uu____3267 :: uu____3334  in
                           uu____3178 :: uu____3245  in
                         uu____3075 :: uu____3156  in
                       uu____2996 :: uu____3053  in
                     uu____2917 :: uu____2974  in
                   uu____2850 :: uu____2895  in
                 uu____2775 :: uu____2828  in
               uu____2708 :: uu____2753  in
             uu____2564 :: uu____2686  in
           uu____2376 :: uu____2542  in
         uu____2243 :: uu____2354  in
       uu____2110 :: uu____2221  in
     uu____2008 :: uu____2088  in
   uu____1884 :: uu____1986)
  
let run_either :
  'Auu____8389 .
    Prims.int ->
      'Auu____8389 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____8389 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____8551 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____8551);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____8664 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____8664 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____8695 =
               let uu____8697 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____8697 expected  in
             FStar_Tests_Util.always i uu____8695)))
  
let (run_interpreter :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        run_either i r expected
          (FStar_TypeChecker_Normalize.normalize
             [FStar_TypeChecker_Env.Beta;
             FStar_TypeChecker_Env.UnfoldUntil
               FStar_Syntax_Syntax.delta_constant;
             FStar_TypeChecker_Env.Primops])
  
let (run_nbe :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        run_either i r expected
          (FStar_TypeChecker_NBE.normalize_for_unit_test
             [FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant])
  
let (run_interpreter_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let interp uu____8840 = run_interpreter i r expected  in
        let uu____8841 =
          let uu____8842 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____8842  in
        (i, uu____8841)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____8896 = run_nbe i r expected  in
        let uu____8897 =
          let uu____8898 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____8898  in
        (i, uu____8897)
  
let run_tests :
  'Auu____8909 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____8909)
      -> 'Auu____8909 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___0_8985  ->
            match uu___0_8985 with | (no,test,res) -> run1 no test res) tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____9040  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____9043 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____9052  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____9055 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____9071  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____9101  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let l = run_tests run_interpreter_with_time  in
     FStar_Util.print_string "Normalizer ok\n"; l)
  
let (run_both_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____9162 = run_nbe i r expected  in
        let norm1 uu____9168 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____9181  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____9184 =
       let uu____9193 = encode (Prims.parse_int "1000")  in
       let uu____9203 =
         let uu____9214 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____9223 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____9214 uu____9223  in
       let_ FStar_Tests_Util.x uu____9193 uu____9203  in
     run_both_with_time (Prims.parse_int "14") uu____9184 z)
  
let (compare_times :
  (Prims.int * FStar_BaseTypes.float) Prims.list ->
    (Prims.int * FStar_BaseTypes.float) Prims.list -> unit)
  =
  fun l_int  ->
    fun l_nbe  ->
      FStar_Util.print_string "Comparing times for normalization and nbe\n";
      FStar_List.iter2
        (fun res1  ->
           fun res2  ->
             let uu____9307 = res1  in
             match uu____9307 with
             | (t1,time_int) ->
                 let uu____9317 = res2  in
                 (match uu____9317 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____9329 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____9329 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____9340  ->
    (let uu____9342 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____9342);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  