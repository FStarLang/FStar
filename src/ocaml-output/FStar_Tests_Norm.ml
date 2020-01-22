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
    if n1 = Prims.int_zero
    then z
    else
      (let uu____39 =
         let uu____42 = encode (n1 - Prims.int_one)  in [uu____42]  in
       FStar_Tests_Util.app succ uu____39)
  
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
        let uu____81 =
          let uu____84 = let uu____85 = b x1  in [uu____85]  in
          FStar_Syntax_Util.abs uu____84 e' FStar_Pervasives_Native.None  in
        FStar_Tests_Util.app uu____81 [e]
  
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
            [FStar_Syntax_Syntax.NM (x1, Prims.int_zero)] e'
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
  let uu____155 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____155 FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____158 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____158 FStar_Syntax_Syntax.delta_constant
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
    let uu____177 =
      let uu____184 =
        let uu____185 =
          let uu____202 = tm_fv snat_l  in
          let uu____205 =
            let uu____216 = FStar_Syntax_Syntax.as_arg s  in [uu____216]  in
          (uu____202, uu____205)  in
        FStar_Syntax_Syntax.Tm_app uu____185  in
      FStar_Syntax_Syntax.mk uu____184  in
    uu____177 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____258 . 'Auu____258 -> 'Auu____258 FStar_Syntax_Syntax.withinfo_t =
  fun p  -> FStar_Syntax_Syntax.withinfo p FStar_Range.dummyRange 
let (snat_type : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  let uu____269 =
    let uu____270 = lid "snat"  in
    FStar_Syntax_Syntax.lid_as_fv uu____270
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  tm_fv uu____269 
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
      let uu____373 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____373, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____417 =
        let uu____420 =
          let uu____421 =
            let uu____435 =
              let uu____445 =
                let uu____453 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____453, false)  in
              [uu____445]  in
            (snat_l, uu____435)  in
          FStar_Syntax_Syntax.Pat_cons uu____421  in
        pat uu____420  in
      let uu____483 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___21_488 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___21_488.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = Prims.int_zero;
                FStar_Syntax_Syntax.sort =
                  (uu___21_488.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____417, FStar_Pervasives_Native.None, uu____483)  in
    mk_match s [zbranch; sbranch]
  
let (minus_nat :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let minus1 = FStar_Tests_Util.m  in
      let x1 =
        let uu___27_515 = FStar_Tests_Util.x  in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___27_515.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index = (uu___27_515.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = snat_type
        }  in
      let y1 =
        let uu___30_517 = FStar_Tests_Util.y  in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___30_517.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index = (uu___30_517.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = snat_type
        }  in
      let zbranch =
        let uu____533 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____552 = FStar_Tests_Util.nm x1  in
        (uu____533, FStar_Pervasives_Native.None, uu____552)  in
      let sbranch =
        let uu____580 =
          let uu____583 =
            let uu____584 =
              let uu____598 =
                let uu____608 =
                  let uu____616 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____616, false)  in
                [uu____608]  in
              (snat_l, uu____598)  in
            FStar_Syntax_Syntax.Pat_cons uu____584  in
          pat uu____583  in
        let uu____646 =
          let uu____649 = FStar_Tests_Util.nm minus1  in
          let uu____652 =
            let uu____655 =
              let uu____656 = FStar_Tests_Util.nm x1  in pred_nat uu____656
               in
            let uu____659 =
              let uu____662 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____662]  in
            uu____655 :: uu____659  in
          FStar_Tests_Util.app uu____649 uu____652  in
        (uu____580, FStar_Pervasives_Native.None, uu____646)  in
      let lb =
        let uu____674 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____678 =
          let uu____681 =
            let uu____682 =
              let uu____683 = b x1  in
              let uu____690 = let uu____699 = b y1  in [uu____699]  in
              uu____683 :: uu____690  in
            let uu____724 =
              let uu____727 = FStar_Tests_Util.nm y1  in
              mk_match uu____727 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____682 uu____724
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, Prims.int_zero)] uu____681
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____674;
          FStar_Syntax_Syntax.lbdef = uu____678;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____734 =
        let uu____741 =
          let uu____742 =
            let uu____756 =
              let uu____759 =
                let uu____760 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____760 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, Prims.int_zero)] uu____759
               in
            ((true, [lb]), uu____756)  in
          FStar_Syntax_Syntax.Tm_let uu____742  in
        FStar_Syntax_Syntax.mk uu____741  in
      uu____734 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = Prims.int_zero
      then out
      else (let uu____804 = snat out  in aux uu____804 (n2 - Prims.int_one))
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
  (let uu____870 =
     let uu____882 =
       let uu____885 =
         let uu____888 =
           let uu____891 =
             let uu____894 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____894]  in
           id :: uu____891  in
         one :: uu____888  in
       FStar_Tests_Util.app apply uu____885  in
     let uu____895 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     (Prims.int_zero, uu____882, uu____895)  in
   let uu____904 =
     let uu____918 =
       let uu____930 =
         let uu____933 =
           let uu____936 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____936]  in
         FStar_Tests_Util.app id uu____933  in
       let uu____937 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       (Prims.int_one, uu____930, uu____937)  in
     let uu____946 =
       let uu____960 =
         let uu____972 =
           let uu____975 =
             let uu____978 =
               let uu____981 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____982 =
                 let uu____985 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____985]  in
               uu____981 :: uu____982  in
             tt :: uu____978  in
           FStar_Tests_Util.app apply uu____975  in
         let uu____986 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         (Prims.int_one, uu____972, uu____986)  in
       let uu____995 =
         let uu____1009 =
           let uu____1021 =
             let uu____1024 =
               let uu____1027 =
                 let uu____1030 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____1031 =
                   let uu____1034 = FStar_Tests_Util.nm FStar_Tests_Util.m
                      in
                   [uu____1034]  in
                 uu____1030 :: uu____1031  in
               ff :: uu____1027  in
             FStar_Tests_Util.app apply uu____1024  in
           let uu____1035 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.of_int (2)), uu____1021, uu____1035)  in
         let uu____1044 =
           let uu____1058 =
             let uu____1070 =
               let uu____1073 =
                 let uu____1076 =
                   let uu____1079 =
                     let uu____1082 =
                       let uu____1085 =
                         let uu____1088 =
                           let uu____1091 =
                             let uu____1094 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____1095 =
                               let uu____1098 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____1098]  in
                             uu____1094 :: uu____1095  in
                           ff :: uu____1091  in
                         apply :: uu____1088  in
                       apply :: uu____1085  in
                     apply :: uu____1082  in
                   apply :: uu____1079  in
                 apply :: uu____1076  in
               FStar_Tests_Util.app apply uu____1073  in
             let uu____1099 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.of_int (3)), uu____1070, uu____1099)  in
           let uu____1108 =
             let uu____1122 =
               let uu____1134 =
                 let uu____1137 =
                   let uu____1140 =
                     let uu____1143 =
                       let uu____1146 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n  in
                       let uu____1147 =
                         let uu____1150 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____1150]  in
                       uu____1146 :: uu____1147  in
                     ff :: uu____1143  in
                   apply :: uu____1140  in
                 FStar_Tests_Util.app twice uu____1137  in
               let uu____1151 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.of_int (4)), uu____1134, uu____1151)  in
             let uu____1160 =
               let uu____1174 =
                 let uu____1186 = minus one z  in
                 ((Prims.of_int (5)), uu____1186, one)  in
               let uu____1195 =
                 let uu____1209 =
                   let uu____1221 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.of_int (6)), uu____1221, z)  in
                 let uu____1230 =
                   let uu____1244 =
                     let uu____1256 = minus one one  in
                     ((Prims.of_int (7)), uu____1256, z)  in
                   let uu____1265 =
                     let uu____1279 =
                       let uu____1291 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.of_int (8)), uu____1291, one)  in
                     let uu____1300 =
                       let uu____1314 =
                         let uu____1326 = FStar_Tests_Util.app mul [two; one]
                            in
                         ((Prims.of_int (9)), uu____1326, two)  in
                       let uu____1335 =
                         let uu____1349 =
                           let uu____1361 =
                             let uu____1364 =
                               let uu____1367 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____1367; one]  in
                             FStar_Tests_Util.app mul uu____1364  in
                           ((Prims.of_int (10)), uu____1361, two)  in
                         let uu____1374 =
                           let uu____1388 =
                             let uu____1400 =
                               let uu____1403 = encode (Prims.of_int (10))
                                  in
                               let uu____1405 = encode (Prims.of_int (10))
                                  in
                               minus uu____1403 uu____1405  in
                             ((Prims.of_int (11)), uu____1400, z)  in
                           let uu____1415 =
                             let uu____1429 =
                               let uu____1441 =
                                 let uu____1444 = encode (Prims.of_int (100))
                                    in
                                 let uu____1446 = encode (Prims.of_int (100))
                                    in
                                 minus uu____1444 uu____1446  in
                               ((Prims.of_int (12)), uu____1441, z)  in
                             let uu____1456 =
                               let uu____1470 =
                                 let uu____1482 =
                                   let uu____1485 =
                                     encode (Prims.of_int (100))  in
                                   let uu____1487 =
                                     let uu____1490 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____1491 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____1490 uu____1491  in
                                   let_ FStar_Tests_Util.x uu____1485
                                     uu____1487
                                    in
                                 ((Prims.of_int (13)), uu____1482, z)  in
                               let uu____1500 =
                                 let uu____1514 =
                                   let uu____1526 =
                                     let uu____1529 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____1530 =
                                       let uu____1533 =
                                         let uu____1534 =
                                           let uu____1537 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____1538 =
                                             let uu____1541 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____1541]  in
                                           uu____1537 :: uu____1538  in
                                         FStar_Tests_Util.app mul uu____1534
                                          in
                                       let uu____1542 =
                                         let uu____1545 =
                                           let uu____1546 =
                                             let uu____1549 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____1550 =
                                               let uu____1553 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____1553]  in
                                             uu____1549 :: uu____1550  in
                                           FStar_Tests_Util.app mul
                                             uu____1546
                                            in
                                         let uu____1554 =
                                           let uu____1557 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____1558 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____1557 uu____1558  in
                                         let_ FStar_Tests_Util.h uu____1545
                                           uu____1554
                                          in
                                       let_ FStar_Tests_Util.y uu____1533
                                         uu____1542
                                        in
                                     let_ FStar_Tests_Util.x uu____1529
                                       uu____1530
                                      in
                                   ((Prims.of_int (15)), uu____1526, z)  in
                                 let uu____1567 =
                                   let uu____1581 =
                                     let uu____1593 =
                                       let uu____1596 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____1599 =
                                         let uu____1600 =
                                           let uu____1603 =
                                             let uu____1606 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____1607 =
                                               let uu____1610 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____1610]  in
                                             uu____1606 :: uu____1607  in
                                           FStar_Tests_Util.app mul
                                             uu____1603
                                            in
                                         let uu____1611 =
                                           let uu____1612 =
                                             let uu____1615 =
                                               let uu____1618 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____1619 =
                                                 let uu____1622 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____1622]  in
                                               uu____1618 :: uu____1619  in
                                             FStar_Tests_Util.app mul
                                               uu____1615
                                              in
                                           let uu____1623 =
                                             let uu____1624 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____1625 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____1624 uu____1625  in
                                           mk_let FStar_Tests_Util.h
                                             uu____1612 uu____1623
                                            in
                                         mk_let FStar_Tests_Util.y uu____1600
                                           uu____1611
                                          in
                                       mk_let FStar_Tests_Util.x uu____1596
                                         uu____1599
                                        in
                                     ((Prims.of_int (16)), uu____1593, z)  in
                                   let uu____1634 =
                                     let uu____1648 =
                                       let uu____1660 =
                                         let uu____1663 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____1664 =
                                           let uu____1667 =
                                             let uu____1668 =
                                               let uu____1671 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____1672 =
                                                 let uu____1675 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____1675]  in
                                               uu____1671 :: uu____1672  in
                                             FStar_Tests_Util.app mul
                                               uu____1668
                                              in
                                           let uu____1676 =
                                             let uu____1679 =
                                               let uu____1680 =
                                                 let uu____1683 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____1684 =
                                                   let uu____1687 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____1687]  in
                                                 uu____1683 :: uu____1684  in
                                               FStar_Tests_Util.app mul
                                                 uu____1680
                                                in
                                             let uu____1688 =
                                               let uu____1691 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____1692 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____1691 uu____1692
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____1679 uu____1688
                                              in
                                           let_ FStar_Tests_Util.y uu____1667
                                             uu____1676
                                            in
                                         let_ FStar_Tests_Util.x uu____1663
                                           uu____1664
                                          in
                                       ((Prims.of_int (17)), uu____1660, z)
                                        in
                                     let uu____1701 =
                                       let uu____1715 =
                                         let uu____1727 =
                                           let uu____1730 =
                                             let uu____1733 = snat znat  in
                                             snat uu____1733  in
                                           pred_nat uu____1730  in
                                         let uu____1734 = snat znat  in
                                         ((Prims.of_int (18)), uu____1727,
                                           uu____1734)
                                          in
                                       let uu____1743 =
                                         let uu____1757 =
                                           let uu____1769 =
                                             let uu____1772 =
                                               let uu____1773 =
                                                 let uu____1774 = snat znat
                                                    in
                                                 snat uu____1774  in
                                               let uu____1775 = snat znat  in
                                               minus_nat uu____1773
                                                 uu____1775
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____1772
                                              in
                                           let uu____1776 = snat znat  in
                                           ((Prims.of_int (19)), uu____1769,
                                             uu____1776)
                                            in
                                         let uu____1785 =
                                           let uu____1799 =
                                             let uu____1811 =
                                               let uu____1814 =
                                                 let uu____1815 =
                                                   encode_nat
                                                     (Prims.of_int (10))
                                                    in
                                                 let uu____1817 =
                                                   encode_nat
                                                     (Prims.of_int (10))
                                                    in
                                                 minus_nat uu____1815
                                                   uu____1817
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____1814
                                                in
                                             ((Prims.of_int (20)),
                                               uu____1811, znat)
                                              in
                                           let uu____1825 =
                                             let uu____1839 =
                                               let uu____1851 =
                                                 let uu____1854 =
                                                   let uu____1855 =
                                                     encode_nat
                                                       (Prims.of_int (100))
                                                      in
                                                   let uu____1857 =
                                                     encode_nat
                                                       (Prims.of_int (100))
                                                      in
                                                   minus_nat uu____1855
                                                     uu____1857
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____1854
                                                  in
                                               ((Prims.of_int (21)),
                                                 uu____1851, znat)
                                                in
                                             let uu____1865 =
                                               let uu____1879 =
                                                 let uu____1891 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____1895 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.of_int (24)),
                                                   uu____1891, uu____1895)
                                                  in
                                               let uu____1905 =
                                                 let uu____1919 =
                                                   let uu____1931 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____1935 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.of_int (241)),
                                                     uu____1931, uu____1935)
                                                    in
                                                 let uu____1945 =
                                                   let uu____1959 =
                                                     let uu____1971 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____1975 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.of_int (25)),
                                                       uu____1971,
                                                       uu____1975)
                                                      in
                                                   let uu____1985 =
                                                     let uu____1999 =
                                                       let uu____2011 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____2015 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.of_int (26)),
                                                         uu____2011,
                                                         uu____2015)
                                                        in
                                                     let uu____2025 =
                                                       let uu____2039 =
                                                         let uu____2051 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____2055 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.of_int (28)),
                                                           uu____2051,
                                                           uu____2055)
                                                          in
                                                       let uu____2065 =
                                                         let uu____2079 =
                                                           let uu____2091 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____2095 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.of_int (29)),
                                                             uu____2091,
                                                             uu____2095)
                                                            in
                                                         let uu____2105 =
                                                           let uu____2119 =
                                                             let uu____2131 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____2135 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.of_int (31)),
                                                               uu____2131,
                                                               uu____2135)
                                                              in
                                                           let uu____2145 =
                                                             let uu____2159 =
                                                               let uu____2171
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____2175
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.of_int (32)),
                                                                 uu____2171,
                                                                 uu____2175)
                                                                in
                                                             let uu____2185 =
                                                               let uu____2199
                                                                 =
                                                                 let uu____2211
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____2215
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.of_int (33)),
                                                                   uu____2211,
                                                                   uu____2215)
                                                                  in
                                                               let uu____2225
                                                                 =
                                                                 let uu____2239
                                                                   =
                                                                   let uu____2251
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____2255
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.of_int (34)),
                                                                    uu____2251,
                                                                    uu____2255)
                                                                    in
                                                                 let uu____2265
                                                                   =
                                                                   let uu____2279
                                                                    =
                                                                    let uu____2291
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____2295
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.of_int (35)),
                                                                    uu____2291,
                                                                    uu____2295)
                                                                     in
                                                                   let uu____2305
                                                                    =
                                                                    let uu____2319
                                                                    =
                                                                    let uu____2331
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____2335
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.of_int (36)),
                                                                    uu____2331,
                                                                    uu____2335)
                                                                     in
                                                                    let uu____2345
                                                                    =
                                                                    let uu____2359
                                                                    =
                                                                    let uu____2371
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____2375
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.of_int (301)),
                                                                    uu____2371,
                                                                    uu____2375)
                                                                     in
                                                                    let uu____2385
                                                                    =
                                                                    let uu____2399
                                                                    =
                                                                    let uu____2411
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____2415
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.of_int (3012)),
                                                                    uu____2411,
                                                                    uu____2415)
                                                                     in
                                                                    let uu____2425
                                                                    =
                                                                    let uu____2439
                                                                    =
                                                                    let uu____2451
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____2455
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.of_int (302)),
                                                                    uu____2451,
                                                                    uu____2455)
                                                                     in
                                                                    let uu____2465
                                                                    =
                                                                    let uu____2479
                                                                    =
                                                                    let uu____2491
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____2495
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.of_int (303)),
                                                                    uu____2491,
                                                                    uu____2495)
                                                                     in
                                                                    let uu____2505
                                                                    =
                                                                    let uu____2519
                                                                    =
                                                                    let uu____2531
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____2535
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.of_int (3031)),
                                                                    uu____2531,
                                                                    uu____2535)
                                                                     in
                                                                    let uu____2545
                                                                    =
                                                                    let uu____2559
                                                                    =
                                                                    let uu____2571
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____2575
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.of_int (3032)),
                                                                    uu____2571,
                                                                    uu____2575)
                                                                     in
                                                                    let uu____2585
                                                                    =
                                                                    let uu____2599
                                                                    =
                                                                    let uu____2611
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____2615
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.of_int (3033)),
                                                                    uu____2611,
                                                                    uu____2615)
                                                                     in
                                                                    let uu____2625
                                                                    =
                                                                    let uu____2639
                                                                    =
                                                                    let uu____2651
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____2655
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.of_int (3034)),
                                                                    uu____2651,
                                                                    uu____2655)
                                                                     in
                                                                    let uu____2665
                                                                    =
                                                                    let uu____2679
                                                                    =
                                                                    let uu____2691
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____2695
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.of_int (3035)),
                                                                    uu____2691,
                                                                    uu____2695)
                                                                     in
                                                                    let uu____2705
                                                                    =
                                                                    let uu____2719
                                                                    =
                                                                    let uu____2731
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____2735
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.of_int (3036)),
                                                                    uu____2731,
                                                                    uu____2735)
                                                                     in
                                                                    let uu____2745
                                                                    =
                                                                    let uu____2759
                                                                    =
                                                                    let uu____2771
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____2775
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.of_int (305)),
                                                                    uu____2771,
                                                                    uu____2775)
                                                                     in
                                                                    let uu____2785
                                                                    =
                                                                    let uu____2799
                                                                    =
                                                                    let uu____2811
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____2815
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.of_int (306)),
                                                                    uu____2811,
                                                                    uu____2815)
                                                                     in
                                                                    let uu____2825
                                                                    =
                                                                    let uu____2839
                                                                    =
                                                                    let uu____2851
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____2855
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.of_int (307)),
                                                                    uu____2851,
                                                                    uu____2855)
                                                                     in
                                                                    let uu____2865
                                                                    =
                                                                    let uu____2879
                                                                    =
                                                                    let uu____2891
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____2895
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.of_int (308)),
                                                                    uu____2891,
                                                                    uu____2895)
                                                                     in
                                                                    let uu____2905
                                                                    =
                                                                    let uu____2919
                                                                    =
                                                                    let uu____2931
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____2935
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.of_int (304)),
                                                                    uu____2931,
                                                                    uu____2935)
                                                                     in
                                                                    let uu____2945
                                                                    =
                                                                    let uu____2959
                                                                    =
                                                                    let uu____2971
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____2975
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.of_int (305)),
                                                                    uu____2971,
                                                                    uu____2975)
                                                                     in
                                                                    let uu____2985
                                                                    =
                                                                    let uu____2999
                                                                    =
                                                                    let uu____3011
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____3015
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.of_int (309)),
                                                                    uu____3011,
                                                                    uu____3015)
                                                                     in
                                                                    let uu____3025
                                                                    =
                                                                    let uu____3039
                                                                    =
                                                                    let uu____3051
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____3055
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.of_int (310)),
                                                                    uu____3051,
                                                                    uu____3055)
                                                                     in
                                                                    let uu____3065
                                                                    =
                                                                    let uu____3079
                                                                    =
                                                                    let uu____3091
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____3095
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.of_int (401)),
                                                                    uu____3091,
                                                                    uu____3095)
                                                                     in
                                                                    let uu____3105
                                                                    =
                                                                    let uu____3119
                                                                    =
                                                                    let uu____3131
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____3135
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.of_int (402)),
                                                                    uu____3131,
                                                                    uu____3135)
                                                                     in
                                                                    let uu____3145
                                                                    =
                                                                    let uu____3159
                                                                    =
                                                                    let uu____3171
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____3175
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.of_int (403)),
                                                                    uu____3171,
                                                                    uu____3175)
                                                                     in
                                                                    let uu____3185
                                                                    =
                                                                    let uu____3199
                                                                    =
                                                                    let uu____3211
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____3215
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.of_int (404)),
                                                                    uu____3211,
                                                                    uu____3215)
                                                                     in
                                                                    let uu____3225
                                                                    =
                                                                    let uu____3239
                                                                    =
                                                                    let uu____3251
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun (x:list int) -> match x with | [] -> 0 | hd::tl -> 1) []"
                                                                     in
                                                                    let uu____3255
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "0"  in
                                                                    ((Prims.of_int (405)),
                                                                    uu____3251,
                                                                    uu____3255)
                                                                     in
                                                                    [uu____3239]
                                                                     in
                                                                    uu____3199
                                                                    ::
                                                                    uu____3225
                                                                     in
                                                                    uu____3159
                                                                    ::
                                                                    uu____3185
                                                                     in
                                                                    uu____3119
                                                                    ::
                                                                    uu____3145
                                                                     in
                                                                    uu____3079
                                                                    ::
                                                                    uu____3105
                                                                     in
                                                                    uu____3039
                                                                    ::
                                                                    uu____3065
                                                                     in
                                                                    uu____2999
                                                                    ::
                                                                    uu____3025
                                                                     in
                                                                    uu____2959
                                                                    ::
                                                                    uu____2985
                                                                     in
                                                                    uu____2919
                                                                    ::
                                                                    uu____2945
                                                                     in
                                                                    uu____2879
                                                                    ::
                                                                    uu____2905
                                                                     in
                                                                    uu____2839
                                                                    ::
                                                                    uu____2865
                                                                     in
                                                                    uu____2799
                                                                    ::
                                                                    uu____2825
                                                                     in
                                                                    uu____2759
                                                                    ::
                                                                    uu____2785
                                                                     in
                                                                    uu____2719
                                                                    ::
                                                                    uu____2745
                                                                     in
                                                                    uu____2679
                                                                    ::
                                                                    uu____2705
                                                                     in
                                                                    uu____2639
                                                                    ::
                                                                    uu____2665
                                                                     in
                                                                    uu____2599
                                                                    ::
                                                                    uu____2625
                                                                     in
                                                                    uu____2559
                                                                    ::
                                                                    uu____2585
                                                                     in
                                                                    uu____2519
                                                                    ::
                                                                    uu____2545
                                                                     in
                                                                    uu____2479
                                                                    ::
                                                                    uu____2505
                                                                     in
                                                                    uu____2439
                                                                    ::
                                                                    uu____2465
                                                                     in
                                                                    uu____2399
                                                                    ::
                                                                    uu____2425
                                                                     in
                                                                    uu____2359
                                                                    ::
                                                                    uu____2385
                                                                     in
                                                                    uu____2319
                                                                    ::
                                                                    uu____2345
                                                                     in
                                                                   uu____2279
                                                                    ::
                                                                    uu____2305
                                                                    in
                                                                 uu____2239
                                                                   ::
                                                                   uu____2265
                                                                  in
                                                               uu____2199 ::
                                                                 uu____2225
                                                                in
                                                             uu____2159 ::
                                                               uu____2185
                                                              in
                                                           uu____2119 ::
                                                             uu____2145
                                                            in
                                                         uu____2079 ::
                                                           uu____2105
                                                          in
                                                       uu____2039 ::
                                                         uu____2065
                                                        in
                                                     uu____1999 :: uu____2025
                                                      in
                                                   uu____1959 :: uu____1985
                                                    in
                                                 uu____1919 :: uu____1945  in
                                               uu____1879 :: uu____1905  in
                                             uu____1839 :: uu____1865  in
                                           uu____1799 :: uu____1825  in
                                         uu____1757 :: uu____1785  in
                                       uu____1715 :: uu____1743  in
                                     uu____1648 :: uu____1701  in
                                   uu____1581 :: uu____1634  in
                                 uu____1514 :: uu____1567  in
                               uu____1470 :: uu____1500  in
                             uu____1429 :: uu____1456  in
                           uu____1388 :: uu____1415  in
                         uu____1349 :: uu____1374  in
                       uu____1314 :: uu____1335  in
                     uu____1279 :: uu____1300  in
                   uu____1244 :: uu____1265  in
                 uu____1209 :: uu____1230  in
               uu____1174 :: uu____1195  in
             uu____1122 :: uu____1160  in
           uu____1058 :: uu____1108  in
         uu____1009 :: uu____1044  in
       uu____960 :: uu____995  in
     uu____918 :: uu____946  in
   uu____870 :: uu____904)
  
let run_either :
  'Auu____3914 .
    Prims.int ->
      'Auu____3914 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____3914 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____3952 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____3952);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____3957 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____3957 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____3980 =
               let uu____3982 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____3982 expected  in
             FStar_Tests_Util.always i uu____3980)))
  
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
        let interp uu____4061 = run_interpreter i r expected  in
        let uu____4062 =
          let uu____4063 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____4063  in
        (i, uu____4062)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____4101 = run_nbe i r expected  in
        let uu____4102 =
          let uu____4103 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____4103  in
        (i, uu____4102)
  
let run_tests :
  'Auu____4114 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____4114)
      -> 'Auu____4114 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___0_4166  ->
            match uu___0_4166 with | (no,test,res) -> run1 no test res) tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____4197  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____4200 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____4209  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____4212 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____4228  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____4258  ->
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
        let nbe1 uu____4303 = run_nbe i r expected  in
        let norm1 uu____4309 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____4322  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____4325 =
       let uu____4326 = encode (Prims.of_int (1000))  in
       let uu____4328 =
         let uu____4331 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____4332 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____4331 uu____4332  in
       let_ FStar_Tests_Util.x uu____4326 uu____4328  in
     run_both_with_time (Prims.of_int (14)) uu____4325 z)
  
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
             let uu____4408 = res1  in
             match uu____4408 with
             | (t1,time_int) ->
                 let uu____4418 = res2  in
                 (match uu____4418 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____4430 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____4430 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____4441  ->
    (let uu____4443 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____4443);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  