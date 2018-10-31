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
      (let uu____40 =
         let uu____43 = encode (n1 - (Prims.parse_int "1"))  in [uu____43]
          in
       FStar_Tests_Util.app succ uu____40)
  
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
        let uu____82 =
          let uu____85 = let uu____86 = b x1  in [uu____86]  in
          FStar_Syntax_Util.abs uu____85 e' FStar_Pervasives_Native.None  in
        FStar_Tests_Util.app uu____82 [e]
  
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
  let uu____156 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____156 FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____159 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____159 FStar_Syntax_Syntax.delta_constant
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
    let uu____178 =
      let uu____185 =
        let uu____186 =
          let uu____203 = tm_fv snat_l  in
          let uu____206 =
            let uu____217 = FStar_Syntax_Syntax.as_arg s  in [uu____217]  in
          (uu____203, uu____206)  in
        FStar_Syntax_Syntax.Tm_app uu____186  in
      FStar_Syntax_Syntax.mk uu____185  in
    uu____178 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____262 . 'Auu____262 -> 'Auu____262 FStar_Syntax_Syntax.withinfo_t =
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
      let uu____371 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____371, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____415 =
        let uu____418 =
          let uu____419 =
            let uu____433 =
              let uu____443 =
                let uu____451 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____451, false)  in
              [uu____443]  in
            (snat_l, uu____433)  in
          FStar_Syntax_Syntax.Pat_cons uu____419  in
        pat uu____418  in
      let uu____481 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___479_486 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___479_486.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___479_486.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____415, FStar_Pervasives_Native.None, uu____481)  in
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
        let uu____527 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____546 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____527, FStar_Pervasives_Native.None, uu____546)  in
      let sbranch =
        let uu____574 =
          let uu____577 =
            let uu____578 =
              let uu____592 =
                let uu____602 =
                  let uu____610 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____610, false)  in
                [uu____602]  in
              (snat_l, uu____592)  in
            FStar_Syntax_Syntax.Pat_cons uu____578  in
          pat uu____577  in
        let uu____640 =
          let uu____643 = FStar_Tests_Util.nm minus1  in
          let uu____646 =
            let uu____649 =
              let uu____650 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____650  in
            let uu____653 =
              let uu____656 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____656]  in
            uu____649 :: uu____653  in
          FStar_Tests_Util.app uu____643 uu____646  in
        (uu____574, FStar_Pervasives_Native.None, uu____640)  in
      let lb =
        let uu____668 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____672 =
          let uu____675 =
            let uu____676 =
              let uu____677 = b FStar_Tests_Util.x  in
              let uu____684 =
                let uu____693 = b FStar_Tests_Util.y  in [uu____693]  in
              uu____677 :: uu____684  in
            let uu____718 =
              let uu____721 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____721 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____676 uu____718
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____675
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____668;
          FStar_Syntax_Syntax.lbdef = uu____672;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____728 =
        let uu____735 =
          let uu____736 =
            let uu____750 =
              let uu____753 =
                let uu____754 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____754 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____753
               in
            ((true, [lb]), uu____750)  in
          FStar_Syntax_Syntax.Tm_let uu____736  in
        FStar_Syntax_Syntax.mk uu____735  in
      uu____728 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____801 = snat out  in
         aux uu____801 (n2 - (Prims.parse_int "1")))
       in
    aux znat n1
  
let (tests :
  (Prims.int,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                                    FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 Prims.list)
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
  (let uu____867 =
     let uu____879 =
       let uu____882 =
         let uu____885 =
           let uu____888 =
             let uu____891 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____891]  in
           id :: uu____888  in
         one :: uu____885  in
       FStar_Tests_Util.app apply uu____882  in
     let uu____892 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____879, uu____892)  in
   let uu____901 =
     let uu____915 =
       let uu____927 =
         let uu____930 =
           let uu____933 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____933]  in
         FStar_Tests_Util.app id uu____930  in
       let uu____934 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____927, uu____934)  in
     let uu____943 =
       let uu____957 =
         let uu____969 =
           let uu____972 =
             let uu____975 =
               let uu____978 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____979 =
                 let uu____982 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____982]  in
               uu____978 :: uu____979  in
             tt :: uu____975  in
           FStar_Tests_Util.app apply uu____972  in
         let uu____983 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____969, uu____983)  in
       let uu____992 =
         let uu____1006 =
           let uu____1018 =
             let uu____1021 =
               let uu____1024 =
                 let uu____1027 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____1028 =
                   let uu____1031 = FStar_Tests_Util.nm FStar_Tests_Util.m
                      in
                   [uu____1031]  in
                 uu____1027 :: uu____1028  in
               ff :: uu____1024  in
             FStar_Tests_Util.app apply uu____1021  in
           let uu____1032 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____1018, uu____1032)  in
         let uu____1041 =
           let uu____1055 =
             let uu____1067 =
               let uu____1070 =
                 let uu____1073 =
                   let uu____1076 =
                     let uu____1079 =
                       let uu____1082 =
                         let uu____1085 =
                           let uu____1088 =
                             let uu____1091 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____1092 =
                               let uu____1095 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____1095]  in
                             uu____1091 :: uu____1092  in
                           ff :: uu____1088  in
                         apply :: uu____1085  in
                       apply :: uu____1082  in
                     apply :: uu____1079  in
                   apply :: uu____1076  in
                 apply :: uu____1073  in
               FStar_Tests_Util.app apply uu____1070  in
             let uu____1096 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____1067, uu____1096)  in
           let uu____1105 =
             let uu____1119 =
               let uu____1131 =
                 let uu____1134 =
                   let uu____1137 =
                     let uu____1140 =
                       let uu____1143 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n  in
                       let uu____1144 =
                         let uu____1147 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____1147]  in
                       uu____1143 :: uu____1144  in
                     ff :: uu____1140  in
                   apply :: uu____1137  in
                 FStar_Tests_Util.app twice uu____1134  in
               let uu____1148 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____1131, uu____1148)  in
             let uu____1157 =
               let uu____1171 =
                 let uu____1183 = minus one z  in
                 ((Prims.parse_int "5"), uu____1183, one)  in
               let uu____1192 =
                 let uu____1206 =
                   let uu____1218 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____1218, z)  in
                 let uu____1227 =
                   let uu____1241 =
                     let uu____1253 = minus one one  in
                     ((Prims.parse_int "7"), uu____1253, z)  in
                   let uu____1262 =
                     let uu____1276 =
                       let uu____1288 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____1288, one)  in
                     let uu____1297 =
                       let uu____1311 =
                         let uu____1323 = FStar_Tests_Util.app mul [two; one]
                            in
                         ((Prims.parse_int "9"), uu____1323, two)  in
                       let uu____1332 =
                         let uu____1346 =
                           let uu____1358 =
                             let uu____1361 =
                               let uu____1364 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____1364; one]  in
                             FStar_Tests_Util.app mul uu____1361  in
                           ((Prims.parse_int "10"), uu____1358, two)  in
                         let uu____1371 =
                           let uu____1385 =
                             let uu____1397 =
                               let uu____1400 = encode (Prims.parse_int "10")
                                  in
                               let uu____1402 = encode (Prims.parse_int "10")
                                  in
                               minus uu____1400 uu____1402  in
                             ((Prims.parse_int "11"), uu____1397, z)  in
                           let uu____1412 =
                             let uu____1426 =
                               let uu____1438 =
                                 let uu____1441 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____1443 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____1441 uu____1443  in
                               ((Prims.parse_int "12"), uu____1438, z)  in
                             let uu____1453 =
                               let uu____1467 =
                                 let uu____1479 =
                                   let uu____1482 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____1484 =
                                     let uu____1487 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____1488 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____1487 uu____1488  in
                                   let_ FStar_Tests_Util.x uu____1482
                                     uu____1484
                                    in
                                 ((Prims.parse_int "13"), uu____1479, z)  in
                               let uu____1497 =
                                 let uu____1511 =
                                   let uu____1523 =
                                     let uu____1526 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____1527 =
                                       let uu____1530 =
                                         let uu____1531 =
                                           let uu____1534 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____1535 =
                                             let uu____1538 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____1538]  in
                                           uu____1534 :: uu____1535  in
                                         FStar_Tests_Util.app mul uu____1531
                                          in
                                       let uu____1539 =
                                         let uu____1542 =
                                           let uu____1543 =
                                             let uu____1546 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____1547 =
                                               let uu____1550 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____1550]  in
                                             uu____1546 :: uu____1547  in
                                           FStar_Tests_Util.app mul
                                             uu____1543
                                            in
                                         let uu____1551 =
                                           let uu____1554 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____1555 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____1554 uu____1555  in
                                         let_ FStar_Tests_Util.h uu____1542
                                           uu____1551
                                          in
                                       let_ FStar_Tests_Util.y uu____1530
                                         uu____1539
                                        in
                                     let_ FStar_Tests_Util.x uu____1526
                                       uu____1527
                                      in
                                   ((Prims.parse_int "15"), uu____1523, z)
                                    in
                                 let uu____1564 =
                                   let uu____1578 =
                                     let uu____1590 =
                                       let uu____1593 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____1596 =
                                         let uu____1597 =
                                           let uu____1600 =
                                             let uu____1603 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____1604 =
                                               let uu____1607 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____1607]  in
                                             uu____1603 :: uu____1604  in
                                           FStar_Tests_Util.app mul
                                             uu____1600
                                            in
                                         let uu____1608 =
                                           let uu____1609 =
                                             let uu____1612 =
                                               let uu____1615 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____1616 =
                                                 let uu____1619 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____1619]  in
                                               uu____1615 :: uu____1616  in
                                             FStar_Tests_Util.app mul
                                               uu____1612
                                              in
                                           let uu____1620 =
                                             let uu____1621 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____1622 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____1621 uu____1622  in
                                           mk_let FStar_Tests_Util.h
                                             uu____1609 uu____1620
                                            in
                                         mk_let FStar_Tests_Util.y uu____1597
                                           uu____1608
                                          in
                                       mk_let FStar_Tests_Util.x uu____1593
                                         uu____1596
                                        in
                                     ((Prims.parse_int "16"), uu____1590, z)
                                      in
                                   let uu____1631 =
                                     let uu____1645 =
                                       let uu____1657 =
                                         let uu____1660 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____1661 =
                                           let uu____1664 =
                                             let uu____1665 =
                                               let uu____1668 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____1669 =
                                                 let uu____1672 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____1672]  in
                                               uu____1668 :: uu____1669  in
                                             FStar_Tests_Util.app mul
                                               uu____1665
                                              in
                                           let uu____1673 =
                                             let uu____1676 =
                                               let uu____1677 =
                                                 let uu____1680 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____1681 =
                                                   let uu____1684 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____1684]  in
                                                 uu____1680 :: uu____1681  in
                                               FStar_Tests_Util.app mul
                                                 uu____1677
                                                in
                                             let uu____1685 =
                                               let uu____1688 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____1689 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____1688 uu____1689
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____1676 uu____1685
                                              in
                                           let_ FStar_Tests_Util.y uu____1664
                                             uu____1673
                                            in
                                         let_ FStar_Tests_Util.x uu____1660
                                           uu____1661
                                          in
                                       ((Prims.parse_int "17"), uu____1657,
                                         z)
                                        in
                                     let uu____1698 =
                                       let uu____1712 =
                                         let uu____1724 =
                                           let uu____1727 =
                                             let uu____1730 = snat znat  in
                                             snat uu____1730  in
                                           pred_nat uu____1727  in
                                         let uu____1731 = snat znat  in
                                         ((Prims.parse_int "18"), uu____1724,
                                           uu____1731)
                                          in
                                       let uu____1740 =
                                         let uu____1754 =
                                           let uu____1766 =
                                             let uu____1769 =
                                               let uu____1770 =
                                                 let uu____1771 = snat znat
                                                    in
                                                 snat uu____1771  in
                                               let uu____1772 = snat znat  in
                                               minus_nat uu____1770
                                                 uu____1772
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____1769
                                              in
                                           let uu____1773 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____1766, uu____1773)
                                            in
                                         let uu____1782 =
                                           let uu____1796 =
                                             let uu____1808 =
                                               let uu____1811 =
                                                 let uu____1812 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 let uu____1814 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 minus_nat uu____1812
                                                   uu____1814
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____1811
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____1808, znat)
                                              in
                                           let uu____1822 =
                                             let uu____1836 =
                                               let uu____1848 =
                                                 let uu____1851 =
                                                   let uu____1852 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   let uu____1854 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   minus_nat uu____1852
                                                     uu____1854
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____1851
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____1848, znat)
                                                in
                                             let uu____1862 =
                                               let uu____1876 =
                                                 let uu____1888 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____1892 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____1888, uu____1892)
                                                  in
                                               let uu____1902 =
                                                 let uu____1916 =
                                                   let uu____1928 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____1932 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____1928, uu____1932)
                                                    in
                                                 let uu____1942 =
                                                   let uu____1956 =
                                                     let uu____1968 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____1972 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____1968,
                                                       uu____1972)
                                                      in
                                                   let uu____1982 =
                                                     let uu____1996 =
                                                       let uu____2008 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____2012 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____2008,
                                                         uu____2012)
                                                        in
                                                     let uu____2022 =
                                                       let uu____2036 =
                                                         let uu____2048 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____2052 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____2048,
                                                           uu____2052)
                                                          in
                                                       let uu____2062 =
                                                         let uu____2076 =
                                                           let uu____2088 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____2092 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____2088,
                                                             uu____2092)
                                                            in
                                                         let uu____2102 =
                                                           let uu____2116 =
                                                             let uu____2128 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____2132 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____2128,
                                                               uu____2132)
                                                              in
                                                           let uu____2142 =
                                                             let uu____2156 =
                                                               let uu____2168
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____2172
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____2168,
                                                                 uu____2172)
                                                                in
                                                             let uu____2182 =
                                                               let uu____2196
                                                                 =
                                                                 let uu____2208
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____2212
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____2208,
                                                                   uu____2212)
                                                                  in
                                                               let uu____2222
                                                                 =
                                                                 let uu____2236
                                                                   =
                                                                   let uu____2248
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____2252
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____2248,
                                                                    uu____2252)
                                                                    in
                                                                 let uu____2262
                                                                   =
                                                                   let uu____2276
                                                                    =
                                                                    let uu____2288
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____2292
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____2288,
                                                                    uu____2292)
                                                                     in
                                                                   let uu____2302
                                                                    =
                                                                    let uu____2316
                                                                    =
                                                                    let uu____2328
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____2332
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____2328,
                                                                    uu____2332)
                                                                     in
                                                                    let uu____2342
                                                                    =
                                                                    let uu____2356
                                                                    =
                                                                    let uu____2368
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____2372
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____2368,
                                                                    uu____2372)
                                                                     in
                                                                    let uu____2382
                                                                    =
                                                                    let uu____2396
                                                                    =
                                                                    let uu____2408
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____2412
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____2408,
                                                                    uu____2412)
                                                                     in
                                                                    let uu____2422
                                                                    =
                                                                    let uu____2436
                                                                    =
                                                                    let uu____2448
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____2452
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____2448,
                                                                    uu____2452)
                                                                     in
                                                                    let uu____2462
                                                                    =
                                                                    let uu____2476
                                                                    =
                                                                    let uu____2488
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____2492
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____2488,
                                                                    uu____2492)
                                                                     in
                                                                    let uu____2502
                                                                    =
                                                                    let uu____2516
                                                                    =
                                                                    let uu____2528
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____2532
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____2528,
                                                                    uu____2532)
                                                                     in
                                                                    let uu____2542
                                                                    =
                                                                    let uu____2556
                                                                    =
                                                                    let uu____2568
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____2572
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____2568,
                                                                    uu____2572)
                                                                     in
                                                                    let uu____2582
                                                                    =
                                                                    let uu____2596
                                                                    =
                                                                    let uu____2608
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____2612
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____2608,
                                                                    uu____2612)
                                                                     in
                                                                    let uu____2622
                                                                    =
                                                                    let uu____2636
                                                                    =
                                                                    let uu____2648
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____2652
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____2648,
                                                                    uu____2652)
                                                                     in
                                                                    let uu____2662
                                                                    =
                                                                    let uu____2676
                                                                    =
                                                                    let uu____2688
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____2692
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____2688,
                                                                    uu____2692)
                                                                     in
                                                                    let uu____2702
                                                                    =
                                                                    let uu____2716
                                                                    =
                                                                    let uu____2728
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____2732
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____2728,
                                                                    uu____2732)
                                                                     in
                                                                    let uu____2742
                                                                    =
                                                                    let uu____2756
                                                                    =
                                                                    let uu____2768
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____2772
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____2768,
                                                                    uu____2772)
                                                                     in
                                                                    let uu____2782
                                                                    =
                                                                    let uu____2796
                                                                    =
                                                                    let uu____2808
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____2812
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____2808,
                                                                    uu____2812)
                                                                     in
                                                                    let uu____2822
                                                                    =
                                                                    let uu____2836
                                                                    =
                                                                    let uu____2848
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____2852
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____2848,
                                                                    uu____2852)
                                                                     in
                                                                    let uu____2862
                                                                    =
                                                                    let uu____2876
                                                                    =
                                                                    let uu____2888
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____2892
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____2888,
                                                                    uu____2892)
                                                                     in
                                                                    let uu____2902
                                                                    =
                                                                    let uu____2916
                                                                    =
                                                                    let uu____2928
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____2932
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____2928,
                                                                    uu____2932)
                                                                     in
                                                                    let uu____2942
                                                                    =
                                                                    let uu____2956
                                                                    =
                                                                    let uu____2968
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____2972
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____2968,
                                                                    uu____2972)
                                                                     in
                                                                    let uu____2982
                                                                    =
                                                                    let uu____2996
                                                                    =
                                                                    let uu____3008
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____3012
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____3008,
                                                                    uu____3012)
                                                                     in
                                                                    let uu____3022
                                                                    =
                                                                    let uu____3036
                                                                    =
                                                                    let uu____3048
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____3052
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____3048,
                                                                    uu____3052)
                                                                     in
                                                                    let uu____3062
                                                                    =
                                                                    let uu____3076
                                                                    =
                                                                    let uu____3088
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____3092
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____3088,
                                                                    uu____3092)
                                                                     in
                                                                    let uu____3102
                                                                    =
                                                                    let uu____3116
                                                                    =
                                                                    let uu____3128
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____3132
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____3128,
                                                                    uu____3132)
                                                                     in
                                                                    let uu____3142
                                                                    =
                                                                    let uu____3156
                                                                    =
                                                                    let uu____3168
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____3172
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____3168,
                                                                    uu____3172)
                                                                     in
                                                                    let uu____3182
                                                                    =
                                                                    let uu____3196
                                                                    =
                                                                    let uu____3208
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____3212
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____3208,
                                                                    uu____3212)
                                                                     in
                                                                    [uu____3196]
                                                                     in
                                                                    uu____3156
                                                                    ::
                                                                    uu____3182
                                                                     in
                                                                    uu____3116
                                                                    ::
                                                                    uu____3142
                                                                     in
                                                                    uu____3076
                                                                    ::
                                                                    uu____3102
                                                                     in
                                                                    uu____3036
                                                                    ::
                                                                    uu____3062
                                                                     in
                                                                    uu____2996
                                                                    ::
                                                                    uu____3022
                                                                     in
                                                                    uu____2956
                                                                    ::
                                                                    uu____2982
                                                                     in
                                                                    uu____2916
                                                                    ::
                                                                    uu____2942
                                                                     in
                                                                    uu____2876
                                                                    ::
                                                                    uu____2902
                                                                     in
                                                                    uu____2836
                                                                    ::
                                                                    uu____2862
                                                                     in
                                                                    uu____2796
                                                                    ::
                                                                    uu____2822
                                                                     in
                                                                    uu____2756
                                                                    ::
                                                                    uu____2782
                                                                     in
                                                                    uu____2716
                                                                    ::
                                                                    uu____2742
                                                                     in
                                                                    uu____2676
                                                                    ::
                                                                    uu____2702
                                                                     in
                                                                    uu____2636
                                                                    ::
                                                                    uu____2662
                                                                     in
                                                                    uu____2596
                                                                    ::
                                                                    uu____2622
                                                                     in
                                                                    uu____2556
                                                                    ::
                                                                    uu____2582
                                                                     in
                                                                    uu____2516
                                                                    ::
                                                                    uu____2542
                                                                     in
                                                                    uu____2476
                                                                    ::
                                                                    uu____2502
                                                                     in
                                                                    uu____2436
                                                                    ::
                                                                    uu____2462
                                                                     in
                                                                    uu____2396
                                                                    ::
                                                                    uu____2422
                                                                     in
                                                                    uu____2356
                                                                    ::
                                                                    uu____2382
                                                                     in
                                                                    uu____2316
                                                                    ::
                                                                    uu____2342
                                                                     in
                                                                   uu____2276
                                                                    ::
                                                                    uu____2302
                                                                    in
                                                                 uu____2236
                                                                   ::
                                                                   uu____2262
                                                                  in
                                                               uu____2196 ::
                                                                 uu____2222
                                                                in
                                                             uu____2156 ::
                                                               uu____2182
                                                              in
                                                           uu____2116 ::
                                                             uu____2142
                                                            in
                                                         uu____2076 ::
                                                           uu____2102
                                                          in
                                                       uu____2036 ::
                                                         uu____2062
                                                        in
                                                     uu____1996 :: uu____2022
                                                      in
                                                   uu____1956 :: uu____1982
                                                    in
                                                 uu____1916 :: uu____1942  in
                                               uu____1876 :: uu____1902  in
                                             uu____1836 :: uu____1862  in
                                           uu____1796 :: uu____1822  in
                                         uu____1754 :: uu____1782  in
                                       uu____1712 :: uu____1740  in
                                     uu____1645 :: uu____1698  in
                                   uu____1578 :: uu____1631  in
                                 uu____1511 :: uu____1564  in
                               uu____1467 :: uu____1497  in
                             uu____1426 :: uu____1453  in
                           uu____1385 :: uu____1412  in
                         uu____1346 :: uu____1371  in
                       uu____1311 :: uu____1332  in
                     uu____1276 :: uu____1297  in
                   uu____1241 :: uu____1262  in
                 uu____1206 :: uu____1227  in
               uu____1171 :: uu____1192  in
             uu____1119 :: uu____1157  in
           uu____1055 :: uu____1105  in
         uu____1006 :: uu____1041  in
       uu____957 :: uu____992  in
     uu____915 :: uu____943  in
   uu____867 :: uu____901)
  
let run_either :
  'Auu____3860 .
    Prims.int ->
      'Auu____3860 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____3860 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____3898 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____3898);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____3903 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____3903 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____3926 =
               let uu____3928 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____3928 expected  in
             FStar_Tests_Util.always i uu____3926)))
  
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
        (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let interp uu____4007 = run_interpreter i r expected  in
        let uu____4008 =
          let uu____4009 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____4009  in
        (i, uu____4008)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____4047 = run_nbe i r expected  in
        let uu____4048 =
          let uu____4049 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____4049  in
        (i, uu____4048)
  
let run_tests :
  'Auu____4060 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____4060)
      -> 'Auu____4060 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___478_4112  ->
            match uu___478_4112 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____4143  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____4146 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____4155  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____4158 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____4174  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____4204  ->
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
        let nbe1 uu____4249 = run_nbe i r expected  in
        let norm1 uu____4255 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____4268  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____4271 =
       let uu____4272 = encode (Prims.parse_int "1000")  in
       let uu____4274 =
         let uu____4277 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____4278 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____4277 uu____4278  in
       let_ FStar_Tests_Util.x uu____4272 uu____4274  in
     run_both_with_time (Prims.parse_int "14") uu____4271 z)
  
let (compare_times :
  (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2 Prims.list
    ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list -> unit)
  =
  fun l_int  ->
    fun l_nbe  ->
      FStar_Util.print_string "Comparing times for normalization and nbe\n";
      FStar_List.iter2
        (fun res1  ->
           fun res2  ->
             let uu____4354 = res1  in
             match uu____4354 with
             | (t1,time_int) ->
                 let uu____4364 = res2  in
                 (match uu____4364 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____4376 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____4376 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____4387  ->
    (let uu____4389 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____4389);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  