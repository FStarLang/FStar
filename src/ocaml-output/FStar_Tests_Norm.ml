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
      (let uu____39 =
         let uu____42 = encode (n1 - (Prims.parse_int "1"))  in [uu____42]
          in
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
      let uu____367 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____367, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____411 =
        let uu____414 =
          let uu____415 =
            let uu____429 =
              let uu____439 =
                let uu____447 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____447, false)  in
              [uu____439]  in
            (snat_l, uu____429)  in
          FStar_Syntax_Syntax.Pat_cons uu____415  in
        pat uu____414  in
      let uu____477 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___21_482 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___21_482.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___21_482.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____411, FStar_Pervasives_Native.None, uu____477)  in
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
        let uu____523 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____542 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____523, FStar_Pervasives_Native.None, uu____542)  in
      let sbranch =
        let uu____570 =
          let uu____573 =
            let uu____574 =
              let uu____588 =
                let uu____598 =
                  let uu____606 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____606, false)  in
                [uu____598]  in
              (snat_l, uu____588)  in
            FStar_Syntax_Syntax.Pat_cons uu____574  in
          pat uu____573  in
        let uu____636 =
          let uu____639 = FStar_Tests_Util.nm minus1  in
          let uu____642 =
            let uu____645 =
              let uu____646 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____646  in
            let uu____649 =
              let uu____652 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____652]  in
            uu____645 :: uu____649  in
          FStar_Tests_Util.app uu____639 uu____642  in
        (uu____570, FStar_Pervasives_Native.None, uu____636)  in
      let lb =
        let uu____664 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____668 =
          let uu____671 =
            let uu____672 =
              let uu____673 = b FStar_Tests_Util.x  in
              let uu____680 =
                let uu____689 = b FStar_Tests_Util.y  in [uu____689]  in
              uu____673 :: uu____680  in
            let uu____714 =
              let uu____717 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____717 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____672 uu____714
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____671
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____664;
          FStar_Syntax_Syntax.lbdef = uu____668;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____724 =
        let uu____731 =
          let uu____732 =
            let uu____746 =
              let uu____749 =
                let uu____750 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____750 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____749
               in
            ((true, [lb]), uu____746)  in
          FStar_Syntax_Syntax.Tm_let uu____732  in
        FStar_Syntax_Syntax.mk uu____731  in
      uu____724 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____794 = snat out  in
         aux uu____794 (n2 - (Prims.parse_int "1")))
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
  (let uu____860 =
     let uu____872 =
       let uu____875 =
         let uu____878 =
           let uu____881 =
             let uu____884 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____884]  in
           id :: uu____881  in
         one :: uu____878  in
       FStar_Tests_Util.app apply uu____875  in
     let uu____885 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____872, uu____885)  in
   let uu____894 =
     let uu____908 =
       let uu____920 =
         let uu____923 =
           let uu____926 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____926]  in
         FStar_Tests_Util.app id uu____923  in
       let uu____927 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____920, uu____927)  in
     let uu____936 =
       let uu____950 =
         let uu____962 =
           let uu____965 =
             let uu____968 =
               let uu____971 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____972 =
                 let uu____975 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____975]  in
               uu____971 :: uu____972  in
             tt :: uu____968  in
           FStar_Tests_Util.app apply uu____965  in
         let uu____976 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____962, uu____976)  in
       let uu____985 =
         let uu____999 =
           let uu____1011 =
             let uu____1014 =
               let uu____1017 =
                 let uu____1020 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____1021 =
                   let uu____1024 = FStar_Tests_Util.nm FStar_Tests_Util.m
                      in
                   [uu____1024]  in
                 uu____1020 :: uu____1021  in
               ff :: uu____1017  in
             FStar_Tests_Util.app apply uu____1014  in
           let uu____1025 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____1011, uu____1025)  in
         let uu____1034 =
           let uu____1048 =
             let uu____1060 =
               let uu____1063 =
                 let uu____1066 =
                   let uu____1069 =
                     let uu____1072 =
                       let uu____1075 =
                         let uu____1078 =
                           let uu____1081 =
                             let uu____1084 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____1085 =
                               let uu____1088 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____1088]  in
                             uu____1084 :: uu____1085  in
                           ff :: uu____1081  in
                         apply :: uu____1078  in
                       apply :: uu____1075  in
                     apply :: uu____1072  in
                   apply :: uu____1069  in
                 apply :: uu____1066  in
               FStar_Tests_Util.app apply uu____1063  in
             let uu____1089 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____1060, uu____1089)  in
           let uu____1098 =
             let uu____1112 =
               let uu____1124 =
                 let uu____1127 =
                   let uu____1130 =
                     let uu____1133 =
                       let uu____1136 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n  in
                       let uu____1137 =
                         let uu____1140 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____1140]  in
                       uu____1136 :: uu____1137  in
                     ff :: uu____1133  in
                   apply :: uu____1130  in
                 FStar_Tests_Util.app twice uu____1127  in
               let uu____1141 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____1124, uu____1141)  in
             let uu____1150 =
               let uu____1164 =
                 let uu____1176 = minus one z  in
                 ((Prims.parse_int "5"), uu____1176, one)  in
               let uu____1185 =
                 let uu____1199 =
                   let uu____1211 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____1211, z)  in
                 let uu____1220 =
                   let uu____1234 =
                     let uu____1246 = minus one one  in
                     ((Prims.parse_int "7"), uu____1246, z)  in
                   let uu____1255 =
                     let uu____1269 =
                       let uu____1281 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____1281, one)  in
                     let uu____1290 =
                       let uu____1304 =
                         let uu____1316 = FStar_Tests_Util.app mul [two; one]
                            in
                         ((Prims.parse_int "9"), uu____1316, two)  in
                       let uu____1325 =
                         let uu____1339 =
                           let uu____1351 =
                             let uu____1354 =
                               let uu____1357 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____1357; one]  in
                             FStar_Tests_Util.app mul uu____1354  in
                           ((Prims.parse_int "10"), uu____1351, two)  in
                         let uu____1364 =
                           let uu____1378 =
                             let uu____1390 =
                               let uu____1393 = encode (Prims.parse_int "10")
                                  in
                               let uu____1395 = encode (Prims.parse_int "10")
                                  in
                               minus uu____1393 uu____1395  in
                             ((Prims.parse_int "11"), uu____1390, z)  in
                           let uu____1405 =
                             let uu____1419 =
                               let uu____1431 =
                                 let uu____1434 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____1436 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____1434 uu____1436  in
                               ((Prims.parse_int "12"), uu____1431, z)  in
                             let uu____1446 =
                               let uu____1460 =
                                 let uu____1472 =
                                   let uu____1475 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____1477 =
                                     let uu____1480 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____1481 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____1480 uu____1481  in
                                   let_ FStar_Tests_Util.x uu____1475
                                     uu____1477
                                    in
                                 ((Prims.parse_int "13"), uu____1472, z)  in
                               let uu____1490 =
                                 let uu____1504 =
                                   let uu____1516 =
                                     let uu____1519 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____1520 =
                                       let uu____1523 =
                                         let uu____1524 =
                                           let uu____1527 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____1528 =
                                             let uu____1531 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____1531]  in
                                           uu____1527 :: uu____1528  in
                                         FStar_Tests_Util.app mul uu____1524
                                          in
                                       let uu____1532 =
                                         let uu____1535 =
                                           let uu____1536 =
                                             let uu____1539 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____1540 =
                                               let uu____1543 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____1543]  in
                                             uu____1539 :: uu____1540  in
                                           FStar_Tests_Util.app mul
                                             uu____1536
                                            in
                                         let uu____1544 =
                                           let uu____1547 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____1548 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____1547 uu____1548  in
                                         let_ FStar_Tests_Util.h uu____1535
                                           uu____1544
                                          in
                                       let_ FStar_Tests_Util.y uu____1523
                                         uu____1532
                                        in
                                     let_ FStar_Tests_Util.x uu____1519
                                       uu____1520
                                      in
                                   ((Prims.parse_int "15"), uu____1516, z)
                                    in
                                 let uu____1557 =
                                   let uu____1571 =
                                     let uu____1583 =
                                       let uu____1586 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____1589 =
                                         let uu____1590 =
                                           let uu____1593 =
                                             let uu____1596 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____1597 =
                                               let uu____1600 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____1600]  in
                                             uu____1596 :: uu____1597  in
                                           FStar_Tests_Util.app mul
                                             uu____1593
                                            in
                                         let uu____1601 =
                                           let uu____1602 =
                                             let uu____1605 =
                                               let uu____1608 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____1609 =
                                                 let uu____1612 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____1612]  in
                                               uu____1608 :: uu____1609  in
                                             FStar_Tests_Util.app mul
                                               uu____1605
                                              in
                                           let uu____1613 =
                                             let uu____1614 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____1615 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____1614 uu____1615  in
                                           mk_let FStar_Tests_Util.h
                                             uu____1602 uu____1613
                                            in
                                         mk_let FStar_Tests_Util.y uu____1590
                                           uu____1601
                                          in
                                       mk_let FStar_Tests_Util.x uu____1586
                                         uu____1589
                                        in
                                     ((Prims.parse_int "16"), uu____1583, z)
                                      in
                                   let uu____1624 =
                                     let uu____1638 =
                                       let uu____1650 =
                                         let uu____1653 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____1654 =
                                           let uu____1657 =
                                             let uu____1658 =
                                               let uu____1661 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____1662 =
                                                 let uu____1665 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____1665]  in
                                               uu____1661 :: uu____1662  in
                                             FStar_Tests_Util.app mul
                                               uu____1658
                                              in
                                           let uu____1666 =
                                             let uu____1669 =
                                               let uu____1670 =
                                                 let uu____1673 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____1674 =
                                                   let uu____1677 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____1677]  in
                                                 uu____1673 :: uu____1674  in
                                               FStar_Tests_Util.app mul
                                                 uu____1670
                                                in
                                             let uu____1678 =
                                               let uu____1681 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____1682 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____1681 uu____1682
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____1669 uu____1678
                                              in
                                           let_ FStar_Tests_Util.y uu____1657
                                             uu____1666
                                            in
                                         let_ FStar_Tests_Util.x uu____1653
                                           uu____1654
                                          in
                                       ((Prims.parse_int "17"), uu____1650,
                                         z)
                                        in
                                     let uu____1691 =
                                       let uu____1705 =
                                         let uu____1717 =
                                           let uu____1720 =
                                             let uu____1723 = snat znat  in
                                             snat uu____1723  in
                                           pred_nat uu____1720  in
                                         let uu____1724 = snat znat  in
                                         ((Prims.parse_int "18"), uu____1717,
                                           uu____1724)
                                          in
                                       let uu____1733 =
                                         let uu____1747 =
                                           let uu____1759 =
                                             let uu____1762 =
                                               let uu____1763 =
                                                 let uu____1764 = snat znat
                                                    in
                                                 snat uu____1764  in
                                               let uu____1765 = snat znat  in
                                               minus_nat uu____1763
                                                 uu____1765
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____1762
                                              in
                                           let uu____1766 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____1759, uu____1766)
                                            in
                                         let uu____1775 =
                                           let uu____1789 =
                                             let uu____1801 =
                                               let uu____1804 =
                                                 let uu____1805 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 let uu____1807 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 minus_nat uu____1805
                                                   uu____1807
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____1804
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____1801, znat)
                                              in
                                           let uu____1815 =
                                             let uu____1829 =
                                               let uu____1841 =
                                                 let uu____1844 =
                                                   let uu____1845 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   let uu____1847 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   minus_nat uu____1845
                                                     uu____1847
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____1844
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____1841, znat)
                                                in
                                             let uu____1855 =
                                               let uu____1869 =
                                                 let uu____1881 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____1885 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____1881, uu____1885)
                                                  in
                                               let uu____1895 =
                                                 let uu____1909 =
                                                   let uu____1921 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____1925 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____1921, uu____1925)
                                                    in
                                                 let uu____1935 =
                                                   let uu____1949 =
                                                     let uu____1961 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____1965 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____1961,
                                                       uu____1965)
                                                      in
                                                   let uu____1975 =
                                                     let uu____1989 =
                                                       let uu____2001 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____2005 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____2001,
                                                         uu____2005)
                                                        in
                                                     let uu____2015 =
                                                       let uu____2029 =
                                                         let uu____2041 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____2045 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____2041,
                                                           uu____2045)
                                                          in
                                                       let uu____2055 =
                                                         let uu____2069 =
                                                           let uu____2081 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____2085 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____2081,
                                                             uu____2085)
                                                            in
                                                         let uu____2095 =
                                                           let uu____2109 =
                                                             let uu____2121 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____2125 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____2121,
                                                               uu____2125)
                                                              in
                                                           let uu____2135 =
                                                             let uu____2149 =
                                                               let uu____2161
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____2165
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____2161,
                                                                 uu____2165)
                                                                in
                                                             let uu____2175 =
                                                               let uu____2189
                                                                 =
                                                                 let uu____2201
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____2205
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____2201,
                                                                   uu____2205)
                                                                  in
                                                               let uu____2215
                                                                 =
                                                                 let uu____2229
                                                                   =
                                                                   let uu____2241
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____2245
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____2241,
                                                                    uu____2245)
                                                                    in
                                                                 let uu____2255
                                                                   =
                                                                   let uu____2269
                                                                    =
                                                                    let uu____2281
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____2285
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____2281,
                                                                    uu____2285)
                                                                     in
                                                                   let uu____2295
                                                                    =
                                                                    let uu____2309
                                                                    =
                                                                    let uu____2321
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____2325
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____2321,
                                                                    uu____2325)
                                                                     in
                                                                    let uu____2335
                                                                    =
                                                                    let uu____2349
                                                                    =
                                                                    let uu____2361
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____2365
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____2361,
                                                                    uu____2365)
                                                                     in
                                                                    let uu____2375
                                                                    =
                                                                    let uu____2389
                                                                    =
                                                                    let uu____2401
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____2405
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____2401,
                                                                    uu____2405)
                                                                     in
                                                                    let uu____2415
                                                                    =
                                                                    let uu____2429
                                                                    =
                                                                    let uu____2441
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____2445
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____2441,
                                                                    uu____2445)
                                                                     in
                                                                    let uu____2455
                                                                    =
                                                                    let uu____2469
                                                                    =
                                                                    let uu____2481
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____2485
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____2481,
                                                                    uu____2485)
                                                                     in
                                                                    let uu____2495
                                                                    =
                                                                    let uu____2509
                                                                    =
                                                                    let uu____2521
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____2525
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____2521,
                                                                    uu____2525)
                                                                     in
                                                                    let uu____2535
                                                                    =
                                                                    let uu____2549
                                                                    =
                                                                    let uu____2561
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____2565
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____2561,
                                                                    uu____2565)
                                                                     in
                                                                    let uu____2575
                                                                    =
                                                                    let uu____2589
                                                                    =
                                                                    let uu____2601
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____2605
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____2601,
                                                                    uu____2605)
                                                                     in
                                                                    let uu____2615
                                                                    =
                                                                    let uu____2629
                                                                    =
                                                                    let uu____2641
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____2645
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____2641,
                                                                    uu____2645)
                                                                     in
                                                                    let uu____2655
                                                                    =
                                                                    let uu____2669
                                                                    =
                                                                    let uu____2681
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____2685
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____2681,
                                                                    uu____2685)
                                                                     in
                                                                    let uu____2695
                                                                    =
                                                                    let uu____2709
                                                                    =
                                                                    let uu____2721
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____2725
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____2721,
                                                                    uu____2725)
                                                                     in
                                                                    let uu____2735
                                                                    =
                                                                    let uu____2749
                                                                    =
                                                                    let uu____2761
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____2765
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____2761,
                                                                    uu____2765)
                                                                     in
                                                                    let uu____2775
                                                                    =
                                                                    let uu____2789
                                                                    =
                                                                    let uu____2801
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____2805
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____2801,
                                                                    uu____2805)
                                                                     in
                                                                    let uu____2815
                                                                    =
                                                                    let uu____2829
                                                                    =
                                                                    let uu____2841
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____2845
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____2841,
                                                                    uu____2845)
                                                                     in
                                                                    let uu____2855
                                                                    =
                                                                    let uu____2869
                                                                    =
                                                                    let uu____2881
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____2885
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____2881,
                                                                    uu____2885)
                                                                     in
                                                                    let uu____2895
                                                                    =
                                                                    let uu____2909
                                                                    =
                                                                    let uu____2921
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____2925
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____2921,
                                                                    uu____2925)
                                                                     in
                                                                    let uu____2935
                                                                    =
                                                                    let uu____2949
                                                                    =
                                                                    let uu____2961
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____2965
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____2961,
                                                                    uu____2965)
                                                                     in
                                                                    let uu____2975
                                                                    =
                                                                    let uu____2989
                                                                    =
                                                                    let uu____3001
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____3005
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____3001,
                                                                    uu____3005)
                                                                     in
                                                                    let uu____3015
                                                                    =
                                                                    let uu____3029
                                                                    =
                                                                    let uu____3041
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____3045
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____3041,
                                                                    uu____3045)
                                                                     in
                                                                    let uu____3055
                                                                    =
                                                                    let uu____3069
                                                                    =
                                                                    let uu____3081
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____3085
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____3081,
                                                                    uu____3085)
                                                                     in
                                                                    let uu____3095
                                                                    =
                                                                    let uu____3109
                                                                    =
                                                                    let uu____3121
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____3125
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____3121,
                                                                    uu____3125)
                                                                     in
                                                                    let uu____3135
                                                                    =
                                                                    let uu____3149
                                                                    =
                                                                    let uu____3161
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____3165
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____3161,
                                                                    uu____3165)
                                                                     in
                                                                    let uu____3175
                                                                    =
                                                                    let uu____3189
                                                                    =
                                                                    let uu____3201
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____3205
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____3201,
                                                                    uu____3205)
                                                                     in
                                                                    [uu____3189]
                                                                     in
                                                                    uu____3149
                                                                    ::
                                                                    uu____3175
                                                                     in
                                                                    uu____3109
                                                                    ::
                                                                    uu____3135
                                                                     in
                                                                    uu____3069
                                                                    ::
                                                                    uu____3095
                                                                     in
                                                                    uu____3029
                                                                    ::
                                                                    uu____3055
                                                                     in
                                                                    uu____2989
                                                                    ::
                                                                    uu____3015
                                                                     in
                                                                    uu____2949
                                                                    ::
                                                                    uu____2975
                                                                     in
                                                                    uu____2909
                                                                    ::
                                                                    uu____2935
                                                                     in
                                                                    uu____2869
                                                                    ::
                                                                    uu____2895
                                                                     in
                                                                    uu____2829
                                                                    ::
                                                                    uu____2855
                                                                     in
                                                                    uu____2789
                                                                    ::
                                                                    uu____2815
                                                                     in
                                                                    uu____2749
                                                                    ::
                                                                    uu____2775
                                                                     in
                                                                    uu____2709
                                                                    ::
                                                                    uu____2735
                                                                     in
                                                                    uu____2669
                                                                    ::
                                                                    uu____2695
                                                                     in
                                                                    uu____2629
                                                                    ::
                                                                    uu____2655
                                                                     in
                                                                    uu____2589
                                                                    ::
                                                                    uu____2615
                                                                     in
                                                                    uu____2549
                                                                    ::
                                                                    uu____2575
                                                                     in
                                                                    uu____2509
                                                                    ::
                                                                    uu____2535
                                                                     in
                                                                    uu____2469
                                                                    ::
                                                                    uu____2495
                                                                     in
                                                                    uu____2429
                                                                    ::
                                                                    uu____2455
                                                                     in
                                                                    uu____2389
                                                                    ::
                                                                    uu____2415
                                                                     in
                                                                    uu____2349
                                                                    ::
                                                                    uu____2375
                                                                     in
                                                                    uu____2309
                                                                    ::
                                                                    uu____2335
                                                                     in
                                                                   uu____2269
                                                                    ::
                                                                    uu____2295
                                                                    in
                                                                 uu____2229
                                                                   ::
                                                                   uu____2255
                                                                  in
                                                               uu____2189 ::
                                                                 uu____2215
                                                                in
                                                             uu____2149 ::
                                                               uu____2175
                                                              in
                                                           uu____2109 ::
                                                             uu____2135
                                                            in
                                                         uu____2069 ::
                                                           uu____2095
                                                          in
                                                       uu____2029 ::
                                                         uu____2055
                                                        in
                                                     uu____1989 :: uu____2015
                                                      in
                                                   uu____1949 :: uu____1975
                                                    in
                                                 uu____1909 :: uu____1935  in
                                               uu____1869 :: uu____1895  in
                                             uu____1829 :: uu____1855  in
                                           uu____1789 :: uu____1815  in
                                         uu____1747 :: uu____1775  in
                                       uu____1705 :: uu____1733  in
                                     uu____1638 :: uu____1691  in
                                   uu____1571 :: uu____1624  in
                                 uu____1504 :: uu____1557  in
                               uu____1460 :: uu____1490  in
                             uu____1419 :: uu____1446  in
                           uu____1378 :: uu____1405  in
                         uu____1339 :: uu____1364  in
                       uu____1304 :: uu____1325  in
                     uu____1269 :: uu____1290  in
                   uu____1234 :: uu____1255  in
                 uu____1199 :: uu____1220  in
               uu____1164 :: uu____1185  in
             uu____1112 :: uu____1150  in
           uu____1048 :: uu____1098  in
         uu____999 :: uu____1034  in
       uu____950 :: uu____985  in
     uu____908 :: uu____936  in
   uu____860 :: uu____894)
  
let run_either :
  'Auu____3853 .
    Prims.int ->
      'Auu____3853 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____3853 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____3891 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____3891);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____3896 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____3896 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____3919 =
               let uu____3921 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____3921 expected  in
             FStar_Tests_Util.always i uu____3919)))
  
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
        let interp uu____4000 = run_interpreter i r expected  in
        let uu____4001 =
          let uu____4002 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____4002  in
        (i, uu____4001)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____4040 = run_nbe i r expected  in
        let uu____4041 =
          let uu____4042 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____4042  in
        (i, uu____4041)
  
let run_tests :
  'Auu____4053 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____4053)
      -> 'Auu____4053 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___0_4105  ->
            match uu___0_4105 with | (no,test,res) -> run1 no test res) tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____4136  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____4139 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____4148  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____4151 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____4167  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____4197  ->
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
        let nbe1 uu____4242 = run_nbe i r expected  in
        let norm1 uu____4248 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____4261  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____4264 =
       let uu____4265 = encode (Prims.parse_int "1000")  in
       let uu____4267 =
         let uu____4270 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____4271 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____4270 uu____4271  in
       let_ FStar_Tests_Util.x uu____4265 uu____4267  in
     run_both_with_time (Prims.parse_int "14") uu____4264 z)
  
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
             let uu____4347 = res1  in
             match uu____4347 with
             | (t1,time_int) ->
                 let uu____4357 = res2  in
                 (match uu____4357 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____4369 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____4369 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____4380  ->
    (let uu____4382 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____4382);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  