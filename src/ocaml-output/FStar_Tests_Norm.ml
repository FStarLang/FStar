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
  fun n ->
    if n = Prims.int_zero
    then z
    else
      (let uu____39 = let uu____42 = encode (n - Prims.int_one) in [uu____42] in
       FStar_Tests_Util.app succ uu____39)
let (minus :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun m -> fun n -> FStar_Tests_Util.app n [pred; m]
let (let_ :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term)
  =
  fun x ->
    fun e ->
      fun e' ->
        let uu____81 =
          let uu____84 = let uu____85 = b x in [uu____85] in
          FStar_Syntax_Util.abs uu____84 e' FStar_Pervasives_Native.None in
        FStar_Tests_Util.app uu____81 [e]
let (mk_let :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun x ->
    fun e ->
      fun e' ->
        let e'1 =
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (x, Prims.int_zero)] e' in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_let
             ((false,
                [{
                   FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                   FStar_Syntax_Syntax.lbunivs = [];
                   FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
                   FStar_Syntax_Syntax.lbeff =
                     FStar_Parser_Const.effect_Tot_lid;
                   FStar_Syntax_Syntax.lbdef = e;
                   FStar_Syntax_Syntax.lbattrs = [];
                   FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
                 }]), e'1)) FStar_Range.dummyRange
let (lid : Prims.string -> FStar_Ident.lident) =
  fun x -> FStar_Ident.lid_of_path ["Test"; x] FStar_Range.dummyRange
let (znat_l : FStar_Syntax_Syntax.fv) =
  let uu____155 = lid "Z" in
  FStar_Syntax_Syntax.lid_as_fv uu____155 FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____158 = lid "S" in
  FStar_Syntax_Syntax.lid_as_fv uu____158 FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
let (tm_fv :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun fv ->
    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
      FStar_Range.dummyRange
let (znat : FStar_Syntax_Syntax.term) = tm_fv znat_l
let (snat :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s ->
    let uu____177 =
      let uu____178 =
        let uu____195 = tm_fv snat_l in
        let uu____198 =
          let uu____209 = FStar_Syntax_Syntax.as_arg s in [uu____209] in
        (uu____195, uu____198) in
      FStar_Syntax_Syntax.Tm_app uu____178 in
    FStar_Syntax_Syntax.mk uu____177 FStar_Range.dummyRange
let pat :
  'uuuuuu251 . 'uuuuuu251 -> 'uuuuuu251 FStar_Syntax_Syntax.withinfo_t =
  fun p -> FStar_Syntax_Syntax.withinfo p FStar_Range.dummyRange
let (snat_type : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  let uu____262 =
    let uu____263 = lid "snat" in
    FStar_Syntax_Syntax.lid_as_fv uu____263
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
  tm_fv uu____262
let (mk_match :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun h ->
    fun branches ->
      let branches1 =
        FStar_All.pipe_right branches
          (FStar_List.map FStar_Syntax_Util.branch) in
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (h, branches1))
        FStar_Range.dummyRange
let (pred_nat :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s ->
    let zbranch =
      let uu____366 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, [])) in
      (uu____366, FStar_Pervasives_Native.None, znat) in
    let sbranch =
      let uu____410 =
        let uu____413 =
          let uu____414 =
            let uu____428 =
              let uu____438 =
                let uu____446 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x) in
                (uu____446, false) in
              [uu____438] in
            (snat_l, uu____428) in
          FStar_Syntax_Syntax.Pat_cons uu____414 in
        pat uu____413 in
      let uu____476 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___21_481 = FStar_Tests_Util.x in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___21_481.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = Prims.int_zero;
                FStar_Syntax_Syntax.sort =
                  (uu___21_481.FStar_Syntax_Syntax.sort)
              })) FStar_Range.dummyRange in
      (uu____410, FStar_Pervasives_Native.None, uu____476) in
    mk_match s [zbranch; sbranch]
let (minus_nat :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1 ->
    fun t2 ->
      let minus1 = FStar_Tests_Util.m in
      let x =
        let uu___27_508 = FStar_Tests_Util.x in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___27_508.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index = (uu___27_508.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = snat_type
        } in
      let y =
        let uu___30_510 = FStar_Tests_Util.y in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___30_510.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index = (uu___30_510.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = snat_type
        } in
      let zbranch =
        let uu____526 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, [])) in
        let uu____545 = FStar_Tests_Util.nm x in
        (uu____526, FStar_Pervasives_Native.None, uu____545) in
      let sbranch =
        let uu____573 =
          let uu____576 =
            let uu____577 =
              let uu____591 =
                let uu____601 =
                  let uu____609 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n) in
                  (uu____609, false) in
                [uu____601] in
              (snat_l, uu____591) in
            FStar_Syntax_Syntax.Pat_cons uu____577 in
          pat uu____576 in
        let uu____639 =
          let uu____642 = FStar_Tests_Util.nm minus1 in
          let uu____645 =
            let uu____648 =
              let uu____649 = FStar_Tests_Util.nm x in pred_nat uu____649 in
            let uu____652 =
              let uu____655 = FStar_Tests_Util.nm FStar_Tests_Util.n in
              [uu____655] in
            uu____648 :: uu____652 in
          FStar_Tests_Util.app uu____642 uu____645 in
        (uu____573, FStar_Pervasives_Native.None, uu____639) in
      let lb =
        let uu____667 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange in
        let uu____671 =
          let uu____674 =
            let uu____675 =
              let uu____676 = b x in
              let uu____683 = let uu____692 = b y in [uu____692] in uu____676
                :: uu____683 in
            let uu____717 =
              let uu____720 = FStar_Tests_Util.nm y in
              mk_match uu____720 [zbranch; sbranch] in
            FStar_Syntax_Util.abs uu____675 uu____717
              FStar_Pervasives_Native.None in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, Prims.int_zero)] uu____674 in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____667;
          FStar_Syntax_Syntax.lbdef = uu____671;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        } in
      let uu____727 =
        let uu____728 =
          let uu____742 =
            let uu____745 =
              let uu____746 = FStar_Tests_Util.nm minus1 in
              FStar_Tests_Util.app uu____746 [t1; t2] in
            FStar_Syntax_Subst.subst
              [FStar_Syntax_Syntax.NM (minus1, Prims.int_zero)] uu____745 in
          ((true, [lb]), uu____742) in
        FStar_Syntax_Syntax.Tm_let uu____728 in
      FStar_Syntax_Syntax.mk uu____727 FStar_Range.dummyRange
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n ->
    let rec aux out n1 =
      if n1 = Prims.int_zero
      then out
      else (let uu____790 = snat out in aux uu____790 (n1 - Prims.int_one)) in
    aux znat n
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
  (let uu____856 =
     let uu____868 =
       let uu____871 =
         let uu____874 =
           let uu____877 =
             let uu____880 = FStar_Tests_Util.nm FStar_Tests_Util.n in
             [uu____880] in
           id :: uu____877 in
         one :: uu____874 in
       FStar_Tests_Util.app apply uu____871 in
     let uu____881 = FStar_Tests_Util.nm FStar_Tests_Util.n in
     (Prims.int_zero, uu____868, uu____881) in
   let uu____890 =
     let uu____904 =
       let uu____916 =
         let uu____919 =
           let uu____922 = FStar_Tests_Util.nm FStar_Tests_Util.x in
           [uu____922] in
         FStar_Tests_Util.app id uu____919 in
       let uu____923 = FStar_Tests_Util.nm FStar_Tests_Util.x in
       (Prims.int_one, uu____916, uu____923) in
     let uu____932 =
       let uu____946 =
         let uu____958 =
           let uu____961 =
             let uu____964 =
               let uu____967 = FStar_Tests_Util.nm FStar_Tests_Util.n in
               let uu____968 =
                 let uu____971 = FStar_Tests_Util.nm FStar_Tests_Util.m in
                 [uu____971] in
               uu____967 :: uu____968 in
             tt :: uu____964 in
           FStar_Tests_Util.app apply uu____961 in
         let uu____972 = FStar_Tests_Util.nm FStar_Tests_Util.n in
         (Prims.int_one, uu____958, uu____972) in
       let uu____981 =
         let uu____995 =
           let uu____1007 =
             let uu____1010 =
               let uu____1013 =
                 let uu____1016 = FStar_Tests_Util.nm FStar_Tests_Util.n in
                 let uu____1017 =
                   let uu____1020 = FStar_Tests_Util.nm FStar_Tests_Util.m in
                   [uu____1020] in
                 uu____1016 :: uu____1017 in
               ff :: uu____1013 in
             FStar_Tests_Util.app apply uu____1010 in
           let uu____1021 = FStar_Tests_Util.nm FStar_Tests_Util.m in
           ((Prims.of_int (2)), uu____1007, uu____1021) in
         let uu____1030 =
           let uu____1044 =
             let uu____1056 =
               let uu____1059 =
                 let uu____1062 =
                   let uu____1065 =
                     let uu____1068 =
                       let uu____1071 =
                         let uu____1074 =
                           let uu____1077 =
                             let uu____1080 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n in
                             let uu____1081 =
                               let uu____1084 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m in
                               [uu____1084] in
                             uu____1080 :: uu____1081 in
                           ff :: uu____1077 in
                         apply :: uu____1074 in
                       apply :: uu____1071 in
                     apply :: uu____1068 in
                   apply :: uu____1065 in
                 apply :: uu____1062 in
               FStar_Tests_Util.app apply uu____1059 in
             let uu____1085 = FStar_Tests_Util.nm FStar_Tests_Util.m in
             ((Prims.of_int (3)), uu____1056, uu____1085) in
           let uu____1094 =
             let uu____1108 =
               let uu____1120 =
                 let uu____1123 =
                   let uu____1126 =
                     let uu____1129 =
                       let uu____1132 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n in
                       let uu____1133 =
                         let uu____1136 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m in
                         [uu____1136] in
                       uu____1132 :: uu____1133 in
                     ff :: uu____1129 in
                   apply :: uu____1126 in
                 FStar_Tests_Util.app twice uu____1123 in
               let uu____1137 = FStar_Tests_Util.nm FStar_Tests_Util.m in
               ((Prims.of_int (4)), uu____1120, uu____1137) in
             let uu____1146 =
               let uu____1160 =
                 let uu____1172 = minus one z in
                 ((Prims.of_int (5)), uu____1172, one) in
               let uu____1181 =
                 let uu____1195 =
                   let uu____1207 = FStar_Tests_Util.app pred [one] in
                   ((Prims.of_int (6)), uu____1207, z) in
                 let uu____1216 =
                   let uu____1230 =
                     let uu____1242 = minus one one in
                     ((Prims.of_int (7)), uu____1242, z) in
                   let uu____1251 =
                     let uu____1265 =
                       let uu____1277 = FStar_Tests_Util.app mul [one; one] in
                       ((Prims.of_int (8)), uu____1277, one) in
                     let uu____1286 =
                       let uu____1300 =
                         let uu____1312 = FStar_Tests_Util.app mul [two; one] in
                         ((Prims.of_int (9)), uu____1312, two) in
                       let uu____1321 =
                         let uu____1335 =
                           let uu____1347 =
                             let uu____1350 =
                               let uu____1353 =
                                 FStar_Tests_Util.app succ [one] in
                               [uu____1353; one] in
                             FStar_Tests_Util.app mul uu____1350 in
                           ((Prims.of_int (10)), uu____1347, two) in
                         let uu____1360 =
                           let uu____1374 =
                             let uu____1386 =
                               let uu____1389 = encode (Prims.of_int (10)) in
                               let uu____1391 = encode (Prims.of_int (10)) in
                               minus uu____1389 uu____1391 in
                             ((Prims.of_int (11)), uu____1386, z) in
                           let uu____1401 =
                             let uu____1415 =
                               let uu____1427 =
                                 let uu____1430 = encode (Prims.of_int (100)) in
                                 let uu____1432 = encode (Prims.of_int (100)) in
                                 minus uu____1430 uu____1432 in
                               ((Prims.of_int (12)), uu____1427, z) in
                             let uu____1442 =
                               let uu____1456 =
                                 let uu____1468 =
                                   let uu____1471 =
                                     encode (Prims.of_int (100)) in
                                   let uu____1473 =
                                     let uu____1476 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x in
                                     let uu____1477 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x in
                                     minus uu____1476 uu____1477 in
                                   let_ FStar_Tests_Util.x uu____1471
                                     uu____1473 in
                                 ((Prims.of_int (13)), uu____1468, z) in
                               let uu____1486 =
                                 let uu____1500 =
                                   let uu____1512 =
                                     let uu____1515 =
                                       FStar_Tests_Util.app succ [one] in
                                     let uu____1516 =
                                       let uu____1519 =
                                         let uu____1520 =
                                           let uu____1523 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x in
                                           let uu____1524 =
                                             let uu____1527 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x in
                                             [uu____1527] in
                                           uu____1523 :: uu____1524 in
                                         FStar_Tests_Util.app mul uu____1520 in
                                       let uu____1528 =
                                         let uu____1531 =
                                           let uu____1532 =
                                             let uu____1535 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y in
                                             let uu____1536 =
                                               let uu____1539 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y in
                                               [uu____1539] in
                                             uu____1535 :: uu____1536 in
                                           FStar_Tests_Util.app mul
                                             uu____1532 in
                                         let uu____1540 =
                                           let uu____1543 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h in
                                           let uu____1544 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h in
                                           minus uu____1543 uu____1544 in
                                         let_ FStar_Tests_Util.h uu____1531
                                           uu____1540 in
                                       let_ FStar_Tests_Util.y uu____1519
                                         uu____1528 in
                                     let_ FStar_Tests_Util.x uu____1515
                                       uu____1516 in
                                   ((Prims.of_int (15)), uu____1512, z) in
                                 let uu____1553 =
                                   let uu____1567 =
                                     let uu____1579 =
                                       let uu____1582 =
                                         FStar_Tests_Util.app succ [one] in
                                       let uu____1585 =
                                         let uu____1586 =
                                           let uu____1589 =
                                             let uu____1592 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x in
                                             let uu____1593 =
                                               let uu____1596 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x in
                                               [uu____1596] in
                                             uu____1592 :: uu____1593 in
                                           FStar_Tests_Util.app mul
                                             uu____1589 in
                                         let uu____1597 =
                                           let uu____1598 =
                                             let uu____1601 =
                                               let uu____1604 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y in
                                               let uu____1605 =
                                                 let uu____1608 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y in
                                                 [uu____1608] in
                                               uu____1604 :: uu____1605 in
                                             FStar_Tests_Util.app mul
                                               uu____1601 in
                                           let uu____1609 =
                                             let uu____1610 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h in
                                             let uu____1611 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h in
                                             minus uu____1610 uu____1611 in
                                           mk_let FStar_Tests_Util.h
                                             uu____1598 uu____1609 in
                                         mk_let FStar_Tests_Util.y uu____1586
                                           uu____1597 in
                                       mk_let FStar_Tests_Util.x uu____1582
                                         uu____1585 in
                                     ((Prims.of_int (16)), uu____1579, z) in
                                   let uu____1620 =
                                     let uu____1634 =
                                       let uu____1646 =
                                         let uu____1649 =
                                           FStar_Tests_Util.app succ [one] in
                                         let uu____1650 =
                                           let uu____1653 =
                                             let uu____1654 =
                                               let uu____1657 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x in
                                               let uu____1658 =
                                                 let uu____1661 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x in
                                                 [uu____1661] in
                                               uu____1657 :: uu____1658 in
                                             FStar_Tests_Util.app mul
                                               uu____1654 in
                                           let uu____1662 =
                                             let uu____1665 =
                                               let uu____1666 =
                                                 let uu____1669 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y in
                                                 let uu____1670 =
                                                   let uu____1673 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y in
                                                   [uu____1673] in
                                                 uu____1669 :: uu____1670 in
                                               FStar_Tests_Util.app mul
                                                 uu____1666 in
                                             let uu____1674 =
                                               let uu____1677 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h in
                                               let uu____1678 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h in
                                               minus uu____1677 uu____1678 in
                                             let_ FStar_Tests_Util.h
                                               uu____1665 uu____1674 in
                                           let_ FStar_Tests_Util.y uu____1653
                                             uu____1662 in
                                         let_ FStar_Tests_Util.x uu____1649
                                           uu____1650 in
                                       ((Prims.of_int (17)), uu____1646, z) in
                                     let uu____1687 =
                                       let uu____1701 =
                                         let uu____1713 =
                                           let uu____1716 =
                                             let uu____1719 = snat znat in
                                             snat uu____1719 in
                                           pred_nat uu____1716 in
                                         let uu____1720 = snat znat in
                                         ((Prims.of_int (18)), uu____1713,
                                           uu____1720) in
                                       let uu____1729 =
                                         let uu____1743 =
                                           let uu____1755 =
                                             let uu____1758 =
                                               let uu____1759 =
                                                 let uu____1760 = snat znat in
                                                 snat uu____1760 in
                                               let uu____1761 = snat znat in
                                               minus_nat uu____1759
                                                 uu____1761 in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____1758 in
                                           let uu____1762 = snat znat in
                                           ((Prims.of_int (19)), uu____1755,
                                             uu____1762) in
                                         let uu____1771 =
                                           let uu____1785 =
                                             let uu____1797 =
                                               let uu____1800 =
                                                 let uu____1801 =
                                                   encode_nat
                                                     (Prims.of_int (10)) in
                                                 let uu____1803 =
                                                   encode_nat
                                                     (Prims.of_int (10)) in
                                                 minus_nat uu____1801
                                                   uu____1803 in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____1800 in
                                             ((Prims.of_int (20)),
                                               uu____1797, znat) in
                                           let uu____1811 =
                                             let uu____1825 =
                                               let uu____1837 =
                                                 let uu____1840 =
                                                   let uu____1841 =
                                                     encode_nat
                                                       (Prims.of_int (100)) in
                                                   let uu____1843 =
                                                     encode_nat
                                                       (Prims.of_int (100)) in
                                                   minus_nat uu____1841
                                                     uu____1843 in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____1840 in
                                               ((Prims.of_int (21)),
                                                 uu____1837, znat) in
                                             let uu____1851 =
                                               let uu____1865 =
                                                 let uu____1877 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]" in
                                                 let uu____1881 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]" in
                                                 ((Prims.of_int (24)),
                                                   uu____1877, uu____1881) in
                                               let uu____1891 =
                                                 let uu____1905 =
                                                   let uu____1917 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]" in
                                                   let uu____1921 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]" in
                                                   ((Prims.of_int (241)),
                                                     uu____1917, uu____1921) in
                                                 let uu____1931 =
                                                   let uu____1945 =
                                                     let uu____1957 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]" in
                                                     let uu____1961 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]" in
                                                     ((Prims.of_int (25)),
                                                       uu____1957,
                                                       uu____1961) in
                                                   let uu____1971 =
                                                     let uu____1985 =
                                                       let uu____1997 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]" in
                                                       let uu____2001 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]" in
                                                       ((Prims.of_int (26)),
                                                         uu____1997,
                                                         uu____2001) in
                                                     let uu____2011 =
                                                       let uu____2025 =
                                                         let uu____2037 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T" in
                                                         let uu____2041 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F" in
                                                         ((Prims.of_int (28)),
                                                           uu____2037,
                                                           uu____2041) in
                                                       let uu____2051 =
                                                         let uu____2065 =
                                                           let uu____2077 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]" in
                                                           let uu____2081 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]" in
                                                           ((Prims.of_int (29)),
                                                             uu____2077,
                                                             uu____2081) in
                                                         let uu____2091 =
                                                           let uu____2105 =
                                                             let uu____2117 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T" in
                                                             let uu____2121 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T" in
                                                             ((Prims.of_int (31)),
                                                               uu____2117,
                                                               uu____2121) in
                                                           let uu____2131 =
                                                             let uu____2145 =
                                                               let uu____2157
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T" in
                                                               let uu____2161
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T" in
                                                               ((Prims.of_int (32)),
                                                                 uu____2157,
                                                                 uu____2161) in
                                                             let uu____2171 =
                                                               let uu____2185
                                                                 =
                                                                 let uu____2197
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T" in
                                                                 let uu____2201
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F" in
                                                                 ((Prims.of_int (33)),
                                                                   uu____2197,
                                                                   uu____2201) in
                                                               let uu____2211
                                                                 =
                                                                 let uu____2225
                                                                   =
                                                                   let uu____2237
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F" in
                                                                   let uu____2241
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T" in
                                                                   ((Prims.of_int (34)),
                                                                    uu____2237,
                                                                    uu____2241) in
                                                                 let uu____2251
                                                                   =
                                                                   let uu____2265
                                                                    =
                                                                    let uu____2277
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F" in
                                                                    let uu____2281
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T" in
                                                                    ((Prims.of_int (35)),
                                                                    uu____2277,
                                                                    uu____2281) in
                                                                   let uu____2291
                                                                    =
                                                                    let uu____2305
                                                                    =
                                                                    let uu____2317
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T" in
                                                                    let uu____2321
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T" in
                                                                    ((Prims.of_int (36)),
                                                                    uu____2317,
                                                                    uu____2321) in
                                                                    let uu____2331
                                                                    =
                                                                    let uu____2345
                                                                    =
                                                                    let uu____2357
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]" in
                                                                    let uu____2361
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]" in
                                                                    ((Prims.of_int (301)),
                                                                    uu____2357,
                                                                    uu____2361) in
                                                                    let uu____2371
                                                                    =
                                                                    let uu____2385
                                                                    =
                                                                    let uu____2397
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]" in
                                                                    let uu____2401
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]" in
                                                                    ((Prims.of_int (3012)),
                                                                    uu____2397,
                                                                    uu____2401) in
                                                                    let uu____2411
                                                                    =
                                                                    let uu____2425
                                                                    =
                                                                    let uu____2437
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]" in
                                                                    let uu____2441
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]" in
                                                                    ((Prims.of_int (302)),
                                                                    uu____2437,
                                                                    uu____2441) in
                                                                    let uu____2451
                                                                    =
                                                                    let uu____2465
                                                                    =
                                                                    let uu____2477
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3" in
                                                                    let uu____2481
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1" in
                                                                    ((Prims.of_int (303)),
                                                                    uu____2477,
                                                                    uu____2481) in
                                                                    let uu____2491
                                                                    =
                                                                    let uu____2505
                                                                    =
                                                                    let uu____2517
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4" in
                                                                    let uu____2521
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3" in
                                                                    ((Prims.of_int (3031)),
                                                                    uu____2517,
                                                                    uu____2521) in
                                                                    let uu____2531
                                                                    =
                                                                    let uu____2545
                                                                    =
                                                                    let uu____2557
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4" in
                                                                    let uu____2561
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4" in
                                                                    ((Prims.of_int (3032)),
                                                                    uu____2557,
                                                                    uu____2561) in
                                                                    let uu____2571
                                                                    =
                                                                    let uu____2585
                                                                    =
                                                                    let uu____2597
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9" in
                                                                    let uu____2601
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8" in
                                                                    ((Prims.of_int (3033)),
                                                                    uu____2597,
                                                                    uu____2601) in
                                                                    let uu____2611
                                                                    =
                                                                    let uu____2625
                                                                    =
                                                                    let uu____2637
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]" in
                                                                    let uu____2641
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]" in
                                                                    ((Prims.of_int (3034)),
                                                                    uu____2637,
                                                                    uu____2641) in
                                                                    let uu____2651
                                                                    =
                                                                    let uu____2665
                                                                    =
                                                                    let uu____2677
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]" in
                                                                    let uu____2681
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]" in
                                                                    ((Prims.of_int (3035)),
                                                                    uu____2677,
                                                                    uu____2681) in
                                                                    let uu____2691
                                                                    =
                                                                    let uu____2705
                                                                    =
                                                                    let uu____2717
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7" in
                                                                    let uu____2721
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6" in
                                                                    ((Prims.of_int (3036)),
                                                                    uu____2717,
                                                                    uu____2721) in
                                                                    let uu____2731
                                                                    =
                                                                    let uu____2745
                                                                    =
                                                                    let uu____2757
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T" in
                                                                    let uu____2761
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T" in
                                                                    ((Prims.of_int (305)),
                                                                    uu____2757,
                                                                    uu____2761) in
                                                                    let uu____2771
                                                                    =
                                                                    let uu____2785
                                                                    =
                                                                    let uu____2797
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]" in
                                                                    let uu____2801
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]" in
                                                                    ((Prims.of_int (306)),
                                                                    uu____2797,
                                                                    uu____2801) in
                                                                    let uu____2811
                                                                    =
                                                                    let uu____2825
                                                                    =
                                                                    let uu____2837
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]" in
                                                                    let uu____2841
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]" in
                                                                    ((Prims.of_int (307)),
                                                                    uu____2837,
                                                                    uu____2841) in
                                                                    let uu____2851
                                                                    =
                                                                    let uu____2865
                                                                    =
                                                                    let uu____2877
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]" in
                                                                    let uu____2881
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]" in
                                                                    ((Prims.of_int (308)),
                                                                    uu____2877,
                                                                    uu____2881) in
                                                                    let uu____2891
                                                                    =
                                                                    let uu____2905
                                                                    =
                                                                    let uu____2917
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]" in
                                                                    let uu____2921
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]" in
                                                                    ((Prims.of_int (304)),
                                                                    uu____2917,
                                                                    uu____2921) in
                                                                    let uu____2931
                                                                    =
                                                                    let uu____2945
                                                                    =
                                                                    let uu____2957
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]" in
                                                                    let uu____2961
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]" in
                                                                    ((Prims.of_int (305)),
                                                                    uu____2957,
                                                                    uu____2961) in
                                                                    let uu____2971
                                                                    =
                                                                    let uu____2985
                                                                    =
                                                                    let uu____2997
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1" in
                                                                    let uu____3001
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6" in
                                                                    ((Prims.of_int (309)),
                                                                    uu____2997,
                                                                    uu____3001) in
                                                                    let uu____3011
                                                                    =
                                                                    let uu____3025
                                                                    =
                                                                    let uu____3037
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2" in
                                                                    let uu____3041
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2" in
                                                                    ((Prims.of_int (310)),
                                                                    uu____3037,
                                                                    uu____3041) in
                                                                    let uu____3051
                                                                    =
                                                                    let uu____3065
                                                                    =
                                                                    let uu____3077
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3" in
                                                                    let uu____3081
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10" in
                                                                    ((Prims.of_int (401)),
                                                                    uu____3077,
                                                                    uu____3081) in
                                                                    let uu____3091
                                                                    =
                                                                    let uu____3105
                                                                    =
                                                                    let uu____3117
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false" in
                                                                    let uu____3121
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false" in
                                                                    ((Prims.of_int (402)),
                                                                    uu____3117,
                                                                    uu____3121) in
                                                                    let uu____3131
                                                                    =
                                                                    let uu____3145
                                                                    =
                                                                    let uu____3157
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5" in
                                                                    let uu____3161
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false" in
                                                                    ((Prims.of_int (403)),
                                                                    uu____3157,
                                                                    uu____3161) in
                                                                    let uu____3171
                                                                    =
                                                                    let uu____3185
                                                                    =
                                                                    let uu____3197
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\"" in
                                                                    let uu____3201
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\"" in
                                                                    ((Prims.of_int (404)),
                                                                    uu____3197,
                                                                    uu____3201) in
                                                                    let uu____3211
                                                                    =
                                                                    let uu____3225
                                                                    =
                                                                    let uu____3237
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun (x:list int) -> match x with | [] -> 0 | hd::tl -> 1) []" in
                                                                    let uu____3241
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "0" in
                                                                    ((Prims.of_int (405)),
                                                                    uu____3237,
                                                                    uu____3241) in
                                                                    [uu____3225] in
                                                                    uu____3185
                                                                    ::
                                                                    uu____3211 in
                                                                    uu____3145
                                                                    ::
                                                                    uu____3171 in
                                                                    uu____3105
                                                                    ::
                                                                    uu____3131 in
                                                                    uu____3065
                                                                    ::
                                                                    uu____3091 in
                                                                    uu____3025
                                                                    ::
                                                                    uu____3051 in
                                                                    uu____2985
                                                                    ::
                                                                    uu____3011 in
                                                                    uu____2945
                                                                    ::
                                                                    uu____2971 in
                                                                    uu____2905
                                                                    ::
                                                                    uu____2931 in
                                                                    uu____2865
                                                                    ::
                                                                    uu____2891 in
                                                                    uu____2825
                                                                    ::
                                                                    uu____2851 in
                                                                    uu____2785
                                                                    ::
                                                                    uu____2811 in
                                                                    uu____2745
                                                                    ::
                                                                    uu____2771 in
                                                                    uu____2705
                                                                    ::
                                                                    uu____2731 in
                                                                    uu____2665
                                                                    ::
                                                                    uu____2691 in
                                                                    uu____2625
                                                                    ::
                                                                    uu____2651 in
                                                                    uu____2585
                                                                    ::
                                                                    uu____2611 in
                                                                    uu____2545
                                                                    ::
                                                                    uu____2571 in
                                                                    uu____2505
                                                                    ::
                                                                    uu____2531 in
                                                                    uu____2465
                                                                    ::
                                                                    uu____2491 in
                                                                    uu____2425
                                                                    ::
                                                                    uu____2451 in
                                                                    uu____2385
                                                                    ::
                                                                    uu____2411 in
                                                                    uu____2345
                                                                    ::
                                                                    uu____2371 in
                                                                    uu____2305
                                                                    ::
                                                                    uu____2331 in
                                                                   uu____2265
                                                                    ::
                                                                    uu____2291 in
                                                                 uu____2225
                                                                   ::
                                                                   uu____2251 in
                                                               uu____2185 ::
                                                                 uu____2211 in
                                                             uu____2145 ::
                                                               uu____2171 in
                                                           uu____2105 ::
                                                             uu____2131 in
                                                         uu____2065 ::
                                                           uu____2091 in
                                                       uu____2025 ::
                                                         uu____2051 in
                                                     uu____1985 :: uu____2011 in
                                                   uu____1945 :: uu____1971 in
                                                 uu____1905 :: uu____1931 in
                                               uu____1865 :: uu____1891 in
                                             uu____1825 :: uu____1851 in
                                           uu____1785 :: uu____1811 in
                                         uu____1743 :: uu____1771 in
                                       uu____1701 :: uu____1729 in
                                     uu____1634 :: uu____1687 in
                                   uu____1567 :: uu____1620 in
                                 uu____1500 :: uu____1553 in
                               uu____1456 :: uu____1486 in
                             uu____1415 :: uu____1442 in
                           uu____1374 :: uu____1401 in
                         uu____1335 :: uu____1360 in
                       uu____1300 :: uu____1321 in
                     uu____1265 :: uu____1286 in
                   uu____1230 :: uu____1251 in
                 uu____1195 :: uu____1216 in
               uu____1160 :: uu____1181 in
             uu____1108 :: uu____1146 in
           uu____1044 :: uu____1094 in
         uu____995 :: uu____1030 in
       uu____946 :: uu____981 in
     uu____904 :: uu____932 in
   uu____856 :: uu____890)
let run_either :
  'uuuuuu3900 .
    Prims.int ->
      'uuuuuu3900 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'uuuuuu3900 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i ->
    fun r ->
      fun expected ->
        fun normalizer ->
          (let uu____3938 = FStar_Util.string_of_int i in
           FStar_Util.print1 "%s: ... \n\n" uu____3938);
          (let tcenv = FStar_Tests_Pars.init () in
           (let uu____3943 = FStar_Main.process_args () in
            FStar_All.pipe_right uu____3943 (fun uu____3958 -> ()));
           (let x = normalizer tcenv r in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____3967 =
               let uu____3969 = FStar_Syntax_Util.unascribe x in
               FStar_Tests_Util.term_eq uu____3969 expected in
             FStar_Tests_Util.always i uu____3967)))
let (run_interpreter :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun i ->
    fun r ->
      fun expected ->
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
  fun i ->
    fun r ->
      fun expected ->
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
  fun i ->
    fun r ->
      fun expected ->
        let interp uu____4048 = run_interpreter i r expected in
        let uu____4049 =
          let uu____4050 = FStar_Util.return_execution_time interp in
          FStar_Pervasives_Native.snd uu____4050 in
        (i, uu____4049)
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i ->
    fun r ->
      fun expected ->
        let nbe uu____4088 = run_nbe i r expected in
        let uu____4089 =
          let uu____4090 = FStar_Util.return_execution_time nbe in
          FStar_Pervasives_Native.snd uu____4090 in
        (i, uu____4089)
let run_tests :
  'uuuuuu4101 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'uuuuuu4101)
      -> 'uuuuuu4101 Prims.list
  =
  fun run ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___0_4153 ->
            match uu___0_4153 with | (no, test, res) -> run no test res)
         tests in
     FStar_Options.__clear_unit_tests (); l)
let (run_all_nbe : unit -> unit) =
  fun uu____4184 ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____4187 = run_tests run_nbe in FStar_Util.print_string "NBE ok\n")
let (run_all_interpreter : unit -> unit) =
  fun uu____4196 ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____4199 = run_tests run_interpreter in
     FStar_Util.print_string "Normalizer ok\n")
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____4215 ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time in
     FStar_Util.print_string "NBE ok\n"; l)
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____4245 ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let l = run_tests run_interpreter_with_time in
     FStar_Util.print_string "Normalizer ok\n"; l)
let (run_both_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun i ->
    fun r ->
      fun expected ->
        let nbe uu____4290 = run_nbe i r expected in
        let norm uu____4296 = run_interpreter i r expected in
        FStar_Util.measure_execution_time "nbe" nbe;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm;
        FStar_Util.print_string "\n"
let (compare : unit -> unit) =
  fun uu____4309 ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____4312 =
       let uu____4313 = encode (Prims.of_int (1000)) in
       let uu____4315 =
         let uu____4318 = FStar_Tests_Util.nm FStar_Tests_Util.x in
         let uu____4319 = FStar_Tests_Util.nm FStar_Tests_Util.x in
         minus uu____4318 uu____4319 in
       let_ FStar_Tests_Util.x uu____4313 uu____4315 in
     run_both_with_time (Prims.of_int (14)) uu____4312 z)
let (compare_times :
  (Prims.int * FStar_BaseTypes.float) Prims.list ->
    (Prims.int * FStar_BaseTypes.float) Prims.list -> unit)
  =
  fun l_int ->
    fun l_nbe ->
      FStar_Util.print_string "Comparing times for normalization and nbe\n";
      FStar_List.iter2
        (fun res1 ->
           fun res2 ->
             let uu____4395 = res1 in
             match uu____4395 with
             | (t1, time_int) ->
                 let uu____4405 = res2 in
                 (match uu____4405 with
                  | (t2, time_nbe) ->
                      if t1 = t2
                      then
                        let uu____4417 = FStar_Util.string_of_int t1 in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____4417 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
let (run_all : unit -> unit) =
  fun uu____4428 ->
    (let uu____4430 = FStar_Syntax_Print.term_to_string znat in
     FStar_Util.print1 "%s" uu____4430);
    (let l_int = run_all_interpreter_with_time () in
     let l_nbe = run_all_nbe_with_time () in compare_times l_int l_nbe)