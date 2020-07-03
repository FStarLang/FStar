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
      (let uu____10 = let uu____13 = encode (n - Prims.int_one) in [uu____13] in
       FStar_Tests_Util.app succ uu____10)
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
        let uu____49 =
          let uu____52 = let uu____53 = b x in [uu____53] in
          FStar_Syntax_Util.abs uu____52 e' FStar_Pervasives_Native.None in
        FStar_Tests_Util.app uu____49 [e]
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
  let uu____109 = lid "Z" in
  FStar_Syntax_Syntax.lid_as_fv uu____109 FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____110 = lid "S" in
  FStar_Syntax_Syntax.lid_as_fv uu____110 FStar_Syntax_Syntax.delta_constant
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
    let uu____125 =
      let uu____126 =
        let uu____143 = tm_fv snat_l in
        let uu____146 =
          let uu____157 = FStar_Syntax_Syntax.as_arg s in [uu____157] in
        (uu____143, uu____146) in
      FStar_Syntax_Syntax.Tm_app uu____126 in
    FStar_Syntax_Syntax.mk uu____125 FStar_Range.dummyRange
let pat :
  'uuuuuu198 . 'uuuuuu198 -> 'uuuuuu198 FStar_Syntax_Syntax.withinfo_t =
  fun p -> FStar_Syntax_Syntax.withinfo p FStar_Range.dummyRange
let (snat_type : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  let uu____208 =
    let uu____209 = lid "snat" in
    FStar_Syntax_Syntax.lid_as_fv uu____209
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
  tm_fv uu____208
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
      let uu____309 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, [])) in
      (uu____309, FStar_Pervasives_Native.None, znat) in
    let sbranch =
      let uu____351 =
        let uu____354 =
          let uu____355 =
            let uu____368 =
              let uu____377 =
                let uu____384 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x) in
                (uu____384, false) in
              [uu____377] in
            (snat_l, uu____368) in
          FStar_Syntax_Syntax.Pat_cons uu____355 in
        pat uu____354 in
      let uu____409 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___21_414 = FStar_Tests_Util.x in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___21_414.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = Prims.int_zero;
                FStar_Syntax_Syntax.sort =
                  (uu___21_414.FStar_Syntax_Syntax.sort)
              })) FStar_Range.dummyRange in
      (uu____351, FStar_Pervasives_Native.None, uu____409) in
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
        let uu___27_439 = FStar_Tests_Util.x in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___27_439.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index = (uu___27_439.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = snat_type
        } in
      let y =
        let uu___30_441 = FStar_Tests_Util.y in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___30_441.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index = (uu___30_441.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = snat_type
        } in
      let zbranch =
        let uu____457 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, [])) in
        let uu____474 = FStar_Tests_Util.nm x in
        (uu____457, FStar_Pervasives_Native.None, uu____474) in
      let sbranch =
        let uu____502 =
          let uu____505 =
            let uu____506 =
              let uu____519 =
                let uu____528 =
                  let uu____535 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n) in
                  (uu____535, false) in
                [uu____528] in
              (snat_l, uu____519) in
            FStar_Syntax_Syntax.Pat_cons uu____506 in
          pat uu____505 in
        let uu____560 =
          let uu____563 = FStar_Tests_Util.nm minus1 in
          let uu____566 =
            let uu____569 =
              let uu____570 = FStar_Tests_Util.nm x in pred_nat uu____570 in
            let uu____573 =
              let uu____576 = FStar_Tests_Util.nm FStar_Tests_Util.n in
              [uu____576] in
            uu____569 :: uu____573 in
          FStar_Tests_Util.app uu____563 uu____566 in
        (uu____502, FStar_Pervasives_Native.None, uu____560) in
      let lb =
        let uu____588 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange in
        let uu____589 =
          let uu____592 =
            let uu____593 =
              let uu____594 = b x in
              let uu____601 = let uu____610 = b y in [uu____610] in uu____594
                :: uu____601 in
            let uu____635 =
              let uu____638 = FStar_Tests_Util.nm y in
              mk_match uu____638 [zbranch; sbranch] in
            FStar_Syntax_Util.abs uu____593 uu____635
              FStar_Pervasives_Native.None in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, Prims.int_zero)] uu____592 in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____588;
          FStar_Syntax_Syntax.lbdef = uu____589;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        } in
      let uu____643 =
        let uu____644 =
          let uu____657 =
            let uu____660 =
              let uu____661 = FStar_Tests_Util.nm minus1 in
              FStar_Tests_Util.app uu____661 [t1; t2] in
            FStar_Syntax_Subst.subst
              [FStar_Syntax_Syntax.NM (minus1, Prims.int_zero)] uu____660 in
          ((true, [lb]), uu____657) in
        FStar_Syntax_Syntax.Tm_let uu____644 in
      FStar_Syntax_Syntax.mk uu____643 FStar_Range.dummyRange
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n ->
    let rec aux out n1 =
      if n1 = Prims.int_zero
      then out
      else (let uu____691 = snat out in aux uu____691 (n1 - Prims.int_one)) in
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
  (let uu____729 =
     let uu____740 =
       let uu____743 =
         let uu____746 =
           let uu____749 =
             let uu____752 = FStar_Tests_Util.nm FStar_Tests_Util.n in
             [uu____752] in
           id :: uu____749 in
         one :: uu____746 in
       FStar_Tests_Util.app apply uu____743 in
     let uu____753 = FStar_Tests_Util.nm FStar_Tests_Util.n in
     (Prims.int_zero, uu____740, uu____753) in
   let uu____760 =
     let uu____773 =
       let uu____784 =
         let uu____787 =
           let uu____790 = FStar_Tests_Util.nm FStar_Tests_Util.x in
           [uu____790] in
         FStar_Tests_Util.app id uu____787 in
       let uu____791 = FStar_Tests_Util.nm FStar_Tests_Util.x in
       (Prims.int_one, uu____784, uu____791) in
     let uu____798 =
       let uu____811 =
         let uu____822 =
           let uu____825 =
             let uu____828 =
               let uu____831 = FStar_Tests_Util.nm FStar_Tests_Util.n in
               let uu____832 =
                 let uu____835 = FStar_Tests_Util.nm FStar_Tests_Util.m in
                 [uu____835] in
               uu____831 :: uu____832 in
             tt :: uu____828 in
           FStar_Tests_Util.app apply uu____825 in
         let uu____836 = FStar_Tests_Util.nm FStar_Tests_Util.n in
         (Prims.int_one, uu____822, uu____836) in
       let uu____843 =
         let uu____856 =
           let uu____867 =
             let uu____870 =
               let uu____873 =
                 let uu____876 = FStar_Tests_Util.nm FStar_Tests_Util.n in
                 let uu____877 =
                   let uu____880 = FStar_Tests_Util.nm FStar_Tests_Util.m in
                   [uu____880] in
                 uu____876 :: uu____877 in
               ff :: uu____873 in
             FStar_Tests_Util.app apply uu____870 in
           let uu____881 = FStar_Tests_Util.nm FStar_Tests_Util.m in
           ((Prims.of_int (2)), uu____867, uu____881) in
         let uu____888 =
           let uu____901 =
             let uu____912 =
               let uu____915 =
                 let uu____918 =
                   let uu____921 =
                     let uu____924 =
                       let uu____927 =
                         let uu____930 =
                           let uu____933 =
                             let uu____936 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n in
                             let uu____937 =
                               let uu____940 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m in
                               [uu____940] in
                             uu____936 :: uu____937 in
                           ff :: uu____933 in
                         apply :: uu____930 in
                       apply :: uu____927 in
                     apply :: uu____924 in
                   apply :: uu____921 in
                 apply :: uu____918 in
               FStar_Tests_Util.app apply uu____915 in
             let uu____941 = FStar_Tests_Util.nm FStar_Tests_Util.m in
             ((Prims.of_int (3)), uu____912, uu____941) in
           let uu____948 =
             let uu____961 =
               let uu____972 =
                 let uu____975 =
                   let uu____978 =
                     let uu____981 =
                       let uu____984 = FStar_Tests_Util.nm FStar_Tests_Util.n in
                       let uu____985 =
                         let uu____988 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m in
                         [uu____988] in
                       uu____984 :: uu____985 in
                     ff :: uu____981 in
                   apply :: uu____978 in
                 FStar_Tests_Util.app twice uu____975 in
               let uu____989 = FStar_Tests_Util.nm FStar_Tests_Util.m in
               ((Prims.of_int (4)), uu____972, uu____989) in
             let uu____996 =
               let uu____1009 =
                 let uu____1020 = minus one z in
                 ((Prims.of_int (5)), uu____1020, one) in
               let uu____1027 =
                 let uu____1040 =
                   let uu____1051 = FStar_Tests_Util.app pred [one] in
                   ((Prims.of_int (6)), uu____1051, z) in
                 let uu____1058 =
                   let uu____1071 =
                     let uu____1082 = minus one one in
                     ((Prims.of_int (7)), uu____1082, z) in
                   let uu____1089 =
                     let uu____1102 =
                       let uu____1113 = FStar_Tests_Util.app mul [one; one] in
                       ((Prims.of_int (8)), uu____1113, one) in
                     let uu____1120 =
                       let uu____1133 =
                         let uu____1144 = FStar_Tests_Util.app mul [two; one] in
                         ((Prims.of_int (9)), uu____1144, two) in
                       let uu____1151 =
                         let uu____1164 =
                           let uu____1175 =
                             let uu____1178 =
                               let uu____1181 =
                                 FStar_Tests_Util.app succ [one] in
                               [uu____1181; one] in
                             FStar_Tests_Util.app mul uu____1178 in
                           ((Prims.of_int (10)), uu____1175, two) in
                         let uu____1186 =
                           let uu____1199 =
                             let uu____1210 =
                               let uu____1213 = encode (Prims.of_int (10)) in
                               let uu____1214 = encode (Prims.of_int (10)) in
                               minus uu____1213 uu____1214 in
                             ((Prims.of_int (11)), uu____1210, z) in
                           let uu____1221 =
                             let uu____1234 =
                               let uu____1245 =
                                 let uu____1248 = encode (Prims.of_int (100)) in
                                 let uu____1249 = encode (Prims.of_int (100)) in
                                 minus uu____1248 uu____1249 in
                               ((Prims.of_int (12)), uu____1245, z) in
                             let uu____1256 =
                               let uu____1269 =
                                 let uu____1280 =
                                   let uu____1283 =
                                     encode (Prims.of_int (100)) in
                                   let uu____1284 =
                                     let uu____1287 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x in
                                     let uu____1288 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x in
                                     minus uu____1287 uu____1288 in
                                   let_ FStar_Tests_Util.x uu____1283
                                     uu____1284 in
                                 ((Prims.of_int (13)), uu____1280, z) in
                               let uu____1295 =
                                 let uu____1308 =
                                   let uu____1319 =
                                     let uu____1322 =
                                       FStar_Tests_Util.app succ [one] in
                                     let uu____1323 =
                                       let uu____1326 =
                                         let uu____1327 =
                                           let uu____1330 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x in
                                           let uu____1331 =
                                             let uu____1334 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x in
                                             [uu____1334] in
                                           uu____1330 :: uu____1331 in
                                         FStar_Tests_Util.app mul uu____1327 in
                                       let uu____1335 =
                                         let uu____1338 =
                                           let uu____1339 =
                                             let uu____1342 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y in
                                             let uu____1343 =
                                               let uu____1346 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y in
                                               [uu____1346] in
                                             uu____1342 :: uu____1343 in
                                           FStar_Tests_Util.app mul
                                             uu____1339 in
                                         let uu____1347 =
                                           let uu____1350 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h in
                                           let uu____1351 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h in
                                           minus uu____1350 uu____1351 in
                                         let_ FStar_Tests_Util.h uu____1338
                                           uu____1347 in
                                       let_ FStar_Tests_Util.y uu____1326
                                         uu____1335 in
                                     let_ FStar_Tests_Util.x uu____1322
                                       uu____1323 in
                                   ((Prims.of_int (15)), uu____1319, z) in
                                 let uu____1358 =
                                   let uu____1371 =
                                     let uu____1382 =
                                       let uu____1385 =
                                         FStar_Tests_Util.app succ [one] in
                                       let uu____1388 =
                                         let uu____1389 =
                                           let uu____1392 =
                                             let uu____1395 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x in
                                             let uu____1396 =
                                               let uu____1399 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x in
                                               [uu____1399] in
                                             uu____1395 :: uu____1396 in
                                           FStar_Tests_Util.app mul
                                             uu____1392 in
                                         let uu____1400 =
                                           let uu____1401 =
                                             let uu____1404 =
                                               let uu____1407 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y in
                                               let uu____1408 =
                                                 let uu____1411 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y in
                                                 [uu____1411] in
                                               uu____1407 :: uu____1408 in
                                             FStar_Tests_Util.app mul
                                               uu____1404 in
                                           let uu____1412 =
                                             let uu____1413 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h in
                                             let uu____1414 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h in
                                             minus uu____1413 uu____1414 in
                                           mk_let FStar_Tests_Util.h
                                             uu____1401 uu____1412 in
                                         mk_let FStar_Tests_Util.y uu____1389
                                           uu____1400 in
                                       mk_let FStar_Tests_Util.x uu____1385
                                         uu____1388 in
                                     ((Prims.of_int (16)), uu____1382, z) in
                                   let uu____1421 =
                                     let uu____1434 =
                                       let uu____1445 =
                                         let uu____1448 =
                                           FStar_Tests_Util.app succ [one] in
                                         let uu____1449 =
                                           let uu____1452 =
                                             let uu____1453 =
                                               let uu____1456 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x in
                                               let uu____1457 =
                                                 let uu____1460 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x in
                                                 [uu____1460] in
                                               uu____1456 :: uu____1457 in
                                             FStar_Tests_Util.app mul
                                               uu____1453 in
                                           let uu____1461 =
                                             let uu____1464 =
                                               let uu____1465 =
                                                 let uu____1468 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y in
                                                 let uu____1469 =
                                                   let uu____1472 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y in
                                                   [uu____1472] in
                                                 uu____1468 :: uu____1469 in
                                               FStar_Tests_Util.app mul
                                                 uu____1465 in
                                             let uu____1473 =
                                               let uu____1476 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h in
                                               let uu____1477 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h in
                                               minus uu____1476 uu____1477 in
                                             let_ FStar_Tests_Util.h
                                               uu____1464 uu____1473 in
                                           let_ FStar_Tests_Util.y uu____1452
                                             uu____1461 in
                                         let_ FStar_Tests_Util.x uu____1448
                                           uu____1449 in
                                       ((Prims.of_int (17)), uu____1445, z) in
                                     let uu____1484 =
                                       let uu____1497 =
                                         let uu____1508 =
                                           let uu____1511 =
                                             let uu____1514 = snat znat in
                                             snat uu____1514 in
                                           pred_nat uu____1511 in
                                         let uu____1515 = snat znat in
                                         ((Prims.of_int (18)), uu____1508,
                                           uu____1515) in
                                       let uu____1522 =
                                         let uu____1535 =
                                           let uu____1546 =
                                             let uu____1549 =
                                               let uu____1550 =
                                                 let uu____1551 = snat znat in
                                                 snat uu____1551 in
                                               let uu____1552 = snat znat in
                                               minus_nat uu____1550
                                                 uu____1552 in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____1549 in
                                           let uu____1553 = snat znat in
                                           ((Prims.of_int (19)), uu____1546,
                                             uu____1553) in
                                         let uu____1560 =
                                           let uu____1573 =
                                             let uu____1584 =
                                               let uu____1587 =
                                                 let uu____1588 =
                                                   encode_nat
                                                     (Prims.of_int (10)) in
                                                 let uu____1589 =
                                                   encode_nat
                                                     (Prims.of_int (10)) in
                                                 minus_nat uu____1588
                                                   uu____1589 in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____1587 in
                                             ((Prims.of_int (20)),
                                               uu____1584, znat) in
                                           let uu____1594 =
                                             let uu____1607 =
                                               let uu____1618 =
                                                 let uu____1621 =
                                                   let uu____1622 =
                                                     encode_nat
                                                       (Prims.of_int (100)) in
                                                   let uu____1623 =
                                                     encode_nat
                                                       (Prims.of_int (100)) in
                                                   minus_nat uu____1622
                                                     uu____1623 in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____1621 in
                                               ((Prims.of_int (21)),
                                                 uu____1618, znat) in
                                             let uu____1628 =
                                               let uu____1641 =
                                                 let uu____1652 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]" in
                                                 let uu____1655 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]" in
                                                 ((Prims.of_int (24)),
                                                   uu____1652, uu____1655) in
                                               let uu____1662 =
                                                 let uu____1675 =
                                                   let uu____1686 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]" in
                                                   let uu____1689 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]" in
                                                   ((Prims.of_int (241)),
                                                     uu____1686, uu____1689) in
                                                 let uu____1696 =
                                                   let uu____1709 =
                                                     let uu____1720 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]" in
                                                     let uu____1723 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]" in
                                                     ((Prims.of_int (25)),
                                                       uu____1720,
                                                       uu____1723) in
                                                   let uu____1730 =
                                                     let uu____1743 =
                                                       let uu____1754 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]" in
                                                       let uu____1757 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]" in
                                                       ((Prims.of_int (26)),
                                                         uu____1754,
                                                         uu____1757) in
                                                     let uu____1764 =
                                                       let uu____1777 =
                                                         let uu____1788 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T" in
                                                         let uu____1791 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F" in
                                                         ((Prims.of_int (28)),
                                                           uu____1788,
                                                           uu____1791) in
                                                       let uu____1798 =
                                                         let uu____1811 =
                                                           let uu____1822 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]" in
                                                           let uu____1825 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]" in
                                                           ((Prims.of_int (29)),
                                                             uu____1822,
                                                             uu____1825) in
                                                         let uu____1832 =
                                                           let uu____1845 =
                                                             let uu____1856 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T" in
                                                             let uu____1859 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T" in
                                                             ((Prims.of_int (31)),
                                                               uu____1856,
                                                               uu____1859) in
                                                           let uu____1866 =
                                                             let uu____1879 =
                                                               let uu____1890
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T" in
                                                               let uu____1893
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T" in
                                                               ((Prims.of_int (32)),
                                                                 uu____1890,
                                                                 uu____1893) in
                                                             let uu____1900 =
                                                               let uu____1913
                                                                 =
                                                                 let uu____1924
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T" in
                                                                 let uu____1927
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F" in
                                                                 ((Prims.of_int (33)),
                                                                   uu____1924,
                                                                   uu____1927) in
                                                               let uu____1934
                                                                 =
                                                                 let uu____1947
                                                                   =
                                                                   let uu____1958
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F" in
                                                                   let uu____1961
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T" in
                                                                   ((Prims.of_int (34)),
                                                                    uu____1958,
                                                                    uu____1961) in
                                                                 let uu____1968
                                                                   =
                                                                   let uu____1981
                                                                    =
                                                                    let uu____1992
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F" in
                                                                    let uu____1995
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T" in
                                                                    ((Prims.of_int (35)),
                                                                    uu____1992,
                                                                    uu____1995) in
                                                                   let uu____2002
                                                                    =
                                                                    let uu____2015
                                                                    =
                                                                    let uu____2026
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T" in
                                                                    let uu____2029
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T" in
                                                                    ((Prims.of_int (36)),
                                                                    uu____2026,
                                                                    uu____2029) in
                                                                    let uu____2036
                                                                    =
                                                                    let uu____2049
                                                                    =
                                                                    let uu____2060
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]" in
                                                                    let uu____2063
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]" in
                                                                    ((Prims.of_int (301)),
                                                                    uu____2060,
                                                                    uu____2063) in
                                                                    let uu____2070
                                                                    =
                                                                    let uu____2083
                                                                    =
                                                                    let uu____2094
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]" in
                                                                    let uu____2097
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]" in
                                                                    ((Prims.of_int (3012)),
                                                                    uu____2094,
                                                                    uu____2097) in
                                                                    let uu____2104
                                                                    =
                                                                    let uu____2117
                                                                    =
                                                                    let uu____2128
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]" in
                                                                    let uu____2131
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]" in
                                                                    ((Prims.of_int (302)),
                                                                    uu____2128,
                                                                    uu____2131) in
                                                                    let uu____2138
                                                                    =
                                                                    let uu____2151
                                                                    =
                                                                    let uu____2162
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3" in
                                                                    let uu____2165
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1" in
                                                                    ((Prims.of_int (303)),
                                                                    uu____2162,
                                                                    uu____2165) in
                                                                    let uu____2172
                                                                    =
                                                                    let uu____2185
                                                                    =
                                                                    let uu____2196
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4" in
                                                                    let uu____2199
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3" in
                                                                    ((Prims.of_int (3031)),
                                                                    uu____2196,
                                                                    uu____2199) in
                                                                    let uu____2206
                                                                    =
                                                                    let uu____2219
                                                                    =
                                                                    let uu____2230
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4" in
                                                                    let uu____2233
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4" in
                                                                    ((Prims.of_int (3032)),
                                                                    uu____2230,
                                                                    uu____2233) in
                                                                    let uu____2240
                                                                    =
                                                                    let uu____2253
                                                                    =
                                                                    let uu____2264
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9" in
                                                                    let uu____2267
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8" in
                                                                    ((Prims.of_int (3033)),
                                                                    uu____2264,
                                                                    uu____2267) in
                                                                    let uu____2274
                                                                    =
                                                                    let uu____2287
                                                                    =
                                                                    let uu____2298
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]" in
                                                                    let uu____2301
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]" in
                                                                    ((Prims.of_int (3034)),
                                                                    uu____2298,
                                                                    uu____2301) in
                                                                    let uu____2308
                                                                    =
                                                                    let uu____2321
                                                                    =
                                                                    let uu____2332
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]" in
                                                                    let uu____2335
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]" in
                                                                    ((Prims.of_int (3035)),
                                                                    uu____2332,
                                                                    uu____2335) in
                                                                    let uu____2342
                                                                    =
                                                                    let uu____2355
                                                                    =
                                                                    let uu____2366
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7" in
                                                                    let uu____2369
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6" in
                                                                    ((Prims.of_int (3036)),
                                                                    uu____2366,
                                                                    uu____2369) in
                                                                    let uu____2376
                                                                    =
                                                                    let uu____2389
                                                                    =
                                                                    let uu____2400
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T" in
                                                                    let uu____2403
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T" in
                                                                    ((Prims.of_int (305)),
                                                                    uu____2400,
                                                                    uu____2403) in
                                                                    let uu____2410
                                                                    =
                                                                    let uu____2423
                                                                    =
                                                                    let uu____2434
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]" in
                                                                    let uu____2437
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]" in
                                                                    ((Prims.of_int (306)),
                                                                    uu____2434,
                                                                    uu____2437) in
                                                                    let uu____2444
                                                                    =
                                                                    let uu____2457
                                                                    =
                                                                    let uu____2468
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]" in
                                                                    let uu____2471
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]" in
                                                                    ((Prims.of_int (307)),
                                                                    uu____2468,
                                                                    uu____2471) in
                                                                    let uu____2478
                                                                    =
                                                                    let uu____2491
                                                                    =
                                                                    let uu____2502
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]" in
                                                                    let uu____2505
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]" in
                                                                    ((Prims.of_int (308)),
                                                                    uu____2502,
                                                                    uu____2505) in
                                                                    let uu____2512
                                                                    =
                                                                    let uu____2525
                                                                    =
                                                                    let uu____2536
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]" in
                                                                    let uu____2539
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]" in
                                                                    ((Prims.of_int (304)),
                                                                    uu____2536,
                                                                    uu____2539) in
                                                                    let uu____2546
                                                                    =
                                                                    let uu____2559
                                                                    =
                                                                    let uu____2570
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]" in
                                                                    let uu____2573
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]" in
                                                                    ((Prims.of_int (305)),
                                                                    uu____2570,
                                                                    uu____2573) in
                                                                    let uu____2580
                                                                    =
                                                                    let uu____2593
                                                                    =
                                                                    let uu____2604
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1" in
                                                                    let uu____2607
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6" in
                                                                    ((Prims.of_int (309)),
                                                                    uu____2604,
                                                                    uu____2607) in
                                                                    let uu____2614
                                                                    =
                                                                    let uu____2627
                                                                    =
                                                                    let uu____2638
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2" in
                                                                    let uu____2641
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2" in
                                                                    ((Prims.of_int (310)),
                                                                    uu____2638,
                                                                    uu____2641) in
                                                                    let uu____2648
                                                                    =
                                                                    let uu____2661
                                                                    =
                                                                    let uu____2672
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3" in
                                                                    let uu____2675
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10" in
                                                                    ((Prims.of_int (401)),
                                                                    uu____2672,
                                                                    uu____2675) in
                                                                    let uu____2682
                                                                    =
                                                                    let uu____2695
                                                                    =
                                                                    let uu____2706
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false" in
                                                                    let uu____2709
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false" in
                                                                    ((Prims.of_int (402)),
                                                                    uu____2706,
                                                                    uu____2709) in
                                                                    let uu____2716
                                                                    =
                                                                    let uu____2729
                                                                    =
                                                                    let uu____2740
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5" in
                                                                    let uu____2743
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false" in
                                                                    ((Prims.of_int (403)),
                                                                    uu____2740,
                                                                    uu____2743) in
                                                                    let uu____2750
                                                                    =
                                                                    let uu____2763
                                                                    =
                                                                    let uu____2774
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\"" in
                                                                    let uu____2777
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\"" in
                                                                    ((Prims.of_int (404)),
                                                                    uu____2774,
                                                                    uu____2777) in
                                                                    let uu____2784
                                                                    =
                                                                    let uu____2797
                                                                    =
                                                                    let uu____2808
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun (x:list int) -> match x with | [] -> 0 | hd::tl -> 1) []" in
                                                                    let uu____2811
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "0" in
                                                                    ((Prims.of_int (405)),
                                                                    uu____2808,
                                                                    uu____2811) in
                                                                    [uu____2797] in
                                                                    uu____2763
                                                                    ::
                                                                    uu____2784 in
                                                                    uu____2729
                                                                    ::
                                                                    uu____2750 in
                                                                    uu____2695
                                                                    ::
                                                                    uu____2716 in
                                                                    uu____2661
                                                                    ::
                                                                    uu____2682 in
                                                                    uu____2627
                                                                    ::
                                                                    uu____2648 in
                                                                    uu____2593
                                                                    ::
                                                                    uu____2614 in
                                                                    uu____2559
                                                                    ::
                                                                    uu____2580 in
                                                                    uu____2525
                                                                    ::
                                                                    uu____2546 in
                                                                    uu____2491
                                                                    ::
                                                                    uu____2512 in
                                                                    uu____2457
                                                                    ::
                                                                    uu____2478 in
                                                                    uu____2423
                                                                    ::
                                                                    uu____2444 in
                                                                    uu____2389
                                                                    ::
                                                                    uu____2410 in
                                                                    uu____2355
                                                                    ::
                                                                    uu____2376 in
                                                                    uu____2321
                                                                    ::
                                                                    uu____2342 in
                                                                    uu____2287
                                                                    ::
                                                                    uu____2308 in
                                                                    uu____2253
                                                                    ::
                                                                    uu____2274 in
                                                                    uu____2219
                                                                    ::
                                                                    uu____2240 in
                                                                    uu____2185
                                                                    ::
                                                                    uu____2206 in
                                                                    uu____2151
                                                                    ::
                                                                    uu____2172 in
                                                                    uu____2117
                                                                    ::
                                                                    uu____2138 in
                                                                    uu____2083
                                                                    ::
                                                                    uu____2104 in
                                                                    uu____2049
                                                                    ::
                                                                    uu____2070 in
                                                                    uu____2015
                                                                    ::
                                                                    uu____2036 in
                                                                   uu____1981
                                                                    ::
                                                                    uu____2002 in
                                                                 uu____1947
                                                                   ::
                                                                   uu____1968 in
                                                               uu____1913 ::
                                                                 uu____1934 in
                                                             uu____1879 ::
                                                               uu____1900 in
                                                           uu____1845 ::
                                                             uu____1866 in
                                                         uu____1811 ::
                                                           uu____1832 in
                                                       uu____1777 ::
                                                         uu____1798 in
                                                     uu____1743 :: uu____1764 in
                                                   uu____1709 :: uu____1730 in
                                                 uu____1675 :: uu____1696 in
                                               uu____1641 :: uu____1662 in
                                             uu____1607 :: uu____1628 in
                                           uu____1573 :: uu____1594 in
                                         uu____1535 :: uu____1560 in
                                       uu____1497 :: uu____1522 in
                                     uu____1434 :: uu____1484 in
                                   uu____1371 :: uu____1421 in
                                 uu____1308 :: uu____1358 in
                               uu____1269 :: uu____1295 in
                             uu____1234 :: uu____1256 in
                           uu____1199 :: uu____1221 in
                         uu____1164 :: uu____1186 in
                       uu____1133 :: uu____1151 in
                     uu____1102 :: uu____1120 in
                   uu____1071 :: uu____1089 in
                 uu____1040 :: uu____1058 in
               uu____1009 :: uu____1027 in
             uu____961 :: uu____996 in
           uu____901 :: uu____948 in
         uu____856 :: uu____888 in
       uu____811 :: uu____843 in
     uu____773 :: uu____798 in
   uu____729 :: uu____760)
let run_either :
  'uuuuuu3408 .
    Prims.int ->
      'uuuuuu3408 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'uuuuuu3408 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i ->
    fun r ->
      fun expected ->
        fun normalizer ->
          (let uu____3444 = FStar_Util.string_of_int i in
           FStar_Util.print1 "%s: ... \n\n" uu____3444);
          (let tcenv = FStar_Tests_Pars.init () in
           (let uu____3447 = FStar_Main.process_args () in
            FStar_All.pipe_right uu____3447 (fun uu____3460 -> ()));
           (let x = normalizer tcenv r in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____3465 =
               let uu____3466 = FStar_Syntax_Util.unascribe x in
               FStar_Tests_Util.term_eq uu____3466 expected in
             FStar_Tests_Util.always i uu____3465)))
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
        let interp uu____3535 = run_interpreter i r expected in
        let uu____3536 =
          let uu____3537 = FStar_Util.return_execution_time interp in
          FStar_Pervasives_Native.snd uu____3537 in
        (i, uu____3536)
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i ->
    fun r ->
      fun expected ->
        let nbe uu____3570 = run_nbe i r expected in
        let uu____3571 =
          let uu____3572 = FStar_Util.return_execution_time nbe in
          FStar_Pervasives_Native.snd uu____3572 in
        (i, uu____3571)
let run_tests :
  'uuuuuu3581 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'uuuuuu3581)
      -> 'uuuuuu3581 Prims.list
  =
  fun run ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___0_3630 ->
            match uu___0_3630 with | (no, test, res) -> run no test res)
         tests in
     FStar_Options.__clear_unit_tests (); l)
let (run_all_nbe : unit -> unit) =
  fun uu____3657 ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____3659 = run_tests run_nbe in FStar_Util.print_string "NBE ok\n")
let (run_all_interpreter : unit -> unit) =
  fun uu____3666 ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____3668 = run_tests run_interpreter in
     FStar_Util.print_string "Normalizer ok\n")
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____3681 ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time in
     FStar_Util.print_string "NBE ok\n"; l)
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____3705 ->
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
        let nbe uu____3743 = run_nbe i r expected in
        let norm uu____3749 = run_interpreter i r expected in
        FStar_Util.measure_execution_time "nbe" nbe;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm;
        FStar_Util.print_string "\n"
let (compare : unit -> unit) =
  fun uu____3757 ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____3759 =
       let uu____3760 = encode (Prims.of_int (1000)) in
       let uu____3761 =
         let uu____3764 = FStar_Tests_Util.nm FStar_Tests_Util.x in
         let uu____3765 = FStar_Tests_Util.nm FStar_Tests_Util.x in
         minus uu____3764 uu____3765 in
       let_ FStar_Tests_Util.x uu____3760 uu____3761 in
     run_both_with_time (Prims.of_int (14)) uu____3759 z)
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
             let uu____3830 = res1 in
             match uu____3830 with
             | (t1, time_int) ->
                 let uu____3837 = res2 in
                 (match uu____3837 with
                  | (t2, time_nbe) ->
                      if t1 = t2
                      then
                        let uu____3844 = FStar_Util.string_of_int t1 in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____3844 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
let (run_all : unit -> unit) =
  fun uu____3850 ->
    (let uu____3852 = FStar_Syntax_Print.term_to_string znat in
     FStar_Util.print1 "%s" uu____3852);
    (let l_int = run_all_interpreter_with_time () in
     let l_nbe = run_all_nbe_with_time () in compare_times l_int l_nbe)