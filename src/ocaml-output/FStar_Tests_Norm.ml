open Prims
let b: FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.binder =
  FStar_Syntax_Syntax.mk_binder
let id: FStar_Syntax_Syntax.term = FStar_Tests_Pars.pars "fun x -> x"
let apply: FStar_Syntax_Syntax.term = FStar_Tests_Pars.pars "fun f x -> f x"
let twice: FStar_Syntax_Syntax.term =
  FStar_Tests_Pars.pars "fun f x -> f (f x)"
let tt: FStar_Syntax_Syntax.term = FStar_Tests_Pars.pars "fun x y -> x"
let ff: FStar_Syntax_Syntax.term = FStar_Tests_Pars.pars "fun x y -> y"
let z: FStar_Syntax_Syntax.term = FStar_Tests_Pars.pars "fun f x -> x"
let one: FStar_Syntax_Syntax.term = FStar_Tests_Pars.pars "fun f x -> f x"
let two: FStar_Syntax_Syntax.term =
  FStar_Tests_Pars.pars "fun f x -> f (f x)"
let succ: FStar_Syntax_Syntax.term =
  FStar_Tests_Pars.pars "fun n f x -> f (n f x)"
let pred: FStar_Syntax_Syntax.term =
  FStar_Tests_Pars.pars
    "fun n f x -> n (fun g h -> h (g f)) (fun y -> x) (fun y -> y)"
let mul: FStar_Syntax_Syntax.term =
  FStar_Tests_Pars.pars "fun m n f -> m (n f)"
let rec encode: Prims.int -> FStar_Syntax_Syntax.term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then z
    else
      (let uu____7 =
         let uu____10 = encode (n1 - (Prims.parse_int "1")) in [uu____10] in
       FStar_Tests_Util.app succ uu____7)
let minus:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun m1  -> fun n1  -> FStar_Tests_Util.app n1 [pred; m1]
let let_:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun x1  ->
    fun e  ->
      fun e'  ->
        let uu____32 =
          let uu____35 = let uu____36 = b x1 in [uu____36] in
          FStar_Syntax_Util.abs uu____35 e' FStar_Pervasives_Native.None in
        FStar_Tests_Util.app uu____32 [e]
let mk_let:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun x1  ->
    fun e  ->
      fun e'  ->
        let e'1 =
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))] e' in
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
                   FStar_Syntax_Syntax.lbattrs = []
                 }]), e'1)) FStar_Pervasives_Native.None
          FStar_Range.dummyRange
let lid: Prims.string -> FStar_Ident.lident =
  fun x1  -> FStar_Ident.lid_of_path [x1] FStar_Range.dummyRange
let znat_l: FStar_Syntax_Syntax.fv =
  let uu____64 = lid "Z" in
  FStar_Syntax_Syntax.lid_as_fv uu____64 FStar_Syntax_Syntax.Delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
let snat_l: FStar_Syntax_Syntax.fv =
  let uu____65 = lid "S" in
  FStar_Syntax_Syntax.lid_as_fv uu____65 FStar_Syntax_Syntax.Delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
let tm_fv:
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun fv  ->
    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
      FStar_Pervasives_Native.None FStar_Range.dummyRange
let znat: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = tm_fv znat_l
let snat:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    let uu____78 =
      let uu____81 =
        let uu____82 =
          let uu____97 = tm_fv snat_l in
          let uu____100 =
            let uu____103 = FStar_Syntax_Syntax.as_arg s in [uu____103] in
          (uu____97, uu____100) in
        FStar_Syntax_Syntax.Tm_app uu____82 in
      FStar_Syntax_Syntax.mk uu____81 in
    uu____78 FStar_Pervasives_Native.None FStar_Range.dummyRange
let pat:
  'Auu____113 . 'Auu____113 -> 'Auu____113 FStar_Syntax_Syntax.withinfo_t =
  fun p  -> FStar_Syntax_Syntax.withinfo p FStar_Range.dummyRange
let mk_match:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun h1  ->
    fun branches  ->
      let branches1 =
        FStar_All.pipe_right branches
          (FStar_List.map FStar_Syntax_Util.branch) in
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (h1, branches1))
        FStar_Pervasives_Native.None FStar_Range.dummyRange
let pred_nat:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    let zbranch =
      let uu____171 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, [])) in
      (uu____171, FStar_Pervasives_Native.None, znat) in
    let sbranch =
      let uu____213 =
        let uu____216 =
          let uu____217 =
            let uu____230 =
              let uu____239 =
                let uu____246 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x) in
                (uu____246, false) in
              [uu____239] in
            (snat_l, uu____230) in
          FStar_Syntax_Syntax.Pat_cons uu____217 in
        pat uu____216 in
      let uu____271 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___77_276 = FStar_Tests_Util.x in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___77_276.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___77_276.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange in
      (uu____213, FStar_Pervasives_Native.None, uu____271) in
    mk_match s [zbranch; sbranch]
let minus_nat:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t1  ->
    fun t2  ->
      let minus1 = FStar_Tests_Util.m in
      let zbranch =
        let uu____351 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, [])) in
        let uu____368 = FStar_Tests_Util.nm FStar_Tests_Util.x in
        (uu____351, FStar_Pervasives_Native.None, uu____368) in
      let sbranch =
        let uu____392 =
          let uu____395 =
            let uu____396 =
              let uu____409 =
                let uu____418 =
                  let uu____425 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n) in
                  (uu____425, false) in
                [uu____418] in
              (snat_l, uu____409) in
            FStar_Syntax_Syntax.Pat_cons uu____396 in
          pat uu____395 in
        let uu____450 =
          let uu____453 = FStar_Tests_Util.nm minus1 in
          let uu____456 =
            let uu____459 =
              let uu____462 = FStar_Tests_Util.nm FStar_Tests_Util.x in
              pred_nat uu____462 in
            let uu____465 =
              let uu____470 = FStar_Tests_Util.nm FStar_Tests_Util.n in
              [uu____470] in
            uu____459 :: uu____465 in
          FStar_Tests_Util.app uu____453 uu____456 in
        (uu____392, FStar_Pervasives_Native.None, uu____450) in
      let lb =
        let uu____484 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange in
        let uu____485 =
          let uu____488 =
            let uu____489 =
              let uu____490 = b FStar_Tests_Util.x in
              let uu____491 =
                let uu____494 = b FStar_Tests_Util.y in [uu____494] in
              uu____490 :: uu____491 in
            let uu____495 =
              let uu____496 = FStar_Tests_Util.nm FStar_Tests_Util.y in
              mk_match uu____496 [zbranch; sbranch] in
            FStar_Syntax_Util.abs uu____489 uu____495
              FStar_Pervasives_Native.None in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____488 in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____484;
          FStar_Syntax_Syntax.lbdef = uu____485;
          FStar_Syntax_Syntax.lbattrs = []
        } in
      let uu____541 =
        let uu____544 =
          let uu____545 =
            let uu____558 =
              let uu____559 =
                let uu____560 = FStar_Tests_Util.nm minus1 in
                FStar_Tests_Util.app uu____560 [t1; t2] in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____559 in
            ((true, [lb]), uu____558) in
          FStar_Syntax_Syntax.Tm_let uu____545 in
        FStar_Syntax_Syntax.mk uu____544 in
      uu____541 FStar_Pervasives_Native.None FStar_Range.dummyRange
let encode_nat: Prims.int -> FStar_Syntax_Syntax.term =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____585 = snat out in
         aux uu____585 (n2 - (Prims.parse_int "1"))) in
    aux znat n1
let tests:
  (Prims.int,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple3 Prims.list
  =
  FStar_Tests_Pars.pars_and_tc_fragment
    "let rec copy (x:list int) : Tot (list int) = match x with | [] -> []  | hd::tl -> hd::copy tl";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let recons (x:list 'a) : Tot (list 'a) = match x with | [] -> []  | hd::tl -> hd::tl";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let rev (x:list 'a) : Tot (list 'a) = let rec aux (x:list 'a) (out:list 'a) : Tot (list 'a) = match x with | [] -> out | hd::tl -> aux tl (hd::out) in aux x []";
  FStar_Tests_Pars.pars_and_tc_fragment
    "type t = | A : int -> int -> t | B : int -> int -> t let f = function | A x y | B y x -> y - x";
  FStar_Tests_Pars.pars_and_tc_fragment "type tb = | T | F";
  FStar_Tests_Pars.pars_and_tc_fragment "type rb = | A1 | A2 | A3";
  FStar_Tests_Pars.pars_and_tc_fragment "type hb = | H : tb -> hb";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let select (i:tb) (x:'a) (y:'a) : Tot 'a = match i with | T -> x | F -> y";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let select_bool (b:bool) (x:'a) (y:'a) : Tot 'a = if b then x else y";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let select_hb (h:hb) : Tot tb = match h with | H t -> t";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let recons_m (x:list tb) = match x with | [] -> []  | hd::tl -> hd::tl";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let rec copy_tb_list_2 (x:list tb) : Tot (list tb) = match x with | [] -> []  | [hd] -> [hd]\n                                          | hd1::hd2::tl -> hd1::hd2::copy_tb_list_2 tl";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let rec copy_list_2 (x:list 'a) : Tot (list 'a) = match x with | [] -> []  | [hd] -> [hd]\n                                          | hd1::hd2::tl -> hd1::hd2::copy_list_2 tl";
  FStar_Tests_Pars.pars_and_tc_fragment "let idd (x: 'a) = x";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let revtb (x: tb) = match x with | T -> F | F -> T";
  FStar_Tests_Pars.pars_and_tc_fragment "let id_tb (x: tb) = x";
  FStar_Tests_Pars.pars_and_tc_fragment "let fst_a (x: 'a) (y: 'a) = x";
  FStar_Tests_Pars.pars_and_tc_fragment "let id_list (x: list 'a) = x";
  FStar_Tests_Pars.pars_and_tc_fragment "let id_list_m (x: list tb) = x";
  (let uu____615 =
     let uu____624 =
       let uu____627 =
         let uu____630 =
           let uu____633 =
             let uu____636 = FStar_Tests_Util.nm FStar_Tests_Util.n in
             [uu____636] in
           id :: uu____633 in
         one :: uu____630 in
       FStar_Tests_Util.app apply uu____627 in
     let uu____637 = FStar_Tests_Util.nm FStar_Tests_Util.n in
     ((Prims.parse_int "0"), uu____624, uu____637) in
   let uu____640 =
     let uu____651 =
       let uu____660 =
         let uu____663 =
           let uu____666 = FStar_Tests_Util.nm FStar_Tests_Util.x in
           [uu____666] in
         FStar_Tests_Util.app id uu____663 in
       let uu____667 = FStar_Tests_Util.nm FStar_Tests_Util.x in
       ((Prims.parse_int "1"), uu____660, uu____667) in
     let uu____670 =
       let uu____681 =
         let uu____690 =
           let uu____693 =
             let uu____696 =
               let uu____699 = FStar_Tests_Util.nm FStar_Tests_Util.n in
               let uu____700 =
                 let uu____703 = FStar_Tests_Util.nm FStar_Tests_Util.m in
                 [uu____703] in
               uu____699 :: uu____700 in
             tt :: uu____696 in
           FStar_Tests_Util.app apply uu____693 in
         let uu____704 = FStar_Tests_Util.nm FStar_Tests_Util.n in
         ((Prims.parse_int "1"), uu____690, uu____704) in
       let uu____707 =
         let uu____718 =
           let uu____727 =
             let uu____730 =
               let uu____733 =
                 let uu____736 = FStar_Tests_Util.nm FStar_Tests_Util.n in
                 let uu____737 =
                   let uu____740 = FStar_Tests_Util.nm FStar_Tests_Util.m in
                   [uu____740] in
                 uu____736 :: uu____737 in
               ff :: uu____733 in
             FStar_Tests_Util.app apply uu____730 in
           let uu____741 = FStar_Tests_Util.nm FStar_Tests_Util.m in
           ((Prims.parse_int "2"), uu____727, uu____741) in
         let uu____744 =
           let uu____755 =
             let uu____764 =
               let uu____767 =
                 let uu____770 =
                   let uu____773 =
                     let uu____776 =
                       let uu____779 =
                         let uu____782 =
                           let uu____785 =
                             let uu____788 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n in
                             let uu____789 =
                               let uu____792 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m in
                               [uu____792] in
                             uu____788 :: uu____789 in
                           ff :: uu____785 in
                         apply :: uu____782 in
                       apply :: uu____779 in
                     apply :: uu____776 in
                   apply :: uu____773 in
                 apply :: uu____770 in
               FStar_Tests_Util.app apply uu____767 in
             let uu____793 = FStar_Tests_Util.nm FStar_Tests_Util.m in
             ((Prims.parse_int "3"), uu____764, uu____793) in
           let uu____796 =
             let uu____807 =
               let uu____816 =
                 let uu____819 =
                   let uu____822 =
                     let uu____825 =
                       let uu____828 = FStar_Tests_Util.nm FStar_Tests_Util.n in
                       let uu____829 =
                         let uu____832 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m in
                         [uu____832] in
                       uu____828 :: uu____829 in
                     ff :: uu____825 in
                   apply :: uu____822 in
                 FStar_Tests_Util.app twice uu____819 in
               let uu____833 = FStar_Tests_Util.nm FStar_Tests_Util.m in
               ((Prims.parse_int "4"), uu____816, uu____833) in
             let uu____836 =
               let uu____847 =
                 let uu____856 = minus one z in
                 ((Prims.parse_int "5"), uu____856, one) in
               let uu____861 =
                 let uu____872 =
                   let uu____881 = FStar_Tests_Util.app pred [one] in
                   ((Prims.parse_int "6"), uu____881, z) in
                 let uu____886 =
                   let uu____897 =
                     let uu____906 = minus one one in
                     ((Prims.parse_int "7"), uu____906, z) in
                   let uu____911 =
                     let uu____922 =
                       let uu____931 = FStar_Tests_Util.app mul [one; one] in
                       ((Prims.parse_int "8"), uu____931, one) in
                     let uu____936 =
                       let uu____947 =
                         let uu____956 = FStar_Tests_Util.app mul [two; one] in
                         ((Prims.parse_int "9"), uu____956, two) in
                       let uu____961 =
                         let uu____972 =
                           let uu____981 =
                             let uu____984 =
                               let uu____987 =
                                 FStar_Tests_Util.app succ [one] in
                               [uu____987; one] in
                             FStar_Tests_Util.app mul uu____984 in
                           ((Prims.parse_int "10"), uu____981, two) in
                         let uu____994 =
                           let uu____1005 =
                             let uu____1014 =
                               let uu____1017 = encode (Prims.parse_int "10") in
                               let uu____1018 = encode (Prims.parse_int "10") in
                               minus uu____1017 uu____1018 in
                             ((Prims.parse_int "11"), uu____1014, z) in
                           let uu____1023 =
                             let uu____1034 =
                               let uu____1043 =
                                 let uu____1046 =
                                   encode (Prims.parse_int "100") in
                                 let uu____1047 =
                                   encode (Prims.parse_int "100") in
                                 minus uu____1046 uu____1047 in
                               ((Prims.parse_int "12"), uu____1043, z) in
                             let uu____1052 =
                               let uu____1063 =
                                 let uu____1070 =
                                   let uu____1071 =
                                     encode (Prims.parse_int "100") in
                                   let uu____1072 =
                                     let uu____1073 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x in
                                     let uu____1074 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x in
                                     minus uu____1073 uu____1074 in
                                   let_ FStar_Tests_Util.x uu____1071
                                     uu____1072 in
                                 ((Prims.parse_int "13"), uu____1070, z) in
                               let uu____1077 =
                                 let uu____1086 =
                                   let uu____1093 =
                                     let uu____1094 =
                                       FStar_Tests_Util.app succ [one] in
                                     let uu____1095 =
                                       let uu____1096 =
                                         let uu____1097 =
                                           let uu____1100 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x in
                                           let uu____1101 =
                                             let uu____1104 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x in
                                             [uu____1104] in
                                           uu____1100 :: uu____1101 in
                                         FStar_Tests_Util.app mul uu____1097 in
                                       let uu____1105 =
                                         let uu____1106 =
                                           let uu____1107 =
                                             let uu____1110 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y in
                                             let uu____1111 =
                                               let uu____1114 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y in
                                               [uu____1114] in
                                             uu____1110 :: uu____1111 in
                                           FStar_Tests_Util.app mul
                                             uu____1107 in
                                         let uu____1115 =
                                           let uu____1116 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h in
                                           let uu____1117 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h in
                                           minus uu____1116 uu____1117 in
                                         let_ FStar_Tests_Util.h uu____1106
                                           uu____1115 in
                                       let_ FStar_Tests_Util.y uu____1096
                                         uu____1105 in
                                     let_ FStar_Tests_Util.x uu____1094
                                       uu____1095 in
                                   ((Prims.parse_int "15"), uu____1093, z) in
                                 let uu____1120 =
                                   let uu____1129 =
                                     let uu____1136 =
                                       let uu____1137 =
                                         FStar_Tests_Util.app succ [one] in
                                       let uu____1140 =
                                         let uu____1141 =
                                           let uu____1144 =
                                             let uu____1147 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x in
                                             let uu____1148 =
                                               let uu____1151 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x in
                                               [uu____1151] in
                                             uu____1147 :: uu____1148 in
                                           FStar_Tests_Util.app mul
                                             uu____1144 in
                                         let uu____1152 =
                                           let uu____1153 =
                                             let uu____1156 =
                                               let uu____1159 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y in
                                               let uu____1160 =
                                                 let uu____1163 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y in
                                                 [uu____1163] in
                                               uu____1159 :: uu____1160 in
                                             FStar_Tests_Util.app mul
                                               uu____1156 in
                                           let uu____1164 =
                                             let uu____1165 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h in
                                             let uu____1166 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h in
                                             minus uu____1165 uu____1166 in
                                           mk_let FStar_Tests_Util.h
                                             uu____1153 uu____1164 in
                                         mk_let FStar_Tests_Util.y uu____1141
                                           uu____1152 in
                                       mk_let FStar_Tests_Util.x uu____1137
                                         uu____1140 in
                                     ((Prims.parse_int "16"), uu____1136, z) in
                                   let uu____1169 =
                                     let uu____1178 =
                                       let uu____1185 =
                                         let uu____1186 =
                                           FStar_Tests_Util.app succ [one] in
                                         let uu____1187 =
                                           let uu____1188 =
                                             let uu____1189 =
                                               let uu____1192 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x in
                                               let uu____1193 =
                                                 let uu____1196 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x in
                                                 [uu____1196] in
                                               uu____1192 :: uu____1193 in
                                             FStar_Tests_Util.app mul
                                               uu____1189 in
                                           let uu____1197 =
                                             let uu____1198 =
                                               let uu____1199 =
                                                 let uu____1202 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y in
                                                 let uu____1203 =
                                                   let uu____1206 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y in
                                                   [uu____1206] in
                                                 uu____1202 :: uu____1203 in
                                               FStar_Tests_Util.app mul
                                                 uu____1199 in
                                             let uu____1207 =
                                               let uu____1208 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h in
                                               let uu____1209 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h in
                                               minus uu____1208 uu____1209 in
                                             let_ FStar_Tests_Util.h
                                               uu____1198 uu____1207 in
                                           let_ FStar_Tests_Util.y uu____1188
                                             uu____1197 in
                                         let_ FStar_Tests_Util.x uu____1186
                                           uu____1187 in
                                       ((Prims.parse_int "17"), uu____1185,
                                         z) in
                                     let uu____1212 =
                                       let uu____1221 =
                                         let uu____1232 =
                                           let uu____1235 =
                                             let uu____1238 = snat znat in
                                             snat uu____1238 in
                                           pred_nat uu____1235 in
                                         let uu____1239 = snat znat in
                                         ((Prims.parse_int "18"), uu____1232,
                                           uu____1239) in
                                       let uu____1246 =
                                         let uu____1259 =
                                           let uu____1270 =
                                             let uu____1273 =
                                               let uu____1274 = snat znat in
                                               snat uu____1274 in
                                             let uu____1275 = snat znat in
                                             minus_nat uu____1273 uu____1275 in
                                           let uu____1276 = snat znat in
                                           ((Prims.parse_int "19"),
                                             uu____1270, uu____1276) in
                                         let uu____1283 =
                                           let uu____1296 =
                                             let uu____1307 =
                                               let uu____1310 =
                                                 encode_nat
                                                   (Prims.parse_int "10") in
                                               let uu____1311 =
                                                 encode_nat
                                                   (Prims.parse_int "10") in
                                               minus_nat uu____1310
                                                 uu____1311 in
                                             ((Prims.parse_int "20"),
                                               uu____1307, znat) in
                                           let uu____1316 =
                                             let uu____1329 =
                                               let uu____1340 =
                                                 let uu____1343 =
                                                   encode_nat
                                                     (Prims.parse_int "100") in
                                                 let uu____1344 =
                                                   encode_nat
                                                     (Prims.parse_int "100") in
                                                 minus_nat uu____1343
                                                   uu____1344 in
                                               ((Prims.parse_int "21"),
                                                 uu____1340, znat) in
                                             let uu____1349 =
                                               let uu____1362 =
                                                 let uu____1369 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]" in
                                                 let uu____1370 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]" in
                                                 ((Prims.parse_int "24"),
                                                   uu____1369, uu____1370) in
                                               let uu____1371 =
                                                 let uu____1380 =
                                                   let uu____1387 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]" in
                                                   let uu____1388 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]" in
                                                   ((Prims.parse_int "241"),
                                                     uu____1387, uu____1388) in
                                                 let uu____1389 =
                                                   let uu____1398 =
                                                     let uu____1405 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]" in
                                                     let uu____1406 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]" in
                                                     ((Prims.parse_int "25"),
                                                       uu____1405,
                                                       uu____1406) in
                                                   let uu____1407 =
                                                     let uu____1416 =
                                                       let uu____1423 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]" in
                                                       let uu____1424 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]" in
                                                       ((Prims.parse_int "26"),
                                                         uu____1423,
                                                         uu____1424) in
                                                     let uu____1425 =
                                                       let uu____1434 =
                                                         let uu____1441 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T" in
                                                         let uu____1442 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F" in
                                                         ((Prims.parse_int
                                                             "28"),
                                                           uu____1441,
                                                           uu____1442) in
                                                       let uu____1443 =
                                                         let uu____1452 =
                                                           let uu____1459 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]" in
                                                           let uu____1460 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]" in
                                                           ((Prims.parse_int
                                                               "29"),
                                                             uu____1459,
                                                             uu____1460) in
                                                         let uu____1461 =
                                                           let uu____1470 =
                                                             let uu____1477 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T" in
                                                             let uu____1478 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T" in
                                                             ((Prims.parse_int
                                                                 "31"),
                                                               uu____1477,
                                                               uu____1478) in
                                                           let uu____1479 =
                                                             let uu____1488 =
                                                               let uu____1495
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T" in
                                                               let uu____1496
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T" in
                                                               ((Prims.parse_int
                                                                   "32"),
                                                                 uu____1495,
                                                                 uu____1496) in
                                                             let uu____1497 =
                                                               let uu____1506
                                                                 =
                                                                 let uu____1513
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T" in
                                                                 let uu____1514
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F" in
                                                                 ((Prims.parse_int
                                                                    "33"),
                                                                   uu____1513,
                                                                   uu____1514) in
                                                               let uu____1515
                                                                 =
                                                                 let uu____1524
                                                                   =
                                                                   let uu____1531
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F" in
                                                                   let uu____1532
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T" in
                                                                   ((Prims.parse_int
                                                                    "34"),
                                                                    uu____1531,
                                                                    uu____1532) in
                                                                 let uu____1533
                                                                   =
                                                                   let uu____1542
                                                                    =
                                                                    let uu____1549
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F" in
                                                                    let uu____1550
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T" in
                                                                    ((Prims.parse_int
                                                                    "35"),
                                                                    uu____1549,
                                                                    uu____1550) in
                                                                   let uu____1551
                                                                    =
                                                                    let uu____1560
                                                                    =
                                                                    let uu____1567
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T" in
                                                                    let uu____1568
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T" in
                                                                    ((Prims.parse_int
                                                                    "36"),
                                                                    uu____1567,
                                                                    uu____1568) in
                                                                    let uu____1569
                                                                    =
                                                                    let uu____1578
                                                                    =
                                                                    let uu____1585
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]" in
                                                                    let uu____1586
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]" in
                                                                    ((Prims.parse_int
                                                                    "301"),
                                                                    uu____1585,
                                                                    uu____1586) in
                                                                    let uu____1587
                                                                    =
                                                                    let uu____1596
                                                                    =
                                                                    let uu____1603
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]" in
                                                                    let uu____1604
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]" in
                                                                    ((Prims.parse_int
                                                                    "3012"),
                                                                    uu____1603,
                                                                    uu____1604) in
                                                                    let uu____1605
                                                                    =
                                                                    let uu____1614
                                                                    =
                                                                    let uu____1621
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]" in
                                                                    let uu____1622
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]" in
                                                                    ((Prims.parse_int
                                                                    "302"),
                                                                    uu____1621,
                                                                    uu____1622) in
                                                                    let uu____1623
                                                                    =
                                                                    let uu____1632
                                                                    =
                                                                    let uu____1639
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3" in
                                                                    let uu____1640
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1" in
                                                                    ((Prims.parse_int
                                                                    "303"),
                                                                    uu____1639,
                                                                    uu____1640) in
                                                                    let uu____1641
                                                                    =
                                                                    let uu____1650
                                                                    =
                                                                    let uu____1657
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_hb (H F)" in
                                                                    let uu____1658
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "F" in
                                                                    ((Prims.parse_int
                                                                    "304"),
                                                                    uu____1657,
                                                                    uu____1658) in
                                                                    let uu____1659
                                                                    =
                                                                    let uu____1668
                                                                    =
                                                                    let uu____1675
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T" in
                                                                    let uu____1676
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T" in
                                                                    ((Prims.parse_int
                                                                    "305"),
                                                                    uu____1675,
                                                                    uu____1676) in
                                                                    let uu____1677
                                                                    =
                                                                    let uu____1686
                                                                    =
                                                                    let uu____1693
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]" in
                                                                    let uu____1694
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]" in
                                                                    ((Prims.parse_int
                                                                    "306"),
                                                                    uu____1693,
                                                                    uu____1694) in
                                                                    let uu____1695
                                                                    =
                                                                    let uu____1704
                                                                    =
                                                                    let uu____1711
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]" in
                                                                    let uu____1712
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]" in
                                                                    ((Prims.parse_int
                                                                    "307"),
                                                                    uu____1711,
                                                                    uu____1712) in
                                                                    let uu____1713
                                                                    =
                                                                    let uu____1722
                                                                    =
                                                                    let uu____1729
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]" in
                                                                    let uu____1730
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]" in
                                                                    ((Prims.parse_int
                                                                    "308"),
                                                                    uu____1729,
                                                                    uu____1730) in
                                                                    [uu____1722] in
                                                                    uu____1704
                                                                    ::
                                                                    uu____1713 in
                                                                    uu____1686
                                                                    ::
                                                                    uu____1695 in
                                                                    uu____1668
                                                                    ::
                                                                    uu____1677 in
                                                                    uu____1650
                                                                    ::
                                                                    uu____1659 in
                                                                    uu____1632
                                                                    ::
                                                                    uu____1641 in
                                                                    uu____1614
                                                                    ::
                                                                    uu____1623 in
                                                                    uu____1596
                                                                    ::
                                                                    uu____1605 in
                                                                    uu____1578
                                                                    ::
                                                                    uu____1587 in
                                                                    uu____1560
                                                                    ::
                                                                    uu____1569 in
                                                                   uu____1542
                                                                    ::
                                                                    uu____1551 in
                                                                 uu____1524
                                                                   ::
                                                                   uu____1533 in
                                                               uu____1506 ::
                                                                 uu____1515 in
                                                             uu____1488 ::
                                                               uu____1497 in
                                                           uu____1470 ::
                                                             uu____1479 in
                                                         uu____1452 ::
                                                           uu____1461 in
                                                       uu____1434 ::
                                                         uu____1443 in
                                                     uu____1416 :: uu____1425 in
                                                   uu____1398 :: uu____1407 in
                                                 uu____1380 :: uu____1389 in
                                               uu____1362 :: uu____1371 in
                                             uu____1329 :: uu____1349 in
                                           uu____1296 :: uu____1316 in
                                         uu____1259 :: uu____1283 in
                                       uu____1221 :: uu____1246 in
                                     uu____1178 :: uu____1212 in
                                   uu____1129 :: uu____1169 in
                                 uu____1086 :: uu____1120 in
                               uu____1063 :: uu____1077 in
                             uu____1034 :: uu____1052 in
                           uu____1005 :: uu____1023 in
                         uu____972 :: uu____994 in
                       uu____947 :: uu____961 in
                     uu____922 :: uu____936 in
                   uu____897 :: uu____911 in
                 uu____872 :: uu____886 in
               uu____847 :: uu____861 in
             uu____807 :: uu____836 in
           uu____755 :: uu____796 in
         uu____718 :: uu____744 in
       uu____681 :: uu____707 in
     uu____651 :: uu____670 in
   uu____615 :: uu____640)
let run_either:
  'Auu____2044 .
    Prims.int ->
      'Auu____2044 ->
        FStar_Syntax_Syntax.term ->
          (FStar_TypeChecker_Env.env ->
             'Auu____2044 -> FStar_Syntax_Syntax.term)
            -> Prims.unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____2072 = FStar_Util.string_of_int i in
           FStar_Util.print1 "%s: ... \n\n" uu____2072);
          (let tcenv = FStar_Tests_Pars.init () in
           (let uu____2075 = FStar_Main.process_args () in
            FStar_All.pipe_right uu____2075 FStar_Pervasives.ignore);
           (let x1 = normalizer tcenv r in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____2098 =
               let uu____2099 = FStar_Syntax_Util.unascribe x1 in
               FStar_Tests_Util.term_eq uu____2099 expected in
             FStar_Tests_Util.always i uu____2098)))
let run_interpreter:
  Prims.int ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        run_either i r expected
          (FStar_TypeChecker_Normalize.normalize
             [FStar_TypeChecker_Normalize.Beta;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.Primops])
let run_nbe:
  Prims.int ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        run_either i r expected FStar_TypeChecker_NBE.normalize
let run_interpreter_with_time:
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let interp uu____2134 = run_interpreter i r expected in
        let uu____2135 =
          let uu____2136 = FStar_Util.return_execution_time interp in
          FStar_Pervasives_Native.snd uu____2136 in
        (i, uu____2135)
let run_nbe_with_time:
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe uu____2157 = run_nbe i r expected in
        let uu____2158 =
          let uu____2159 = FStar_Util.return_execution_time nbe in
          FStar_Pervasives_Native.snd uu____2159 in
        (i, uu____2158)
let run_tests:
  'Auu____2166 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term -> 'Auu____2166)
      -> 'Auu____2166 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___76_2208  ->
            match uu___76_2208 with | (no,test,res) -> run1 no test res)
         tests in
     FStar_Options.__clear_unit_tests (); l)
let run_all_nbe: Prims.unit -> Prims.unit =
  fun uu____2227  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____2229 = run_tests run_nbe in FStar_Util.print_string "NBE ok\n")
let run_all_interpreter: Prims.unit -> Prims.unit =
  fun uu____2234  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____2236 = run_tests run_interpreter in
     FStar_Util.print_string "Normalizer ok\n")
let run_all_nbe_with_time:
  Prims.unit ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list
  =
  fun uu____2247  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time in
     FStar_Util.print_string "NBE ok\n"; l)
let run_all_interpreter_with_time:
  Prims.unit ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list
  =
  fun uu____2269  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let l = run_tests run_interpreter_with_time in
     FStar_Util.print_string "Normalizer ok\n"; l)
let run_both_with_time:
  Prims.int ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe uu____2295 = run_nbe i r expected in
        let norm1 uu____2299 = run_interpreter i r expected in
        FStar_Util.measure_execution_time "nbe" nbe;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
let compare: Prims.unit -> Prims.unit =
  fun uu____2305  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____2307 =
       let uu____2308 = encode (Prims.parse_int "1000") in
       let uu____2309 =
         let uu____2310 = FStar_Tests_Util.nm FStar_Tests_Util.x in
         let uu____2311 = FStar_Tests_Util.nm FStar_Tests_Util.x in
         minus uu____2310 uu____2311 in
       let_ FStar_Tests_Util.x uu____2308 uu____2309 in
     run_both_with_time (Prims.parse_int "14") uu____2307 z)
let compare_times:
  (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2 Prims.list
    ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.unit
  =
  fun l_int  ->
    fun l_nbe  ->
      FStar_Util.print_string "Comparing times for normalization and nbe\n";
      FStar_List.iter2
        (fun res1  ->
           fun res2  ->
             let uu____2372 = res1 in
             match uu____2372 with
             | (t1,time_int) ->
                 let uu____2379 = res2 in
                 (match uu____2379 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____2386 = FStar_Util.string_of_int t1 in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____2386 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
let run_all: Prims.unit -> Prims.unit =
  fun uu____2390  ->
    let l_int = run_all_interpreter_with_time () in
    let l_nbe = run_all_nbe_with_time () in compare_times l_int l_nbe