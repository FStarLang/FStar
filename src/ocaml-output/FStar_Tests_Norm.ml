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
                   FStar_Syntax_Syntax.lbdef = e
                 }]), e'1)) FStar_Pervasives_Native.None
          FStar_Range.dummyRange
let lid: Prims.string -> FStar_Ident.lident =
  fun x1  -> FStar_Ident.lid_of_path [x1] FStar_Range.dummyRange
let znat_l: FStar_Syntax_Syntax.fv =
  let uu____62 = lid "Z" in
  FStar_Syntax_Syntax.lid_as_fv uu____62 FStar_Syntax_Syntax.Delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
let snat_l: FStar_Syntax_Syntax.fv =
  let uu____63 = lid "S" in
  FStar_Syntax_Syntax.lid_as_fv uu____63 FStar_Syntax_Syntax.Delta_constant
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
    let uu____76 =
      let uu____79 =
        let uu____80 =
          let uu____95 = tm_fv snat_l in
          let uu____98 =
            let uu____101 = FStar_Syntax_Syntax.as_arg s in [uu____101] in
          (uu____95, uu____98) in
        FStar_Syntax_Syntax.Tm_app uu____80 in
      FStar_Syntax_Syntax.mk uu____79 in
    uu____76 FStar_Pervasives_Native.None FStar_Range.dummyRange
let pat:
  'Auu____111 . 'Auu____111 -> 'Auu____111 FStar_Syntax_Syntax.withinfo_t =
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
      let uu____169 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, [])) in
      (uu____169, FStar_Pervasives_Native.None, znat) in
    let sbranch =
      let uu____211 =
        let uu____214 =
          let uu____215 =
            let uu____228 =
              let uu____237 =
                let uu____244 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x) in
                (uu____244, false) in
              [uu____237] in
            (snat_l, uu____228) in
          FStar_Syntax_Syntax.Pat_cons uu____215 in
        pat uu____214 in
      let uu____269 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___616_274 = FStar_Tests_Util.x in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___616_274.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___616_274.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange in
      (uu____211, FStar_Pervasives_Native.None, uu____269) in
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
        let uu____349 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, [])) in
        let uu____366 = FStar_Tests_Util.nm FStar_Tests_Util.x in
        (uu____349, FStar_Pervasives_Native.None, uu____366) in
      let sbranch =
        let uu____390 =
          let uu____393 =
            let uu____394 =
              let uu____407 =
                let uu____416 =
                  let uu____423 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n) in
                  (uu____423, false) in
                [uu____416] in
              (snat_l, uu____407) in
            FStar_Syntax_Syntax.Pat_cons uu____394 in
          pat uu____393 in
        let uu____448 =
          let uu____451 = FStar_Tests_Util.nm minus1 in
          let uu____454 =
            let uu____457 =
              let uu____460 = FStar_Tests_Util.nm FStar_Tests_Util.x in
              pred_nat uu____460 in
            let uu____463 =
              let uu____468 = FStar_Tests_Util.nm FStar_Tests_Util.n in
              [uu____468] in
            uu____457 :: uu____463 in
          FStar_Tests_Util.app uu____451 uu____454 in
        (uu____390, FStar_Pervasives_Native.None, uu____448) in
      let lb =
        let uu____482 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange in
        let uu____483 =
          let uu____486 =
            let uu____487 =
              let uu____488 = b FStar_Tests_Util.x in
              let uu____489 =
                let uu____492 = b FStar_Tests_Util.y in [uu____492] in
              uu____488 :: uu____489 in
            let uu____493 =
              let uu____494 = FStar_Tests_Util.nm FStar_Tests_Util.y in
              mk_match uu____494 [zbranch; sbranch] in
            FStar_Syntax_Util.abs uu____487 uu____493
              FStar_Pervasives_Native.None in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____486 in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____482;
          FStar_Syntax_Syntax.lbdef = uu____483
        } in
      let uu____537 =
        let uu____540 =
          let uu____541 =
            let uu____554 =
              let uu____555 =
                let uu____556 = FStar_Tests_Util.nm minus1 in
                FStar_Tests_Util.app uu____556 [t1; t2] in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____555 in
            ((true, [lb]), uu____554) in
          FStar_Syntax_Syntax.Tm_let uu____541 in
        FStar_Syntax_Syntax.mk uu____540 in
      uu____537 FStar_Pervasives_Native.None FStar_Range.dummyRange
let encode_nat: Prims.int -> FStar_Syntax_Syntax.term =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____581 = snat out in
         aux uu____581 (n2 - (Prims.parse_int "1"))) in
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
  FStar_Tests_Pars.pars_and_tc_fragment "let idd (x: 'a) = x";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let revtb (x: tb) = match x with | T -> F | F -> T";
  FStar_Tests_Pars.pars_and_tc_fragment "let id_tb (x: tb) = x";
  FStar_Tests_Pars.pars_and_tc_fragment "let fst_a (x: 'a) (y: 'a) = x";
  FStar_Tests_Pars.pars_and_tc_fragment "let id_list (x: list 'a) = x";
  (let uu____602 =
     let uu____611 =
       let uu____614 =
         let uu____617 =
           let uu____620 =
             let uu____623 = FStar_Tests_Util.nm FStar_Tests_Util.n in
             [uu____623] in
           id :: uu____620 in
         one :: uu____617 in
       FStar_Tests_Util.app apply uu____614 in
     let uu____624 = FStar_Tests_Util.nm FStar_Tests_Util.n in
     ((Prims.parse_int "0"), uu____611, uu____624) in
   let uu____627 =
     let uu____638 =
       let uu____647 =
         let uu____650 =
           let uu____653 = FStar_Tests_Util.nm FStar_Tests_Util.x in
           [uu____653] in
         FStar_Tests_Util.app id uu____650 in
       let uu____654 = FStar_Tests_Util.nm FStar_Tests_Util.x in
       ((Prims.parse_int "1"), uu____647, uu____654) in
     let uu____657 =
       let uu____668 =
         let uu____677 =
           let uu____680 =
             let uu____683 =
               let uu____686 = FStar_Tests_Util.nm FStar_Tests_Util.n in
               let uu____687 =
                 let uu____690 = FStar_Tests_Util.nm FStar_Tests_Util.m in
                 [uu____690] in
               uu____686 :: uu____687 in
             tt :: uu____683 in
           FStar_Tests_Util.app apply uu____680 in
         let uu____691 = FStar_Tests_Util.nm FStar_Tests_Util.n in
         ((Prims.parse_int "1"), uu____677, uu____691) in
       let uu____694 =
         let uu____705 =
           let uu____714 =
             let uu____717 =
               let uu____720 =
                 let uu____723 = FStar_Tests_Util.nm FStar_Tests_Util.n in
                 let uu____724 =
                   let uu____727 = FStar_Tests_Util.nm FStar_Tests_Util.m in
                   [uu____727] in
                 uu____723 :: uu____724 in
               ff :: uu____720 in
             FStar_Tests_Util.app apply uu____717 in
           let uu____728 = FStar_Tests_Util.nm FStar_Tests_Util.m in
           ((Prims.parse_int "2"), uu____714, uu____728) in
         let uu____731 =
           let uu____742 =
             let uu____751 =
               let uu____754 =
                 let uu____757 =
                   let uu____760 =
                     let uu____763 =
                       let uu____766 =
                         let uu____769 =
                           let uu____772 =
                             let uu____775 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n in
                             let uu____776 =
                               let uu____779 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m in
                               [uu____779] in
                             uu____775 :: uu____776 in
                           ff :: uu____772 in
                         apply :: uu____769 in
                       apply :: uu____766 in
                     apply :: uu____763 in
                   apply :: uu____760 in
                 apply :: uu____757 in
               FStar_Tests_Util.app apply uu____754 in
             let uu____780 = FStar_Tests_Util.nm FStar_Tests_Util.m in
             ((Prims.parse_int "3"), uu____751, uu____780) in
           let uu____783 =
             let uu____794 =
               let uu____803 =
                 let uu____806 =
                   let uu____809 =
                     let uu____812 =
                       let uu____815 = FStar_Tests_Util.nm FStar_Tests_Util.n in
                       let uu____816 =
                         let uu____819 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m in
                         [uu____819] in
                       uu____815 :: uu____816 in
                     ff :: uu____812 in
                   apply :: uu____809 in
                 FStar_Tests_Util.app twice uu____806 in
               let uu____820 = FStar_Tests_Util.nm FStar_Tests_Util.m in
               ((Prims.parse_int "4"), uu____803, uu____820) in
             let uu____823 =
               let uu____834 =
                 let uu____843 = minus one z in
                 ((Prims.parse_int "5"), uu____843, one) in
               let uu____848 =
                 let uu____859 =
                   let uu____868 = FStar_Tests_Util.app pred [one] in
                   ((Prims.parse_int "6"), uu____868, z) in
                 let uu____873 =
                   let uu____884 =
                     let uu____893 = minus one one in
                     ((Prims.parse_int "7"), uu____893, z) in
                   let uu____898 =
                     let uu____909 =
                       let uu____918 = FStar_Tests_Util.app mul [one; one] in
                       ((Prims.parse_int "8"), uu____918, one) in
                     let uu____923 =
                       let uu____934 =
                         let uu____943 = FStar_Tests_Util.app mul [two; one] in
                         ((Prims.parse_int "9"), uu____943, two) in
                       let uu____948 =
                         let uu____959 =
                           let uu____968 =
                             let uu____971 =
                               let uu____974 =
                                 FStar_Tests_Util.app succ [one] in
                               [uu____974; one] in
                             FStar_Tests_Util.app mul uu____971 in
                           ((Prims.parse_int "10"), uu____968, two) in
                         let uu____981 =
                           let uu____992 =
                             let uu____1001 =
                               let uu____1004 = encode (Prims.parse_int "10") in
                               let uu____1005 = encode (Prims.parse_int "10") in
                               minus uu____1004 uu____1005 in
                             ((Prims.parse_int "11"), uu____1001, z) in
                           let uu____1010 =
                             let uu____1021 =
                               let uu____1030 =
                                 let uu____1033 =
                                   encode (Prims.parse_int "100") in
                                 let uu____1034 =
                                   encode (Prims.parse_int "100") in
                                 minus uu____1033 uu____1034 in
                               ((Prims.parse_int "12"), uu____1030, z) in
                             let uu____1039 =
                               let uu____1050 =
                                 let uu____1057 =
                                   let uu____1058 =
                                     encode (Prims.parse_int "100") in
                                   let uu____1059 =
                                     let uu____1060 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x in
                                     let uu____1061 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x in
                                     minus uu____1060 uu____1061 in
                                   let_ FStar_Tests_Util.x uu____1058
                                     uu____1059 in
                                 ((Prims.parse_int "13"), uu____1057, z) in
                               let uu____1064 =
                                 let uu____1073 =
                                   let uu____1080 =
                                     let uu____1081 =
                                       encode (Prims.parse_int "1000") in
                                     let uu____1082 =
                                       let uu____1083 =
                                         FStar_Tests_Util.nm
                                           FStar_Tests_Util.x in
                                       let uu____1084 =
                                         FStar_Tests_Util.nm
                                           FStar_Tests_Util.x in
                                       minus uu____1083 uu____1084 in
                                     let_ FStar_Tests_Util.x uu____1081
                                       uu____1082 in
                                   ((Prims.parse_int "14"), uu____1080, z) in
                                 let uu____1087 =
                                   let uu____1096 =
                                     let uu____1103 =
                                       let uu____1104 =
                                         FStar_Tests_Util.app succ [one] in
                                       let uu____1105 =
                                         let uu____1106 =
                                           let uu____1107 =
                                             let uu____1110 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x in
                                             let uu____1111 =
                                               let uu____1114 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x in
                                               [uu____1114] in
                                             uu____1110 :: uu____1111 in
                                           FStar_Tests_Util.app mul
                                             uu____1107 in
                                         let uu____1115 =
                                           let uu____1116 =
                                             let uu____1117 =
                                               let uu____1120 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y in
                                               let uu____1121 =
                                                 let uu____1124 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y in
                                                 [uu____1124] in
                                               uu____1120 :: uu____1121 in
                                             FStar_Tests_Util.app mul
                                               uu____1117 in
                                           let uu____1125 =
                                             let uu____1126 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h in
                                             let uu____1127 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h in
                                             minus uu____1126 uu____1127 in
                                           let_ FStar_Tests_Util.h uu____1116
                                             uu____1125 in
                                         let_ FStar_Tests_Util.y uu____1106
                                           uu____1115 in
                                       let_ FStar_Tests_Util.x uu____1104
                                         uu____1105 in
                                     ((Prims.parse_int "15"), uu____1103, z) in
                                   let uu____1130 =
                                     let uu____1139 =
                                       let uu____1146 =
                                         let uu____1147 =
                                           FStar_Tests_Util.app succ [one] in
                                         let uu____1150 =
                                           let uu____1151 =
                                             let uu____1154 =
                                               let uu____1157 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x in
                                               let uu____1158 =
                                                 let uu____1161 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x in
                                                 [uu____1161] in
                                               uu____1157 :: uu____1158 in
                                             FStar_Tests_Util.app mul
                                               uu____1154 in
                                           let uu____1162 =
                                             let uu____1163 =
                                               let uu____1166 =
                                                 let uu____1169 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y in
                                                 let uu____1170 =
                                                   let uu____1173 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y in
                                                   [uu____1173] in
                                                 uu____1169 :: uu____1170 in
                                               FStar_Tests_Util.app mul
                                                 uu____1166 in
                                             let uu____1174 =
                                               let uu____1175 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h in
                                               let uu____1176 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h in
                                               minus uu____1175 uu____1176 in
                                             mk_let FStar_Tests_Util.h
                                               uu____1163 uu____1174 in
                                           mk_let FStar_Tests_Util.y
                                             uu____1151 uu____1162 in
                                         mk_let FStar_Tests_Util.x uu____1147
                                           uu____1150 in
                                       ((Prims.parse_int "16"), uu____1146,
                                         z) in
                                     let uu____1179 =
                                       let uu____1188 =
                                         let uu____1195 =
                                           let uu____1196 =
                                             FStar_Tests_Util.app succ [one] in
                                           let uu____1197 =
                                             let uu____1198 =
                                               let uu____1199 =
                                                 let uu____1202 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x in
                                                 let uu____1203 =
                                                   let uu____1206 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.x in
                                                   [uu____1206] in
                                                 uu____1202 :: uu____1203 in
                                               FStar_Tests_Util.app mul
                                                 uu____1199 in
                                             let uu____1207 =
                                               let uu____1208 =
                                                 let uu____1209 =
                                                   let uu____1212 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y in
                                                   let uu____1213 =
                                                     let uu____1216 =
                                                       FStar_Tests_Util.nm
                                                         FStar_Tests_Util.y in
                                                     [uu____1216] in
                                                   uu____1212 :: uu____1213 in
                                                 FStar_Tests_Util.app mul
                                                   uu____1209 in
                                               let uu____1217 =
                                                 let uu____1218 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.h in
                                                 let uu____1219 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.h in
                                                 minus uu____1218 uu____1219 in
                                               let_ FStar_Tests_Util.h
                                                 uu____1208 uu____1217 in
                                             let_ FStar_Tests_Util.y
                                               uu____1198 uu____1207 in
                                           let_ FStar_Tests_Util.x uu____1196
                                             uu____1197 in
                                         ((Prims.parse_int "17"), uu____1195,
                                           z) in
                                       let uu____1222 =
                                         let uu____1231 =
                                           let uu____1242 =
                                             let uu____1245 =
                                               let uu____1248 = snat znat in
                                               snat uu____1248 in
                                             pred_nat uu____1245 in
                                           let uu____1249 = snat znat in
                                           ((Prims.parse_int "18"),
                                             uu____1242, uu____1249) in
                                         let uu____1256 =
                                           let uu____1269 =
                                             let uu____1280 =
                                               let uu____1283 =
                                                 let uu____1284 = snat znat in
                                                 snat uu____1284 in
                                               let uu____1285 = snat znat in
                                               minus_nat uu____1283
                                                 uu____1285 in
                                             let uu____1286 = snat znat in
                                             ((Prims.parse_int "19"),
                                               uu____1280, uu____1286) in
                                           let uu____1293 =
                                             let uu____1306 =
                                               let uu____1317 =
                                                 let uu____1320 =
                                                   encode_nat
                                                     (Prims.parse_int "10") in
                                                 let uu____1321 =
                                                   encode_nat
                                                     (Prims.parse_int "10") in
                                                 minus_nat uu____1320
                                                   uu____1321 in
                                               ((Prims.parse_int "20"),
                                                 uu____1317, znat) in
                                             let uu____1326 =
                                               let uu____1339 =
                                                 let uu____1350 =
                                                   let uu____1353 =
                                                     encode_nat
                                                       (Prims.parse_int "100") in
                                                   let uu____1354 =
                                                     encode_nat
                                                       (Prims.parse_int "100") in
                                                   minus_nat uu____1353
                                                     uu____1354 in
                                                 ((Prims.parse_int "21"),
                                                   uu____1350, znat) in
                                               let uu____1359 =
                                                 let uu____1372 =
                                                   let uu____1379 =
                                                     FStar_Tests_Pars.tc
                                                       "(fun x y z q -> z) T T F T" in
                                                   let uu____1380 =
                                                     FStar_Tests_Pars.tc "F" in
                                                   ((Prims.parse_int "28"),
                                                     uu____1379, uu____1380) in
                                                 let uu____1381 =
                                                   let uu____1390 =
                                                     let uu____1397 =
                                                       FStar_Tests_Pars.tc
                                                         "[T; F]" in
                                                     let uu____1398 =
                                                       FStar_Tests_Pars.tc
                                                         "[T; F]" in
                                                     ((Prims.parse_int "29"),
                                                       uu____1397,
                                                       uu____1398) in
                                                   let uu____1399 =
                                                     let uu____1408 =
                                                       let uu____1415 =
                                                         FStar_Tests_Pars.tc
                                                           "id_tb T" in
                                                       let uu____1416 =
                                                         FStar_Tests_Pars.tc
                                                           "T" in
                                                       ((Prims.parse_int "31"),
                                                         uu____1415,
                                                         uu____1416) in
                                                     let uu____1417 =
                                                       let uu____1426 =
                                                         let uu____1433 =
                                                           FStar_Tests_Pars.tc
                                                             "(fun #a x -> x) #tb T" in
                                                         let uu____1434 =
                                                           FStar_Tests_Pars.tc
                                                             "T" in
                                                         ((Prims.parse_int
                                                             "32"),
                                                           uu____1433,
                                                           uu____1434) in
                                                       let uu____1435 =
                                                         let uu____1444 =
                                                           let uu____1451 =
                                                             FStar_Tests_Pars.tc
                                                               "revtb T" in
                                                           let uu____1452 =
                                                             FStar_Tests_Pars.tc
                                                               "F" in
                                                           ((Prims.parse_int
                                                               "33"),
                                                             uu____1451,
                                                             uu____1452) in
                                                         let uu____1453 =
                                                           let uu____1462 =
                                                             let uu____1469 =
                                                               FStar_Tests_Pars.tc
                                                                 "(fun x y -> x) T F" in
                                                             let uu____1470 =
                                                               FStar_Tests_Pars.tc
                                                                 "T" in
                                                             ((Prims.parse_int
                                                                 "34"),
                                                               uu____1469,
                                                               uu____1470) in
                                                           let uu____1471 =
                                                             let uu____1480 =
                                                               let uu____1487
                                                                 =
                                                                 FStar_Tests_Pars.tc
                                                                   "fst_a T F" in
                                                               let uu____1488
                                                                 =
                                                                 FStar_Tests_Pars.tc
                                                                   "T" in
                                                               ((Prims.parse_int
                                                                   "35"),
                                                                 uu____1487,
                                                                 uu____1488) in
                                                             let uu____1489 =
                                                               let uu____1498
                                                                 =
                                                                 let uu____1505
                                                                   =
                                                                   FStar_Tests_Pars.tc
                                                                    "idd T" in
                                                                 let uu____1506
                                                                   =
                                                                   FStar_Tests_Pars.tc
                                                                    "T" in
                                                                 ((Prims.parse_int
                                                                    "36"),
                                                                   uu____1505,
                                                                   uu____1506) in
                                                               let uu____1507
                                                                 =
                                                                 let uu____1516
                                                                   =
                                                                   let uu____1523
                                                                    =
                                                                    FStar_Tests_Pars.tc
                                                                    "id_list [T; F]" in
                                                                   let uu____1524
                                                                    =
                                                                    FStar_Tests_Pars.tc
                                                                    "[T; F]" in
                                                                   ((Prims.parse_int
                                                                    "301"),
                                                                    uu____1523,
                                                                    uu____1524) in
                                                                 [uu____1516] in
                                                               uu____1498 ::
                                                                 uu____1507 in
                                                             uu____1480 ::
                                                               uu____1489 in
                                                           uu____1462 ::
                                                             uu____1471 in
                                                         uu____1444 ::
                                                           uu____1453 in
                                                       uu____1426 ::
                                                         uu____1435 in
                                                     uu____1408 :: uu____1417 in
                                                   uu____1390 :: uu____1399 in
                                                 uu____1372 :: uu____1381 in
                                               uu____1339 :: uu____1359 in
                                             uu____1306 :: uu____1326 in
                                           uu____1269 :: uu____1293 in
                                         uu____1231 :: uu____1256 in
                                       uu____1188 :: uu____1222 in
                                     uu____1139 :: uu____1179 in
                                   uu____1096 :: uu____1130 in
                                 uu____1073 :: uu____1087 in
                               uu____1050 :: uu____1064 in
                             uu____1021 :: uu____1039 in
                           uu____992 :: uu____1010 in
                         uu____959 :: uu____981 in
                       uu____934 :: uu____948 in
                     uu____909 :: uu____923 in
                   uu____884 :: uu____898 in
                 uu____859 :: uu____873 in
               uu____834 :: uu____848 in
             uu____794 :: uu____823 in
           uu____742 :: uu____783 in
         uu____705 :: uu____731 in
       uu____668 :: uu____694 in
     uu____638 :: uu____657 in
   uu____602 :: uu____627)
let run_either:
  'Auu____1772 .
    Prims.int ->
      'Auu____1772 ->
        FStar_Syntax_Syntax.term ->
          (FStar_TypeChecker_Env.env ->
             'Auu____1772 -> FStar_Syntax_Syntax.term)
            -> Prims.unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____1800 = FStar_Util.string_of_int i in
           FStar_Util.print1 "%s: ... \n" uu____1800);
          (let tcenv = FStar_Tests_Pars.init () in
           (let uu____1803 = FStar_Main.process_args () in
            FStar_All.pipe_right uu____1803 FStar_Pervasives.ignore);
           (let x1 = normalizer tcenv r in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____1826 =
               let uu____1827 = FStar_Syntax_Util.unascribe x1 in
               FStar_Tests_Util.term_eq uu____1827 expected in
             FStar_Tests_Util.always i uu____1826)))
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
        let interp uu____1862 = run_interpreter i r expected in
        let uu____1863 =
          let uu____1864 = FStar_Util.return_execution_time interp in
          FStar_Pervasives_Native.snd uu____1864 in
        (i, uu____1863)
let run_nbe_with_time:
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe uu____1885 = run_nbe i r expected in
        let uu____1886 =
          let uu____1887 = FStar_Util.return_execution_time nbe in
          FStar_Pervasives_Native.snd uu____1887 in
        (i, uu____1886)
let run_tests:
  'Auu____1894 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term -> 'Auu____1894)
      -> 'Auu____1894 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___615_1936  ->
            match uu___615_1936 with | (no,test,res) -> run1 no test res)
         tests in
     FStar_Options.__clear_unit_tests (); l)
let run_all_nbe: Prims.unit -> Prims.unit =
  fun uu____1955  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____1957 = run_tests run_nbe in FStar_Util.print_string "NBE ok\n")
let run_all_interpreter: Prims.unit -> Prims.unit =
  fun uu____1962  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____1964 = run_tests run_interpreter in
     FStar_Util.print_string "Normalizer ok\n")
let run_all_nbe_with_time:
  Prims.unit ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list
  =
  fun uu____1975  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time in
     FStar_Util.print_string "NBE ok\n"; l)
let run_all_interpreter_with_time:
  Prims.unit ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list
  =
  fun uu____1997  ->
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
        let nbe uu____2023 = run_nbe i r expected in
        let norm1 uu____2027 = run_interpreter i r expected in
        FStar_Util.measure_execution_time "nbe" nbe;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
let compare: Prims.unit -> Prims.unit =
  fun uu____2033  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____2035 =
       let uu____2036 = encode (Prims.parse_int "1000") in
       let uu____2037 =
         let uu____2038 = FStar_Tests_Util.nm FStar_Tests_Util.x in
         let uu____2039 = FStar_Tests_Util.nm FStar_Tests_Util.x in
         minus uu____2038 uu____2039 in
       let_ FStar_Tests_Util.x uu____2036 uu____2037 in
     run_both_with_time (Prims.parse_int "14") uu____2035 z)
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
             let uu____2100 = res1 in
             match uu____2100 with
             | (t1,time_int) ->
                 let uu____2107 = res2 in
                 (match uu____2107 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____2114 = FStar_Util.string_of_int t1 in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____2114 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
let run_all: Prims.unit -> Prims.unit =
  fun uu____2118  ->
    let l_int = run_all_interpreter_with_time () in
    let l_nbe = run_all_nbe_with_time () in compare_times l_int l_nbe