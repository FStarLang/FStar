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
  (let uu____614 =
     let uu____623 =
       let uu____626 =
         let uu____629 =
           let uu____632 =
             let uu____635 = FStar_Tests_Util.nm FStar_Tests_Util.n in
             [uu____635] in
           id :: uu____632 in
         one :: uu____629 in
       FStar_Tests_Util.app apply uu____626 in
     let uu____636 = FStar_Tests_Util.nm FStar_Tests_Util.n in
     ((Prims.parse_int "0"), uu____623, uu____636) in
   let uu____639 =
     let uu____650 =
       let uu____659 =
         let uu____662 =
           let uu____665 = FStar_Tests_Util.nm FStar_Tests_Util.x in
           [uu____665] in
         FStar_Tests_Util.app id uu____662 in
       let uu____666 = FStar_Tests_Util.nm FStar_Tests_Util.x in
       ((Prims.parse_int "1"), uu____659, uu____666) in
     let uu____669 =
       let uu____680 =
         let uu____689 =
           let uu____692 =
             let uu____695 =
               let uu____698 = FStar_Tests_Util.nm FStar_Tests_Util.n in
               let uu____699 =
                 let uu____702 = FStar_Tests_Util.nm FStar_Tests_Util.m in
                 [uu____702] in
               uu____698 :: uu____699 in
             tt :: uu____695 in
           FStar_Tests_Util.app apply uu____692 in
         let uu____703 = FStar_Tests_Util.nm FStar_Tests_Util.n in
         ((Prims.parse_int "1"), uu____689, uu____703) in
       let uu____706 =
         let uu____717 =
           let uu____726 =
             let uu____729 =
               let uu____732 =
                 let uu____735 = FStar_Tests_Util.nm FStar_Tests_Util.n in
                 let uu____736 =
                   let uu____739 = FStar_Tests_Util.nm FStar_Tests_Util.m in
                   [uu____739] in
                 uu____735 :: uu____736 in
               ff :: uu____732 in
             FStar_Tests_Util.app apply uu____729 in
           let uu____740 = FStar_Tests_Util.nm FStar_Tests_Util.m in
           ((Prims.parse_int "2"), uu____726, uu____740) in
         let uu____743 =
           let uu____754 =
             let uu____763 =
               let uu____766 =
                 let uu____769 =
                   let uu____772 =
                     let uu____775 =
                       let uu____778 =
                         let uu____781 =
                           let uu____784 =
                             let uu____787 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n in
                             let uu____788 =
                               let uu____791 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m in
                               [uu____791] in
                             uu____787 :: uu____788 in
                           ff :: uu____784 in
                         apply :: uu____781 in
                       apply :: uu____778 in
                     apply :: uu____775 in
                   apply :: uu____772 in
                 apply :: uu____769 in
               FStar_Tests_Util.app apply uu____766 in
             let uu____792 = FStar_Tests_Util.nm FStar_Tests_Util.m in
             ((Prims.parse_int "3"), uu____763, uu____792) in
           let uu____795 =
             let uu____806 =
               let uu____815 =
                 let uu____818 =
                   let uu____821 =
                     let uu____824 =
                       let uu____827 = FStar_Tests_Util.nm FStar_Tests_Util.n in
                       let uu____828 =
                         let uu____831 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m in
                         [uu____831] in
                       uu____827 :: uu____828 in
                     ff :: uu____824 in
                   apply :: uu____821 in
                 FStar_Tests_Util.app twice uu____818 in
               let uu____832 = FStar_Tests_Util.nm FStar_Tests_Util.m in
               ((Prims.parse_int "4"), uu____815, uu____832) in
             let uu____835 =
               let uu____846 =
                 let uu____855 = minus one z in
                 ((Prims.parse_int "5"), uu____855, one) in
               let uu____860 =
                 let uu____871 =
                   let uu____880 = FStar_Tests_Util.app pred [one] in
                   ((Prims.parse_int "6"), uu____880, z) in
                 let uu____885 =
                   let uu____896 =
                     let uu____905 = minus one one in
                     ((Prims.parse_int "7"), uu____905, z) in
                   let uu____910 =
                     let uu____921 =
                       let uu____928 =
                         let uu____929 = FStar_Tests_Util.app succ [one] in
                         let uu____930 =
                           let uu____931 =
                             let uu____932 =
                               let uu____935 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.x in
                               let uu____936 =
                                 let uu____939 =
                                   FStar_Tests_Util.nm FStar_Tests_Util.x in
                                 [uu____939] in
                               uu____935 :: uu____936 in
                             FStar_Tests_Util.app mul uu____932 in
                           let uu____940 =
                             let uu____941 =
                               let uu____942 =
                                 let uu____945 =
                                   FStar_Tests_Util.nm FStar_Tests_Util.y in
                                 let uu____946 =
                                   let uu____949 =
                                     FStar_Tests_Util.nm FStar_Tests_Util.y in
                                   [uu____949] in
                                 uu____945 :: uu____946 in
                               FStar_Tests_Util.app mul uu____942 in
                             let uu____950 =
                               let uu____951 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.h in
                               let uu____952 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.h in
                               minus uu____951 uu____952 in
                             let_ FStar_Tests_Util.h uu____941 uu____950 in
                           let_ FStar_Tests_Util.y uu____931 uu____940 in
                         let_ FStar_Tests_Util.x uu____929 uu____930 in
                       ((Prims.parse_int "15"), uu____928, z) in
                     let uu____955 =
                       let uu____964 =
                         let uu____971 =
                           let uu____972 = FStar_Tests_Util.app succ [one] in
                           let uu____975 =
                             let uu____976 =
                               let uu____979 =
                                 let uu____982 =
                                   FStar_Tests_Util.nm FStar_Tests_Util.x in
                                 let uu____983 =
                                   let uu____986 =
                                     FStar_Tests_Util.nm FStar_Tests_Util.x in
                                   [uu____986] in
                                 uu____982 :: uu____983 in
                               FStar_Tests_Util.app mul uu____979 in
                             let uu____987 =
                               let uu____988 =
                                 let uu____991 =
                                   let uu____994 =
                                     FStar_Tests_Util.nm FStar_Tests_Util.y in
                                   let uu____995 =
                                     let uu____998 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.y in
                                     [uu____998] in
                                   uu____994 :: uu____995 in
                                 FStar_Tests_Util.app mul uu____991 in
                               let uu____999 =
                                 let uu____1000 =
                                   FStar_Tests_Util.nm FStar_Tests_Util.h in
                                 let uu____1001 =
                                   FStar_Tests_Util.nm FStar_Tests_Util.h in
                                 minus uu____1000 uu____1001 in
                               mk_let FStar_Tests_Util.h uu____988 uu____999 in
                             mk_let FStar_Tests_Util.y uu____976 uu____987 in
                           mk_let FStar_Tests_Util.x uu____972 uu____975 in
                         ((Prims.parse_int "16"), uu____971, z) in
                       let uu____1004 =
                         let uu____1013 =
                           let uu____1020 =
                             let uu____1021 = FStar_Tests_Util.app succ [one] in
                             let uu____1022 =
                               let uu____1023 =
                                 let uu____1024 =
                                   let uu____1027 =
                                     FStar_Tests_Util.nm FStar_Tests_Util.x in
                                   let uu____1028 =
                                     let uu____1031 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x in
                                     [uu____1031] in
                                   uu____1027 :: uu____1028 in
                                 FStar_Tests_Util.app mul uu____1024 in
                               let uu____1032 =
                                 let uu____1033 =
                                   let uu____1034 =
                                     let uu____1037 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.y in
                                     let uu____1038 =
                                       let uu____1041 =
                                         FStar_Tests_Util.nm
                                           FStar_Tests_Util.y in
                                       [uu____1041] in
                                     uu____1037 :: uu____1038 in
                                   FStar_Tests_Util.app mul uu____1034 in
                                 let uu____1042 =
                                   let uu____1043 =
                                     FStar_Tests_Util.nm FStar_Tests_Util.h in
                                   let uu____1044 =
                                     FStar_Tests_Util.nm FStar_Tests_Util.h in
                                   minus uu____1043 uu____1044 in
                                 let_ FStar_Tests_Util.h uu____1033
                                   uu____1042 in
                               let_ FStar_Tests_Util.y uu____1023 uu____1032 in
                             let_ FStar_Tests_Util.x uu____1021 uu____1022 in
                           ((Prims.parse_int "17"), uu____1020, z) in
                         let uu____1047 =
                           let uu____1056 =
                             let uu____1063 =
                               FStar_Tests_Pars.tc_nbe "recons_m [T; F]" in
                             let uu____1064 =
                               FStar_Tests_Pars.tc_nbe "[T; F]" in
                             ((Prims.parse_int "302"), uu____1063,
                               uu____1064) in
                           let uu____1065 =
                             let uu____1074 =
                               let uu____1081 =
                                 FStar_Tests_Pars.tc_nbe "select T A1 A3" in
                               let uu____1082 = FStar_Tests_Pars.tc_nbe "A1" in
                               ((Prims.parse_int "303"), uu____1081,
                                 uu____1082) in
                             let uu____1083 =
                               let uu____1092 =
                                 let uu____1099 =
                                   FStar_Tests_Pars.tc_nbe "select_hb (H F)" in
                                 let uu____1100 = FStar_Tests_Pars.tc_nbe "F" in
                                 ((Prims.parse_int "304"), uu____1099,
                                   uu____1100) in
                               let uu____1101 =
                                 let uu____1110 =
                                   let uu____1117 =
                                     FStar_Tests_Pars.tc_nbe "idd T" in
                                   let uu____1118 =
                                     FStar_Tests_Pars.tc_nbe "T" in
                                   ((Prims.parse_int "305"), uu____1117,
                                     uu____1118) in
                                 let uu____1119 =
                                   let uu____1128 =
                                     let uu____1135 =
                                       FStar_Tests_Pars.tc_nbe "recons [T]" in
                                     let uu____1136 =
                                       FStar_Tests_Pars.tc_nbe "[T]" in
                                     ((Prims.parse_int "306"), uu____1135,
                                       uu____1136) in
                                   let uu____1137 =
                                     let uu____1146 =
                                       let uu____1153 =
                                         FStar_Tests_Pars.tc_nbe
                                           "copy_tb_list_2 [T;F;T;F;T;F;F]" in
                                       let uu____1154 =
                                         FStar_Tests_Pars.tc_nbe
                                           "[T;F;T;F;T;F;F]" in
                                       ((Prims.parse_int "307"), uu____1153,
                                         uu____1154) in
                                     let uu____1155 =
                                       let uu____1164 =
                                         let uu____1171 =
                                           FStar_Tests_Pars.tc_nbe
                                             "copy_list_2    [T;F;T;F;T;F;F]" in
                                         let uu____1172 =
                                           FStar_Tests_Pars.tc_nbe
                                             "[T;F;T;F;T;F;F]" in
                                         ((Prims.parse_int "308"),
                                           uu____1171, uu____1172) in
                                       [uu____1164] in
                                     uu____1146 :: uu____1155 in
                                   uu____1128 :: uu____1137 in
                                 uu____1110 :: uu____1119 in
                               uu____1092 :: uu____1101 in
                             uu____1074 :: uu____1083 in
                           uu____1056 :: uu____1065 in
                         uu____1013 :: uu____1047 in
                       uu____964 :: uu____1004 in
                     uu____921 :: uu____955 in
                   uu____896 :: uu____910 in
                 uu____871 :: uu____885 in
               uu____846 :: uu____860 in
             uu____806 :: uu____835 in
           uu____754 :: uu____795 in
         uu____717 :: uu____743 in
       uu____680 :: uu____706 in
     uu____650 :: uu____669 in
   uu____614 :: uu____639)
let run_either:
  'Auu____1316 .
    Prims.int ->
      'Auu____1316 ->
        FStar_Syntax_Syntax.term ->
          (FStar_TypeChecker_Env.env ->
             'Auu____1316 -> FStar_Syntax_Syntax.term)
            -> Prims.unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____1344 = FStar_Util.string_of_int i in
           FStar_Util.print1 "%s: ... \n\n" uu____1344);
          (let tcenv = FStar_Tests_Pars.init () in
           (let uu____1347 = FStar_Main.process_args () in
            FStar_All.pipe_right uu____1347 FStar_Pervasives.ignore);
           (let x1 = normalizer tcenv r in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____1370 =
               let uu____1371 = FStar_Syntax_Util.unascribe x1 in
               FStar_Tests_Util.term_eq uu____1371 expected in
             FStar_Tests_Util.always i uu____1370)))
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
        let interp uu____1406 = run_interpreter i r expected in
        let uu____1407 =
          let uu____1408 = FStar_Util.return_execution_time interp in
          FStar_Pervasives_Native.snd uu____1408 in
        (i, uu____1407)
let run_nbe_with_time:
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe uu____1429 = run_nbe i r expected in
        let uu____1430 =
          let uu____1431 = FStar_Util.return_execution_time nbe in
          FStar_Pervasives_Native.snd uu____1431 in
        (i, uu____1430)
let run_tests:
  'Auu____1438 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term -> 'Auu____1438)
      -> 'Auu____1438 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___76_1480  ->
            match uu___76_1480 with | (no,test,res) -> run1 no test res)
         tests in
     FStar_Options.__clear_unit_tests (); l)
let run_all_nbe: Prims.unit -> Prims.unit =
  fun uu____1499  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____1501 = run_tests run_nbe in FStar_Util.print_string "NBE ok\n")
let run_all_interpreter: Prims.unit -> Prims.unit =
  fun uu____1506  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____1508 = run_tests run_interpreter in
     FStar_Util.print_string "Normalizer ok\n")
let run_all_nbe_with_time:
  Prims.unit ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list
  =
  fun uu____1519  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time in
     FStar_Util.print_string "NBE ok\n"; l)
let run_all_interpreter_with_time:
  Prims.unit ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list
  =
  fun uu____1541  ->
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
        let nbe uu____1567 = run_nbe i r expected in
        let norm1 uu____1571 = run_interpreter i r expected in
        FStar_Util.measure_execution_time "nbe" nbe;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
let compare: Prims.unit -> Prims.unit =
  fun uu____1577  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____1579 =
       let uu____1580 = encode (Prims.parse_int "1000") in
       let uu____1581 =
         let uu____1582 = FStar_Tests_Util.nm FStar_Tests_Util.x in
         let uu____1583 = FStar_Tests_Util.nm FStar_Tests_Util.x in
         minus uu____1582 uu____1583 in
       let_ FStar_Tests_Util.x uu____1580 uu____1581 in
     run_both_with_time (Prims.parse_int "14") uu____1579 z)
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
             let uu____1644 = res1 in
             match uu____1644 with
             | (t1,time_int) ->
                 let uu____1651 = res2 in
                 (match uu____1651 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____1658 = FStar_Util.string_of_int t1 in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____1658 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
let run_all: Prims.unit -> Prims.unit =
  fun uu____1662  ->
    let l_int = run_all_interpreter_with_time () in
    let l_nbe = run_all_nbe_with_time () in compare_times l_int l_nbe