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
             (let uu___613_274 = FStar_Tests_Util.x in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___613_274.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___613_274.FStar_Syntax_Syntax.sort)
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
let run_either:
  'Auu____587 .
    Prims.int ->
      'Auu____587 ->
        FStar_Syntax_Syntax.term ->
          (FStar_TypeChecker_Env.env ->
             'Auu____587 -> FStar_Syntax_Syntax.term)
            -> Prims.unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____615 = FStar_Util.string_of_int i in
           FStar_Util.print1 "%s: ... \n" uu____615);
          (let tcenv = FStar_Tests_Pars.init () in
           (let uu____618 = FStar_Main.process_args () in
            FStar_All.pipe_right uu____618 FStar_Pervasives.ignore);
           (let x1 = normalizer tcenv r in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____641 =
               let uu____642 = FStar_Syntax_Util.unascribe x1 in
               FStar_Tests_Util.term_eq uu____642 expected in
             FStar_Tests_Util.always i uu____641)))
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
        run_either i r expected
          (fun _tcenv  -> FStar_TypeChecker_NBE.normalize)
let run_both_with_time:
  Prims.int ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe uu____675 = run_nbe i r expected in
        let norm1 uu____679 = run_interpreter i r expected in
        FStar_Util.measure_execution_time "nbe" nbe;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
let run_all_nbe: Prims.unit -> Prims.unit =
  fun uu____685  ->
    FStar_Util.print_string "Testing NBE\n";
    FStar_Options.__set_unit_tests ();
    (let run1 = run_nbe in
     (let uu____696 =
        let uu____697 =
          let uu____700 =
            let uu____703 =
              let uu____706 = FStar_Tests_Util.nm FStar_Tests_Util.n in
              [uu____706] in
            id :: uu____703 in
          one :: uu____700 in
        FStar_Tests_Util.app apply uu____697 in
      let uu____707 = FStar_Tests_Util.nm FStar_Tests_Util.n in
      run1 (Prims.parse_int "0") uu____696 uu____707);
     (let uu____709 =
        let uu____710 =
          let uu____713 =
            let uu____716 = FStar_Tests_Util.nm FStar_Tests_Util.n in
            let uu____717 =
              let uu____720 = FStar_Tests_Util.nm FStar_Tests_Util.m in
              [uu____720] in
            uu____716 :: uu____717 in
          tt :: uu____713 in
        FStar_Tests_Util.app apply uu____710 in
      let uu____721 = FStar_Tests_Util.nm FStar_Tests_Util.n in
      run1 (Prims.parse_int "1") uu____709 uu____721);
     (let uu____723 =
        let uu____724 =
          let uu____727 =
            let uu____730 = FStar_Tests_Util.nm FStar_Tests_Util.n in
            let uu____731 =
              let uu____734 = FStar_Tests_Util.nm FStar_Tests_Util.m in
              [uu____734] in
            uu____730 :: uu____731 in
          ff :: uu____727 in
        FStar_Tests_Util.app apply uu____724 in
      let uu____735 = FStar_Tests_Util.nm FStar_Tests_Util.m in
      run1 (Prims.parse_int "2") uu____723 uu____735);
     (let uu____737 =
        let uu____738 =
          let uu____741 =
            let uu____744 =
              let uu____747 =
                let uu____750 =
                  let uu____753 =
                    let uu____756 =
                      let uu____759 = FStar_Tests_Util.nm FStar_Tests_Util.n in
                      let uu____760 =
                        let uu____763 =
                          FStar_Tests_Util.nm FStar_Tests_Util.m in
                        [uu____763] in
                      uu____759 :: uu____760 in
                    ff :: uu____756 in
                  apply :: uu____753 in
                apply :: uu____750 in
              apply :: uu____747 in
            apply :: uu____744 in
          apply :: uu____741 in
        FStar_Tests_Util.app apply uu____738 in
      let uu____764 = FStar_Tests_Util.nm FStar_Tests_Util.m in
      run1 (Prims.parse_int "3") uu____737 uu____764);
     (let uu____766 =
        let uu____767 =
          let uu____770 =
            let uu____773 =
              let uu____776 = FStar_Tests_Util.nm FStar_Tests_Util.n in
              let uu____777 =
                let uu____780 = FStar_Tests_Util.nm FStar_Tests_Util.m in
                [uu____780] in
              uu____776 :: uu____777 in
            ff :: uu____773 in
          apply :: uu____770 in
        FStar_Tests_Util.app twice uu____767 in
      let uu____781 = FStar_Tests_Util.nm FStar_Tests_Util.m in
      run1 (Prims.parse_int "4") uu____766 uu____781);
     (let uu____783 = minus one z in run1 (Prims.parse_int "5") uu____783 one);
     (let uu____785 = FStar_Tests_Util.app pred [one] in
      run1 (Prims.parse_int "6") uu____785 z);
     (let uu____787 = minus one one in run1 (Prims.parse_int "7") uu____787 z);
     (let uu____789 = FStar_Tests_Util.app mul [one; one] in
      run1 (Prims.parse_int "8") uu____789 one);
     (let uu____791 = FStar_Tests_Util.app mul [two; one] in
      run1 (Prims.parse_int "9") uu____791 two);
     (let uu____793 =
        let uu____794 =
          let uu____797 = FStar_Tests_Util.app succ [one] in [uu____797; one] in
        FStar_Tests_Util.app mul uu____794 in
      run1 (Prims.parse_int "10") uu____793 two);
     (let uu____803 =
        let uu____804 = encode (Prims.parse_int "10") in
        let uu____805 = encode (Prims.parse_int "10") in
        minus uu____804 uu____805 in
      run1 (Prims.parse_int "11") uu____803 z);
     (let uu____809 =
        let uu____810 = encode (Prims.parse_int "100") in
        let uu____811 = encode (Prims.parse_int "100") in
        minus uu____810 uu____811 in
      run1 (Prims.parse_int "12") uu____809 z);
     (let uu____815 =
        let uu____816 = encode (Prims.parse_int "100") in
        let uu____817 =
          let uu____818 = FStar_Tests_Util.nm FStar_Tests_Util.x in
          let uu____819 = FStar_Tests_Util.nm FStar_Tests_Util.x in
          minus uu____818 uu____819 in
        let_ FStar_Tests_Util.x uu____816 uu____817 in
      run1 (Prims.parse_int "13") uu____815 z);
     (let uu____823 =
        let uu____824 = FStar_Tests_Util.app succ [one] in
        let uu____825 =
          let uu____826 =
            let uu____827 =
              let uu____830 = FStar_Tests_Util.nm FStar_Tests_Util.x in
              let uu____831 =
                let uu____834 = FStar_Tests_Util.nm FStar_Tests_Util.x in
                [uu____834] in
              uu____830 :: uu____831 in
            FStar_Tests_Util.app mul uu____827 in
          let uu____835 =
            let uu____836 =
              let uu____837 =
                let uu____840 = FStar_Tests_Util.nm FStar_Tests_Util.y in
                let uu____841 =
                  let uu____844 = FStar_Tests_Util.nm FStar_Tests_Util.y in
                  [uu____844] in
                uu____840 :: uu____841 in
              FStar_Tests_Util.app mul uu____837 in
            let uu____845 =
              let uu____846 = FStar_Tests_Util.nm FStar_Tests_Util.h in
              let uu____847 = FStar_Tests_Util.nm FStar_Tests_Util.h in
              minus uu____846 uu____847 in
            let_ FStar_Tests_Util.h uu____836 uu____845 in
          let_ FStar_Tests_Util.y uu____826 uu____835 in
        let_ FStar_Tests_Util.x uu____824 uu____825 in
      run1 (Prims.parse_int "15") uu____823 z);
     (let uu____851 =
        let uu____852 = FStar_Tests_Util.app succ [one] in
        let uu____855 =
          let uu____856 =
            let uu____859 =
              let uu____862 = FStar_Tests_Util.nm FStar_Tests_Util.x in
              let uu____863 =
                let uu____866 = FStar_Tests_Util.nm FStar_Tests_Util.x in
                [uu____866] in
              uu____862 :: uu____863 in
            FStar_Tests_Util.app mul uu____859 in
          let uu____867 =
            let uu____868 =
              let uu____871 =
                let uu____874 = FStar_Tests_Util.nm FStar_Tests_Util.y in
                let uu____875 =
                  let uu____878 = FStar_Tests_Util.nm FStar_Tests_Util.y in
                  [uu____878] in
                uu____874 :: uu____875 in
              FStar_Tests_Util.app mul uu____871 in
            let uu____879 =
              let uu____880 = FStar_Tests_Util.nm FStar_Tests_Util.h in
              let uu____881 = FStar_Tests_Util.nm FStar_Tests_Util.h in
              minus uu____880 uu____881 in
            mk_let FStar_Tests_Util.h uu____868 uu____879 in
          mk_let FStar_Tests_Util.y uu____856 uu____867 in
        mk_let FStar_Tests_Util.x uu____852 uu____855 in
      run1 (Prims.parse_int "16") uu____851 z);
     (let uu____885 =
        let uu____886 = FStar_Tests_Util.app succ [one] in
        let uu____887 =
          let uu____888 =
            let uu____889 =
              let uu____892 = FStar_Tests_Util.nm FStar_Tests_Util.x in
              let uu____893 =
                let uu____896 = FStar_Tests_Util.nm FStar_Tests_Util.x in
                [uu____896] in
              uu____892 :: uu____893 in
            FStar_Tests_Util.app mul uu____889 in
          let uu____897 =
            let uu____898 =
              let uu____899 =
                let uu____902 = FStar_Tests_Util.nm FStar_Tests_Util.y in
                let uu____903 =
                  let uu____906 = FStar_Tests_Util.nm FStar_Tests_Util.y in
                  [uu____906] in
                uu____902 :: uu____903 in
              FStar_Tests_Util.app mul uu____899 in
            let uu____907 =
              let uu____908 = FStar_Tests_Util.nm FStar_Tests_Util.h in
              let uu____909 = FStar_Tests_Util.nm FStar_Tests_Util.h in
              minus uu____908 uu____909 in
            let_ FStar_Tests_Util.h uu____898 uu____907 in
          let_ FStar_Tests_Util.y uu____888 uu____897 in
        let_ FStar_Tests_Util.x uu____886 uu____887 in
      run1 (Prims.parse_int "17") uu____885 z);
     (let uu____913 =
        let uu____914 = let uu____917 = snat znat in snat uu____917 in
        pred_nat uu____914 in
      let uu____918 = snat znat in
      run1 (Prims.parse_int "18") uu____913 uu____918);
     (let uu____920 =
        let uu____921 = let uu____922 = snat znat in snat uu____922 in
        let uu____923 = snat znat in minus_nat uu____921 uu____923 in
      let uu____924 = snat znat in
      run1 (Prims.parse_int "19") uu____920 uu____924);
     FStar_Options.__clear_unit_tests ();
     FStar_Util.print_string "NBE ok\n")
let run_all_interpreter: Prims.unit -> Prims.unit =
  fun uu____928  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let run1 = run_interpreter in
     FStar_Tests_Pars.pars_and_tc_fragment
       "let rec copy (x:list int) : Tot (list int) = match x with | [] -> []  | hd::tl -> hd::copy tl";
     FStar_Tests_Pars.pars_and_tc_fragment
       "let recons (x:list int) : Tot (list int) = match x with | [] -> []  | hd::tl -> hd::tl";
     FStar_Tests_Pars.pars_and_tc_fragment
       "let rev (x:list 'a) : Tot (list 'a) = let rec aux (x:list 'a) (out:list 'a) : Tot (list 'a) = match x with | [] -> out | hd::tl -> aux tl (hd::out) in aux x []";
     FStar_Tests_Pars.pars_and_tc_fragment
       "type t = | A : int -> int -> t | B : int -> int -> t let f = function | A x y | B y x -> y - x";
     FStar_Options.__set_unit_tests ();
     (let uu____943 =
        let uu____944 =
          let uu____947 =
            let uu____950 =
              let uu____953 = FStar_Tests_Util.nm FStar_Tests_Util.n in
              [uu____953] in
            id :: uu____950 in
          one :: uu____947 in
        FStar_Tests_Util.app apply uu____944 in
      let uu____954 = FStar_Tests_Util.nm FStar_Tests_Util.n in
      run1 (Prims.parse_int "0") uu____943 uu____954);
     (let uu____956 =
        let uu____957 =
          let uu____960 =
            let uu____963 = FStar_Tests_Util.nm FStar_Tests_Util.n in
            let uu____964 =
              let uu____967 = FStar_Tests_Util.nm FStar_Tests_Util.m in
              [uu____967] in
            uu____963 :: uu____964 in
          tt :: uu____960 in
        FStar_Tests_Util.app apply uu____957 in
      let uu____968 = FStar_Tests_Util.nm FStar_Tests_Util.n in
      run1 (Prims.parse_int "1") uu____956 uu____968);
     (let uu____970 =
        let uu____971 =
          let uu____974 =
            let uu____977 = FStar_Tests_Util.nm FStar_Tests_Util.n in
            let uu____978 =
              let uu____981 = FStar_Tests_Util.nm FStar_Tests_Util.m in
              [uu____981] in
            uu____977 :: uu____978 in
          ff :: uu____974 in
        FStar_Tests_Util.app apply uu____971 in
      let uu____982 = FStar_Tests_Util.nm FStar_Tests_Util.m in
      run1 (Prims.parse_int "2") uu____970 uu____982);
     (let uu____984 =
        let uu____985 =
          let uu____988 =
            let uu____991 =
              let uu____994 =
                let uu____997 =
                  let uu____1000 =
                    let uu____1003 =
                      let uu____1006 = FStar_Tests_Util.nm FStar_Tests_Util.n in
                      let uu____1007 =
                        let uu____1010 =
                          FStar_Tests_Util.nm FStar_Tests_Util.m in
                        [uu____1010] in
                      uu____1006 :: uu____1007 in
                    ff :: uu____1003 in
                  apply :: uu____1000 in
                apply :: uu____997 in
              apply :: uu____994 in
            apply :: uu____991 in
          apply :: uu____988 in
        FStar_Tests_Util.app apply uu____985 in
      let uu____1011 = FStar_Tests_Util.nm FStar_Tests_Util.m in
      run1 (Prims.parse_int "3") uu____984 uu____1011);
     (let uu____1013 =
        let uu____1014 =
          let uu____1017 =
            let uu____1020 =
              let uu____1023 = FStar_Tests_Util.nm FStar_Tests_Util.n in
              let uu____1024 =
                let uu____1027 = FStar_Tests_Util.nm FStar_Tests_Util.m in
                [uu____1027] in
              uu____1023 :: uu____1024 in
            ff :: uu____1020 in
          apply :: uu____1017 in
        FStar_Tests_Util.app twice uu____1014 in
      let uu____1028 = FStar_Tests_Util.nm FStar_Tests_Util.m in
      run1 (Prims.parse_int "4") uu____1013 uu____1028);
     (let uu____1030 = minus one z in
      run1 (Prims.parse_int "5") uu____1030 one);
     (let uu____1032 = FStar_Tests_Util.app pred [one] in
      run1 (Prims.parse_int "6") uu____1032 z);
     (let uu____1034 = minus one one in
      run1 (Prims.parse_int "7") uu____1034 z);
     (let uu____1036 = FStar_Tests_Util.app mul [one; one] in
      run1 (Prims.parse_int "8") uu____1036 one);
     (let uu____1038 = FStar_Tests_Util.app mul [two; one] in
      run1 (Prims.parse_int "9") uu____1038 two);
     (let uu____1040 =
        let uu____1041 =
          let uu____1044 = FStar_Tests_Util.app succ [one] in
          [uu____1044; one] in
        FStar_Tests_Util.app mul uu____1041 in
      run1 (Prims.parse_int "10") uu____1040 two);
     (let uu____1050 =
        let uu____1051 = encode (Prims.parse_int "10") in
        let uu____1052 = encode (Prims.parse_int "10") in
        minus uu____1051 uu____1052 in
      run1 (Prims.parse_int "11") uu____1050 z);
     (let uu____1056 =
        let uu____1057 = encode (Prims.parse_int "100") in
        let uu____1058 = encode (Prims.parse_int "100") in
        minus uu____1057 uu____1058 in
      run1 (Prims.parse_int "12") uu____1056 z);
     (let uu____1062 =
        let uu____1063 = encode (Prims.parse_int "100") in
        let uu____1064 =
          let uu____1065 = FStar_Tests_Util.nm FStar_Tests_Util.x in
          let uu____1066 = FStar_Tests_Util.nm FStar_Tests_Util.x in
          minus uu____1065 uu____1066 in
        let_ FStar_Tests_Util.x uu____1063 uu____1064 in
      run1 (Prims.parse_int "13") uu____1062 z);
     (let uu____1070 =
        let uu____1071 = FStar_Tests_Util.app succ [one] in
        let uu____1072 =
          let uu____1073 =
            let uu____1074 =
              let uu____1077 = FStar_Tests_Util.nm FStar_Tests_Util.x in
              let uu____1078 =
                let uu____1081 = FStar_Tests_Util.nm FStar_Tests_Util.x in
                [uu____1081] in
              uu____1077 :: uu____1078 in
            FStar_Tests_Util.app mul uu____1074 in
          let uu____1082 =
            let uu____1083 =
              let uu____1084 =
                let uu____1087 = FStar_Tests_Util.nm FStar_Tests_Util.y in
                let uu____1088 =
                  let uu____1091 = FStar_Tests_Util.nm FStar_Tests_Util.y in
                  [uu____1091] in
                uu____1087 :: uu____1088 in
              FStar_Tests_Util.app mul uu____1084 in
            let uu____1092 =
              let uu____1093 = FStar_Tests_Util.nm FStar_Tests_Util.h in
              let uu____1094 = FStar_Tests_Util.nm FStar_Tests_Util.h in
              minus uu____1093 uu____1094 in
            let_ FStar_Tests_Util.h uu____1083 uu____1092 in
          let_ FStar_Tests_Util.y uu____1073 uu____1082 in
        let_ FStar_Tests_Util.x uu____1071 uu____1072 in
      run1 (Prims.parse_int "14") uu____1070 z);
     (let uu____1098 =
        let uu____1099 = FStar_Tests_Util.app succ [one] in
        let uu____1102 =
          let uu____1103 =
            let uu____1106 =
              let uu____1109 = FStar_Tests_Util.nm FStar_Tests_Util.x in
              let uu____1110 =
                let uu____1113 = FStar_Tests_Util.nm FStar_Tests_Util.x in
                [uu____1113] in
              uu____1109 :: uu____1110 in
            FStar_Tests_Util.app mul uu____1106 in
          let uu____1114 =
            let uu____1115 =
              let uu____1118 =
                let uu____1121 = FStar_Tests_Util.nm FStar_Tests_Util.y in
                let uu____1122 =
                  let uu____1125 = FStar_Tests_Util.nm FStar_Tests_Util.y in
                  [uu____1125] in
                uu____1121 :: uu____1122 in
              FStar_Tests_Util.app mul uu____1118 in
            let uu____1126 =
              let uu____1127 = FStar_Tests_Util.nm FStar_Tests_Util.h in
              let uu____1128 = FStar_Tests_Util.nm FStar_Tests_Util.h in
              minus uu____1127 uu____1128 in
            mk_let FStar_Tests_Util.h uu____1115 uu____1126 in
          mk_let FStar_Tests_Util.y uu____1103 uu____1114 in
        mk_let FStar_Tests_Util.x uu____1099 uu____1102 in
      run1 (Prims.parse_int "15") uu____1098 z);
     (let uu____1132 =
        let uu____1133 = let uu____1136 = snat znat in snat uu____1136 in
        pred_nat uu____1133 in
      let uu____1137 = snat znat in
      run1 (Prims.parse_int "16") uu____1132 uu____1137);
     (let uu____1139 =
        let uu____1140 = let uu____1141 = snat znat in snat uu____1141 in
        let uu____1142 = snat znat in minus_nat uu____1140 uu____1142 in
      let uu____1143 = snat znat in
      run1 (Prims.parse_int "17") uu____1139 uu____1143);
     (let uu____1145 =
        let uu____1146 = encode_nat (Prims.parse_int "100") in
        let uu____1147 = encode_nat (Prims.parse_int "100") in
        minus_nat uu____1146 uu____1147 in
      run1 (Prims.parse_int "18") uu____1145 znat);
     (let uu____1149 =
        let uu____1150 = encode_nat (Prims.parse_int "10000") in
        let uu____1151 = encode_nat (Prims.parse_int "10000") in
        minus_nat uu____1150 uu____1151 in
      run1 (Prims.parse_int "19") uu____1149 znat);
     (let uu____1153 =
        let uu____1154 = encode_nat (Prims.parse_int "10") in
        let uu____1155 = encode_nat (Prims.parse_int "10") in
        minus_nat uu____1154 uu____1155 in
      run1 (Prims.parse_int "20") uu____1153 znat);
     FStar_Options.__clear_unit_tests ();
     (let uu____1158 = FStar_Tests_Pars.tc "recons [0;1]" in
      let uu____1159 = FStar_Tests_Pars.tc "[0;1]" in
      run1 (Prims.parse_int "21") uu____1158 uu____1159);
     (let uu____1161 = FStar_Tests_Pars.tc "copy [0;1]" in
      let uu____1162 = FStar_Tests_Pars.tc "[0;1]" in
      run1 (Prims.parse_int "22") uu____1161 uu____1162);
     (let uu____1164 = FStar_Tests_Pars.tc "rev [0;1;2;3;4;5;6;7;8;9;10]" in
      let uu____1165 = FStar_Tests_Pars.tc "[10;9;8;7;6;5;4;3;2;1;0]" in
      run1 (Prims.parse_int "23") uu____1164 uu____1165);
     (let uu____1167 = FStar_Tests_Pars.tc "f (B 5 3)" in
      let uu____1168 = FStar_Tests_Pars.tc "2" in
      run1 (Prims.parse_int "1062") uu____1167 uu____1168);
     FStar_Util.print_string "Normalizer ok\n")
let compare: Prims.unit -> Prims.unit =
  fun uu____1171  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____1173 =
       let uu____1174 = encode (Prims.parse_int "1000") in
       let uu____1175 =
         let uu____1176 = FStar_Tests_Util.nm FStar_Tests_Util.x in
         let uu____1177 = FStar_Tests_Util.nm FStar_Tests_Util.x in
         minus uu____1176 uu____1177 in
       let_ FStar_Tests_Util.x uu____1174 uu____1175 in
     run_both_with_time (Prims.parse_int "14") uu____1173 z)
let run_all: Prims.unit -> Prims.unit =
  fun uu____1182  -> run_all_nbe (); compare ()