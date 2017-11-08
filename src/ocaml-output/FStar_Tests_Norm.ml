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
let run:
  Prims.int ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        (let uu____592 = FStar_Util.string_of_int i in
         FStar_Util.print1 "%s: ... \n" uu____592);
        (let tcenv = FStar_Tests_Pars.init () in
         (let uu____595 = FStar_Main.process_args () in
          FStar_All.pipe_right uu____595 FStar_Pervasives.ignore);
         (let x1 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.Beta;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant;
              FStar_TypeChecker_Normalize.Primops] tcenv r in
          FStar_Options.init ();
          FStar_Options.set_option "print_universes"
            (FStar_Options.Bool true);
          FStar_Options.set_option "print_implicits"
            (FStar_Options.Bool true);
          (let uu____618 =
             let uu____619 = FStar_Syntax_Util.unascribe x1 in
             FStar_Tests_Util.term_eq uu____619 expected in
           FStar_Tests_Util.always i uu____618)))
let run_all: Prims.unit -> Prims.unit =
  fun uu____622  ->
    FStar_Util.print_string "Testing the normalizer\n";
    FStar_Tests_Pars.pars_and_tc_fragment
      "let rec copy (x:list int) : Tot (list int) = match x with | [] -> []  | hd::tl -> hd::copy tl";
    FStar_Tests_Pars.pars_and_tc_fragment
      "let recons (x:list int) : Tot (list int) = match x with | [] -> []  | hd::tl -> hd::tl";
    FStar_Tests_Pars.pars_and_tc_fragment
      "let rev (x:list 'a) : Tot (list 'a) = let rec aux (x:list 'a) (out:list 'a) : Tot (list 'a) = match x with | [] -> out | hd::tl -> aux tl (hd::out) in aux x []";
    FStar_Tests_Pars.pars_and_tc_fragment
      "type t = | A : int -> int -> t | B : int -> int -> t let f = function | A x y | B y x -> y - x";
    FStar_Options.__set_unit_tests ();
    (let uu____630 =
       let uu____631 =
         let uu____634 =
           let uu____637 =
             let uu____640 = FStar_Tests_Util.nm FStar_Tests_Util.n in
             [uu____640] in
           id :: uu____637 in
         one :: uu____634 in
       FStar_Tests_Util.app apply uu____631 in
     let uu____641 = FStar_Tests_Util.nm FStar_Tests_Util.n in
     run (Prims.parse_int "0") uu____630 uu____641);
    (let uu____643 =
       let uu____644 =
         let uu____647 =
           let uu____650 = FStar_Tests_Util.nm FStar_Tests_Util.n in
           let uu____651 =
             let uu____654 = FStar_Tests_Util.nm FStar_Tests_Util.m in
             [uu____654] in
           uu____650 :: uu____651 in
         tt :: uu____647 in
       FStar_Tests_Util.app apply uu____644 in
     let uu____655 = FStar_Tests_Util.nm FStar_Tests_Util.n in
     run (Prims.parse_int "1") uu____643 uu____655);
    (let uu____657 =
       let uu____658 =
         let uu____661 =
           let uu____664 = FStar_Tests_Util.nm FStar_Tests_Util.n in
           let uu____665 =
             let uu____668 = FStar_Tests_Util.nm FStar_Tests_Util.m in
             [uu____668] in
           uu____664 :: uu____665 in
         ff :: uu____661 in
       FStar_Tests_Util.app apply uu____658 in
     let uu____669 = FStar_Tests_Util.nm FStar_Tests_Util.m in
     run (Prims.parse_int "2") uu____657 uu____669);
    (let uu____671 =
       let uu____672 =
         let uu____675 =
           let uu____678 =
             let uu____681 =
               let uu____684 =
                 let uu____687 =
                   let uu____690 =
                     let uu____693 = FStar_Tests_Util.nm FStar_Tests_Util.n in
                     let uu____694 =
                       let uu____697 = FStar_Tests_Util.nm FStar_Tests_Util.m in
                       [uu____697] in
                     uu____693 :: uu____694 in
                   ff :: uu____690 in
                 apply :: uu____687 in
               apply :: uu____684 in
             apply :: uu____681 in
           apply :: uu____678 in
         apply :: uu____675 in
       FStar_Tests_Util.app apply uu____672 in
     let uu____698 = FStar_Tests_Util.nm FStar_Tests_Util.m in
     run (Prims.parse_int "3") uu____671 uu____698);
    (let uu____700 =
       let uu____701 =
         let uu____704 =
           let uu____707 =
             let uu____710 = FStar_Tests_Util.nm FStar_Tests_Util.n in
             let uu____711 =
               let uu____714 = FStar_Tests_Util.nm FStar_Tests_Util.m in
               [uu____714] in
             uu____710 :: uu____711 in
           ff :: uu____707 in
         apply :: uu____704 in
       FStar_Tests_Util.app twice uu____701 in
     let uu____715 = FStar_Tests_Util.nm FStar_Tests_Util.m in
     run (Prims.parse_int "4") uu____700 uu____715);
    (let uu____717 = minus one z in run (Prims.parse_int "5") uu____717 one);
    (let uu____719 = FStar_Tests_Util.app pred [one] in
     run (Prims.parse_int "6") uu____719 z);
    (let uu____721 = minus one one in run (Prims.parse_int "7") uu____721 z);
    (let uu____723 = FStar_Tests_Util.app mul [one; one] in
     run (Prims.parse_int "8") uu____723 one);
    (let uu____725 = FStar_Tests_Util.app mul [two; one] in
     run (Prims.parse_int "9") uu____725 two);
    (let uu____727 =
       let uu____728 =
         let uu____731 = FStar_Tests_Util.app succ [one] in [uu____731; one] in
       FStar_Tests_Util.app mul uu____728 in
     run (Prims.parse_int "10") uu____727 two);
    (let uu____737 =
       let uu____738 = encode (Prims.parse_int "10") in
       let uu____739 = encode (Prims.parse_int "10") in
       minus uu____738 uu____739 in
     run (Prims.parse_int "11") uu____737 z);
    (let uu____743 =
       let uu____744 = encode (Prims.parse_int "100") in
       let uu____745 = encode (Prims.parse_int "100") in
       minus uu____744 uu____745 in
     run (Prims.parse_int "12") uu____743 z);
    (let uu____749 =
       let uu____750 = encode (Prims.parse_int "100") in
       let uu____751 =
         let uu____752 = FStar_Tests_Util.nm FStar_Tests_Util.x in
         let uu____753 = FStar_Tests_Util.nm FStar_Tests_Util.x in
         minus uu____752 uu____753 in
       let_ FStar_Tests_Util.x uu____750 uu____751 in
     run (Prims.parse_int "13") uu____749 z);
    (let uu____757 =
       let uu____758 = FStar_Tests_Util.app succ [one] in
       let uu____759 =
         let uu____760 =
           let uu____761 =
             let uu____764 = FStar_Tests_Util.nm FStar_Tests_Util.x in
             let uu____765 =
               let uu____768 = FStar_Tests_Util.nm FStar_Tests_Util.x in
               [uu____768] in
             uu____764 :: uu____765 in
           FStar_Tests_Util.app mul uu____761 in
         let uu____769 =
           let uu____770 =
             let uu____771 =
               let uu____774 = FStar_Tests_Util.nm FStar_Tests_Util.y in
               let uu____775 =
                 let uu____778 = FStar_Tests_Util.nm FStar_Tests_Util.y in
                 [uu____778] in
               uu____774 :: uu____775 in
             FStar_Tests_Util.app mul uu____771 in
           let uu____779 =
             let uu____780 = FStar_Tests_Util.nm FStar_Tests_Util.h in
             let uu____781 = FStar_Tests_Util.nm FStar_Tests_Util.h in
             minus uu____780 uu____781 in
           let_ FStar_Tests_Util.h uu____770 uu____779 in
         let_ FStar_Tests_Util.y uu____760 uu____769 in
       let_ FStar_Tests_Util.x uu____758 uu____759 in
     run (Prims.parse_int "14") uu____757 z);
    (let uu____785 =
       let uu____786 = FStar_Tests_Util.app succ [one] in
       let uu____789 =
         let uu____790 =
           let uu____793 =
             let uu____796 = FStar_Tests_Util.nm FStar_Tests_Util.x in
             let uu____797 =
               let uu____800 = FStar_Tests_Util.nm FStar_Tests_Util.x in
               [uu____800] in
             uu____796 :: uu____797 in
           FStar_Tests_Util.app mul uu____793 in
         let uu____801 =
           let uu____802 =
             let uu____805 =
               let uu____808 = FStar_Tests_Util.nm FStar_Tests_Util.y in
               let uu____809 =
                 let uu____812 = FStar_Tests_Util.nm FStar_Tests_Util.y in
                 [uu____812] in
               uu____808 :: uu____809 in
             FStar_Tests_Util.app mul uu____805 in
           let uu____813 =
             let uu____814 = FStar_Tests_Util.nm FStar_Tests_Util.h in
             let uu____815 = FStar_Tests_Util.nm FStar_Tests_Util.h in
             minus uu____814 uu____815 in
           mk_let FStar_Tests_Util.h uu____802 uu____813 in
         mk_let FStar_Tests_Util.y uu____790 uu____801 in
       mk_let FStar_Tests_Util.x uu____786 uu____789 in
     run (Prims.parse_int "15") uu____785 z);
    (let uu____819 =
       let uu____820 = let uu____823 = snat znat in snat uu____823 in
       pred_nat uu____820 in
     let uu____824 = snat znat in
     run (Prims.parse_int "16") uu____819 uu____824);
    (let uu____826 =
       let uu____827 = let uu____828 = snat znat in snat uu____828 in
       let uu____829 = snat znat in minus_nat uu____827 uu____829 in
     let uu____830 = snat znat in
     run (Prims.parse_int "17") uu____826 uu____830);
    (let uu____832 =
       let uu____833 = encode_nat (Prims.parse_int "100") in
       let uu____834 = encode_nat (Prims.parse_int "100") in
       minus_nat uu____833 uu____834 in
     run (Prims.parse_int "18") uu____832 znat);
    (let uu____836 =
       let uu____837 = encode_nat (Prims.parse_int "10000") in
       let uu____838 = encode_nat (Prims.parse_int "10000") in
       minus_nat uu____837 uu____838 in
     run (Prims.parse_int "19") uu____836 znat);
    (let uu____840 =
       let uu____841 = encode_nat (Prims.parse_int "10") in
       let uu____842 = encode_nat (Prims.parse_int "10") in
       minus_nat uu____841 uu____842 in
     run (Prims.parse_int "20") uu____840 znat);
    FStar_Options.__clear_unit_tests ();
    (let uu____845 = FStar_Tests_Pars.tc "recons [0;1]" in
     let uu____846 = FStar_Tests_Pars.tc "[0;1]" in
     run (Prims.parse_int "21") uu____845 uu____846);
    (let uu____848 = FStar_Tests_Pars.tc "copy [0;1]" in
     let uu____849 = FStar_Tests_Pars.tc "[0;1]" in
     run (Prims.parse_int "22") uu____848 uu____849);
    (let uu____851 = FStar_Tests_Pars.tc "rev [0;1;2;3;4;5;6;7;8;9;10]" in
     let uu____852 = FStar_Tests_Pars.tc "[10;9;8;7;6;5;4;3;2;1;0]" in
     run (Prims.parse_int "23") uu____851 uu____852);
    (let uu____854 = FStar_Tests_Pars.tc "f (B 5 3)" in
     let uu____855 = FStar_Tests_Pars.tc "2" in
     run (Prims.parse_int "1062") uu____854 uu____855);
    FStar_Util.print_string "Normalizer ok\n"