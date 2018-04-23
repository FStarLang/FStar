open Prims
let b : FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.binder =
  FStar_Syntax_Syntax.mk_binder 
let id : FStar_Syntax_Syntax.term = FStar_Tests_Pars.pars "fun x -> x" 
let apply : FStar_Syntax_Syntax.term = FStar_Tests_Pars.pars "fun f x -> f x" 
let twice : FStar_Syntax_Syntax.term =
  FStar_Tests_Pars.pars "fun f x -> f (f x)" 
let tt : FStar_Syntax_Syntax.term = FStar_Tests_Pars.pars "fun x y -> x" 
let ff : FStar_Syntax_Syntax.term = FStar_Tests_Pars.pars "fun x y -> y" 
let z : FStar_Syntax_Syntax.term = FStar_Tests_Pars.pars "fun f x -> x" 
let one : FStar_Syntax_Syntax.term = FStar_Tests_Pars.pars "fun f x -> f x" 
let two : FStar_Syntax_Syntax.term =
  FStar_Tests_Pars.pars "fun f x -> f (f x)" 
let succ : FStar_Syntax_Syntax.term =
  FStar_Tests_Pars.pars "fun n f x -> f (n f x)" 
let pred : FStar_Syntax_Syntax.term =
  FStar_Tests_Pars.pars
    "fun n f x -> n (fun g h -> h (g f)) (fun y -> x) (fun y -> y)"
  
let mul : FStar_Syntax_Syntax.term =
  FStar_Tests_Pars.pars "fun m n f -> m (n f)" 
let rec encode : Prims.int -> FStar_Syntax_Syntax.term =
  fun n1  ->
    if n1 = (Prims.lift_native_int (0))
    then z
    else
      (let uu____11 =
         let uu____14 = encode (n1 - (Prims.lift_native_int (1)))  in
         [uu____14]  in
       FStar_Tests_Util.app succ uu____11)
  
let minus :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun m1  -> fun n1  -> FStar_Tests_Util.app n1 [pred; m1] 
let let_ :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun x1  ->
    fun e  ->
      fun e'  ->
        let uu____46 =
          let uu____49 = let uu____50 = b x1  in [uu____50]  in
          FStar_Syntax_Util.abs uu____49 e' FStar_Pervasives_Native.None  in
        FStar_Tests_Util.app uu____46 [e]
  
let mk_let :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun x1  ->
    fun e  ->
      fun e'  ->
        let e'1 =
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (x1, (Prims.lift_native_int (0)))] e'
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
  
let lid : Prims.string -> FStar_Ident.lident =
  fun x1  -> FStar_Ident.lid_of_path [x1] FStar_Range.dummyRange 
let znat_l : FStar_Syntax_Syntax.fv =
  let uu____86 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____86 FStar_Syntax_Syntax.Delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let snat_l : FStar_Syntax_Syntax.fv =
  let uu____87 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____87 FStar_Syntax_Syntax.Delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let tm_fv :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun fv  ->
    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
      FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let znat : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  tm_fv znat_l 
let snat :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    let uu____104 =
      let uu____111 =
        let uu____112 =
          let uu____127 = tm_fv snat_l  in
          let uu____130 =
            let uu____133 = FStar_Syntax_Syntax.as_arg s  in [uu____133]  in
          (uu____127, uu____130)  in
        FStar_Syntax_Syntax.Tm_app uu____112  in
      FStar_Syntax_Syntax.mk uu____111  in
    uu____104 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____145 . 'Auu____145 -> 'Auu____145 FStar_Syntax_Syntax.withinfo_t =
  fun p  -> FStar_Syntax_Syntax.withinfo p FStar_Range.dummyRange 
let mk_match :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun h1  ->
    fun branches  ->
      let branches1 =
        FStar_All.pipe_right branches
          (FStar_List.map FStar_Syntax_Util.branch)
         in
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (h1, branches1))
        FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pred_nat :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    let zbranch =
      let uu____210 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____210, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____252 =
        let uu____255 =
          let uu____256 =
            let uu____269 =
              let uu____278 =
                let uu____285 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____285, false)  in
              [uu____278]  in
            (snat_l, uu____269)  in
          FStar_Syntax_Syntax.Pat_cons uu____256  in
        pat uu____255  in
      let uu____310 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___77_315 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___77_315.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.lift_native_int (0));
                FStar_Syntax_Syntax.sort =
                  (uu___77_315.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____252, FStar_Pervasives_Native.None, uu____310)  in
    mk_match s [zbranch; sbranch]
  
let minus_nat :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t1  ->
    fun t2  ->
      let minus1 = FStar_Tests_Util.m  in
      let zbranch =
        let uu____394 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____411 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____394, FStar_Pervasives_Native.None, uu____411)  in
      let sbranch =
        let uu____435 =
          let uu____438 =
            let uu____439 =
              let uu____452 =
                let uu____461 =
                  let uu____468 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____468, false)  in
                [uu____461]  in
              (snat_l, uu____452)  in
            FStar_Syntax_Syntax.Pat_cons uu____439  in
          pat uu____438  in
        let uu____493 =
          let uu____496 = FStar_Tests_Util.nm minus1  in
          let uu____499 =
            let uu____502 =
              let uu____505 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____505  in
            let uu____508 =
              let uu____513 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____513]  in
            uu____502 :: uu____508  in
          FStar_Tests_Util.app uu____496 uu____499  in
        (uu____435, FStar_Pervasives_Native.None, uu____493)  in
      let lb =
        let uu____527 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____528 =
          let uu____531 =
            let uu____532 =
              let uu____533 = b FStar_Tests_Util.x  in
              let uu____534 =
                let uu____537 = b FStar_Tests_Util.y  in [uu____537]  in
              uu____533 :: uu____534  in
            let uu____538 =
              let uu____539 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____539 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____532 uu____538
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.lift_native_int (0)))]
            uu____531
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____527;
          FStar_Syntax_Syntax.lbdef = uu____528;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____584 =
        let uu____591 =
          let uu____592 =
            let uu____605 =
              let uu____606 =
                let uu____607 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____607 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.lift_native_int (0)))]
                uu____606
               in
            ((true, [lb]), uu____605)  in
          FStar_Syntax_Syntax.Tm_let uu____592  in
        FStar_Syntax_Syntax.mk uu____591  in
      uu____584 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let encode_nat : Prims.int -> FStar_Syntax_Syntax.term =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.lift_native_int (0))
      then out
      else
        (let uu____638 = snat out  in
         aux uu____638 (n2 - (Prims.lift_native_int (1))))
       in
    aux znat n1
  
let run :
  Prims.int -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> unit =
  fun i  ->
    fun r  ->
      fun expected  ->
        (let uu____655 = FStar_Util.string_of_int i  in
         FStar_Util.print1 "%s: ... \n" uu____655);
        (let tcenv = FStar_Tests_Pars.init ()  in
         (let uu____658 = FStar_Main.process_args ()  in
          FStar_All.pipe_right uu____658 (fun a246  -> ()));
         (let x1 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.Beta;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant;
              FStar_TypeChecker_Normalize.Primops] tcenv r
             in
          FStar_Options.init ();
          FStar_Options.set_option "print_universes"
            (FStar_Options.Bool true);
          FStar_Options.set_option "print_implicits"
            (FStar_Options.Bool true);
          (let uu____675 =
             let uu____676 = FStar_Syntax_Util.unascribe x1  in
             FStar_Tests_Util.term_eq uu____676 expected  in
           FStar_Tests_Util.always i uu____675)))
  
let run_all : unit -> unit =
  fun uu____681  ->
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
    (let uu____689 =
       let uu____690 =
         let uu____693 =
           let uu____696 =
             let uu____699 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____699]  in
           id :: uu____696  in
         one :: uu____693  in
       FStar_Tests_Util.app apply uu____690  in
     let uu____700 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     run (Prims.lift_native_int (0)) uu____689 uu____700);
    (let uu____702 =
       let uu____703 =
         let uu____706 =
           let uu____709 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
           let uu____710 =
             let uu____713 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             [uu____713]  in
           uu____709 :: uu____710  in
         tt :: uu____706  in
       FStar_Tests_Util.app apply uu____703  in
     let uu____714 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     run (Prims.lift_native_int (1)) uu____702 uu____714);
    (let uu____716 =
       let uu____717 =
         let uu____720 =
           let uu____723 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
           let uu____724 =
             let uu____727 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             [uu____727]  in
           uu____723 :: uu____724  in
         ff :: uu____720  in
       FStar_Tests_Util.app apply uu____717  in
     let uu____728 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.lift_native_int (2)) uu____716 uu____728);
    (let uu____730 =
       let uu____731 =
         let uu____734 =
           let uu____737 =
             let uu____740 =
               let uu____743 =
                 let uu____746 =
                   let uu____749 =
                     let uu____752 = FStar_Tests_Util.nm FStar_Tests_Util.n
                        in
                     let uu____753 =
                       let uu____756 = FStar_Tests_Util.nm FStar_Tests_Util.m
                          in
                       [uu____756]  in
                     uu____752 :: uu____753  in
                   ff :: uu____749  in
                 apply :: uu____746  in
               apply :: uu____743  in
             apply :: uu____740  in
           apply :: uu____737  in
         apply :: uu____734  in
       FStar_Tests_Util.app apply uu____731  in
     let uu____757 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.lift_native_int (3)) uu____730 uu____757);
    (let uu____759 =
       let uu____760 =
         let uu____763 =
           let uu____766 =
             let uu____769 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             let uu____770 =
               let uu____773 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               [uu____773]  in
             uu____769 :: uu____770  in
           ff :: uu____766  in
         apply :: uu____763  in
       FStar_Tests_Util.app twice uu____760  in
     let uu____774 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.lift_native_int (4)) uu____759 uu____774);
    (let uu____776 = minus one z  in
     run (Prims.lift_native_int (5)) uu____776 one);
    (let uu____778 = FStar_Tests_Util.app pred [one]  in
     run (Prims.lift_native_int (6)) uu____778 z);
    (let uu____780 = minus one one  in
     run (Prims.lift_native_int (7)) uu____780 z);
    (let uu____782 = FStar_Tests_Util.app mul [one; one]  in
     run (Prims.lift_native_int (8)) uu____782 one);
    (let uu____784 = FStar_Tests_Util.app mul [two; one]  in
     run (Prims.lift_native_int (9)) uu____784 two);
    (let uu____786 =
       let uu____787 =
         let uu____790 = FStar_Tests_Util.app succ [one]  in [uu____790; one]
          in
       FStar_Tests_Util.app mul uu____787  in
     run (Prims.lift_native_int (10)) uu____786 two);
    (let uu____796 =
       let uu____797 = encode (Prims.lift_native_int (10))  in
       let uu____798 = encode (Prims.lift_native_int (10))  in
       minus uu____797 uu____798  in
     run (Prims.lift_native_int (11)) uu____796 z);
    (let uu____802 =
       let uu____803 = encode (Prims.lift_native_int (100))  in
       let uu____804 = encode (Prims.lift_native_int (100))  in
       minus uu____803 uu____804  in
     run (Prims.lift_native_int (12)) uu____802 z);
    (let uu____808 =
       let uu____809 = encode (Prims.lift_native_int (100))  in
       let uu____810 =
         let uu____811 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____812 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____811 uu____812  in
       let_ FStar_Tests_Util.x uu____809 uu____810  in
     run (Prims.lift_native_int (13)) uu____808 z);
    (let uu____816 =
       let uu____817 = FStar_Tests_Util.app succ [one]  in
       let uu____818 =
         let uu____819 =
           let uu____820 =
             let uu____823 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
             let uu____824 =
               let uu____827 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
               [uu____827]  in
             uu____823 :: uu____824  in
           FStar_Tests_Util.app mul uu____820  in
         let uu____828 =
           let uu____829 =
             let uu____830 =
               let uu____833 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
               let uu____834 =
                 let uu____837 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
                 [uu____837]  in
               uu____833 :: uu____834  in
             FStar_Tests_Util.app mul uu____830  in
           let uu____838 =
             let uu____839 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             let uu____840 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             minus uu____839 uu____840  in
           let_ FStar_Tests_Util.h uu____829 uu____838  in
         let_ FStar_Tests_Util.y uu____819 uu____828  in
       let_ FStar_Tests_Util.x uu____817 uu____818  in
     run (Prims.lift_native_int (14)) uu____816 z);
    (let uu____844 =
       let uu____845 = FStar_Tests_Util.app succ [one]  in
       let uu____848 =
         let uu____849 =
           let uu____852 =
             let uu____855 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
             let uu____856 =
               let uu____859 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
               [uu____859]  in
             uu____855 :: uu____856  in
           FStar_Tests_Util.app mul uu____852  in
         let uu____860 =
           let uu____861 =
             let uu____864 =
               let uu____867 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
               let uu____868 =
                 let uu____871 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
                 [uu____871]  in
               uu____867 :: uu____868  in
             FStar_Tests_Util.app mul uu____864  in
           let uu____872 =
             let uu____873 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             let uu____874 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             minus uu____873 uu____874  in
           mk_let FStar_Tests_Util.h uu____861 uu____872  in
         mk_let FStar_Tests_Util.y uu____849 uu____860  in
       mk_let FStar_Tests_Util.x uu____845 uu____848  in
     run (Prims.lift_native_int (15)) uu____844 z);
    (let uu____878 =
       let uu____879 = let uu____882 = snat znat  in snat uu____882  in
       pred_nat uu____879  in
     let uu____883 = snat znat  in
     run (Prims.lift_native_int (16)) uu____878 uu____883);
    (let uu____885 =
       let uu____886 = let uu____887 = snat znat  in snat uu____887  in
       let uu____888 = snat znat  in minus_nat uu____886 uu____888  in
     let uu____889 = snat znat  in
     run (Prims.lift_native_int (17)) uu____885 uu____889);
    (let uu____891 =
       let uu____892 = encode_nat (Prims.lift_native_int (100))  in
       let uu____893 = encode_nat (Prims.lift_native_int (100))  in
       minus_nat uu____892 uu____893  in
     run (Prims.lift_native_int (18)) uu____891 znat);
    (let uu____895 =
       let uu____896 = encode_nat (Prims.lift_native_int (10000))  in
       let uu____897 = encode_nat (Prims.lift_native_int (10000))  in
       minus_nat uu____896 uu____897  in
     run (Prims.lift_native_int (19)) uu____895 znat);
    (let uu____899 =
       let uu____900 = encode_nat (Prims.lift_native_int (10))  in
       let uu____901 = encode_nat (Prims.lift_native_int (10))  in
       minus_nat uu____900 uu____901  in
     run (Prims.lift_native_int (20)) uu____899 znat);
    FStar_Options.__clear_unit_tests ();
    (let uu____904 = FStar_Tests_Pars.tc "recons [0;1]"  in
     let uu____905 = FStar_Tests_Pars.tc "[0;1]"  in
     run (Prims.lift_native_int (21)) uu____904 uu____905);
    (let uu____907 = FStar_Tests_Pars.tc "copy [0;1]"  in
     let uu____908 = FStar_Tests_Pars.tc "[0;1]"  in
     run (Prims.lift_native_int (22)) uu____907 uu____908);
    (let uu____910 = FStar_Tests_Pars.tc "rev [0;1;2;3;4;5;6;7;8;9;10]"  in
     let uu____911 = FStar_Tests_Pars.tc "[10;9;8;7;6;5;4;3;2;1;0]"  in
     run (Prims.lift_native_int (23)) uu____910 uu____911);
    (let uu____913 = FStar_Tests_Pars.tc "f (B 5 3)"  in
     let uu____914 = FStar_Tests_Pars.tc "2"  in
     run (Prims.lift_native_int (1062)) uu____913 uu____914);
    FStar_Util.print_string "Normalizer ok\n"
  