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
      (let uu____11 =
         let uu____14 = encode (n1 - (Prims.parse_int "1"))  in [uu____14]
          in
       FStar_Tests_Util.app succ uu____11)
  
let (minus :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun m1  -> fun n1  -> FStar_Tests_Util.app n1 [pred; m1] 
let (let_ :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun x1  ->
    fun e  ->
      fun e'  ->
        let uu____46 =
          let uu____49 = let uu____50 = b x1  in [uu____50]  in
          FStar_Syntax_Util.abs uu____49 e' FStar_Pervasives_Native.None  in
        FStar_Tests_Util.app uu____46 [e]
  
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
  fun x1  -> FStar_Ident.lid_of_path [x1] FStar_Range.dummyRange 
let (znat_l : FStar_Syntax_Syntax.fv) =
  let uu____86 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____86 FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____87 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____87 FStar_Syntax_Syntax.delta_constant
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
    let uu____102 =
      let uu____109 =
        let uu____110 =
          let uu____125 = tm_fv snat_l  in
          let uu____128 =
            let uu____131 = FStar_Syntax_Syntax.as_arg s  in [uu____131]  in
          (uu____125, uu____128)  in
        FStar_Syntax_Syntax.Tm_app uu____110  in
      FStar_Syntax_Syntax.mk uu____109  in
    uu____102 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____143 . 'Auu____143 -> 'Auu____143 FStar_Syntax_Syntax.withinfo_t =
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
      let uu____206 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____206, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____246 =
        let uu____249 =
          let uu____250 =
            let uu____263 =
              let uu____272 =
                let uu____279 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____279, false)  in
              [uu____272]  in
            (snat_l, uu____263)  in
          FStar_Syntax_Syntax.Pat_cons uu____250  in
        pat uu____249  in
      let uu____304 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___101_309 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___101_309.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___101_309.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____246, FStar_Pervasives_Native.None, uu____304)  in
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
        let uu____386 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____403 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____386, FStar_Pervasives_Native.None, uu____403)  in
      let sbranch =
        let uu____427 =
          let uu____430 =
            let uu____431 =
              let uu____444 =
                let uu____453 =
                  let uu____460 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____460, false)  in
                [uu____453]  in
              (snat_l, uu____444)  in
            FStar_Syntax_Syntax.Pat_cons uu____431  in
          pat uu____430  in
        let uu____485 =
          let uu____488 = FStar_Tests_Util.nm minus1  in
          let uu____491 =
            let uu____494 =
              let uu____497 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____497  in
            let uu____500 =
              let uu____505 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____505]  in
            uu____494 :: uu____500  in
          FStar_Tests_Util.app uu____488 uu____491  in
        (uu____427, FStar_Pervasives_Native.None, uu____485)  in
      let lb =
        let uu____519 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____520 =
          let uu____523 =
            let uu____524 =
              let uu____525 = b FStar_Tests_Util.x  in
              let uu____526 =
                let uu____529 = b FStar_Tests_Util.y  in [uu____529]  in
              uu____525 :: uu____526  in
            let uu____530 =
              let uu____531 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____531 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____524 uu____530
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____523
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____519;
          FStar_Syntax_Syntax.lbdef = uu____520;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____576 =
        let uu____583 =
          let uu____584 =
            let uu____597 =
              let uu____598 =
                let uu____599 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____599 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____598
               in
            ((true, [lb]), uu____597)  in
          FStar_Syntax_Syntax.Tm_let uu____584  in
        FStar_Syntax_Syntax.mk uu____583  in
      uu____576 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____630 = snat out  in
         aux uu____630 (n2 - (Prims.parse_int "1")))
       in
    aux znat n1
  
let (run :
  Prims.int -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> unit)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        (let uu____647 = FStar_Util.string_of_int i  in
         FStar_Util.print1 "%s: ... \n" uu____647);
        (let tcenv = FStar_Tests_Pars.init ()  in
         (let uu____650 = FStar_Main.process_args ()  in
          FStar_All.pipe_right uu____650 (fun a243  -> ()));
         (let x1 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.Beta;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant;
              FStar_TypeChecker_Normalize.Primops] tcenv r
             in
          FStar_Options.init ();
          FStar_Options.set_option "print_universes"
            (FStar_Options.Bool true);
          FStar_Options.set_option "print_implicits"
            (FStar_Options.Bool true);
          (let uu____667 =
             let uu____668 = FStar_Syntax_Util.unascribe x1  in
             FStar_Tests_Util.term_eq uu____668 expected  in
           FStar_Tests_Util.always i uu____667)))
  
let (run_all : unit -> unit) =
  fun uu____673  ->
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
    (let uu____681 =
       let uu____682 =
         let uu____685 =
           let uu____688 =
             let uu____691 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____691]  in
           id :: uu____688  in
         one :: uu____685  in
       FStar_Tests_Util.app apply uu____682  in
     let uu____692 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     run (Prims.parse_int "0") uu____681 uu____692);
    (let uu____694 =
       let uu____695 =
         let uu____698 =
           let uu____701 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
           let uu____702 =
             let uu____705 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             [uu____705]  in
           uu____701 :: uu____702  in
         tt :: uu____698  in
       FStar_Tests_Util.app apply uu____695  in
     let uu____706 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     run (Prims.parse_int "1") uu____694 uu____706);
    (let uu____708 =
       let uu____709 =
         let uu____712 =
           let uu____715 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
           let uu____716 =
             let uu____719 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             [uu____719]  in
           uu____715 :: uu____716  in
         ff :: uu____712  in
       FStar_Tests_Util.app apply uu____709  in
     let uu____720 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.parse_int "2") uu____708 uu____720);
    (let uu____722 =
       let uu____723 =
         let uu____726 =
           let uu____729 =
             let uu____732 =
               let uu____735 =
                 let uu____738 =
                   let uu____741 =
                     let uu____744 = FStar_Tests_Util.nm FStar_Tests_Util.n
                        in
                     let uu____745 =
                       let uu____748 = FStar_Tests_Util.nm FStar_Tests_Util.m
                          in
                       [uu____748]  in
                     uu____744 :: uu____745  in
                   ff :: uu____741  in
                 apply :: uu____738  in
               apply :: uu____735  in
             apply :: uu____732  in
           apply :: uu____729  in
         apply :: uu____726  in
       FStar_Tests_Util.app apply uu____723  in
     let uu____749 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.parse_int "3") uu____722 uu____749);
    (let uu____751 =
       let uu____752 =
         let uu____755 =
           let uu____758 =
             let uu____761 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             let uu____762 =
               let uu____765 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               [uu____765]  in
             uu____761 :: uu____762  in
           ff :: uu____758  in
         apply :: uu____755  in
       FStar_Tests_Util.app twice uu____752  in
     let uu____766 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.parse_int "4") uu____751 uu____766);
    (let uu____768 = minus one z  in run (Prims.parse_int "5") uu____768 one);
    (let uu____770 = FStar_Tests_Util.app pred [one]  in
     run (Prims.parse_int "6") uu____770 z);
    (let uu____772 = minus one one  in run (Prims.parse_int "7") uu____772 z);
    (let uu____774 = FStar_Tests_Util.app mul [one; one]  in
     run (Prims.parse_int "8") uu____774 one);
    (let uu____776 = FStar_Tests_Util.app mul [two; one]  in
     run (Prims.parse_int "9") uu____776 two);
    (let uu____778 =
       let uu____779 =
         let uu____782 = FStar_Tests_Util.app succ [one]  in [uu____782; one]
          in
       FStar_Tests_Util.app mul uu____779  in
     run (Prims.parse_int "10") uu____778 two);
    (let uu____788 =
       let uu____789 = encode (Prims.parse_int "10")  in
       let uu____790 = encode (Prims.parse_int "10")  in
       minus uu____789 uu____790  in
     run (Prims.parse_int "11") uu____788 z);
    (let uu____794 =
       let uu____795 = encode (Prims.parse_int "100")  in
       let uu____796 = encode (Prims.parse_int "100")  in
       minus uu____795 uu____796  in
     run (Prims.parse_int "12") uu____794 z);
    (let uu____800 =
       let uu____801 = encode (Prims.parse_int "100")  in
       let uu____802 =
         let uu____803 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____804 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____803 uu____804  in
       let_ FStar_Tests_Util.x uu____801 uu____802  in
     run (Prims.parse_int "13") uu____800 z);
    (let uu____808 =
       let uu____809 = FStar_Tests_Util.app succ [one]  in
       let uu____810 =
         let uu____811 =
           let uu____812 =
             let uu____815 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
             let uu____816 =
               let uu____819 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
               [uu____819]  in
             uu____815 :: uu____816  in
           FStar_Tests_Util.app mul uu____812  in
         let uu____820 =
           let uu____821 =
             let uu____822 =
               let uu____825 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
               let uu____826 =
                 let uu____829 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
                 [uu____829]  in
               uu____825 :: uu____826  in
             FStar_Tests_Util.app mul uu____822  in
           let uu____830 =
             let uu____831 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             let uu____832 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             minus uu____831 uu____832  in
           let_ FStar_Tests_Util.h uu____821 uu____830  in
         let_ FStar_Tests_Util.y uu____811 uu____820  in
       let_ FStar_Tests_Util.x uu____809 uu____810  in
     run (Prims.parse_int "14") uu____808 z);
    (let uu____836 =
       let uu____837 = FStar_Tests_Util.app succ [one]  in
       let uu____840 =
         let uu____841 =
           let uu____844 =
             let uu____847 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
             let uu____848 =
               let uu____851 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
               [uu____851]  in
             uu____847 :: uu____848  in
           FStar_Tests_Util.app mul uu____844  in
         let uu____852 =
           let uu____853 =
             let uu____856 =
               let uu____859 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
               let uu____860 =
                 let uu____863 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
                 [uu____863]  in
               uu____859 :: uu____860  in
             FStar_Tests_Util.app mul uu____856  in
           let uu____864 =
             let uu____865 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             let uu____866 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             minus uu____865 uu____866  in
           mk_let FStar_Tests_Util.h uu____853 uu____864  in
         mk_let FStar_Tests_Util.y uu____841 uu____852  in
       mk_let FStar_Tests_Util.x uu____837 uu____840  in
     run (Prims.parse_int "15") uu____836 z);
    (let uu____870 =
       let uu____871 = let uu____874 = snat znat  in snat uu____874  in
       pred_nat uu____871  in
     let uu____875 = snat znat  in
     run (Prims.parse_int "16") uu____870 uu____875);
    (let uu____877 =
       let uu____878 = let uu____879 = snat znat  in snat uu____879  in
       let uu____880 = snat znat  in minus_nat uu____878 uu____880  in
     let uu____881 = snat znat  in
     run (Prims.parse_int "17") uu____877 uu____881);
    (let uu____883 =
       let uu____884 = encode_nat (Prims.parse_int "100")  in
       let uu____885 = encode_nat (Prims.parse_int "100")  in
       minus_nat uu____884 uu____885  in
     run (Prims.parse_int "18") uu____883 znat);
    (let uu____887 =
       let uu____888 = encode_nat (Prims.parse_int "10000")  in
       let uu____889 = encode_nat (Prims.parse_int "10000")  in
       minus_nat uu____888 uu____889  in
     run (Prims.parse_int "19") uu____887 znat);
    (let uu____891 =
       let uu____892 = encode_nat (Prims.parse_int "10")  in
       let uu____893 = encode_nat (Prims.parse_int "10")  in
       minus_nat uu____892 uu____893  in
     run (Prims.parse_int "20") uu____891 znat);
    FStar_Options.__clear_unit_tests ();
    (let uu____896 = FStar_Tests_Pars.tc "recons [0;1]"  in
     let uu____897 = FStar_Tests_Pars.tc "[0;1]"  in
     run (Prims.parse_int "21") uu____896 uu____897);
    (let uu____899 = FStar_Tests_Pars.tc "copy [0;1]"  in
     let uu____900 = FStar_Tests_Pars.tc "[0;1]"  in
     run (Prims.parse_int "22") uu____899 uu____900);
    (let uu____902 = FStar_Tests_Pars.tc "rev [0;1;2;3;4;5;6;7;8;9;10]"  in
     let uu____903 = FStar_Tests_Pars.tc "[10;9;8;7;6;5;4;3;2;1;0]"  in
     run (Prims.parse_int "23") uu____902 uu____903);
    (let uu____905 = FStar_Tests_Pars.tc "f (B 5 3)"  in
     let uu____906 = FStar_Tests_Pars.tc "2"  in
     run (Prims.parse_int "1062") uu____905 uu____906);
    FStar_Util.print_string "Normalizer ok\n"
  