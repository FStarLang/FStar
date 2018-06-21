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
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term)
  =
  fun x1  ->
    fun e  ->
      fun e'  ->
        let uu____50 =
          let uu____53 = let uu____54 = b x1  in [uu____54]  in
          FStar_Syntax_Util.abs uu____53 e' FStar_Pervasives_Native.None  in
        FStar_Tests_Util.app uu____50 [e]
  
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
  let uu____104 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____104 FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____105 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____105 FStar_Syntax_Syntax.delta_constant
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
    let uu____120 =
      let uu____127 =
        let uu____128 =
          let uu____143 = tm_fv snat_l  in
          let uu____146 =
            let uu____155 = FStar_Syntax_Syntax.as_arg s  in [uu____155]  in
          (uu____143, uu____146)  in
        FStar_Syntax_Syntax.Tm_app uu____128  in
      FStar_Syntax_Syntax.mk uu____127  in
    uu____120 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____191 . 'Auu____191 -> 'Auu____191 FStar_Syntax_Syntax.withinfo_t =
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
      let uu____298 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____298, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____340 =
        let uu____343 =
          let uu____344 =
            let uu____357 =
              let uu____366 =
                let uu____373 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____373, false)  in
              [uu____366]  in
            (snat_l, uu____357)  in
          FStar_Syntax_Syntax.Pat_cons uu____344  in
        pat uu____343  in
      let uu____398 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___452_403 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___452_403.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___452_403.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____340, FStar_Pervasives_Native.None, uu____398)  in
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
        let uu____442 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____459 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____442, FStar_Pervasives_Native.None, uu____459)  in
      let sbranch =
        let uu____487 =
          let uu____490 =
            let uu____491 =
              let uu____504 =
                let uu____513 =
                  let uu____520 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____520, false)  in
                [uu____513]  in
              (snat_l, uu____504)  in
            FStar_Syntax_Syntax.Pat_cons uu____491  in
          pat uu____490  in
        let uu____545 =
          let uu____548 = FStar_Tests_Util.nm minus1  in
          let uu____551 =
            let uu____554 =
              let uu____555 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____555  in
            let uu____558 =
              let uu____561 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____561]  in
            uu____554 :: uu____558  in
          FStar_Tests_Util.app uu____548 uu____551  in
        (uu____487, FStar_Pervasives_Native.None, uu____545)  in
      let lb =
        let uu____573 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____574 =
          let uu____577 =
            let uu____578 =
              let uu____579 = b FStar_Tests_Util.x  in
              let uu____584 =
                let uu____591 = b FStar_Tests_Util.y  in [uu____591]  in
              uu____579 :: uu____584  in
            let uu____608 =
              let uu____611 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____611 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____578 uu____608
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____577
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____573;
          FStar_Syntax_Syntax.lbdef = uu____574;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____616 =
        let uu____623 =
          let uu____624 =
            let uu____637 =
              let uu____640 =
                let uu____641 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____641 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____640
               in
            ((true, [lb]), uu____637)  in
          FStar_Syntax_Syntax.Tm_let uu____624  in
        FStar_Syntax_Syntax.mk uu____623  in
      uu____616 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____674 = snat out  in
         aux uu____674 (n2 - (Prims.parse_int "1")))
       in
    aux znat n1
  
let (run :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        (let uu____695 = FStar_Util.string_of_int i  in
         FStar_Util.print1 "%s: ... \n" uu____695);
        (let tcenv = FStar_Tests_Pars.init ()  in
         (let uu____698 = FStar_Main.process_args ()  in
          FStar_All.pipe_right uu____698 (fun a242  -> ()));
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
          (let uu____715 =
             let uu____716 = FStar_Syntax_Util.unascribe x1  in
             FStar_Tests_Util.term_eq uu____716 expected  in
           FStar_Tests_Util.always i uu____715)))
  
let (run_all : unit -> unit) =
  fun uu____723  ->
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
    (let uu____731 =
       let uu____732 =
         let uu____735 =
           let uu____738 =
             let uu____741 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____741]  in
           id :: uu____738  in
         one :: uu____735  in
       FStar_Tests_Util.app apply uu____732  in
     let uu____742 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     run (Prims.parse_int "0") uu____731 uu____742);
    (let uu____746 =
       let uu____747 =
         let uu____750 =
           let uu____753 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
           let uu____754 =
             let uu____757 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             [uu____757]  in
           uu____753 :: uu____754  in
         tt :: uu____750  in
       FStar_Tests_Util.app apply uu____747  in
     let uu____758 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     run (Prims.parse_int "1") uu____746 uu____758);
    (let uu____762 =
       let uu____763 =
         let uu____766 =
           let uu____769 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
           let uu____770 =
             let uu____773 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             [uu____773]  in
           uu____769 :: uu____770  in
         ff :: uu____766  in
       FStar_Tests_Util.app apply uu____763  in
     let uu____774 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.parse_int "2") uu____762 uu____774);
    (let uu____778 =
       let uu____779 =
         let uu____782 =
           let uu____785 =
             let uu____788 =
               let uu____791 =
                 let uu____794 =
                   let uu____797 =
                     let uu____800 = FStar_Tests_Util.nm FStar_Tests_Util.n
                        in
                     let uu____801 =
                       let uu____804 = FStar_Tests_Util.nm FStar_Tests_Util.m
                          in
                       [uu____804]  in
                     uu____800 :: uu____801  in
                   ff :: uu____797  in
                 apply :: uu____794  in
               apply :: uu____791  in
             apply :: uu____788  in
           apply :: uu____785  in
         apply :: uu____782  in
       FStar_Tests_Util.app apply uu____779  in
     let uu____805 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.parse_int "3") uu____778 uu____805);
    (let uu____809 =
       let uu____810 =
         let uu____813 =
           let uu____816 =
             let uu____819 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             let uu____820 =
               let uu____823 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               [uu____823]  in
             uu____819 :: uu____820  in
           ff :: uu____816  in
         apply :: uu____813  in
       FStar_Tests_Util.app twice uu____810  in
     let uu____824 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.parse_int "4") uu____809 uu____824);
    (let uu____828 = minus one z  in run (Prims.parse_int "5") uu____828 one);
    (let uu____830 = FStar_Tests_Util.app pred [one]  in
     run (Prims.parse_int "6") uu____830 z);
    (let uu____832 = minus one one  in run (Prims.parse_int "7") uu____832 z);
    (let uu____834 = FStar_Tests_Util.app mul [one; one]  in
     run (Prims.parse_int "8") uu____834 one);
    (let uu____836 = FStar_Tests_Util.app mul [two; one]  in
     run (Prims.parse_int "9") uu____836 two);
    (let uu____838 =
       let uu____839 =
         let uu____842 = FStar_Tests_Util.app succ [one]  in [uu____842; one]
          in
       FStar_Tests_Util.app mul uu____839  in
     run (Prims.parse_int "10") uu____838 two);
    (let uu____844 =
       let uu____845 = encode (Prims.parse_int "10")  in
       let uu____846 = encode (Prims.parse_int "10")  in
       minus uu____845 uu____846  in
     run (Prims.parse_int "11") uu____844 z);
    (let uu____850 =
       let uu____851 = encode (Prims.parse_int "100")  in
       let uu____852 = encode (Prims.parse_int "100")  in
       minus uu____851 uu____852  in
     run (Prims.parse_int "12") uu____850 z);
    (let uu____856 =
       let uu____857 = encode (Prims.parse_int "100")  in
       let uu____858 =
         let uu____861 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____862 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____861 uu____862  in
       let_ FStar_Tests_Util.x uu____857 uu____858  in
     run (Prims.parse_int "13") uu____856 z);
    (let uu____866 =
       let uu____867 = FStar_Tests_Util.app succ [one]  in
       let uu____868 =
         let uu____871 =
           let uu____872 =
             let uu____875 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
             let uu____876 =
               let uu____879 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
               [uu____879]  in
             uu____875 :: uu____876  in
           FStar_Tests_Util.app mul uu____872  in
         let uu____880 =
           let uu____883 =
             let uu____884 =
               let uu____887 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
               let uu____888 =
                 let uu____891 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
                 [uu____891]  in
               uu____887 :: uu____888  in
             FStar_Tests_Util.app mul uu____884  in
           let uu____892 =
             let uu____895 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             let uu____896 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             minus uu____895 uu____896  in
           let_ FStar_Tests_Util.h uu____883 uu____892  in
         let_ FStar_Tests_Util.y uu____871 uu____880  in
       let_ FStar_Tests_Util.x uu____867 uu____868  in
     run (Prims.parse_int "14") uu____866 z);
    (let uu____900 =
       let uu____901 = FStar_Tests_Util.app succ [one]  in
       let uu____904 =
         let uu____905 =
           let uu____908 =
             let uu____911 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
             let uu____912 =
               let uu____915 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
               [uu____915]  in
             uu____911 :: uu____912  in
           FStar_Tests_Util.app mul uu____908  in
         let uu____916 =
           let uu____917 =
             let uu____920 =
               let uu____923 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
               let uu____924 =
                 let uu____927 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
                 [uu____927]  in
               uu____923 :: uu____924  in
             FStar_Tests_Util.app mul uu____920  in
           let uu____928 =
             let uu____929 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             let uu____930 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             minus uu____929 uu____930  in
           mk_let FStar_Tests_Util.h uu____917 uu____928  in
         mk_let FStar_Tests_Util.y uu____905 uu____916  in
       mk_let FStar_Tests_Util.x uu____901 uu____904  in
     run (Prims.parse_int "15") uu____900 z);
    (let uu____934 =
       let uu____935 = let uu____938 = snat znat  in snat uu____938  in
       pred_nat uu____935  in
     let uu____939 = snat znat  in
     run (Prims.parse_int "16") uu____934 uu____939);
    (let uu____943 =
       let uu____944 = let uu____945 = snat znat  in snat uu____945  in
       let uu____946 = snat znat  in minus_nat uu____944 uu____946  in
     let uu____947 = snat znat  in
     run (Prims.parse_int "17") uu____943 uu____947);
    (let uu____951 =
       let uu____952 = encode_nat (Prims.parse_int "100")  in
       let uu____953 = encode_nat (Prims.parse_int "100")  in
       minus_nat uu____952 uu____953  in
     run (Prims.parse_int "18") uu____951 znat);
    (let uu____955 =
       let uu____956 = encode_nat (Prims.parse_int "10000")  in
       let uu____957 = encode_nat (Prims.parse_int "10000")  in
       minus_nat uu____956 uu____957  in
     run (Prims.parse_int "19") uu____955 znat);
    (let uu____959 =
       let uu____960 = encode_nat (Prims.parse_int "10")  in
       let uu____961 = encode_nat (Prims.parse_int "10")  in
       minus_nat uu____960 uu____961  in
     run (Prims.parse_int "20") uu____959 znat);
    FStar_Options.__clear_unit_tests ();
    (let uu____964 = FStar_Tests_Pars.tc "recons [0;1]"  in
     let uu____965 = FStar_Tests_Pars.tc "[0;1]"  in
     run (Prims.parse_int "21") uu____964 uu____965);
    (let uu____969 = FStar_Tests_Pars.tc "copy [0;1]"  in
     let uu____970 = FStar_Tests_Pars.tc "[0;1]"  in
     run (Prims.parse_int "22") uu____969 uu____970);
    (let uu____974 = FStar_Tests_Pars.tc "rev [0;1;2;3;4;5;6;7;8;9;10]"  in
     let uu____975 = FStar_Tests_Pars.tc "[10;9;8;7;6;5;4;3;2;1;0]"  in
     run (Prims.parse_int "23") uu____974 uu____975);
    (let uu____979 = FStar_Tests_Pars.tc "f (B 5 3)"  in
     let uu____980 = FStar_Tests_Pars.tc "2"  in
     run (Prims.parse_int "1062") uu____979 uu____980);
    FStar_Util.print_string "Normalizer ok\n"
  