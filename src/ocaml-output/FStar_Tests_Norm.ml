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
  let uu____110 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____110 FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____111 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____111 FStar_Syntax_Syntax.delta_constant
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
    let uu____126 =
      let uu____133 =
        let uu____134 =
          let uu____151 = tm_fv snat_l  in
          let uu____154 =
            let uu____165 = FStar_Syntax_Syntax.as_arg s  in [uu____165]  in
          (uu____151, uu____154)  in
        FStar_Syntax_Syntax.Tm_app uu____134  in
      FStar_Syntax_Syntax.mk uu____133  in
    uu____126 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____209 . 'Auu____209 -> 'Auu____209 FStar_Syntax_Syntax.withinfo_t =
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
      let uu____316 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____316, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____358 =
        let uu____361 =
          let uu____362 =
            let uu____375 =
              let uu____384 =
                let uu____391 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____391, false)  in
              [uu____384]  in
            (snat_l, uu____375)  in
          FStar_Syntax_Syntax.Pat_cons uu____362  in
        pat uu____361  in
      let uu____416 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___457_421 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___457_421.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___457_421.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____358, FStar_Pervasives_Native.None, uu____416)  in
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
        let uu____460 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____477 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____460, FStar_Pervasives_Native.None, uu____477)  in
      let sbranch =
        let uu____505 =
          let uu____508 =
            let uu____509 =
              let uu____522 =
                let uu____531 =
                  let uu____538 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____538, false)  in
                [uu____531]  in
              (snat_l, uu____522)  in
            FStar_Syntax_Syntax.Pat_cons uu____509  in
          pat uu____508  in
        let uu____563 =
          let uu____566 = FStar_Tests_Util.nm minus1  in
          let uu____569 =
            let uu____572 =
              let uu____573 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____573  in
            let uu____576 =
              let uu____579 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____579]  in
            uu____572 :: uu____576  in
          FStar_Tests_Util.app uu____566 uu____569  in
        (uu____505, FStar_Pervasives_Native.None, uu____563)  in
      let lb =
        let uu____591 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____592 =
          let uu____595 =
            let uu____596 =
              let uu____597 = b FStar_Tests_Util.x  in
              let uu____604 =
                let uu____613 = b FStar_Tests_Util.y  in [uu____613]  in
              uu____597 :: uu____604  in
            let uu____638 =
              let uu____641 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____641 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____596 uu____638
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____595
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____591;
          FStar_Syntax_Syntax.lbdef = uu____592;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____646 =
        let uu____653 =
          let uu____654 =
            let uu____667 =
              let uu____670 =
                let uu____671 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____671 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____670
               in
            ((true, [lb]), uu____667)  in
          FStar_Syntax_Syntax.Tm_let uu____654  in
        FStar_Syntax_Syntax.mk uu____653  in
      uu____646 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____704 = snat out  in
         aux uu____704 (n2 - (Prims.parse_int "1")))
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
        (let uu____725 = FStar_Util.string_of_int i  in
         FStar_Util.print1 "%s: ... \n" uu____725);
        (let tcenv = FStar_Tests_Pars.init ()  in
         (let uu____728 = FStar_Main.process_args ()  in
          FStar_All.pipe_right uu____728 (fun a242  -> ()));
         (let x1 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.Beta;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant;
              FStar_TypeChecker_Normalize.Primops] tcenv r
             in
          FStar_Options.set_option "print_universes"
            (FStar_Options.Bool true);
          FStar_Options.set_option "print_implicits"
            (FStar_Options.Bool true);
          (let uu____745 =
             let uu____746 = FStar_Syntax_Util.unascribe x1  in
             FStar_Tests_Util.term_eq uu____746 expected  in
           FStar_Tests_Util.always i uu____745);
          FStar_Options.init ()))
  
let (run_all : unit -> unit) =
  fun uu____754  ->
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
    (let uu____762 =
       let uu____763 =
         let uu____766 =
           let uu____769 =
             let uu____772 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____772]  in
           id :: uu____769  in
         one :: uu____766  in
       FStar_Tests_Util.app apply uu____763  in
     let uu____773 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     run (Prims.parse_int "0") uu____762 uu____773);
    (let uu____777 =
       let uu____778 =
         let uu____781 =
           let uu____784 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
           let uu____785 =
             let uu____788 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             [uu____788]  in
           uu____784 :: uu____785  in
         tt :: uu____781  in
       FStar_Tests_Util.app apply uu____778  in
     let uu____789 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     run (Prims.parse_int "1") uu____777 uu____789);
    (let uu____793 =
       let uu____794 =
         let uu____797 =
           let uu____800 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
           let uu____801 =
             let uu____804 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             [uu____804]  in
           uu____800 :: uu____801  in
         ff :: uu____797  in
       FStar_Tests_Util.app apply uu____794  in
     let uu____805 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.parse_int "2") uu____793 uu____805);
    (let uu____809 =
       let uu____810 =
         let uu____813 =
           let uu____816 =
             let uu____819 =
               let uu____822 =
                 let uu____825 =
                   let uu____828 =
                     let uu____831 = FStar_Tests_Util.nm FStar_Tests_Util.n
                        in
                     let uu____832 =
                       let uu____835 = FStar_Tests_Util.nm FStar_Tests_Util.m
                          in
                       [uu____835]  in
                     uu____831 :: uu____832  in
                   ff :: uu____828  in
                 apply :: uu____825  in
               apply :: uu____822  in
             apply :: uu____819  in
           apply :: uu____816  in
         apply :: uu____813  in
       FStar_Tests_Util.app apply uu____810  in
     let uu____836 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.parse_int "3") uu____809 uu____836);
    (let uu____840 =
       let uu____841 =
         let uu____844 =
           let uu____847 =
             let uu____850 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             let uu____851 =
               let uu____854 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               [uu____854]  in
             uu____850 :: uu____851  in
           ff :: uu____847  in
         apply :: uu____844  in
       FStar_Tests_Util.app twice uu____841  in
     let uu____855 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.parse_int "4") uu____840 uu____855);
    (let uu____859 = minus one z  in run (Prims.parse_int "5") uu____859 one);
    (let uu____861 = FStar_Tests_Util.app pred [one]  in
     run (Prims.parse_int "6") uu____861 z);
    (let uu____863 = minus one one  in run (Prims.parse_int "7") uu____863 z);
    (let uu____865 = FStar_Tests_Util.app mul [one; one]  in
     run (Prims.parse_int "8") uu____865 one);
    (let uu____867 = FStar_Tests_Util.app mul [two; one]  in
     run (Prims.parse_int "9") uu____867 two);
    (let uu____869 =
       let uu____870 =
         let uu____873 = FStar_Tests_Util.app succ [one]  in [uu____873; one]
          in
       FStar_Tests_Util.app mul uu____870  in
     run (Prims.parse_int "10") uu____869 two);
    (let uu____875 =
       let uu____876 = encode (Prims.parse_int "10")  in
       let uu____877 = encode (Prims.parse_int "10")  in
       minus uu____876 uu____877  in
     run (Prims.parse_int "11") uu____875 z);
    (let uu____881 =
       let uu____882 = encode (Prims.parse_int "100")  in
       let uu____883 = encode (Prims.parse_int "100")  in
       minus uu____882 uu____883  in
     run (Prims.parse_int "12") uu____881 z);
    (let uu____887 =
       let uu____888 = encode (Prims.parse_int "100")  in
       let uu____889 =
         let uu____892 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____893 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____892 uu____893  in
       let_ FStar_Tests_Util.x uu____888 uu____889  in
     run (Prims.parse_int "13") uu____887 z);
    (let uu____897 =
       let uu____898 = FStar_Tests_Util.app succ [one]  in
       let uu____899 =
         let uu____902 =
           let uu____903 =
             let uu____906 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
             let uu____907 =
               let uu____910 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
               [uu____910]  in
             uu____906 :: uu____907  in
           FStar_Tests_Util.app mul uu____903  in
         let uu____911 =
           let uu____914 =
             let uu____915 =
               let uu____918 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
               let uu____919 =
                 let uu____922 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
                 [uu____922]  in
               uu____918 :: uu____919  in
             FStar_Tests_Util.app mul uu____915  in
           let uu____923 =
             let uu____926 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             let uu____927 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             minus uu____926 uu____927  in
           let_ FStar_Tests_Util.h uu____914 uu____923  in
         let_ FStar_Tests_Util.y uu____902 uu____911  in
       let_ FStar_Tests_Util.x uu____898 uu____899  in
     run (Prims.parse_int "14") uu____897 z);
    (let uu____931 =
       let uu____932 = FStar_Tests_Util.app succ [one]  in
       let uu____935 =
         let uu____936 =
           let uu____939 =
             let uu____942 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
             let uu____943 =
               let uu____946 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
               [uu____946]  in
             uu____942 :: uu____943  in
           FStar_Tests_Util.app mul uu____939  in
         let uu____947 =
           let uu____948 =
             let uu____951 =
               let uu____954 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
               let uu____955 =
                 let uu____958 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
                 [uu____958]  in
               uu____954 :: uu____955  in
             FStar_Tests_Util.app mul uu____951  in
           let uu____959 =
             let uu____960 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             let uu____961 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             minus uu____960 uu____961  in
           mk_let FStar_Tests_Util.h uu____948 uu____959  in
         mk_let FStar_Tests_Util.y uu____936 uu____947  in
       mk_let FStar_Tests_Util.x uu____932 uu____935  in
     run (Prims.parse_int "15") uu____931 z);
    (let uu____965 =
       let uu____966 = let uu____969 = snat znat  in snat uu____969  in
       pred_nat uu____966  in
     let uu____970 = snat znat  in
     run (Prims.parse_int "16") uu____965 uu____970);
    (let uu____974 =
       let uu____975 = let uu____976 = snat znat  in snat uu____976  in
       let uu____977 = snat znat  in minus_nat uu____975 uu____977  in
     let uu____978 = snat znat  in
     run (Prims.parse_int "17") uu____974 uu____978);
    (let uu____982 =
       let uu____983 = encode_nat (Prims.parse_int "100")  in
       let uu____984 = encode_nat (Prims.parse_int "100")  in
       minus_nat uu____983 uu____984  in
     run (Prims.parse_int "18") uu____982 znat);
    (let uu____986 =
       let uu____987 = encode_nat (Prims.parse_int "1000")  in
       let uu____988 = encode_nat (Prims.parse_int "1000")  in
       minus_nat uu____987 uu____988  in
     run (Prims.parse_int "19") uu____986 znat);
    (let uu____990 =
       let uu____991 = encode_nat (Prims.parse_int "10")  in
       let uu____992 = encode_nat (Prims.parse_int "10")  in
       minus_nat uu____991 uu____992  in
     run (Prims.parse_int "20") uu____990 znat);
    FStar_Options.__clear_unit_tests ();
    (let uu____995 = FStar_Tests_Pars.tc "recons [0;1]"  in
     let uu____996 = FStar_Tests_Pars.tc "[0;1]"  in
     run (Prims.parse_int "21") uu____995 uu____996);
    (let uu____1000 = FStar_Tests_Pars.tc "copy [0;1]"  in
     let uu____1001 = FStar_Tests_Pars.tc "[0;1]"  in
     run (Prims.parse_int "22") uu____1000 uu____1001);
    (let uu____1005 = FStar_Tests_Pars.tc "rev [0;1;2;3;4;5;6;7;8;9;10]"  in
     let uu____1006 = FStar_Tests_Pars.tc "[10;9;8;7;6;5;4;3;2;1;0]"  in
     run (Prims.parse_int "23") uu____1005 uu____1006);
    (let uu____1010 = FStar_Tests_Pars.tc "f (B 5 3)"  in
     let uu____1011 = FStar_Tests_Pars.tc "2"  in
     run (Prims.parse_int "1062") uu____1010 uu____1011);
    FStar_Util.print_string "Normalizer ok\n"
  