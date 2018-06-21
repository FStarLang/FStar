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
             (let uu___453_421 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___453_421.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___453_421.FStar_Syntax_Syntax.sort)
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
          FStar_All.pipe_right uu____728 (fun a243  -> ()));
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
          (let uu____745 =
             let uu____746 = FStar_Syntax_Util.unascribe x1  in
             FStar_Tests_Util.term_eq uu____746 expected  in
           FStar_Tests_Util.always i uu____745)))
  
let (run_all : unit -> unit) =
  fun uu____753  ->
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
    (let uu____761 =
       let uu____762 =
         let uu____765 =
           let uu____768 =
             let uu____771 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____771]  in
           id :: uu____768  in
         one :: uu____765  in
       FStar_Tests_Util.app apply uu____762  in
     let uu____772 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     run (Prims.parse_int "0") uu____761 uu____772);
    (let uu____776 =
       let uu____777 =
         let uu____780 =
           let uu____783 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
           let uu____784 =
             let uu____787 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             [uu____787]  in
           uu____783 :: uu____784  in
         tt :: uu____780  in
       FStar_Tests_Util.app apply uu____777  in
     let uu____788 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     run (Prims.parse_int "1") uu____776 uu____788);
    (let uu____792 =
       let uu____793 =
         let uu____796 =
           let uu____799 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
           let uu____800 =
             let uu____803 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             [uu____803]  in
           uu____799 :: uu____800  in
         ff :: uu____796  in
       FStar_Tests_Util.app apply uu____793  in
     let uu____804 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.parse_int "2") uu____792 uu____804);
    (let uu____808 =
       let uu____809 =
         let uu____812 =
           let uu____815 =
             let uu____818 =
               let uu____821 =
                 let uu____824 =
                   let uu____827 =
                     let uu____830 = FStar_Tests_Util.nm FStar_Tests_Util.n
                        in
                     let uu____831 =
                       let uu____834 = FStar_Tests_Util.nm FStar_Tests_Util.m
                          in
                       [uu____834]  in
                     uu____830 :: uu____831  in
                   ff :: uu____827  in
                 apply :: uu____824  in
               apply :: uu____821  in
             apply :: uu____818  in
           apply :: uu____815  in
         apply :: uu____812  in
       FStar_Tests_Util.app apply uu____809  in
     let uu____835 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.parse_int "3") uu____808 uu____835);
    (let uu____839 =
       let uu____840 =
         let uu____843 =
           let uu____846 =
             let uu____849 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             let uu____850 =
               let uu____853 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               [uu____853]  in
             uu____849 :: uu____850  in
           ff :: uu____846  in
         apply :: uu____843  in
       FStar_Tests_Util.app twice uu____840  in
     let uu____854 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.parse_int "4") uu____839 uu____854);
    (let uu____858 = minus one z  in run (Prims.parse_int "5") uu____858 one);
    (let uu____860 = FStar_Tests_Util.app pred [one]  in
     run (Prims.parse_int "6") uu____860 z);
    (let uu____862 = minus one one  in run (Prims.parse_int "7") uu____862 z);
    (let uu____864 = FStar_Tests_Util.app mul [one; one]  in
     run (Prims.parse_int "8") uu____864 one);
    (let uu____866 = FStar_Tests_Util.app mul [two; one]  in
     run (Prims.parse_int "9") uu____866 two);
    (let uu____868 =
       let uu____869 =
         let uu____872 = FStar_Tests_Util.app succ [one]  in [uu____872; one]
          in
       FStar_Tests_Util.app mul uu____869  in
     run (Prims.parse_int "10") uu____868 two);
    (let uu____874 =
       let uu____875 = encode (Prims.parse_int "10")  in
       let uu____876 = encode (Prims.parse_int "10")  in
       minus uu____875 uu____876  in
     run (Prims.parse_int "11") uu____874 z);
    (let uu____880 =
       let uu____881 = encode (Prims.parse_int "100")  in
       let uu____882 = encode (Prims.parse_int "100")  in
       minus uu____881 uu____882  in
     run (Prims.parse_int "12") uu____880 z);
    (let uu____886 =
       let uu____887 = encode (Prims.parse_int "100")  in
       let uu____888 =
         let uu____891 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____892 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____891 uu____892  in
       let_ FStar_Tests_Util.x uu____887 uu____888  in
     run (Prims.parse_int "13") uu____886 z);
    (let uu____896 =
       let uu____897 = FStar_Tests_Util.app succ [one]  in
       let uu____898 =
         let uu____901 =
           let uu____902 =
             let uu____905 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
             let uu____906 =
               let uu____909 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
               [uu____909]  in
             uu____905 :: uu____906  in
           FStar_Tests_Util.app mul uu____902  in
         let uu____910 =
           let uu____913 =
             let uu____914 =
               let uu____917 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
               let uu____918 =
                 let uu____921 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
                 [uu____921]  in
               uu____917 :: uu____918  in
             FStar_Tests_Util.app mul uu____914  in
           let uu____922 =
             let uu____925 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             let uu____926 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             minus uu____925 uu____926  in
           let_ FStar_Tests_Util.h uu____913 uu____922  in
         let_ FStar_Tests_Util.y uu____901 uu____910  in
       let_ FStar_Tests_Util.x uu____897 uu____898  in
     run (Prims.parse_int "14") uu____896 z);
    (let uu____930 =
       let uu____931 = FStar_Tests_Util.app succ [one]  in
       let uu____934 =
         let uu____935 =
           let uu____938 =
             let uu____941 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
             let uu____942 =
               let uu____945 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
               [uu____945]  in
             uu____941 :: uu____942  in
           FStar_Tests_Util.app mul uu____938  in
         let uu____946 =
           let uu____947 =
             let uu____950 =
               let uu____953 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
               let uu____954 =
                 let uu____957 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
                 [uu____957]  in
               uu____953 :: uu____954  in
             FStar_Tests_Util.app mul uu____950  in
           let uu____958 =
             let uu____959 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             let uu____960 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             minus uu____959 uu____960  in
           mk_let FStar_Tests_Util.h uu____947 uu____958  in
         mk_let FStar_Tests_Util.y uu____935 uu____946  in
       mk_let FStar_Tests_Util.x uu____931 uu____934  in
     run (Prims.parse_int "15") uu____930 z);
    (let uu____964 =
       let uu____965 = let uu____968 = snat znat  in snat uu____968  in
       pred_nat uu____965  in
     let uu____969 = snat znat  in
     run (Prims.parse_int "16") uu____964 uu____969);
    (let uu____973 =
       let uu____974 = let uu____975 = snat znat  in snat uu____975  in
       let uu____976 = snat znat  in minus_nat uu____974 uu____976  in
     let uu____977 = snat znat  in
     run (Prims.parse_int "17") uu____973 uu____977);
    (let uu____981 =
       let uu____982 = encode_nat (Prims.parse_int "100")  in
       let uu____983 = encode_nat (Prims.parse_int "100")  in
       minus_nat uu____982 uu____983  in
     run (Prims.parse_int "18") uu____981 znat);
    (let uu____985 =
       let uu____986 = encode_nat (Prims.parse_int "10000")  in
       let uu____987 = encode_nat (Prims.parse_int "10000")  in
       minus_nat uu____986 uu____987  in
     run (Prims.parse_int "19") uu____985 znat);
    (let uu____989 =
       let uu____990 = encode_nat (Prims.parse_int "10")  in
       let uu____991 = encode_nat (Prims.parse_int "10")  in
       minus_nat uu____990 uu____991  in
     run (Prims.parse_int "20") uu____989 znat);
    FStar_Options.__clear_unit_tests ();
    (let uu____994 = FStar_Tests_Pars.tc "recons [0;1]"  in
     let uu____995 = FStar_Tests_Pars.tc "[0;1]"  in
     run (Prims.parse_int "21") uu____994 uu____995);
    (let uu____999 = FStar_Tests_Pars.tc "copy [0;1]"  in
     let uu____1000 = FStar_Tests_Pars.tc "[0;1]"  in
     run (Prims.parse_int "22") uu____999 uu____1000);
    (let uu____1004 = FStar_Tests_Pars.tc "rev [0;1;2;3;4;5;6;7;8;9;10]"  in
     let uu____1005 = FStar_Tests_Pars.tc "[10;9;8;7;6;5;4;3;2;1;0]"  in
     run (Prims.parse_int "23") uu____1004 uu____1005);
    (let uu____1009 = FStar_Tests_Pars.tc "f (B 5 3)"  in
     let uu____1010 = FStar_Tests_Pars.tc "2"  in
     run (Prims.parse_int "1062") uu____1009 uu____1010);
    FStar_Util.print_string "Normalizer ok\n"
  