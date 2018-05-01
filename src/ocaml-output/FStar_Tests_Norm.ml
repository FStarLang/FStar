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
  
let (znat : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  tm_fv znat_l 
let (snat :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    let uu____122 =
      let uu____129 =
        let uu____130 =
          let uu____145 = tm_fv snat_l  in
          let uu____148 =
            let uu____157 = FStar_Syntax_Syntax.as_arg s  in [uu____157]  in
          (uu____145, uu____148)  in
        FStar_Syntax_Syntax.Tm_app uu____130  in
      FStar_Syntax_Syntax.mk uu____129  in
    uu____122 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____193 . 'Auu____193 -> 'Auu____193 FStar_Syntax_Syntax.withinfo_t =
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
      let uu____300 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____300, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____342 =
        let uu____345 =
          let uu____346 =
            let uu____359 =
              let uu____368 =
                let uu____375 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____375, false)  in
              [uu____368]  in
            (snat_l, uu____359)  in
          FStar_Syntax_Syntax.Pat_cons uu____346  in
        pat uu____345  in
      let uu____400 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___105_405 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___105_405.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___105_405.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____342, FStar_Pervasives_Native.None, uu____400)  in
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
        let uu____444 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____461 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____444, FStar_Pervasives_Native.None, uu____461)  in
      let sbranch =
        let uu____489 =
          let uu____492 =
            let uu____493 =
              let uu____506 =
                let uu____515 =
                  let uu____522 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____522, false)  in
                [uu____515]  in
              (snat_l, uu____506)  in
            FStar_Syntax_Syntax.Pat_cons uu____493  in
          pat uu____492  in
        let uu____547 =
          let uu____550 = FStar_Tests_Util.nm minus1  in
          let uu____553 =
            let uu____556 =
              let uu____557 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____557  in
            let uu____560 =
              let uu____563 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____563]  in
            uu____556 :: uu____560  in
          FStar_Tests_Util.app uu____550 uu____553  in
        (uu____489, FStar_Pervasives_Native.None, uu____547)  in
      let lb =
        let uu____575 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____576 =
          let uu____579 =
            let uu____580 =
              let uu____581 = b FStar_Tests_Util.x  in
              let uu____586 =
                let uu____593 = b FStar_Tests_Util.y  in [uu____593]  in
              uu____581 :: uu____586  in
            let uu____610 =
              let uu____613 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____613 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____580 uu____610
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____579
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____575;
          FStar_Syntax_Syntax.lbdef = uu____576;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____618 =
        let uu____625 =
          let uu____626 =
            let uu____639 =
              let uu____642 =
                let uu____643 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____643 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____642
               in
            ((true, [lb]), uu____639)  in
          FStar_Syntax_Syntax.Tm_let uu____626  in
        FStar_Syntax_Syntax.mk uu____625  in
      uu____618 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____676 = snat out  in
         aux uu____676 (n2 - (Prims.parse_int "1")))
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
        (let uu____697 = FStar_Util.string_of_int i  in
         FStar_Util.print1 "%s: ... \n" uu____697);
        (let tcenv = FStar_Tests_Pars.init ()  in
         (let uu____700 = FStar_Main.process_args ()  in
          FStar_All.pipe_right uu____700 (fun a244  -> ()));
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
          (let uu____717 =
             let uu____718 = FStar_Syntax_Util.unascribe x1  in
             FStar_Tests_Util.term_eq uu____718 expected  in
           FStar_Tests_Util.always i uu____717)))
  
let (run_all : unit -> unit) =
  fun uu____725  ->
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
    (let uu____733 =
       let uu____734 =
         let uu____737 =
           let uu____740 =
             let uu____743 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____743]  in
           id :: uu____740  in
         one :: uu____737  in
       FStar_Tests_Util.app apply uu____734  in
     let uu____744 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     run (Prims.parse_int "0") uu____733 uu____744);
    (let uu____748 =
       let uu____749 =
         let uu____752 =
           let uu____755 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
           let uu____756 =
             let uu____759 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             [uu____759]  in
           uu____755 :: uu____756  in
         tt :: uu____752  in
       FStar_Tests_Util.app apply uu____749  in
     let uu____760 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     run (Prims.parse_int "1") uu____748 uu____760);
    (let uu____764 =
       let uu____765 =
         let uu____768 =
           let uu____771 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
           let uu____772 =
             let uu____775 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             [uu____775]  in
           uu____771 :: uu____772  in
         ff :: uu____768  in
       FStar_Tests_Util.app apply uu____765  in
     let uu____776 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.parse_int "2") uu____764 uu____776);
    (let uu____780 =
       let uu____781 =
         let uu____784 =
           let uu____787 =
             let uu____790 =
               let uu____793 =
                 let uu____796 =
                   let uu____799 =
                     let uu____802 = FStar_Tests_Util.nm FStar_Tests_Util.n
                        in
                     let uu____803 =
                       let uu____806 = FStar_Tests_Util.nm FStar_Tests_Util.m
                          in
                       [uu____806]  in
                     uu____802 :: uu____803  in
                   ff :: uu____799  in
                 apply :: uu____796  in
               apply :: uu____793  in
             apply :: uu____790  in
           apply :: uu____787  in
         apply :: uu____784  in
       FStar_Tests_Util.app apply uu____781  in
     let uu____807 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.parse_int "3") uu____780 uu____807);
    (let uu____811 =
       let uu____812 =
         let uu____815 =
           let uu____818 =
             let uu____821 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             let uu____822 =
               let uu____825 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               [uu____825]  in
             uu____821 :: uu____822  in
           ff :: uu____818  in
         apply :: uu____815  in
       FStar_Tests_Util.app twice uu____812  in
     let uu____826 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.parse_int "4") uu____811 uu____826);
    (let uu____830 = minus one z  in run (Prims.parse_int "5") uu____830 one);
    (let uu____832 = FStar_Tests_Util.app pred [one]  in
     run (Prims.parse_int "6") uu____832 z);
    (let uu____834 = minus one one  in run (Prims.parse_int "7") uu____834 z);
    (let uu____836 = FStar_Tests_Util.app mul [one; one]  in
     run (Prims.parse_int "8") uu____836 one);
    (let uu____838 = FStar_Tests_Util.app mul [two; one]  in
     run (Prims.parse_int "9") uu____838 two);
    (let uu____840 =
       let uu____841 =
         let uu____844 = FStar_Tests_Util.app succ [one]  in [uu____844; one]
          in
       FStar_Tests_Util.app mul uu____841  in
     run (Prims.parse_int "10") uu____840 two);
    (let uu____846 =
       let uu____847 = encode (Prims.parse_int "10")  in
       let uu____848 = encode (Prims.parse_int "10")  in
       minus uu____847 uu____848  in
     run (Prims.parse_int "11") uu____846 z);
    (let uu____852 =
       let uu____853 = encode (Prims.parse_int "100")  in
       let uu____854 = encode (Prims.parse_int "100")  in
       minus uu____853 uu____854  in
     run (Prims.parse_int "12") uu____852 z);
    (let uu____858 =
       let uu____859 = encode (Prims.parse_int "100")  in
       let uu____860 =
         let uu____863 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____864 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____863 uu____864  in
       let_ FStar_Tests_Util.x uu____859 uu____860  in
     run (Prims.parse_int "13") uu____858 z);
    (let uu____868 =
       let uu____869 = FStar_Tests_Util.app succ [one]  in
       let uu____870 =
         let uu____873 =
           let uu____874 =
             let uu____877 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
             let uu____878 =
               let uu____881 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
               [uu____881]  in
             uu____877 :: uu____878  in
           FStar_Tests_Util.app mul uu____874  in
         let uu____882 =
           let uu____885 =
             let uu____886 =
               let uu____889 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
               let uu____890 =
                 let uu____893 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
                 [uu____893]  in
               uu____889 :: uu____890  in
             FStar_Tests_Util.app mul uu____886  in
           let uu____894 =
             let uu____897 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             let uu____898 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             minus uu____897 uu____898  in
           let_ FStar_Tests_Util.h uu____885 uu____894  in
         let_ FStar_Tests_Util.y uu____873 uu____882  in
       let_ FStar_Tests_Util.x uu____869 uu____870  in
     run (Prims.parse_int "14") uu____868 z);
    (let uu____902 =
       let uu____903 = FStar_Tests_Util.app succ [one]  in
       let uu____906 =
         let uu____907 =
           let uu____910 =
             let uu____913 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
             let uu____914 =
               let uu____917 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
               [uu____917]  in
             uu____913 :: uu____914  in
           FStar_Tests_Util.app mul uu____910  in
         let uu____918 =
           let uu____919 =
             let uu____922 =
               let uu____925 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
               let uu____926 =
                 let uu____929 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
                 [uu____929]  in
               uu____925 :: uu____926  in
             FStar_Tests_Util.app mul uu____922  in
           let uu____930 =
             let uu____931 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             let uu____932 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             minus uu____931 uu____932  in
           mk_let FStar_Tests_Util.h uu____919 uu____930  in
         mk_let FStar_Tests_Util.y uu____907 uu____918  in
       mk_let FStar_Tests_Util.x uu____903 uu____906  in
     run (Prims.parse_int "15") uu____902 z);
    (let uu____936 =
       let uu____937 = let uu____940 = snat znat  in snat uu____940  in
       pred_nat uu____937  in
     let uu____941 = snat znat  in
     run (Prims.parse_int "16") uu____936 uu____941);
    (let uu____945 =
       let uu____946 = let uu____947 = snat znat  in snat uu____947  in
       let uu____948 = snat znat  in minus_nat uu____946 uu____948  in
     let uu____949 = snat znat  in
     run (Prims.parse_int "17") uu____945 uu____949);
    (let uu____953 =
       let uu____954 = encode_nat (Prims.parse_int "100")  in
       let uu____955 = encode_nat (Prims.parse_int "100")  in
       minus_nat uu____954 uu____955  in
     run (Prims.parse_int "18") uu____953 znat);
    (let uu____957 =
       let uu____958 = encode_nat (Prims.parse_int "10000")  in
       let uu____959 = encode_nat (Prims.parse_int "10000")  in
       minus_nat uu____958 uu____959  in
     run (Prims.parse_int "19") uu____957 znat);
    (let uu____961 =
       let uu____962 = encode_nat (Prims.parse_int "10")  in
       let uu____963 = encode_nat (Prims.parse_int "10")  in
       minus_nat uu____962 uu____963  in
     run (Prims.parse_int "20") uu____961 znat);
    FStar_Options.__clear_unit_tests ();
    (let uu____966 = FStar_Tests_Pars.tc "recons [0;1]"  in
     let uu____967 = FStar_Tests_Pars.tc "[0;1]"  in
     run (Prims.parse_int "21") uu____966 uu____967);
    (let uu____971 = FStar_Tests_Pars.tc "copy [0;1]"  in
     let uu____972 = FStar_Tests_Pars.tc "[0;1]"  in
     run (Prims.parse_int "22") uu____971 uu____972);
    (let uu____976 = FStar_Tests_Pars.tc "rev [0;1;2;3;4;5;6;7;8;9;10]"  in
     let uu____977 = FStar_Tests_Pars.tc "[10;9;8;7;6;5;4;3;2;1;0]"  in
     run (Prims.parse_int "23") uu____976 uu____977);
    (let uu____981 = FStar_Tests_Pars.tc "f (B 5 3)"  in
     let uu____982 = FStar_Tests_Pars.tc "2"  in
     run (Prims.parse_int "1062") uu____981 uu____982);
    FStar_Util.print_string "Normalizer ok\n"
  