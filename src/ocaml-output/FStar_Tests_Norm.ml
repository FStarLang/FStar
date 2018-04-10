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
  FStar_Syntax_Syntax.lid_as_fv uu____86 FStar_Syntax_Syntax.Delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____87 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____87 FStar_Syntax_Syntax.Delta_constant
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
    let uu____104 =
      let uu____109 =
        let uu____110 =
          let uu____125 = tm_fv snat_l  in
          let uu____128 =
            let uu____131 = FStar_Syntax_Syntax.as_arg s  in [uu____131]  in
          (uu____125, uu____128)  in
        FStar_Syntax_Syntax.Tm_app uu____110  in
      FStar_Syntax_Syntax.mk uu____109  in
    uu____104 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
      let uu____208 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____208, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____250 =
        let uu____253 =
          let uu____254 =
            let uu____267 =
              let uu____276 =
                let uu____283 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____283, false)  in
              [uu____276]  in
            (snat_l, uu____267)  in
          FStar_Syntax_Syntax.Pat_cons uu____254  in
        pat uu____253  in
      let uu____308 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___77_313 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___77_313.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___77_313.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____250, FStar_Pervasives_Native.None, uu____308)  in
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
        let uu____392 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____409 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____392, FStar_Pervasives_Native.None, uu____409)  in
      let sbranch =
        let uu____433 =
          let uu____436 =
            let uu____437 =
              let uu____450 =
                let uu____459 =
                  let uu____466 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____466, false)  in
                [uu____459]  in
              (snat_l, uu____450)  in
            FStar_Syntax_Syntax.Pat_cons uu____437  in
          pat uu____436  in
        let uu____491 =
          let uu____494 = FStar_Tests_Util.nm minus1  in
          let uu____497 =
            let uu____500 =
              let uu____503 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____503  in
            let uu____506 =
              let uu____511 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____511]  in
            uu____500 :: uu____506  in
          FStar_Tests_Util.app uu____494 uu____497  in
        (uu____433, FStar_Pervasives_Native.None, uu____491)  in
      let lb =
        let uu____525 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____526 =
          let uu____529 =
            let uu____530 =
              let uu____531 = b FStar_Tests_Util.x  in
              let uu____532 =
                let uu____535 = b FStar_Tests_Util.y  in [uu____535]  in
              uu____531 :: uu____532  in
            let uu____536 =
              let uu____537 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____537 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____530 uu____536
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____529
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____525;
          FStar_Syntax_Syntax.lbdef = uu____526;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____582 =
        let uu____587 =
          let uu____588 =
            let uu____601 =
              let uu____602 =
                let uu____603 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____603 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____602
               in
            ((true, [lb]), uu____601)  in
          FStar_Syntax_Syntax.Tm_let uu____588  in
        FStar_Syntax_Syntax.mk uu____587  in
      uu____582 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____632 = snat out  in
         aux uu____632 (n2 - (Prims.parse_int "1")))
       in
    aux znat n1
  
let (run :
  Prims.int -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> unit)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let uu____648 =
          let uu____649 = FStar_Util.string_of_int i  in
          FStar_Util.print1 "%s: ... \n" uu____649  in
        let tcenv = FStar_Tests_Pars.init ()  in
        let uu____651 =
          let uu____652 = FStar_Main.process_args ()  in
          FStar_All.pipe_right uu____652 (fun a253  -> (Obj.magic ()) a253)
           in
        let x1 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.UnfoldUntil
              FStar_Syntax_Syntax.Delta_constant;
            FStar_TypeChecker_Normalize.Primops] tcenv r
           in
        let uu____666 = FStar_Options.init ()  in
        let uu____667 =
          FStar_Options.set_option "print_universes"
            (FStar_Options.Bool true)
           in
        let uu____668 =
          FStar_Options.set_option "print_implicits"
            (FStar_Options.Bool true)
           in
        let uu____669 =
          let uu____670 = FStar_Syntax_Util.unascribe x1  in
          FStar_Tests_Util.term_eq uu____670 expected  in
        FStar_Tests_Util.always i uu____669
  
let (run_all : unit -> unit) =
  fun uu____675  ->
    let uu____676 = FStar_Util.print_string "Testing the normalizer\n"  in
    let uu____677 =
      FStar_Tests_Pars.pars_and_tc_fragment
        "let rec copy (x:list int) : Tot (list int) = match x with | [] -> []  | hd::tl -> hd::copy tl"
       in
    let uu____678 =
      FStar_Tests_Pars.pars_and_tc_fragment
        "let recons (x:list int) : Tot (list int) = match x with | [] -> []  | hd::tl -> hd::tl"
       in
    let uu____679 =
      FStar_Tests_Pars.pars_and_tc_fragment
        "let rev (x:list 'a) : Tot (list 'a) = let rec aux (x:list 'a) (out:list 'a) : Tot (list 'a) = match x with | [] -> out | hd::tl -> aux tl (hd::out) in aux x []"
       in
    let uu____680 =
      FStar_Tests_Pars.pars_and_tc_fragment
        "type t = | A : int -> int -> t | B : int -> int -> t let f = function | A x y | B y x -> y - x"
       in
    let uu____681 = FStar_Options.__set_unit_tests ()  in
    let uu____682 =
      let uu____683 =
        let uu____684 =
          let uu____687 =
            let uu____690 =
              let uu____693 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____693]  in
            id :: uu____690  in
          one :: uu____687  in
        FStar_Tests_Util.app apply uu____684  in
      let uu____694 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
      run (Prims.parse_int "0") uu____683 uu____694  in
    let uu____695 =
      let uu____696 =
        let uu____697 =
          let uu____700 =
            let uu____703 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
            let uu____704 =
              let uu____707 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
              [uu____707]  in
            uu____703 :: uu____704  in
          tt :: uu____700  in
        FStar_Tests_Util.app apply uu____697  in
      let uu____708 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
      run (Prims.parse_int "1") uu____696 uu____708  in
    let uu____709 =
      let uu____710 =
        let uu____711 =
          let uu____714 =
            let uu____717 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
            let uu____718 =
              let uu____721 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
              [uu____721]  in
            uu____717 :: uu____718  in
          ff :: uu____714  in
        FStar_Tests_Util.app apply uu____711  in
      let uu____722 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
      run (Prims.parse_int "2") uu____710 uu____722  in
    let uu____723 =
      let uu____724 =
        let uu____725 =
          let uu____728 =
            let uu____731 =
              let uu____734 =
                let uu____737 =
                  let uu____740 =
                    let uu____743 =
                      let uu____746 = FStar_Tests_Util.nm FStar_Tests_Util.n
                         in
                      let uu____747 =
                        let uu____750 =
                          FStar_Tests_Util.nm FStar_Tests_Util.m  in
                        [uu____750]  in
                      uu____746 :: uu____747  in
                    ff :: uu____743  in
                  apply :: uu____740  in
                apply :: uu____737  in
              apply :: uu____734  in
            apply :: uu____731  in
          apply :: uu____728  in
        FStar_Tests_Util.app apply uu____725  in
      let uu____751 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
      run (Prims.parse_int "3") uu____724 uu____751  in
    let uu____752 =
      let uu____753 =
        let uu____754 =
          let uu____757 =
            let uu____760 =
              let uu____763 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              let uu____764 =
                let uu____767 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                [uu____767]  in
              uu____763 :: uu____764  in
            ff :: uu____760  in
          apply :: uu____757  in
        FStar_Tests_Util.app twice uu____754  in
      let uu____768 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
      run (Prims.parse_int "4") uu____753 uu____768  in
    let uu____769 =
      let uu____770 = minus one z  in run (Prims.parse_int "5") uu____770 one
       in
    let uu____771 =
      let uu____772 = FStar_Tests_Util.app pred [one]  in
      run (Prims.parse_int "6") uu____772 z  in
    let uu____773 =
      let uu____774 = minus one one  in run (Prims.parse_int "7") uu____774 z
       in
    let uu____775 =
      let uu____776 = FStar_Tests_Util.app mul [one; one]  in
      run (Prims.parse_int "8") uu____776 one  in
    let uu____777 =
      let uu____778 = FStar_Tests_Util.app mul [two; one]  in
      run (Prims.parse_int "9") uu____778 two  in
    let uu____779 =
      let uu____780 =
        let uu____781 =
          let uu____784 = FStar_Tests_Util.app succ [one]  in
          [uu____784; one]  in
        FStar_Tests_Util.app mul uu____781  in
      run (Prims.parse_int "10") uu____780 two  in
    let uu____789 =
      let uu____790 =
        let uu____791 = encode (Prims.parse_int "10")  in
        let uu____792 = encode (Prims.parse_int "10")  in
        minus uu____791 uu____792  in
      run (Prims.parse_int "11") uu____790 z  in
    let uu____795 =
      let uu____796 =
        let uu____797 = encode (Prims.parse_int "100")  in
        let uu____798 = encode (Prims.parse_int "100")  in
        minus uu____797 uu____798  in
      run (Prims.parse_int "12") uu____796 z  in
    let uu____801 =
      let uu____802 =
        let uu____803 = encode (Prims.parse_int "100")  in
        let uu____804 =
          let uu____805 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
          let uu____806 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
          minus uu____805 uu____806  in
        let_ FStar_Tests_Util.x uu____803 uu____804  in
      run (Prims.parse_int "13") uu____802 z  in
    let uu____809 =
      let uu____810 =
        let uu____811 = FStar_Tests_Util.app succ [one]  in
        let uu____812 =
          let uu____813 =
            let uu____814 =
              let uu____817 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              let uu____818 =
                let uu____821 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
                [uu____821]  in
              uu____817 :: uu____818  in
            FStar_Tests_Util.app mul uu____814  in
          let uu____822 =
            let uu____823 =
              let uu____824 =
                let uu____827 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
                let uu____828 =
                  let uu____831 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
                  [uu____831]  in
                uu____827 :: uu____828  in
              FStar_Tests_Util.app mul uu____824  in
            let uu____832 =
              let uu____833 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
              let uu____834 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
              minus uu____833 uu____834  in
            let_ FStar_Tests_Util.h uu____823 uu____832  in
          let_ FStar_Tests_Util.y uu____813 uu____822  in
        let_ FStar_Tests_Util.x uu____811 uu____812  in
      run (Prims.parse_int "14") uu____810 z  in
    let uu____837 =
      let uu____838 =
        let uu____839 = FStar_Tests_Util.app succ [one]  in
        let uu____842 =
          let uu____843 =
            let uu____846 =
              let uu____849 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              let uu____850 =
                let uu____853 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
                [uu____853]  in
              uu____849 :: uu____850  in
            FStar_Tests_Util.app mul uu____846  in
          let uu____854 =
            let uu____855 =
              let uu____858 =
                let uu____861 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
                let uu____862 =
                  let uu____865 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
                  [uu____865]  in
                uu____861 :: uu____862  in
              FStar_Tests_Util.app mul uu____858  in
            let uu____866 =
              let uu____867 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
              let uu____868 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
              minus uu____867 uu____868  in
            mk_let FStar_Tests_Util.h uu____855 uu____866  in
          mk_let FStar_Tests_Util.y uu____843 uu____854  in
        mk_let FStar_Tests_Util.x uu____839 uu____842  in
      run (Prims.parse_int "15") uu____838 z  in
    let uu____871 =
      let uu____872 =
        let uu____873 = let uu____876 = snat znat  in snat uu____876  in
        pred_nat uu____873  in
      let uu____877 = snat znat  in
      run (Prims.parse_int "16") uu____872 uu____877  in
    let uu____878 =
      let uu____879 =
        let uu____880 = let uu____881 = snat znat  in snat uu____881  in
        let uu____882 = snat znat  in minus_nat uu____880 uu____882  in
      let uu____883 = snat znat  in
      run (Prims.parse_int "17") uu____879 uu____883  in
    let uu____884 =
      let uu____885 =
        let uu____886 = encode_nat (Prims.parse_int "100")  in
        let uu____887 = encode_nat (Prims.parse_int "100")  in
        minus_nat uu____886 uu____887  in
      run (Prims.parse_int "18") uu____885 znat  in
    let uu____888 =
      let uu____889 =
        let uu____890 = encode_nat (Prims.parse_int "10000")  in
        let uu____891 = encode_nat (Prims.parse_int "10000")  in
        minus_nat uu____890 uu____891  in
      run (Prims.parse_int "19") uu____889 znat  in
    let uu____892 =
      let uu____893 =
        let uu____894 = encode_nat (Prims.parse_int "10")  in
        let uu____895 = encode_nat (Prims.parse_int "10")  in
        minus_nat uu____894 uu____895  in
      run (Prims.parse_int "20") uu____893 znat  in
    let uu____896 = FStar_Options.__clear_unit_tests ()  in
    let uu____897 =
      let uu____898 = FStar_Tests_Pars.tc "recons [0;1]"  in
      let uu____899 = FStar_Tests_Pars.tc "[0;1]"  in
      run (Prims.parse_int "21") uu____898 uu____899  in
    let uu____900 =
      let uu____901 = FStar_Tests_Pars.tc "copy [0;1]"  in
      let uu____902 = FStar_Tests_Pars.tc "[0;1]"  in
      run (Prims.parse_int "22") uu____901 uu____902  in
    let uu____903 =
      let uu____904 = FStar_Tests_Pars.tc "rev [0;1;2;3;4;5;6;7;8;9;10]"  in
      let uu____905 = FStar_Tests_Pars.tc "[10;9;8;7;6;5;4;3;2;1;0]"  in
      run (Prims.parse_int "23") uu____904 uu____905  in
    let uu____906 =
      let uu____907 = FStar_Tests_Pars.tc "f (B 5 3)"  in
      let uu____908 = FStar_Tests_Pars.tc "2"  in
      run (Prims.parse_int "1062") uu____907 uu____908  in
    FStar_Util.print_string "Normalizer ok\n"
  