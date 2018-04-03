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
      (let uu____7 =
         let uu____10 = encode (n1 - (Prims.parse_int "1"))  in [uu____10]
          in
       FStar_Tests_Util.app succ uu____7)
  
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
        let uu____32 =
          let uu____35 = let uu____36 = b x1  in [uu____36]  in
          FStar_Syntax_Util.abs uu____35 e' FStar_Pervasives_Native.None  in
        FStar_Tests_Util.app uu____32 [e]
  
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
  let uu____64 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____64 FStar_Syntax_Syntax.Delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____65 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____65 FStar_Syntax_Syntax.Delta_constant
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
    let uu____78 =
      let uu____81 =
        let uu____82 =
          let uu____97 = tm_fv snat_l  in
          let uu____100 =
            let uu____103 = FStar_Syntax_Syntax.as_arg s  in [uu____103]  in
          (uu____97, uu____100)  in
        FStar_Syntax_Syntax.Tm_app uu____82  in
      FStar_Syntax_Syntax.mk uu____81  in
    uu____78 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____113 . 'Auu____113 -> 'Auu____113 FStar_Syntax_Syntax.withinfo_t =
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
      let uu____171 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____171, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____213 =
        let uu____216 =
          let uu____217 =
            let uu____230 =
              let uu____239 =
                let uu____246 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____246, false)  in
              [uu____239]  in
            (snat_l, uu____230)  in
          FStar_Syntax_Syntax.Pat_cons uu____217  in
        pat uu____216  in
      let uu____271 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___77_276 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___77_276.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___77_276.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____213, FStar_Pervasives_Native.None, uu____271)  in
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
        let uu____351 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____368 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____351, FStar_Pervasives_Native.None, uu____368)  in
      let sbranch =
        let uu____392 =
          let uu____395 =
            let uu____396 =
              let uu____409 =
                let uu____418 =
                  let uu____425 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____425, false)  in
                [uu____418]  in
              (snat_l, uu____409)  in
            FStar_Syntax_Syntax.Pat_cons uu____396  in
          pat uu____395  in
        let uu____450 =
          let uu____453 = FStar_Tests_Util.nm minus1  in
          let uu____456 =
            let uu____459 =
              let uu____462 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____462  in
            let uu____465 =
              let uu____470 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____470]  in
            uu____459 :: uu____465  in
          FStar_Tests_Util.app uu____453 uu____456  in
        (uu____392, FStar_Pervasives_Native.None, uu____450)  in
      let lb =
        let uu____484 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____485 =
          let uu____488 =
            let uu____489 =
              let uu____490 = b FStar_Tests_Util.x  in
              let uu____491 =
                let uu____494 = b FStar_Tests_Util.y  in [uu____494]  in
              uu____490 :: uu____491  in
            let uu____495 =
              let uu____496 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____496 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____489 uu____495
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____488
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____484;
          FStar_Syntax_Syntax.lbdef = uu____485;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____541 =
        let uu____544 =
          let uu____545 =
            let uu____558 =
              let uu____559 =
                let uu____560 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____560 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____559
               in
            ((true, [lb]), uu____558)  in
          FStar_Syntax_Syntax.Tm_let uu____545  in
        FStar_Syntax_Syntax.mk uu____544  in
      uu____541 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____585 = snat out  in
         aux uu____585 (n2 - (Prims.parse_int "1")))
       in
    aux znat n1
  
let (run :
  Prims.int ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        (let uu____596 = FStar_Util.string_of_int i  in
         FStar_Util.print1 "%s: ... \n" uu____596);
        (let tcenv = FStar_Tests_Pars.init ()  in
         (let uu____599 = FStar_Main.process_args ()  in
          FStar_All.pipe_right uu____599 FStar_Pervasives.ignore);
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
          (let uu____622 =
             let uu____623 = FStar_Syntax_Util.unascribe x1  in
             FStar_Tests_Util.term_eq uu____623 expected  in
           FStar_Tests_Util.always i uu____622)))
  
let (run_all : Prims.unit -> Prims.unit) =
  fun uu____626  ->
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
    (let uu____634 =
       let uu____635 =
         let uu____638 =
           let uu____641 =
             let uu____644 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____644]  in
           id :: uu____641  in
         one :: uu____638  in
       FStar_Tests_Util.app apply uu____635  in
     let uu____645 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     run (Prims.parse_int "0") uu____634 uu____645);
    (let uu____647 =
       let uu____648 =
         let uu____651 =
           let uu____654 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
           let uu____655 =
             let uu____658 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             [uu____658]  in
           uu____654 :: uu____655  in
         tt :: uu____651  in
       FStar_Tests_Util.app apply uu____648  in
     let uu____659 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     run (Prims.parse_int "1") uu____647 uu____659);
    (let uu____661 =
       let uu____662 =
         let uu____665 =
           let uu____668 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
           let uu____669 =
             let uu____672 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             [uu____672]  in
           uu____668 :: uu____669  in
         ff :: uu____665  in
       FStar_Tests_Util.app apply uu____662  in
     let uu____673 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.parse_int "2") uu____661 uu____673);
    (let uu____675 =
       let uu____676 =
         let uu____679 =
           let uu____682 =
             let uu____685 =
               let uu____688 =
                 let uu____691 =
                   let uu____694 =
                     let uu____697 = FStar_Tests_Util.nm FStar_Tests_Util.n
                        in
                     let uu____698 =
                       let uu____701 = FStar_Tests_Util.nm FStar_Tests_Util.m
                          in
                       [uu____701]  in
                     uu____697 :: uu____698  in
                   ff :: uu____694  in
                 apply :: uu____691  in
               apply :: uu____688  in
             apply :: uu____685  in
           apply :: uu____682  in
         apply :: uu____679  in
       FStar_Tests_Util.app apply uu____676  in
     let uu____702 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.parse_int "3") uu____675 uu____702);
    (let uu____704 =
       let uu____705 =
         let uu____708 =
           let uu____711 =
             let uu____714 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             let uu____715 =
               let uu____718 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               [uu____718]  in
             uu____714 :: uu____715  in
           ff :: uu____711  in
         apply :: uu____708  in
       FStar_Tests_Util.app twice uu____705  in
     let uu____719 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
     run (Prims.parse_int "4") uu____704 uu____719);
    (let uu____721 = minus one z  in run (Prims.parse_int "5") uu____721 one);
    (let uu____723 = FStar_Tests_Util.app pred [one]  in
     run (Prims.parse_int "6") uu____723 z);
    (let uu____725 = minus one one  in run (Prims.parse_int "7") uu____725 z);
    (let uu____727 = FStar_Tests_Util.app mul [one; one]  in
     run (Prims.parse_int "8") uu____727 one);
    (let uu____729 = FStar_Tests_Util.app mul [two; one]  in
     run (Prims.parse_int "9") uu____729 two);
    (let uu____731 =
       let uu____732 =
         let uu____735 = FStar_Tests_Util.app succ [one]  in [uu____735; one]
          in
       FStar_Tests_Util.app mul uu____732  in
     run (Prims.parse_int "10") uu____731 two);
    (let uu____741 =
       let uu____742 = encode (Prims.parse_int "10")  in
       let uu____743 = encode (Prims.parse_int "10")  in
       minus uu____742 uu____743  in
     run (Prims.parse_int "11") uu____741 z);
    (let uu____747 =
       let uu____748 = encode (Prims.parse_int "100")  in
       let uu____749 = encode (Prims.parse_int "100")  in
       minus uu____748 uu____749  in
     run (Prims.parse_int "12") uu____747 z);
    (let uu____753 =
       let uu____754 = encode (Prims.parse_int "100")  in
       let uu____755 =
         let uu____756 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____757 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____756 uu____757  in
       let_ FStar_Tests_Util.x uu____754 uu____755  in
     run (Prims.parse_int "13") uu____753 z);
    (let uu____761 =
       let uu____762 = FStar_Tests_Util.app succ [one]  in
       let uu____763 =
         let uu____764 =
           let uu____765 =
             let uu____768 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
             let uu____769 =
               let uu____772 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
               [uu____772]  in
             uu____768 :: uu____769  in
           FStar_Tests_Util.app mul uu____765  in
         let uu____773 =
           let uu____774 =
             let uu____775 =
               let uu____778 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
               let uu____779 =
                 let uu____782 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
                 [uu____782]  in
               uu____778 :: uu____779  in
             FStar_Tests_Util.app mul uu____775  in
           let uu____783 =
             let uu____784 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             let uu____785 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             minus uu____784 uu____785  in
           let_ FStar_Tests_Util.h uu____774 uu____783  in
         let_ FStar_Tests_Util.y uu____764 uu____773  in
       let_ FStar_Tests_Util.x uu____762 uu____763  in
     run (Prims.parse_int "14") uu____761 z);
    (let uu____789 =
       let uu____790 = FStar_Tests_Util.app succ [one]  in
       let uu____793 =
         let uu____794 =
           let uu____797 =
             let uu____800 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
             let uu____801 =
               let uu____804 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
               [uu____804]  in
             uu____800 :: uu____801  in
           FStar_Tests_Util.app mul uu____797  in
         let uu____805 =
           let uu____806 =
             let uu____809 =
               let uu____812 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
               let uu____813 =
                 let uu____816 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
                 [uu____816]  in
               uu____812 :: uu____813  in
             FStar_Tests_Util.app mul uu____809  in
           let uu____817 =
             let uu____818 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             let uu____819 = FStar_Tests_Util.nm FStar_Tests_Util.h  in
             minus uu____818 uu____819  in
           mk_let FStar_Tests_Util.h uu____806 uu____817  in
         mk_let FStar_Tests_Util.y uu____794 uu____805  in
       mk_let FStar_Tests_Util.x uu____790 uu____793  in
     run (Prims.parse_int "15") uu____789 z);
    (let uu____823 =
       let uu____824 = let uu____827 = snat znat  in snat uu____827  in
       pred_nat uu____824  in
     let uu____828 = snat znat  in
     run (Prims.parse_int "16") uu____823 uu____828);
    (let uu____830 =
       let uu____831 = let uu____832 = snat znat  in snat uu____832  in
       let uu____833 = snat znat  in minus_nat uu____831 uu____833  in
     let uu____834 = snat znat  in
     run (Prims.parse_int "17") uu____830 uu____834);
    (let uu____836 =
       let uu____837 = encode_nat (Prims.parse_int "100")  in
       let uu____838 = encode_nat (Prims.parse_int "100")  in
       minus_nat uu____837 uu____838  in
     run (Prims.parse_int "18") uu____836 znat);
    (let uu____840 =
       let uu____841 = encode_nat (Prims.parse_int "10000")  in
       let uu____842 = encode_nat (Prims.parse_int "10000")  in
       minus_nat uu____841 uu____842  in
     run (Prims.parse_int "19") uu____840 znat);
    (let uu____844 =
       let uu____845 = encode_nat (Prims.parse_int "10")  in
       let uu____846 = encode_nat (Prims.parse_int "10")  in
       minus_nat uu____845 uu____846  in
     run (Prims.parse_int "20") uu____844 znat);
    FStar_Options.__clear_unit_tests ();
    (let uu____849 = FStar_Tests_Pars.tc "recons [0;1]"  in
     let uu____850 = FStar_Tests_Pars.tc "[0;1]"  in
     run (Prims.parse_int "21") uu____849 uu____850);
    (let uu____852 = FStar_Tests_Pars.tc "copy [0;1]"  in
     let uu____853 = FStar_Tests_Pars.tc "[0;1]"  in
     run (Prims.parse_int "22") uu____852 uu____853);
    (let uu____855 = FStar_Tests_Pars.tc "rev [0;1;2;3;4;5;6;7;8;9;10]"  in
     let uu____856 = FStar_Tests_Pars.tc "[10;9;8;7;6;5;4;3;2;1;0]"  in
     run (Prims.parse_int "23") uu____855 uu____856);
    (let uu____858 = FStar_Tests_Pars.tc "f (B 5 3)"  in
     let uu____859 = FStar_Tests_Pars.tc "2"  in
     run (Prims.parse_int "1062") uu____858 uu____859);
    FStar_Util.print_string "Normalizer ok\n"
  