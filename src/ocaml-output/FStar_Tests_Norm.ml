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
      (let uu____83356 =
         let uu____83359 = encode (n1 - (Prims.parse_int "1"))  in
         [uu____83359]  in
       FStar_Tests_Util.app succ uu____83356)
  
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
        let uu____83398 =
          let uu____83401 = let uu____83402 = b x1  in [uu____83402]  in
          FStar_Syntax_Util.abs uu____83401 e' FStar_Pervasives_Native.None
           in
        FStar_Tests_Util.app uu____83398 [e]
  
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
  fun x1  -> FStar_Ident.lid_of_path ["Test"; x1] FStar_Range.dummyRange 
let (znat_l : FStar_Syntax_Syntax.fv) =
  let uu____83472 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____83472
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____83475 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____83475
    FStar_Syntax_Syntax.delta_constant
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
    let uu____83494 =
      let uu____83501 =
        let uu____83502 =
          let uu____83519 = tm_fv snat_l  in
          let uu____83522 =
            let uu____83533 = FStar_Syntax_Syntax.as_arg s  in [uu____83533]
             in
          (uu____83519, uu____83522)  in
        FStar_Syntax_Syntax.Tm_app uu____83502  in
      FStar_Syntax_Syntax.mk uu____83501  in
    uu____83494 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____83578 .
    'Auu____83578 -> 'Auu____83578 FStar_Syntax_Syntax.withinfo_t
  = fun p  -> FStar_Syntax_Syntax.withinfo p FStar_Range.dummyRange 
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
      let uu____83687 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____83687, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____83731 =
        let uu____83734 =
          let uu____83735 =
            let uu____83749 =
              let uu____83759 =
                let uu____83767 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____83767, false)  in
              [uu____83759]  in
            (snat_l, uu____83749)  in
          FStar_Syntax_Syntax.Pat_cons uu____83735  in
        pat uu____83734  in
      let uu____83797 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___763_83802 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___763_83802.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___763_83802.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____83731, FStar_Pervasives_Native.None, uu____83797)  in
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
        let uu____83843 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____83862 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____83843, FStar_Pervasives_Native.None, uu____83862)  in
      let sbranch =
        let uu____83890 =
          let uu____83893 =
            let uu____83894 =
              let uu____83908 =
                let uu____83918 =
                  let uu____83926 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____83926, false)  in
                [uu____83918]  in
              (snat_l, uu____83908)  in
            FStar_Syntax_Syntax.Pat_cons uu____83894  in
          pat uu____83893  in
        let uu____83956 =
          let uu____83959 = FStar_Tests_Util.nm minus1  in
          let uu____83962 =
            let uu____83965 =
              let uu____83966 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____83966  in
            let uu____83969 =
              let uu____83972 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____83972]  in
            uu____83965 :: uu____83969  in
          FStar_Tests_Util.app uu____83959 uu____83962  in
        (uu____83890, FStar_Pervasives_Native.None, uu____83956)  in
      let lb =
        let uu____83984 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____83988 =
          let uu____83991 =
            let uu____83992 =
              let uu____83993 = b FStar_Tests_Util.x  in
              let uu____84000 =
                let uu____84009 = b FStar_Tests_Util.y  in [uu____84009]  in
              uu____83993 :: uu____84000  in
            let uu____84034 =
              let uu____84037 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____84037 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____83992 uu____84034
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____83991
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____83984;
          FStar_Syntax_Syntax.lbdef = uu____83988;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____84044 =
        let uu____84051 =
          let uu____84052 =
            let uu____84066 =
              let uu____84069 =
                let uu____84070 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____84070 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____84069
               in
            ((true, [lb]), uu____84066)  in
          FStar_Syntax_Syntax.Tm_let uu____84052  in
        FStar_Syntax_Syntax.mk uu____84051  in
      uu____84044 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____84117 = snat out  in
         aux uu____84117 (n2 - (Prims.parse_int "1")))
       in
    aux znat n1
  
let (tests :
  (Prims.int * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list)
  =
  FStar_Tests_Pars.pars_and_tc_fragment
    "let rec copy (x:list int) : Tot (list int) = match x with | [] -> []  | hd::tl -> hd::copy tl";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let recons (x:list 'a) : Tot (list 'a) = match x with | [] -> []  | hd::tl -> hd::tl";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let rev (x:list 'a) : Tot (list 'a) = let rec aux (x:list 'a) (out:list 'a) : Tot (list 'a) = match x with | [] -> out | hd::tl -> aux tl (hd::out) in aux x []";
  FStar_Tests_Pars.pars_and_tc_fragment
    "type t = | A : int -> int -> t | B : int -> int -> t let f = function | A x y | B y x -> y - x";
  FStar_Tests_Pars.pars_and_tc_fragment "type snat = | Z | S : snat -> snat";
  FStar_Tests_Pars.pars_and_tc_fragment "type tb = | T | F";
  FStar_Tests_Pars.pars_and_tc_fragment "type rb = | A1 | A2 | A3";
  FStar_Tests_Pars.pars_and_tc_fragment "type hb = | H : tb -> hb";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let select (i:tb) (x:'a) (y:'a) : Tot 'a = match i with | T -> x | F -> y";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let select_int3 (i:int) (x:'a) (y:'a) (z:'a) : Tot 'a = match i with | 0 -> x | 1 -> y | _ -> z";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let select_bool (b:bool) (x:'a) (y:'a) : Tot 'a = if b then x else y";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let select_string3 (s:string) (x:'a) (y:'a) (z:'a) : Tot 'a = match s with | \"abc\" -> x | \"def\" -> y | _ -> z";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let recons_m (x:list tb) = match x with | [] -> []  | hd::tl -> hd::tl";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let rec copy_tb_list_2 (x:list tb) : Tot (list tb) = match x with | [] -> []  | [hd] -> [hd]\n                                          | hd1::hd2::tl -> hd1::hd2::copy_tb_list_2 tl";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let rec copy_list_2 (x:list 'a) : Tot (list 'a) = match x with | [] -> []  | [hd] -> [hd]\n                                          | hd1::hd2::tl -> hd1::hd2::copy_list_2 tl";
  FStar_Tests_Pars.pars_and_tc_fragment "let (x1:int{x1>3}) = 6";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let (x2:int{x2+1>3 /\\ not (x2-5>0)}) = 2";
  FStar_Tests_Pars.pars_and_tc_fragment "let my_plus (x:int) (y:int) = x + y";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let (x3:int{forall (a:nat). a > x2}) = 7";
  FStar_Tests_Pars.pars_and_tc_fragment "let idd (x: 'a) = x";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let revtb (x: tb) = match x with | T -> F | F -> T";
  FStar_Tests_Pars.pars_and_tc_fragment "let id_tb (x: tb) = x";
  FStar_Tests_Pars.pars_and_tc_fragment "let fst_a (x: 'a) (y: 'a) = x";
  FStar_Tests_Pars.pars_and_tc_fragment "let id_list (x: list 'a) = x";
  FStar_Tests_Pars.pars_and_tc_fragment "let id_list_m (x: list tb) = x";
  (let uu____84183 =
     let uu____84195 =
       let uu____84198 =
         let uu____84201 =
           let uu____84204 =
             let uu____84207 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____84207]  in
           id :: uu____84204  in
         one :: uu____84201  in
       FStar_Tests_Util.app apply uu____84198  in
     let uu____84208 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____84195, uu____84208)  in
   let uu____84217 =
     let uu____84231 =
       let uu____84243 =
         let uu____84246 =
           let uu____84249 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____84249]  in
         FStar_Tests_Util.app id uu____84246  in
       let uu____84250 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____84243, uu____84250)  in
     let uu____84259 =
       let uu____84273 =
         let uu____84285 =
           let uu____84288 =
             let uu____84291 =
               let uu____84294 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____84295 =
                 let uu____84298 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____84298]  in
               uu____84294 :: uu____84295  in
             tt :: uu____84291  in
           FStar_Tests_Util.app apply uu____84288  in
         let uu____84299 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____84285, uu____84299)  in
       let uu____84308 =
         let uu____84322 =
           let uu____84334 =
             let uu____84337 =
               let uu____84340 =
                 let uu____84343 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____84344 =
                   let uu____84347 = FStar_Tests_Util.nm FStar_Tests_Util.m
                      in
                   [uu____84347]  in
                 uu____84343 :: uu____84344  in
               ff :: uu____84340  in
             FStar_Tests_Util.app apply uu____84337  in
           let uu____84348 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____84334, uu____84348)  in
         let uu____84357 =
           let uu____84371 =
             let uu____84383 =
               let uu____84386 =
                 let uu____84389 =
                   let uu____84392 =
                     let uu____84395 =
                       let uu____84398 =
                         let uu____84401 =
                           let uu____84404 =
                             let uu____84407 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____84408 =
                               let uu____84411 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____84411]  in
                             uu____84407 :: uu____84408  in
                           ff :: uu____84404  in
                         apply :: uu____84401  in
                       apply :: uu____84398  in
                     apply :: uu____84395  in
                   apply :: uu____84392  in
                 apply :: uu____84389  in
               FStar_Tests_Util.app apply uu____84386  in
             let uu____84412 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____84383, uu____84412)  in
           let uu____84421 =
             let uu____84435 =
               let uu____84447 =
                 let uu____84450 =
                   let uu____84453 =
                     let uu____84456 =
                       let uu____84459 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n  in
                       let uu____84460 =
                         let uu____84463 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____84463]  in
                       uu____84459 :: uu____84460  in
                     ff :: uu____84456  in
                   apply :: uu____84453  in
                 FStar_Tests_Util.app twice uu____84450  in
               let uu____84464 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____84447, uu____84464)  in
             let uu____84473 =
               let uu____84487 =
                 let uu____84499 = minus one z  in
                 ((Prims.parse_int "5"), uu____84499, one)  in
               let uu____84508 =
                 let uu____84522 =
                   let uu____84534 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____84534, z)  in
                 let uu____84543 =
                   let uu____84557 =
                     let uu____84569 = minus one one  in
                     ((Prims.parse_int "7"), uu____84569, z)  in
                   let uu____84578 =
                     let uu____84592 =
                       let uu____84604 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____84604, one)  in
                     let uu____84613 =
                       let uu____84627 =
                         let uu____84639 =
                           FStar_Tests_Util.app mul [two; one]  in
                         ((Prims.parse_int "9"), uu____84639, two)  in
                       let uu____84648 =
                         let uu____84662 =
                           let uu____84674 =
                             let uu____84677 =
                               let uu____84680 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____84680; one]  in
                             FStar_Tests_Util.app mul uu____84677  in
                           ((Prims.parse_int "10"), uu____84674, two)  in
                         let uu____84687 =
                           let uu____84701 =
                             let uu____84713 =
                               let uu____84716 =
                                 encode (Prims.parse_int "10")  in
                               let uu____84718 =
                                 encode (Prims.parse_int "10")  in
                               minus uu____84716 uu____84718  in
                             ((Prims.parse_int "11"), uu____84713, z)  in
                           let uu____84728 =
                             let uu____84742 =
                               let uu____84754 =
                                 let uu____84757 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____84759 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____84757 uu____84759  in
                               ((Prims.parse_int "12"), uu____84754, z)  in
                             let uu____84769 =
                               let uu____84783 =
                                 let uu____84795 =
                                   let uu____84798 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____84800 =
                                     let uu____84803 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____84804 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____84803 uu____84804  in
                                   let_ FStar_Tests_Util.x uu____84798
                                     uu____84800
                                    in
                                 ((Prims.parse_int "13"), uu____84795, z)  in
                               let uu____84813 =
                                 let uu____84827 =
                                   let uu____84839 =
                                     let uu____84842 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____84843 =
                                       let uu____84846 =
                                         let uu____84847 =
                                           let uu____84850 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____84851 =
                                             let uu____84854 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____84854]  in
                                           uu____84850 :: uu____84851  in
                                         FStar_Tests_Util.app mul uu____84847
                                          in
                                       let uu____84855 =
                                         let uu____84858 =
                                           let uu____84859 =
                                             let uu____84862 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____84863 =
                                               let uu____84866 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____84866]  in
                                             uu____84862 :: uu____84863  in
                                           FStar_Tests_Util.app mul
                                             uu____84859
                                            in
                                         let uu____84867 =
                                           let uu____84870 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____84871 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____84870 uu____84871  in
                                         let_ FStar_Tests_Util.h uu____84858
                                           uu____84867
                                          in
                                       let_ FStar_Tests_Util.y uu____84846
                                         uu____84855
                                        in
                                     let_ FStar_Tests_Util.x uu____84842
                                       uu____84843
                                      in
                                   ((Prims.parse_int "15"), uu____84839, z)
                                    in
                                 let uu____84880 =
                                   let uu____84894 =
                                     let uu____84906 =
                                       let uu____84909 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____84912 =
                                         let uu____84913 =
                                           let uu____84916 =
                                             let uu____84919 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____84920 =
                                               let uu____84923 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____84923]  in
                                             uu____84919 :: uu____84920  in
                                           FStar_Tests_Util.app mul
                                             uu____84916
                                            in
                                         let uu____84924 =
                                           let uu____84925 =
                                             let uu____84928 =
                                               let uu____84931 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____84932 =
                                                 let uu____84935 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____84935]  in
                                               uu____84931 :: uu____84932  in
                                             FStar_Tests_Util.app mul
                                               uu____84928
                                              in
                                           let uu____84936 =
                                             let uu____84937 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____84938 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____84937 uu____84938
                                              in
                                           mk_let FStar_Tests_Util.h
                                             uu____84925 uu____84936
                                            in
                                         mk_let FStar_Tests_Util.y
                                           uu____84913 uu____84924
                                          in
                                       mk_let FStar_Tests_Util.x uu____84909
                                         uu____84912
                                        in
                                     ((Prims.parse_int "16"), uu____84906, z)
                                      in
                                   let uu____84947 =
                                     let uu____84961 =
                                       let uu____84973 =
                                         let uu____84976 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____84977 =
                                           let uu____84980 =
                                             let uu____84981 =
                                               let uu____84984 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____84985 =
                                                 let uu____84988 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____84988]  in
                                               uu____84984 :: uu____84985  in
                                             FStar_Tests_Util.app mul
                                               uu____84981
                                              in
                                           let uu____84989 =
                                             let uu____84992 =
                                               let uu____84993 =
                                                 let uu____84996 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____84997 =
                                                   let uu____85000 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____85000]  in
                                                 uu____84996 :: uu____84997
                                                  in
                                               FStar_Tests_Util.app mul
                                                 uu____84993
                                                in
                                             let uu____85001 =
                                               let uu____85004 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____85005 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____85004 uu____85005
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____84992 uu____85001
                                              in
                                           let_ FStar_Tests_Util.y
                                             uu____84980 uu____84989
                                            in
                                         let_ FStar_Tests_Util.x uu____84976
                                           uu____84977
                                          in
                                       ((Prims.parse_int "17"), uu____84973,
                                         z)
                                        in
                                     let uu____85014 =
                                       let uu____85028 =
                                         let uu____85040 =
                                           let uu____85043 =
                                             let uu____85046 = snat znat  in
                                             snat uu____85046  in
                                           pred_nat uu____85043  in
                                         let uu____85047 = snat znat  in
                                         ((Prims.parse_int "18"),
                                           uu____85040, uu____85047)
                                          in
                                       let uu____85056 =
                                         let uu____85070 =
                                           let uu____85082 =
                                             let uu____85085 =
                                               let uu____85086 =
                                                 let uu____85087 = snat znat
                                                    in
                                                 snat uu____85087  in
                                               let uu____85088 = snat znat
                                                  in
                                               minus_nat uu____85086
                                                 uu____85088
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____85085
                                              in
                                           let uu____85089 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____85082, uu____85089)
                                            in
                                         let uu____85098 =
                                           let uu____85112 =
                                             let uu____85124 =
                                               let uu____85127 =
                                                 let uu____85128 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 let uu____85130 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 minus_nat uu____85128
                                                   uu____85130
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____85127
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____85124, znat)
                                              in
                                           let uu____85138 =
                                             let uu____85152 =
                                               let uu____85164 =
                                                 let uu____85167 =
                                                   let uu____85168 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   let uu____85170 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   minus_nat uu____85168
                                                     uu____85170
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____85167
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____85164, znat)
                                                in
                                             let uu____85178 =
                                               let uu____85192 =
                                                 let uu____85204 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____85208 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____85204, uu____85208)
                                                  in
                                               let uu____85218 =
                                                 let uu____85232 =
                                                   let uu____85244 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____85248 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____85244,
                                                     uu____85248)
                                                    in
                                                 let uu____85258 =
                                                   let uu____85272 =
                                                     let uu____85284 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____85288 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____85284,
                                                       uu____85288)
                                                      in
                                                   let uu____85298 =
                                                     let uu____85312 =
                                                       let uu____85324 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____85328 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____85324,
                                                         uu____85328)
                                                        in
                                                     let uu____85338 =
                                                       let uu____85352 =
                                                         let uu____85364 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____85368 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____85364,
                                                           uu____85368)
                                                          in
                                                       let uu____85378 =
                                                         let uu____85392 =
                                                           let uu____85404 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____85408 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____85404,
                                                             uu____85408)
                                                            in
                                                         let uu____85418 =
                                                           let uu____85432 =
                                                             let uu____85444
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____85448
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____85444,
                                                               uu____85448)
                                                              in
                                                           let uu____85458 =
                                                             let uu____85472
                                                               =
                                                               let uu____85484
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____85488
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____85484,
                                                                 uu____85488)
                                                                in
                                                             let uu____85498
                                                               =
                                                               let uu____85512
                                                                 =
                                                                 let uu____85524
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____85528
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____85524,
                                                                   uu____85528)
                                                                  in
                                                               let uu____85538
                                                                 =
                                                                 let uu____85552
                                                                   =
                                                                   let uu____85564
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____85568
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____85564,
                                                                    uu____85568)
                                                                    in
                                                                 let uu____85578
                                                                   =
                                                                   let uu____85592
                                                                    =
                                                                    let uu____85604
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____85608
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____85604,
                                                                    uu____85608)
                                                                     in
                                                                   let uu____85618
                                                                    =
                                                                    let uu____85632
                                                                    =
                                                                    let uu____85644
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____85648
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____85644,
                                                                    uu____85648)
                                                                     in
                                                                    let uu____85658
                                                                    =
                                                                    let uu____85672
                                                                    =
                                                                    let uu____85684
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____85688
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____85684,
                                                                    uu____85688)
                                                                     in
                                                                    let uu____85698
                                                                    =
                                                                    let uu____85712
                                                                    =
                                                                    let uu____85724
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____85728
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____85724,
                                                                    uu____85728)
                                                                     in
                                                                    let uu____85738
                                                                    =
                                                                    let uu____85752
                                                                    =
                                                                    let uu____85764
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____85768
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____85764,
                                                                    uu____85768)
                                                                     in
                                                                    let uu____85778
                                                                    =
                                                                    let uu____85792
                                                                    =
                                                                    let uu____85804
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____85808
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____85804,
                                                                    uu____85808)
                                                                     in
                                                                    let uu____85818
                                                                    =
                                                                    let uu____85832
                                                                    =
                                                                    let uu____85844
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____85848
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____85844,
                                                                    uu____85848)
                                                                     in
                                                                    let uu____85858
                                                                    =
                                                                    let uu____85872
                                                                    =
                                                                    let uu____85884
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____85888
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____85884,
                                                                    uu____85888)
                                                                     in
                                                                    let uu____85898
                                                                    =
                                                                    let uu____85912
                                                                    =
                                                                    let uu____85924
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____85928
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____85924,
                                                                    uu____85928)
                                                                     in
                                                                    let uu____85938
                                                                    =
                                                                    let uu____85952
                                                                    =
                                                                    let uu____85964
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____85968
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____85964,
                                                                    uu____85968)
                                                                     in
                                                                    let uu____85978
                                                                    =
                                                                    let uu____85992
                                                                    =
                                                                    let uu____86004
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____86008
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____86004,
                                                                    uu____86008)
                                                                     in
                                                                    let uu____86018
                                                                    =
                                                                    let uu____86032
                                                                    =
                                                                    let uu____86044
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____86048
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____86044,
                                                                    uu____86048)
                                                                     in
                                                                    let uu____86058
                                                                    =
                                                                    let uu____86072
                                                                    =
                                                                    let uu____86084
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____86088
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____86084,
                                                                    uu____86088)
                                                                     in
                                                                    let uu____86098
                                                                    =
                                                                    let uu____86112
                                                                    =
                                                                    let uu____86124
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____86128
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____86124,
                                                                    uu____86128)
                                                                     in
                                                                    let uu____86138
                                                                    =
                                                                    let uu____86152
                                                                    =
                                                                    let uu____86164
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____86168
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____86164,
                                                                    uu____86168)
                                                                     in
                                                                    let uu____86178
                                                                    =
                                                                    let uu____86192
                                                                    =
                                                                    let uu____86204
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____86208
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____86204,
                                                                    uu____86208)
                                                                     in
                                                                    let uu____86218
                                                                    =
                                                                    let uu____86232
                                                                    =
                                                                    let uu____86244
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____86248
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____86244,
                                                                    uu____86248)
                                                                     in
                                                                    let uu____86258
                                                                    =
                                                                    let uu____86272
                                                                    =
                                                                    let uu____86284
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____86288
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____86284,
                                                                    uu____86288)
                                                                     in
                                                                    let uu____86298
                                                                    =
                                                                    let uu____86312
                                                                    =
                                                                    let uu____86324
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____86328
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____86324,
                                                                    uu____86328)
                                                                     in
                                                                    let uu____86338
                                                                    =
                                                                    let uu____86352
                                                                    =
                                                                    let uu____86364
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____86368
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____86364,
                                                                    uu____86368)
                                                                     in
                                                                    let uu____86378
                                                                    =
                                                                    let uu____86392
                                                                    =
                                                                    let uu____86404
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____86408
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____86404,
                                                                    uu____86408)
                                                                     in
                                                                    let uu____86418
                                                                    =
                                                                    let uu____86432
                                                                    =
                                                                    let uu____86444
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____86448
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____86444,
                                                                    uu____86448)
                                                                     in
                                                                    let uu____86458
                                                                    =
                                                                    let uu____86472
                                                                    =
                                                                    let uu____86484
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____86488
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____86484,
                                                                    uu____86488)
                                                                     in
                                                                    let uu____86498
                                                                    =
                                                                    let uu____86512
                                                                    =
                                                                    let uu____86524
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____86528
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____86524,
                                                                    uu____86528)
                                                                     in
                                                                    [uu____86512]
                                                                     in
                                                                    uu____86472
                                                                    ::
                                                                    uu____86498
                                                                     in
                                                                    uu____86432
                                                                    ::
                                                                    uu____86458
                                                                     in
                                                                    uu____86392
                                                                    ::
                                                                    uu____86418
                                                                     in
                                                                    uu____86352
                                                                    ::
                                                                    uu____86378
                                                                     in
                                                                    uu____86312
                                                                    ::
                                                                    uu____86338
                                                                     in
                                                                    uu____86272
                                                                    ::
                                                                    uu____86298
                                                                     in
                                                                    uu____86232
                                                                    ::
                                                                    uu____86258
                                                                     in
                                                                    uu____86192
                                                                    ::
                                                                    uu____86218
                                                                     in
                                                                    uu____86152
                                                                    ::
                                                                    uu____86178
                                                                     in
                                                                    uu____86112
                                                                    ::
                                                                    uu____86138
                                                                     in
                                                                    uu____86072
                                                                    ::
                                                                    uu____86098
                                                                     in
                                                                    uu____86032
                                                                    ::
                                                                    uu____86058
                                                                     in
                                                                    uu____85992
                                                                    ::
                                                                    uu____86018
                                                                     in
                                                                    uu____85952
                                                                    ::
                                                                    uu____85978
                                                                     in
                                                                    uu____85912
                                                                    ::
                                                                    uu____85938
                                                                     in
                                                                    uu____85872
                                                                    ::
                                                                    uu____85898
                                                                     in
                                                                    uu____85832
                                                                    ::
                                                                    uu____85858
                                                                     in
                                                                    uu____85792
                                                                    ::
                                                                    uu____85818
                                                                     in
                                                                    uu____85752
                                                                    ::
                                                                    uu____85778
                                                                     in
                                                                    uu____85712
                                                                    ::
                                                                    uu____85738
                                                                     in
                                                                    uu____85672
                                                                    ::
                                                                    uu____85698
                                                                     in
                                                                    uu____85632
                                                                    ::
                                                                    uu____85658
                                                                     in
                                                                   uu____85592
                                                                    ::
                                                                    uu____85618
                                                                    in
                                                                 uu____85552
                                                                   ::
                                                                   uu____85578
                                                                  in
                                                               uu____85512 ::
                                                                 uu____85538
                                                                in
                                                             uu____85472 ::
                                                               uu____85498
                                                              in
                                                           uu____85432 ::
                                                             uu____85458
                                                            in
                                                         uu____85392 ::
                                                           uu____85418
                                                          in
                                                       uu____85352 ::
                                                         uu____85378
                                                        in
                                                     uu____85312 ::
                                                       uu____85338
                                                      in
                                                   uu____85272 :: uu____85298
                                                    in
                                                 uu____85232 :: uu____85258
                                                  in
                                               uu____85192 :: uu____85218  in
                                             uu____85152 :: uu____85178  in
                                           uu____85112 :: uu____85138  in
                                         uu____85070 :: uu____85098  in
                                       uu____85028 :: uu____85056  in
                                     uu____84961 :: uu____85014  in
                                   uu____84894 :: uu____84947  in
                                 uu____84827 :: uu____84880  in
                               uu____84783 :: uu____84813  in
                             uu____84742 :: uu____84769  in
                           uu____84701 :: uu____84728  in
                         uu____84662 :: uu____84687  in
                       uu____84627 :: uu____84648  in
                     uu____84592 :: uu____84613  in
                   uu____84557 :: uu____84578  in
                 uu____84522 :: uu____84543  in
               uu____84487 :: uu____84508  in
             uu____84435 :: uu____84473  in
           uu____84371 :: uu____84421  in
         uu____84322 :: uu____84357  in
       uu____84273 :: uu____84308  in
     uu____84231 :: uu____84259  in
   uu____84183 :: uu____84217)
  
let run_either :
  'Auu____87176 .
    Prims.int ->
      'Auu____87176 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____87176 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____87214 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____87214);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____87219 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____87219 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____87242 =
               let uu____87244 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____87244 expected  in
             FStar_Tests_Util.always i uu____87242)))
  
let (run_interpreter :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        run_either i r expected
          (FStar_TypeChecker_Normalize.normalize
             [FStar_TypeChecker_Env.Beta;
             FStar_TypeChecker_Env.UnfoldUntil
               FStar_Syntax_Syntax.delta_constant;
             FStar_TypeChecker_Env.Primops])
  
let (run_nbe :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        run_either i r expected
          (FStar_TypeChecker_NBE.normalize_for_unit_test
             [FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant])
  
let (run_interpreter_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let interp uu____87323 = run_interpreter i r expected  in
        let uu____87324 =
          let uu____87325 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____87325  in
        (i, uu____87324)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____87363 = run_nbe i r expected  in
        let uu____87364 =
          let uu____87365 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____87365  in
        (i, uu____87364)
  
let run_tests :
  'Auu____87376 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
           'Auu____87376)
      -> 'Auu____87376 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___742_87428  ->
            match uu___742_87428 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____87459  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____87462 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____87471  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____87474 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____87490  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____87520  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let l = run_tests run_interpreter_with_time  in
     FStar_Util.print_string "Normalizer ok\n"; l)
  
let (run_both_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____87565 = run_nbe i r expected  in
        let norm1 uu____87571 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____87584  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____87587 =
       let uu____87588 = encode (Prims.parse_int "1000")  in
       let uu____87590 =
         let uu____87593 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____87594 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____87593 uu____87594  in
       let_ FStar_Tests_Util.x uu____87588 uu____87590  in
     run_both_with_time (Prims.parse_int "14") uu____87587 z)
  
let (compare_times :
  (Prims.int * FStar_BaseTypes.float) Prims.list ->
    (Prims.int * FStar_BaseTypes.float) Prims.list -> unit)
  =
  fun l_int  ->
    fun l_nbe  ->
      FStar_Util.print_string "Comparing times for normalization and nbe\n";
      FStar_List.iter2
        (fun res1  ->
           fun res2  ->
             let uu____87670 = res1  in
             match uu____87670 with
             | (t1,time_int) ->
                 let uu____87680 = res2  in
                 (match uu____87680 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____87692 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____87692 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____87703  ->
    (let uu____87705 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____87705);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  