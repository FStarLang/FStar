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
      (let uu____83333 =
         let uu____83336 = encode (n1 - (Prims.parse_int "1"))  in
         [uu____83336]  in
       FStar_Tests_Util.app succ uu____83333)
  
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
        let uu____83375 =
          let uu____83378 = let uu____83379 = b x1  in [uu____83379]  in
          FStar_Syntax_Util.abs uu____83378 e' FStar_Pervasives_Native.None
           in
        FStar_Tests_Util.app uu____83375 [e]
  
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
  let uu____83449 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____83449
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____83452 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____83452
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
    let uu____83471 =
      let uu____83478 =
        let uu____83479 =
          let uu____83496 = tm_fv snat_l  in
          let uu____83499 =
            let uu____83510 = FStar_Syntax_Syntax.as_arg s  in [uu____83510]
             in
          (uu____83496, uu____83499)  in
        FStar_Syntax_Syntax.Tm_app uu____83479  in
      FStar_Syntax_Syntax.mk uu____83478  in
    uu____83471 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____83555 .
    'Auu____83555 -> 'Auu____83555 FStar_Syntax_Syntax.withinfo_t
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
      let uu____83664 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____83664, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____83708 =
        let uu____83711 =
          let uu____83712 =
            let uu____83726 =
              let uu____83736 =
                let uu____83744 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____83744, false)  in
              [uu____83736]  in
            (snat_l, uu____83726)  in
          FStar_Syntax_Syntax.Pat_cons uu____83712  in
        pat uu____83711  in
      let uu____83774 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___763_83779 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___763_83779.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___763_83779.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____83708, FStar_Pervasives_Native.None, uu____83774)  in
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
        let uu____83820 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____83839 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____83820, FStar_Pervasives_Native.None, uu____83839)  in
      let sbranch =
        let uu____83867 =
          let uu____83870 =
            let uu____83871 =
              let uu____83885 =
                let uu____83895 =
                  let uu____83903 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____83903, false)  in
                [uu____83895]  in
              (snat_l, uu____83885)  in
            FStar_Syntax_Syntax.Pat_cons uu____83871  in
          pat uu____83870  in
        let uu____83933 =
          let uu____83936 = FStar_Tests_Util.nm minus1  in
          let uu____83939 =
            let uu____83942 =
              let uu____83943 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____83943  in
            let uu____83946 =
              let uu____83949 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____83949]  in
            uu____83942 :: uu____83946  in
          FStar_Tests_Util.app uu____83936 uu____83939  in
        (uu____83867, FStar_Pervasives_Native.None, uu____83933)  in
      let lb =
        let uu____83961 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____83965 =
          let uu____83968 =
            let uu____83969 =
              let uu____83970 = b FStar_Tests_Util.x  in
              let uu____83977 =
                let uu____83986 = b FStar_Tests_Util.y  in [uu____83986]  in
              uu____83970 :: uu____83977  in
            let uu____84011 =
              let uu____84014 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____84014 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____83969 uu____84011
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____83968
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____83961;
          FStar_Syntax_Syntax.lbdef = uu____83965;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____84021 =
        let uu____84028 =
          let uu____84029 =
            let uu____84043 =
              let uu____84046 =
                let uu____84047 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____84047 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____84046
               in
            ((true, [lb]), uu____84043)  in
          FStar_Syntax_Syntax.Tm_let uu____84029  in
        FStar_Syntax_Syntax.mk uu____84028  in
      uu____84021 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____84094 = snat out  in
         aux uu____84094 (n2 - (Prims.parse_int "1")))
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
  (let uu____84160 =
     let uu____84172 =
       let uu____84175 =
         let uu____84178 =
           let uu____84181 =
             let uu____84184 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____84184]  in
           id :: uu____84181  in
         one :: uu____84178  in
       FStar_Tests_Util.app apply uu____84175  in
     let uu____84185 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____84172, uu____84185)  in
   let uu____84194 =
     let uu____84208 =
       let uu____84220 =
         let uu____84223 =
           let uu____84226 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____84226]  in
         FStar_Tests_Util.app id uu____84223  in
       let uu____84227 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____84220, uu____84227)  in
     let uu____84236 =
       let uu____84250 =
         let uu____84262 =
           let uu____84265 =
             let uu____84268 =
               let uu____84271 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____84272 =
                 let uu____84275 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____84275]  in
               uu____84271 :: uu____84272  in
             tt :: uu____84268  in
           FStar_Tests_Util.app apply uu____84265  in
         let uu____84276 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____84262, uu____84276)  in
       let uu____84285 =
         let uu____84299 =
           let uu____84311 =
             let uu____84314 =
               let uu____84317 =
                 let uu____84320 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____84321 =
                   let uu____84324 = FStar_Tests_Util.nm FStar_Tests_Util.m
                      in
                   [uu____84324]  in
                 uu____84320 :: uu____84321  in
               ff :: uu____84317  in
             FStar_Tests_Util.app apply uu____84314  in
           let uu____84325 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____84311, uu____84325)  in
         let uu____84334 =
           let uu____84348 =
             let uu____84360 =
               let uu____84363 =
                 let uu____84366 =
                   let uu____84369 =
                     let uu____84372 =
                       let uu____84375 =
                         let uu____84378 =
                           let uu____84381 =
                             let uu____84384 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____84385 =
                               let uu____84388 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____84388]  in
                             uu____84384 :: uu____84385  in
                           ff :: uu____84381  in
                         apply :: uu____84378  in
                       apply :: uu____84375  in
                     apply :: uu____84372  in
                   apply :: uu____84369  in
                 apply :: uu____84366  in
               FStar_Tests_Util.app apply uu____84363  in
             let uu____84389 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____84360, uu____84389)  in
           let uu____84398 =
             let uu____84412 =
               let uu____84424 =
                 let uu____84427 =
                   let uu____84430 =
                     let uu____84433 =
                       let uu____84436 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n  in
                       let uu____84437 =
                         let uu____84440 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____84440]  in
                       uu____84436 :: uu____84437  in
                     ff :: uu____84433  in
                   apply :: uu____84430  in
                 FStar_Tests_Util.app twice uu____84427  in
               let uu____84441 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____84424, uu____84441)  in
             let uu____84450 =
               let uu____84464 =
                 let uu____84476 = minus one z  in
                 ((Prims.parse_int "5"), uu____84476, one)  in
               let uu____84485 =
                 let uu____84499 =
                   let uu____84511 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____84511, z)  in
                 let uu____84520 =
                   let uu____84534 =
                     let uu____84546 = minus one one  in
                     ((Prims.parse_int "7"), uu____84546, z)  in
                   let uu____84555 =
                     let uu____84569 =
                       let uu____84581 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____84581, one)  in
                     let uu____84590 =
                       let uu____84604 =
                         let uu____84616 =
                           FStar_Tests_Util.app mul [two; one]  in
                         ((Prims.parse_int "9"), uu____84616, two)  in
                       let uu____84625 =
                         let uu____84639 =
                           let uu____84651 =
                             let uu____84654 =
                               let uu____84657 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____84657; one]  in
                             FStar_Tests_Util.app mul uu____84654  in
                           ((Prims.parse_int "10"), uu____84651, two)  in
                         let uu____84664 =
                           let uu____84678 =
                             let uu____84690 =
                               let uu____84693 =
                                 encode (Prims.parse_int "10")  in
                               let uu____84695 =
                                 encode (Prims.parse_int "10")  in
                               minus uu____84693 uu____84695  in
                             ((Prims.parse_int "11"), uu____84690, z)  in
                           let uu____84705 =
                             let uu____84719 =
                               let uu____84731 =
                                 let uu____84734 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____84736 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____84734 uu____84736  in
                               ((Prims.parse_int "12"), uu____84731, z)  in
                             let uu____84746 =
                               let uu____84760 =
                                 let uu____84772 =
                                   let uu____84775 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____84777 =
                                     let uu____84780 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____84781 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____84780 uu____84781  in
                                   let_ FStar_Tests_Util.x uu____84775
                                     uu____84777
                                    in
                                 ((Prims.parse_int "13"), uu____84772, z)  in
                               let uu____84790 =
                                 let uu____84804 =
                                   let uu____84816 =
                                     let uu____84819 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____84820 =
                                       let uu____84823 =
                                         let uu____84824 =
                                           let uu____84827 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____84828 =
                                             let uu____84831 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____84831]  in
                                           uu____84827 :: uu____84828  in
                                         FStar_Tests_Util.app mul uu____84824
                                          in
                                       let uu____84832 =
                                         let uu____84835 =
                                           let uu____84836 =
                                             let uu____84839 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____84840 =
                                               let uu____84843 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____84843]  in
                                             uu____84839 :: uu____84840  in
                                           FStar_Tests_Util.app mul
                                             uu____84836
                                            in
                                         let uu____84844 =
                                           let uu____84847 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____84848 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____84847 uu____84848  in
                                         let_ FStar_Tests_Util.h uu____84835
                                           uu____84844
                                          in
                                       let_ FStar_Tests_Util.y uu____84823
                                         uu____84832
                                        in
                                     let_ FStar_Tests_Util.x uu____84819
                                       uu____84820
                                      in
                                   ((Prims.parse_int "15"), uu____84816, z)
                                    in
                                 let uu____84857 =
                                   let uu____84871 =
                                     let uu____84883 =
                                       let uu____84886 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____84889 =
                                         let uu____84890 =
                                           let uu____84893 =
                                             let uu____84896 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____84897 =
                                               let uu____84900 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____84900]  in
                                             uu____84896 :: uu____84897  in
                                           FStar_Tests_Util.app mul
                                             uu____84893
                                            in
                                         let uu____84901 =
                                           let uu____84902 =
                                             let uu____84905 =
                                               let uu____84908 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____84909 =
                                                 let uu____84912 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____84912]  in
                                               uu____84908 :: uu____84909  in
                                             FStar_Tests_Util.app mul
                                               uu____84905
                                              in
                                           let uu____84913 =
                                             let uu____84914 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____84915 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____84914 uu____84915
                                              in
                                           mk_let FStar_Tests_Util.h
                                             uu____84902 uu____84913
                                            in
                                         mk_let FStar_Tests_Util.y
                                           uu____84890 uu____84901
                                          in
                                       mk_let FStar_Tests_Util.x uu____84886
                                         uu____84889
                                        in
                                     ((Prims.parse_int "16"), uu____84883, z)
                                      in
                                   let uu____84924 =
                                     let uu____84938 =
                                       let uu____84950 =
                                         let uu____84953 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____84954 =
                                           let uu____84957 =
                                             let uu____84958 =
                                               let uu____84961 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____84962 =
                                                 let uu____84965 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____84965]  in
                                               uu____84961 :: uu____84962  in
                                             FStar_Tests_Util.app mul
                                               uu____84958
                                              in
                                           let uu____84966 =
                                             let uu____84969 =
                                               let uu____84970 =
                                                 let uu____84973 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____84974 =
                                                   let uu____84977 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____84977]  in
                                                 uu____84973 :: uu____84974
                                                  in
                                               FStar_Tests_Util.app mul
                                                 uu____84970
                                                in
                                             let uu____84978 =
                                               let uu____84981 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____84982 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____84981 uu____84982
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____84969 uu____84978
                                              in
                                           let_ FStar_Tests_Util.y
                                             uu____84957 uu____84966
                                            in
                                         let_ FStar_Tests_Util.x uu____84953
                                           uu____84954
                                          in
                                       ((Prims.parse_int "17"), uu____84950,
                                         z)
                                        in
                                     let uu____84991 =
                                       let uu____85005 =
                                         let uu____85017 =
                                           let uu____85020 =
                                             let uu____85023 = snat znat  in
                                             snat uu____85023  in
                                           pred_nat uu____85020  in
                                         let uu____85024 = snat znat  in
                                         ((Prims.parse_int "18"),
                                           uu____85017, uu____85024)
                                          in
                                       let uu____85033 =
                                         let uu____85047 =
                                           let uu____85059 =
                                             let uu____85062 =
                                               let uu____85063 =
                                                 let uu____85064 = snat znat
                                                    in
                                                 snat uu____85064  in
                                               let uu____85065 = snat znat
                                                  in
                                               minus_nat uu____85063
                                                 uu____85065
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____85062
                                              in
                                           let uu____85066 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____85059, uu____85066)
                                            in
                                         let uu____85075 =
                                           let uu____85089 =
                                             let uu____85101 =
                                               let uu____85104 =
                                                 let uu____85105 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 let uu____85107 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 minus_nat uu____85105
                                                   uu____85107
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____85104
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____85101, znat)
                                              in
                                           let uu____85115 =
                                             let uu____85129 =
                                               let uu____85141 =
                                                 let uu____85144 =
                                                   let uu____85145 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   let uu____85147 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   minus_nat uu____85145
                                                     uu____85147
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____85144
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____85141, znat)
                                                in
                                             let uu____85155 =
                                               let uu____85169 =
                                                 let uu____85181 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____85185 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____85181, uu____85185)
                                                  in
                                               let uu____85195 =
                                                 let uu____85209 =
                                                   let uu____85221 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____85225 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____85221,
                                                     uu____85225)
                                                    in
                                                 let uu____85235 =
                                                   let uu____85249 =
                                                     let uu____85261 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____85265 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____85261,
                                                       uu____85265)
                                                      in
                                                   let uu____85275 =
                                                     let uu____85289 =
                                                       let uu____85301 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____85305 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____85301,
                                                         uu____85305)
                                                        in
                                                     let uu____85315 =
                                                       let uu____85329 =
                                                         let uu____85341 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____85345 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____85341,
                                                           uu____85345)
                                                          in
                                                       let uu____85355 =
                                                         let uu____85369 =
                                                           let uu____85381 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____85385 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____85381,
                                                             uu____85385)
                                                            in
                                                         let uu____85395 =
                                                           let uu____85409 =
                                                             let uu____85421
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____85425
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____85421,
                                                               uu____85425)
                                                              in
                                                           let uu____85435 =
                                                             let uu____85449
                                                               =
                                                               let uu____85461
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____85465
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____85461,
                                                                 uu____85465)
                                                                in
                                                             let uu____85475
                                                               =
                                                               let uu____85489
                                                                 =
                                                                 let uu____85501
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____85505
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____85501,
                                                                   uu____85505)
                                                                  in
                                                               let uu____85515
                                                                 =
                                                                 let uu____85529
                                                                   =
                                                                   let uu____85541
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____85545
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____85541,
                                                                    uu____85545)
                                                                    in
                                                                 let uu____85555
                                                                   =
                                                                   let uu____85569
                                                                    =
                                                                    let uu____85581
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____85585
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____85581,
                                                                    uu____85585)
                                                                     in
                                                                   let uu____85595
                                                                    =
                                                                    let uu____85609
                                                                    =
                                                                    let uu____85621
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____85625
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____85621,
                                                                    uu____85625)
                                                                     in
                                                                    let uu____85635
                                                                    =
                                                                    let uu____85649
                                                                    =
                                                                    let uu____85661
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____85665
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____85661,
                                                                    uu____85665)
                                                                     in
                                                                    let uu____85675
                                                                    =
                                                                    let uu____85689
                                                                    =
                                                                    let uu____85701
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____85705
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____85701,
                                                                    uu____85705)
                                                                     in
                                                                    let uu____85715
                                                                    =
                                                                    let uu____85729
                                                                    =
                                                                    let uu____85741
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____85745
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____85741,
                                                                    uu____85745)
                                                                     in
                                                                    let uu____85755
                                                                    =
                                                                    let uu____85769
                                                                    =
                                                                    let uu____85781
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____85785
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____85781,
                                                                    uu____85785)
                                                                     in
                                                                    let uu____85795
                                                                    =
                                                                    let uu____85809
                                                                    =
                                                                    let uu____85821
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____85825
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____85821,
                                                                    uu____85825)
                                                                     in
                                                                    let uu____85835
                                                                    =
                                                                    let uu____85849
                                                                    =
                                                                    let uu____85861
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____85865
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____85861,
                                                                    uu____85865)
                                                                     in
                                                                    let uu____85875
                                                                    =
                                                                    let uu____85889
                                                                    =
                                                                    let uu____85901
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____85905
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____85901,
                                                                    uu____85905)
                                                                     in
                                                                    let uu____85915
                                                                    =
                                                                    let uu____85929
                                                                    =
                                                                    let uu____85941
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____85945
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____85941,
                                                                    uu____85945)
                                                                     in
                                                                    let uu____85955
                                                                    =
                                                                    let uu____85969
                                                                    =
                                                                    let uu____85981
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____85985
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____85981,
                                                                    uu____85985)
                                                                     in
                                                                    let uu____85995
                                                                    =
                                                                    let uu____86009
                                                                    =
                                                                    let uu____86021
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____86025
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____86021,
                                                                    uu____86025)
                                                                     in
                                                                    let uu____86035
                                                                    =
                                                                    let uu____86049
                                                                    =
                                                                    let uu____86061
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____86065
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____86061,
                                                                    uu____86065)
                                                                     in
                                                                    let uu____86075
                                                                    =
                                                                    let uu____86089
                                                                    =
                                                                    let uu____86101
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____86105
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____86101,
                                                                    uu____86105)
                                                                     in
                                                                    let uu____86115
                                                                    =
                                                                    let uu____86129
                                                                    =
                                                                    let uu____86141
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____86145
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____86141,
                                                                    uu____86145)
                                                                     in
                                                                    let uu____86155
                                                                    =
                                                                    let uu____86169
                                                                    =
                                                                    let uu____86181
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____86185
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____86181,
                                                                    uu____86185)
                                                                     in
                                                                    let uu____86195
                                                                    =
                                                                    let uu____86209
                                                                    =
                                                                    let uu____86221
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____86225
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____86221,
                                                                    uu____86225)
                                                                     in
                                                                    let uu____86235
                                                                    =
                                                                    let uu____86249
                                                                    =
                                                                    let uu____86261
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____86265
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____86261,
                                                                    uu____86265)
                                                                     in
                                                                    let uu____86275
                                                                    =
                                                                    let uu____86289
                                                                    =
                                                                    let uu____86301
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____86305
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____86301,
                                                                    uu____86305)
                                                                     in
                                                                    let uu____86315
                                                                    =
                                                                    let uu____86329
                                                                    =
                                                                    let uu____86341
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____86345
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____86341,
                                                                    uu____86345)
                                                                     in
                                                                    let uu____86355
                                                                    =
                                                                    let uu____86369
                                                                    =
                                                                    let uu____86381
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____86385
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____86381,
                                                                    uu____86385)
                                                                     in
                                                                    let uu____86395
                                                                    =
                                                                    let uu____86409
                                                                    =
                                                                    let uu____86421
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____86425
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____86421,
                                                                    uu____86425)
                                                                     in
                                                                    let uu____86435
                                                                    =
                                                                    let uu____86449
                                                                    =
                                                                    let uu____86461
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____86465
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____86461,
                                                                    uu____86465)
                                                                     in
                                                                    let uu____86475
                                                                    =
                                                                    let uu____86489
                                                                    =
                                                                    let uu____86501
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____86505
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____86501,
                                                                    uu____86505)
                                                                     in
                                                                    [uu____86489]
                                                                     in
                                                                    uu____86449
                                                                    ::
                                                                    uu____86475
                                                                     in
                                                                    uu____86409
                                                                    ::
                                                                    uu____86435
                                                                     in
                                                                    uu____86369
                                                                    ::
                                                                    uu____86395
                                                                     in
                                                                    uu____86329
                                                                    ::
                                                                    uu____86355
                                                                     in
                                                                    uu____86289
                                                                    ::
                                                                    uu____86315
                                                                     in
                                                                    uu____86249
                                                                    ::
                                                                    uu____86275
                                                                     in
                                                                    uu____86209
                                                                    ::
                                                                    uu____86235
                                                                     in
                                                                    uu____86169
                                                                    ::
                                                                    uu____86195
                                                                     in
                                                                    uu____86129
                                                                    ::
                                                                    uu____86155
                                                                     in
                                                                    uu____86089
                                                                    ::
                                                                    uu____86115
                                                                     in
                                                                    uu____86049
                                                                    ::
                                                                    uu____86075
                                                                     in
                                                                    uu____86009
                                                                    ::
                                                                    uu____86035
                                                                     in
                                                                    uu____85969
                                                                    ::
                                                                    uu____85995
                                                                     in
                                                                    uu____85929
                                                                    ::
                                                                    uu____85955
                                                                     in
                                                                    uu____85889
                                                                    ::
                                                                    uu____85915
                                                                     in
                                                                    uu____85849
                                                                    ::
                                                                    uu____85875
                                                                     in
                                                                    uu____85809
                                                                    ::
                                                                    uu____85835
                                                                     in
                                                                    uu____85769
                                                                    ::
                                                                    uu____85795
                                                                     in
                                                                    uu____85729
                                                                    ::
                                                                    uu____85755
                                                                     in
                                                                    uu____85689
                                                                    ::
                                                                    uu____85715
                                                                     in
                                                                    uu____85649
                                                                    ::
                                                                    uu____85675
                                                                     in
                                                                    uu____85609
                                                                    ::
                                                                    uu____85635
                                                                     in
                                                                   uu____85569
                                                                    ::
                                                                    uu____85595
                                                                    in
                                                                 uu____85529
                                                                   ::
                                                                   uu____85555
                                                                  in
                                                               uu____85489 ::
                                                                 uu____85515
                                                                in
                                                             uu____85449 ::
                                                               uu____85475
                                                              in
                                                           uu____85409 ::
                                                             uu____85435
                                                            in
                                                         uu____85369 ::
                                                           uu____85395
                                                          in
                                                       uu____85329 ::
                                                         uu____85355
                                                        in
                                                     uu____85289 ::
                                                       uu____85315
                                                      in
                                                   uu____85249 :: uu____85275
                                                    in
                                                 uu____85209 :: uu____85235
                                                  in
                                               uu____85169 :: uu____85195  in
                                             uu____85129 :: uu____85155  in
                                           uu____85089 :: uu____85115  in
                                         uu____85047 :: uu____85075  in
                                       uu____85005 :: uu____85033  in
                                     uu____84938 :: uu____84991  in
                                   uu____84871 :: uu____84924  in
                                 uu____84804 :: uu____84857  in
                               uu____84760 :: uu____84790  in
                             uu____84719 :: uu____84746  in
                           uu____84678 :: uu____84705  in
                         uu____84639 :: uu____84664  in
                       uu____84604 :: uu____84625  in
                     uu____84569 :: uu____84590  in
                   uu____84534 :: uu____84555  in
                 uu____84499 :: uu____84520  in
               uu____84464 :: uu____84485  in
             uu____84412 :: uu____84450  in
           uu____84348 :: uu____84398  in
         uu____84299 :: uu____84334  in
       uu____84250 :: uu____84285  in
     uu____84208 :: uu____84236  in
   uu____84160 :: uu____84194)
  
let run_either :
  'Auu____87153 .
    Prims.int ->
      'Auu____87153 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____87153 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____87191 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____87191);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____87196 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____87196 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____87219 =
               let uu____87221 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____87221 expected  in
             FStar_Tests_Util.always i uu____87219)))
  
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
        let interp uu____87300 = run_interpreter i r expected  in
        let uu____87301 =
          let uu____87302 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____87302  in
        (i, uu____87301)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____87340 = run_nbe i r expected  in
        let uu____87341 =
          let uu____87342 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____87342  in
        (i, uu____87341)
  
let run_tests :
  'Auu____87353 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
           'Auu____87353)
      -> 'Auu____87353 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___742_87405  ->
            match uu___742_87405 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____87436  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____87439 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____87448  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____87451 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____87467  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____87497  ->
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
        let nbe1 uu____87542 = run_nbe i r expected  in
        let norm1 uu____87548 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____87561  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____87564 =
       let uu____87565 = encode (Prims.parse_int "1000")  in
       let uu____87567 =
         let uu____87570 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____87571 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____87570 uu____87571  in
       let_ FStar_Tests_Util.x uu____87565 uu____87567  in
     run_both_with_time (Prims.parse_int "14") uu____87564 z)
  
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
             let uu____87647 = res1  in
             match uu____87647 with
             | (t1,time_int) ->
                 let uu____87657 = res2  in
                 (match uu____87657 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____87669 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____87669 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____87680  ->
    (let uu____87682 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____87682);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  