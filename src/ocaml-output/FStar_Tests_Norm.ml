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
      (let uu____77934 =
         let uu____77937 = encode (n1 - (Prims.parse_int "1"))  in
         [uu____77937]  in
       FStar_Tests_Util.app succ uu____77934)
  
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
        let uu____77976 =
          let uu____77979 = let uu____77980 = b x1  in [uu____77980]  in
          FStar_Syntax_Util.abs uu____77979 e' FStar_Pervasives_Native.None
           in
        FStar_Tests_Util.app uu____77976 [e]
  
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
  let uu____78050 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____78050
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____78053 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____78053
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
    let uu____78072 =
      let uu____78079 =
        let uu____78080 =
          let uu____78097 = tm_fv snat_l  in
          let uu____78100 =
            let uu____78111 = FStar_Syntax_Syntax.as_arg s  in [uu____78111]
             in
          (uu____78097, uu____78100)  in
        FStar_Syntax_Syntax.Tm_app uu____78080  in
      FStar_Syntax_Syntax.mk uu____78079  in
    uu____78072 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____78153 .
    'Auu____78153 -> 'Auu____78153 FStar_Syntax_Syntax.withinfo_t
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
      let uu____78262 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____78262, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____78306 =
        let uu____78309 =
          let uu____78310 =
            let uu____78324 =
              let uu____78334 =
                let uu____78342 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____78342, false)  in
              [uu____78334]  in
            (snat_l, uu____78324)  in
          FStar_Syntax_Syntax.Pat_cons uu____78310  in
        pat uu____78309  in
      let uu____78372 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___763_78377 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___763_78377.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___763_78377.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____78306, FStar_Pervasives_Native.None, uu____78372)  in
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
        let uu____78418 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____78437 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____78418, FStar_Pervasives_Native.None, uu____78437)  in
      let sbranch =
        let uu____78465 =
          let uu____78468 =
            let uu____78469 =
              let uu____78483 =
                let uu____78493 =
                  let uu____78501 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____78501, false)  in
                [uu____78493]  in
              (snat_l, uu____78483)  in
            FStar_Syntax_Syntax.Pat_cons uu____78469  in
          pat uu____78468  in
        let uu____78531 =
          let uu____78534 = FStar_Tests_Util.nm minus1  in
          let uu____78537 =
            let uu____78540 =
              let uu____78541 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____78541  in
            let uu____78544 =
              let uu____78547 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____78547]  in
            uu____78540 :: uu____78544  in
          FStar_Tests_Util.app uu____78534 uu____78537  in
        (uu____78465, FStar_Pervasives_Native.None, uu____78531)  in
      let lb =
        let uu____78559 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____78563 =
          let uu____78566 =
            let uu____78567 =
              let uu____78568 = b FStar_Tests_Util.x  in
              let uu____78575 =
                let uu____78584 = b FStar_Tests_Util.y  in [uu____78584]  in
              uu____78568 :: uu____78575  in
            let uu____78609 =
              let uu____78612 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____78612 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____78567 uu____78609
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____78566
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____78559;
          FStar_Syntax_Syntax.lbdef = uu____78563;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____78619 =
        let uu____78626 =
          let uu____78627 =
            let uu____78641 =
              let uu____78644 =
                let uu____78645 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____78645 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____78644
               in
            ((true, [lb]), uu____78641)  in
          FStar_Syntax_Syntax.Tm_let uu____78627  in
        FStar_Syntax_Syntax.mk uu____78626  in
      uu____78619 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____78689 = snat out  in
         aux uu____78689 (n2 - (Prims.parse_int "1")))
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
  (let uu____78755 =
     let uu____78767 =
       let uu____78770 =
         let uu____78773 =
           let uu____78776 =
             let uu____78779 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____78779]  in
           id :: uu____78776  in
         one :: uu____78773  in
       FStar_Tests_Util.app apply uu____78770  in
     let uu____78780 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____78767, uu____78780)  in
   let uu____78789 =
     let uu____78803 =
       let uu____78815 =
         let uu____78818 =
           let uu____78821 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____78821]  in
         FStar_Tests_Util.app id uu____78818  in
       let uu____78822 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____78815, uu____78822)  in
     let uu____78831 =
       let uu____78845 =
         let uu____78857 =
           let uu____78860 =
             let uu____78863 =
               let uu____78866 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____78867 =
                 let uu____78870 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____78870]  in
               uu____78866 :: uu____78867  in
             tt :: uu____78863  in
           FStar_Tests_Util.app apply uu____78860  in
         let uu____78871 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____78857, uu____78871)  in
       let uu____78880 =
         let uu____78894 =
           let uu____78906 =
             let uu____78909 =
               let uu____78912 =
                 let uu____78915 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____78916 =
                   let uu____78919 = FStar_Tests_Util.nm FStar_Tests_Util.m
                      in
                   [uu____78919]  in
                 uu____78915 :: uu____78916  in
               ff :: uu____78912  in
             FStar_Tests_Util.app apply uu____78909  in
           let uu____78920 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____78906, uu____78920)  in
         let uu____78929 =
           let uu____78943 =
             let uu____78955 =
               let uu____78958 =
                 let uu____78961 =
                   let uu____78964 =
                     let uu____78967 =
                       let uu____78970 =
                         let uu____78973 =
                           let uu____78976 =
                             let uu____78979 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____78980 =
                               let uu____78983 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____78983]  in
                             uu____78979 :: uu____78980  in
                           ff :: uu____78976  in
                         apply :: uu____78973  in
                       apply :: uu____78970  in
                     apply :: uu____78967  in
                   apply :: uu____78964  in
                 apply :: uu____78961  in
               FStar_Tests_Util.app apply uu____78958  in
             let uu____78984 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____78955, uu____78984)  in
           let uu____78993 =
             let uu____79007 =
               let uu____79019 =
                 let uu____79022 =
                   let uu____79025 =
                     let uu____79028 =
                       let uu____79031 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n  in
                       let uu____79032 =
                         let uu____79035 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____79035]  in
                       uu____79031 :: uu____79032  in
                     ff :: uu____79028  in
                   apply :: uu____79025  in
                 FStar_Tests_Util.app twice uu____79022  in
               let uu____79036 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____79019, uu____79036)  in
             let uu____79045 =
               let uu____79059 =
                 let uu____79071 = minus one z  in
                 ((Prims.parse_int "5"), uu____79071, one)  in
               let uu____79080 =
                 let uu____79094 =
                   let uu____79106 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____79106, z)  in
                 let uu____79115 =
                   let uu____79129 =
                     let uu____79141 = minus one one  in
                     ((Prims.parse_int "7"), uu____79141, z)  in
                   let uu____79150 =
                     let uu____79164 =
                       let uu____79176 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____79176, one)  in
                     let uu____79185 =
                       let uu____79199 =
                         let uu____79211 =
                           FStar_Tests_Util.app mul [two; one]  in
                         ((Prims.parse_int "9"), uu____79211, two)  in
                       let uu____79220 =
                         let uu____79234 =
                           let uu____79246 =
                             let uu____79249 =
                               let uu____79252 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____79252; one]  in
                             FStar_Tests_Util.app mul uu____79249  in
                           ((Prims.parse_int "10"), uu____79246, two)  in
                         let uu____79259 =
                           let uu____79273 =
                             let uu____79285 =
                               let uu____79288 =
                                 encode (Prims.parse_int "10")  in
                               let uu____79290 =
                                 encode (Prims.parse_int "10")  in
                               minus uu____79288 uu____79290  in
                             ((Prims.parse_int "11"), uu____79285, z)  in
                           let uu____79300 =
                             let uu____79314 =
                               let uu____79326 =
                                 let uu____79329 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____79331 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____79329 uu____79331  in
                               ((Prims.parse_int "12"), uu____79326, z)  in
                             let uu____79341 =
                               let uu____79355 =
                                 let uu____79367 =
                                   let uu____79370 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____79372 =
                                     let uu____79375 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____79376 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____79375 uu____79376  in
                                   let_ FStar_Tests_Util.x uu____79370
                                     uu____79372
                                    in
                                 ((Prims.parse_int "13"), uu____79367, z)  in
                               let uu____79385 =
                                 let uu____79399 =
                                   let uu____79411 =
                                     let uu____79414 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____79415 =
                                       let uu____79418 =
                                         let uu____79419 =
                                           let uu____79422 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____79423 =
                                             let uu____79426 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____79426]  in
                                           uu____79422 :: uu____79423  in
                                         FStar_Tests_Util.app mul uu____79419
                                          in
                                       let uu____79427 =
                                         let uu____79430 =
                                           let uu____79431 =
                                             let uu____79434 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____79435 =
                                               let uu____79438 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____79438]  in
                                             uu____79434 :: uu____79435  in
                                           FStar_Tests_Util.app mul
                                             uu____79431
                                            in
                                         let uu____79439 =
                                           let uu____79442 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____79443 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____79442 uu____79443  in
                                         let_ FStar_Tests_Util.h uu____79430
                                           uu____79439
                                          in
                                       let_ FStar_Tests_Util.y uu____79418
                                         uu____79427
                                        in
                                     let_ FStar_Tests_Util.x uu____79414
                                       uu____79415
                                      in
                                   ((Prims.parse_int "15"), uu____79411, z)
                                    in
                                 let uu____79452 =
                                   let uu____79466 =
                                     let uu____79478 =
                                       let uu____79481 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____79484 =
                                         let uu____79485 =
                                           let uu____79488 =
                                             let uu____79491 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____79492 =
                                               let uu____79495 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____79495]  in
                                             uu____79491 :: uu____79492  in
                                           FStar_Tests_Util.app mul
                                             uu____79488
                                            in
                                         let uu____79496 =
                                           let uu____79497 =
                                             let uu____79500 =
                                               let uu____79503 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____79504 =
                                                 let uu____79507 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____79507]  in
                                               uu____79503 :: uu____79504  in
                                             FStar_Tests_Util.app mul
                                               uu____79500
                                              in
                                           let uu____79508 =
                                             let uu____79509 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____79510 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____79509 uu____79510
                                              in
                                           mk_let FStar_Tests_Util.h
                                             uu____79497 uu____79508
                                            in
                                         mk_let FStar_Tests_Util.y
                                           uu____79485 uu____79496
                                          in
                                       mk_let FStar_Tests_Util.x uu____79481
                                         uu____79484
                                        in
                                     ((Prims.parse_int "16"), uu____79478, z)
                                      in
                                   let uu____79519 =
                                     let uu____79533 =
                                       let uu____79545 =
                                         let uu____79548 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____79549 =
                                           let uu____79552 =
                                             let uu____79553 =
                                               let uu____79556 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____79557 =
                                                 let uu____79560 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____79560]  in
                                               uu____79556 :: uu____79557  in
                                             FStar_Tests_Util.app mul
                                               uu____79553
                                              in
                                           let uu____79561 =
                                             let uu____79564 =
                                               let uu____79565 =
                                                 let uu____79568 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____79569 =
                                                   let uu____79572 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____79572]  in
                                                 uu____79568 :: uu____79569
                                                  in
                                               FStar_Tests_Util.app mul
                                                 uu____79565
                                                in
                                             let uu____79573 =
                                               let uu____79576 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____79577 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____79576 uu____79577
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____79564 uu____79573
                                              in
                                           let_ FStar_Tests_Util.y
                                             uu____79552 uu____79561
                                            in
                                         let_ FStar_Tests_Util.x uu____79548
                                           uu____79549
                                          in
                                       ((Prims.parse_int "17"), uu____79545,
                                         z)
                                        in
                                     let uu____79586 =
                                       let uu____79600 =
                                         let uu____79612 =
                                           let uu____79615 =
                                             let uu____79618 = snat znat  in
                                             snat uu____79618  in
                                           pred_nat uu____79615  in
                                         let uu____79619 = snat znat  in
                                         ((Prims.parse_int "18"),
                                           uu____79612, uu____79619)
                                          in
                                       let uu____79628 =
                                         let uu____79642 =
                                           let uu____79654 =
                                             let uu____79657 =
                                               let uu____79658 =
                                                 let uu____79659 = snat znat
                                                    in
                                                 snat uu____79659  in
                                               let uu____79660 = snat znat
                                                  in
                                               minus_nat uu____79658
                                                 uu____79660
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____79657
                                              in
                                           let uu____79661 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____79654, uu____79661)
                                            in
                                         let uu____79670 =
                                           let uu____79684 =
                                             let uu____79696 =
                                               let uu____79699 =
                                                 let uu____79700 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 let uu____79702 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 minus_nat uu____79700
                                                   uu____79702
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____79699
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____79696, znat)
                                              in
                                           let uu____79710 =
                                             let uu____79724 =
                                               let uu____79736 =
                                                 let uu____79739 =
                                                   let uu____79740 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   let uu____79742 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   minus_nat uu____79740
                                                     uu____79742
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____79739
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____79736, znat)
                                                in
                                             let uu____79750 =
                                               let uu____79764 =
                                                 let uu____79776 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____79780 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____79776, uu____79780)
                                                  in
                                               let uu____79790 =
                                                 let uu____79804 =
                                                   let uu____79816 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____79820 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____79816,
                                                     uu____79820)
                                                    in
                                                 let uu____79830 =
                                                   let uu____79844 =
                                                     let uu____79856 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____79860 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____79856,
                                                       uu____79860)
                                                      in
                                                   let uu____79870 =
                                                     let uu____79884 =
                                                       let uu____79896 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____79900 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____79896,
                                                         uu____79900)
                                                        in
                                                     let uu____79910 =
                                                       let uu____79924 =
                                                         let uu____79936 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____79940 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____79936,
                                                           uu____79940)
                                                          in
                                                       let uu____79950 =
                                                         let uu____79964 =
                                                           let uu____79976 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____79980 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____79976,
                                                             uu____79980)
                                                            in
                                                         let uu____79990 =
                                                           let uu____80004 =
                                                             let uu____80016
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____80020
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____80016,
                                                               uu____80020)
                                                              in
                                                           let uu____80030 =
                                                             let uu____80044
                                                               =
                                                               let uu____80056
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____80060
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____80056,
                                                                 uu____80060)
                                                                in
                                                             let uu____80070
                                                               =
                                                               let uu____80084
                                                                 =
                                                                 let uu____80096
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____80100
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____80096,
                                                                   uu____80100)
                                                                  in
                                                               let uu____80110
                                                                 =
                                                                 let uu____80124
                                                                   =
                                                                   let uu____80136
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____80140
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____80136,
                                                                    uu____80140)
                                                                    in
                                                                 let uu____80150
                                                                   =
                                                                   let uu____80164
                                                                    =
                                                                    let uu____80176
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____80180
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____80176,
                                                                    uu____80180)
                                                                     in
                                                                   let uu____80190
                                                                    =
                                                                    let uu____80204
                                                                    =
                                                                    let uu____80216
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____80220
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____80216,
                                                                    uu____80220)
                                                                     in
                                                                    let uu____80230
                                                                    =
                                                                    let uu____80244
                                                                    =
                                                                    let uu____80256
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____80260
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____80256,
                                                                    uu____80260)
                                                                     in
                                                                    let uu____80270
                                                                    =
                                                                    let uu____80284
                                                                    =
                                                                    let uu____80296
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____80300
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____80296,
                                                                    uu____80300)
                                                                     in
                                                                    let uu____80310
                                                                    =
                                                                    let uu____80324
                                                                    =
                                                                    let uu____80336
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____80340
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____80336,
                                                                    uu____80340)
                                                                     in
                                                                    let uu____80350
                                                                    =
                                                                    let uu____80364
                                                                    =
                                                                    let uu____80376
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____80380
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____80376,
                                                                    uu____80380)
                                                                     in
                                                                    let uu____80390
                                                                    =
                                                                    let uu____80404
                                                                    =
                                                                    let uu____80416
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____80420
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____80416,
                                                                    uu____80420)
                                                                     in
                                                                    let uu____80430
                                                                    =
                                                                    let uu____80444
                                                                    =
                                                                    let uu____80456
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____80460
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____80456,
                                                                    uu____80460)
                                                                     in
                                                                    let uu____80470
                                                                    =
                                                                    let uu____80484
                                                                    =
                                                                    let uu____80496
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____80500
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____80496,
                                                                    uu____80500)
                                                                     in
                                                                    let uu____80510
                                                                    =
                                                                    let uu____80524
                                                                    =
                                                                    let uu____80536
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____80540
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____80536,
                                                                    uu____80540)
                                                                     in
                                                                    let uu____80550
                                                                    =
                                                                    let uu____80564
                                                                    =
                                                                    let uu____80576
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____80580
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____80576,
                                                                    uu____80580)
                                                                     in
                                                                    let uu____80590
                                                                    =
                                                                    let uu____80604
                                                                    =
                                                                    let uu____80616
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____80620
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____80616,
                                                                    uu____80620)
                                                                     in
                                                                    let uu____80630
                                                                    =
                                                                    let uu____80644
                                                                    =
                                                                    let uu____80656
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____80660
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____80656,
                                                                    uu____80660)
                                                                     in
                                                                    let uu____80670
                                                                    =
                                                                    let uu____80684
                                                                    =
                                                                    let uu____80696
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____80700
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____80696,
                                                                    uu____80700)
                                                                     in
                                                                    let uu____80710
                                                                    =
                                                                    let uu____80724
                                                                    =
                                                                    let uu____80736
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____80740
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____80736,
                                                                    uu____80740)
                                                                     in
                                                                    let uu____80750
                                                                    =
                                                                    let uu____80764
                                                                    =
                                                                    let uu____80776
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____80780
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____80776,
                                                                    uu____80780)
                                                                     in
                                                                    let uu____80790
                                                                    =
                                                                    let uu____80804
                                                                    =
                                                                    let uu____80816
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____80820
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____80816,
                                                                    uu____80820)
                                                                     in
                                                                    let uu____80830
                                                                    =
                                                                    let uu____80844
                                                                    =
                                                                    let uu____80856
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____80860
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____80856,
                                                                    uu____80860)
                                                                     in
                                                                    let uu____80870
                                                                    =
                                                                    let uu____80884
                                                                    =
                                                                    let uu____80896
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____80900
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____80896,
                                                                    uu____80900)
                                                                     in
                                                                    let uu____80910
                                                                    =
                                                                    let uu____80924
                                                                    =
                                                                    let uu____80936
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____80940
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____80936,
                                                                    uu____80940)
                                                                     in
                                                                    let uu____80950
                                                                    =
                                                                    let uu____80964
                                                                    =
                                                                    let uu____80976
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____80980
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____80976,
                                                                    uu____80980)
                                                                     in
                                                                    let uu____80990
                                                                    =
                                                                    let uu____81004
                                                                    =
                                                                    let uu____81016
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____81020
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____81016,
                                                                    uu____81020)
                                                                     in
                                                                    let uu____81030
                                                                    =
                                                                    let uu____81044
                                                                    =
                                                                    let uu____81056
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____81060
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____81056,
                                                                    uu____81060)
                                                                     in
                                                                    let uu____81070
                                                                    =
                                                                    let uu____81084
                                                                    =
                                                                    let uu____81096
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____81100
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____81096,
                                                                    uu____81100)
                                                                     in
                                                                    [uu____81084]
                                                                     in
                                                                    uu____81044
                                                                    ::
                                                                    uu____81070
                                                                     in
                                                                    uu____81004
                                                                    ::
                                                                    uu____81030
                                                                     in
                                                                    uu____80964
                                                                    ::
                                                                    uu____80990
                                                                     in
                                                                    uu____80924
                                                                    ::
                                                                    uu____80950
                                                                     in
                                                                    uu____80884
                                                                    ::
                                                                    uu____80910
                                                                     in
                                                                    uu____80844
                                                                    ::
                                                                    uu____80870
                                                                     in
                                                                    uu____80804
                                                                    ::
                                                                    uu____80830
                                                                     in
                                                                    uu____80764
                                                                    ::
                                                                    uu____80790
                                                                     in
                                                                    uu____80724
                                                                    ::
                                                                    uu____80750
                                                                     in
                                                                    uu____80684
                                                                    ::
                                                                    uu____80710
                                                                     in
                                                                    uu____80644
                                                                    ::
                                                                    uu____80670
                                                                     in
                                                                    uu____80604
                                                                    ::
                                                                    uu____80630
                                                                     in
                                                                    uu____80564
                                                                    ::
                                                                    uu____80590
                                                                     in
                                                                    uu____80524
                                                                    ::
                                                                    uu____80550
                                                                     in
                                                                    uu____80484
                                                                    ::
                                                                    uu____80510
                                                                     in
                                                                    uu____80444
                                                                    ::
                                                                    uu____80470
                                                                     in
                                                                    uu____80404
                                                                    ::
                                                                    uu____80430
                                                                     in
                                                                    uu____80364
                                                                    ::
                                                                    uu____80390
                                                                     in
                                                                    uu____80324
                                                                    ::
                                                                    uu____80350
                                                                     in
                                                                    uu____80284
                                                                    ::
                                                                    uu____80310
                                                                     in
                                                                    uu____80244
                                                                    ::
                                                                    uu____80270
                                                                     in
                                                                    uu____80204
                                                                    ::
                                                                    uu____80230
                                                                     in
                                                                   uu____80164
                                                                    ::
                                                                    uu____80190
                                                                    in
                                                                 uu____80124
                                                                   ::
                                                                   uu____80150
                                                                  in
                                                               uu____80084 ::
                                                                 uu____80110
                                                                in
                                                             uu____80044 ::
                                                               uu____80070
                                                              in
                                                           uu____80004 ::
                                                             uu____80030
                                                            in
                                                         uu____79964 ::
                                                           uu____79990
                                                          in
                                                       uu____79924 ::
                                                         uu____79950
                                                        in
                                                     uu____79884 ::
                                                       uu____79910
                                                      in
                                                   uu____79844 :: uu____79870
                                                    in
                                                 uu____79804 :: uu____79830
                                                  in
                                               uu____79764 :: uu____79790  in
                                             uu____79724 :: uu____79750  in
                                           uu____79684 :: uu____79710  in
                                         uu____79642 :: uu____79670  in
                                       uu____79600 :: uu____79628  in
                                     uu____79533 :: uu____79586  in
                                   uu____79466 :: uu____79519  in
                                 uu____79399 :: uu____79452  in
                               uu____79355 :: uu____79385  in
                             uu____79314 :: uu____79341  in
                           uu____79273 :: uu____79300  in
                         uu____79234 :: uu____79259  in
                       uu____79199 :: uu____79220  in
                     uu____79164 :: uu____79185  in
                   uu____79129 :: uu____79150  in
                 uu____79094 :: uu____79115  in
               uu____79059 :: uu____79080  in
             uu____79007 :: uu____79045  in
           uu____78943 :: uu____78993  in
         uu____78894 :: uu____78929  in
       uu____78845 :: uu____78880  in
     uu____78803 :: uu____78831  in
   uu____78755 :: uu____78789)
  
let run_either :
  'Auu____81748 .
    Prims.int ->
      'Auu____81748 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____81748 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____81786 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____81786);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____81791 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____81791 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____81814 =
               let uu____81816 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____81816 expected  in
             FStar_Tests_Util.always i uu____81814)))
  
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
        let interp uu____81895 = run_interpreter i r expected  in
        let uu____81896 =
          let uu____81897 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____81897  in
        (i, uu____81896)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____81935 = run_nbe i r expected  in
        let uu____81936 =
          let uu____81937 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____81937  in
        (i, uu____81936)
  
let run_tests :
  'Auu____81948 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
           'Auu____81948)
      -> 'Auu____81948 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___742_82000  ->
            match uu___742_82000 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____82031  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____82034 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____82043  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____82046 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____82062  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____82092  ->
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
        let nbe1 uu____82137 = run_nbe i r expected  in
        let norm1 uu____82143 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____82156  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____82159 =
       let uu____82160 = encode (Prims.parse_int "1000")  in
       let uu____82162 =
         let uu____82165 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____82166 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____82165 uu____82166  in
       let_ FStar_Tests_Util.x uu____82160 uu____82162  in
     run_both_with_time (Prims.parse_int "14") uu____82159 z)
  
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
             let uu____82242 = res1  in
             match uu____82242 with
             | (t1,time_int) ->
                 let uu____82252 = res2  in
                 (match uu____82252 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____82264 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____82264 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____82275  ->
    (let uu____82277 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____82277);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  