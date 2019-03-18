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
      (let uu____78135 =
         let uu____78138 = encode (n1 - (Prims.parse_int "1"))  in
         [uu____78138]  in
       FStar_Tests_Util.app succ uu____78135)
  
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
        let uu____78177 =
          let uu____78180 = let uu____78181 = b x1  in [uu____78181]  in
          FStar_Syntax_Util.abs uu____78180 e' FStar_Pervasives_Native.None
           in
        FStar_Tests_Util.app uu____78177 [e]
  
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
  let uu____78251 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____78251
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____78254 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____78254
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
    let uu____78273 =
      let uu____78280 =
        let uu____78281 =
          let uu____78298 = tm_fv snat_l  in
          let uu____78301 =
            let uu____78312 = FStar_Syntax_Syntax.as_arg s  in [uu____78312]
             in
          (uu____78298, uu____78301)  in
        FStar_Syntax_Syntax.Tm_app uu____78281  in
      FStar_Syntax_Syntax.mk uu____78280  in
    uu____78273 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____78354 .
    'Auu____78354 -> 'Auu____78354 FStar_Syntax_Syntax.withinfo_t
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
      let uu____78463 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____78463, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____78507 =
        let uu____78510 =
          let uu____78511 =
            let uu____78525 =
              let uu____78535 =
                let uu____78543 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____78543, false)  in
              [uu____78535]  in
            (snat_l, uu____78525)  in
          FStar_Syntax_Syntax.Pat_cons uu____78511  in
        pat uu____78510  in
      let uu____78573 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___763_78578 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___763_78578.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___763_78578.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____78507, FStar_Pervasives_Native.None, uu____78573)  in
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
        let uu____78619 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____78638 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____78619, FStar_Pervasives_Native.None, uu____78638)  in
      let sbranch =
        let uu____78666 =
          let uu____78669 =
            let uu____78670 =
              let uu____78684 =
                let uu____78694 =
                  let uu____78702 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____78702, false)  in
                [uu____78694]  in
              (snat_l, uu____78684)  in
            FStar_Syntax_Syntax.Pat_cons uu____78670  in
          pat uu____78669  in
        let uu____78732 =
          let uu____78735 = FStar_Tests_Util.nm minus1  in
          let uu____78738 =
            let uu____78741 =
              let uu____78742 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____78742  in
            let uu____78745 =
              let uu____78748 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____78748]  in
            uu____78741 :: uu____78745  in
          FStar_Tests_Util.app uu____78735 uu____78738  in
        (uu____78666, FStar_Pervasives_Native.None, uu____78732)  in
      let lb =
        let uu____78760 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____78764 =
          let uu____78767 =
            let uu____78768 =
              let uu____78769 = b FStar_Tests_Util.x  in
              let uu____78776 =
                let uu____78785 = b FStar_Tests_Util.y  in [uu____78785]  in
              uu____78769 :: uu____78776  in
            let uu____78810 =
              let uu____78813 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____78813 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____78768 uu____78810
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____78767
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____78760;
          FStar_Syntax_Syntax.lbdef = uu____78764;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____78820 =
        let uu____78827 =
          let uu____78828 =
            let uu____78842 =
              let uu____78845 =
                let uu____78846 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____78846 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____78845
               in
            ((true, [lb]), uu____78842)  in
          FStar_Syntax_Syntax.Tm_let uu____78828  in
        FStar_Syntax_Syntax.mk uu____78827  in
      uu____78820 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____78890 = snat out  in
         aux uu____78890 (n2 - (Prims.parse_int "1")))
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
  (let uu____78956 =
     let uu____78968 =
       let uu____78971 =
         let uu____78974 =
           let uu____78977 =
             let uu____78980 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____78980]  in
           id :: uu____78977  in
         one :: uu____78974  in
       FStar_Tests_Util.app apply uu____78971  in
     let uu____78981 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____78968, uu____78981)  in
   let uu____78990 =
     let uu____79004 =
       let uu____79016 =
         let uu____79019 =
           let uu____79022 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____79022]  in
         FStar_Tests_Util.app id uu____79019  in
       let uu____79023 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____79016, uu____79023)  in
     let uu____79032 =
       let uu____79046 =
         let uu____79058 =
           let uu____79061 =
             let uu____79064 =
               let uu____79067 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____79068 =
                 let uu____79071 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____79071]  in
               uu____79067 :: uu____79068  in
             tt :: uu____79064  in
           FStar_Tests_Util.app apply uu____79061  in
         let uu____79072 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____79058, uu____79072)  in
       let uu____79081 =
         let uu____79095 =
           let uu____79107 =
             let uu____79110 =
               let uu____79113 =
                 let uu____79116 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____79117 =
                   let uu____79120 = FStar_Tests_Util.nm FStar_Tests_Util.m
                      in
                   [uu____79120]  in
                 uu____79116 :: uu____79117  in
               ff :: uu____79113  in
             FStar_Tests_Util.app apply uu____79110  in
           let uu____79121 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____79107, uu____79121)  in
         let uu____79130 =
           let uu____79144 =
             let uu____79156 =
               let uu____79159 =
                 let uu____79162 =
                   let uu____79165 =
                     let uu____79168 =
                       let uu____79171 =
                         let uu____79174 =
                           let uu____79177 =
                             let uu____79180 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____79181 =
                               let uu____79184 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____79184]  in
                             uu____79180 :: uu____79181  in
                           ff :: uu____79177  in
                         apply :: uu____79174  in
                       apply :: uu____79171  in
                     apply :: uu____79168  in
                   apply :: uu____79165  in
                 apply :: uu____79162  in
               FStar_Tests_Util.app apply uu____79159  in
             let uu____79185 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____79156, uu____79185)  in
           let uu____79194 =
             let uu____79208 =
               let uu____79220 =
                 let uu____79223 =
                   let uu____79226 =
                     let uu____79229 =
                       let uu____79232 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n  in
                       let uu____79233 =
                         let uu____79236 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____79236]  in
                       uu____79232 :: uu____79233  in
                     ff :: uu____79229  in
                   apply :: uu____79226  in
                 FStar_Tests_Util.app twice uu____79223  in
               let uu____79237 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____79220, uu____79237)  in
             let uu____79246 =
               let uu____79260 =
                 let uu____79272 = minus one z  in
                 ((Prims.parse_int "5"), uu____79272, one)  in
               let uu____79281 =
                 let uu____79295 =
                   let uu____79307 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____79307, z)  in
                 let uu____79316 =
                   let uu____79330 =
                     let uu____79342 = minus one one  in
                     ((Prims.parse_int "7"), uu____79342, z)  in
                   let uu____79351 =
                     let uu____79365 =
                       let uu____79377 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____79377, one)  in
                     let uu____79386 =
                       let uu____79400 =
                         let uu____79412 =
                           FStar_Tests_Util.app mul [two; one]  in
                         ((Prims.parse_int "9"), uu____79412, two)  in
                       let uu____79421 =
                         let uu____79435 =
                           let uu____79447 =
                             let uu____79450 =
                               let uu____79453 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____79453; one]  in
                             FStar_Tests_Util.app mul uu____79450  in
                           ((Prims.parse_int "10"), uu____79447, two)  in
                         let uu____79460 =
                           let uu____79474 =
                             let uu____79486 =
                               let uu____79489 =
                                 encode (Prims.parse_int "10")  in
                               let uu____79491 =
                                 encode (Prims.parse_int "10")  in
                               minus uu____79489 uu____79491  in
                             ((Prims.parse_int "11"), uu____79486, z)  in
                           let uu____79501 =
                             let uu____79515 =
                               let uu____79527 =
                                 let uu____79530 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____79532 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____79530 uu____79532  in
                               ((Prims.parse_int "12"), uu____79527, z)  in
                             let uu____79542 =
                               let uu____79556 =
                                 let uu____79568 =
                                   let uu____79571 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____79573 =
                                     let uu____79576 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____79577 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____79576 uu____79577  in
                                   let_ FStar_Tests_Util.x uu____79571
                                     uu____79573
                                    in
                                 ((Prims.parse_int "13"), uu____79568, z)  in
                               let uu____79586 =
                                 let uu____79600 =
                                   let uu____79612 =
                                     let uu____79615 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____79616 =
                                       let uu____79619 =
                                         let uu____79620 =
                                           let uu____79623 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____79624 =
                                             let uu____79627 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____79627]  in
                                           uu____79623 :: uu____79624  in
                                         FStar_Tests_Util.app mul uu____79620
                                          in
                                       let uu____79628 =
                                         let uu____79631 =
                                           let uu____79632 =
                                             let uu____79635 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____79636 =
                                               let uu____79639 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____79639]  in
                                             uu____79635 :: uu____79636  in
                                           FStar_Tests_Util.app mul
                                             uu____79632
                                            in
                                         let uu____79640 =
                                           let uu____79643 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____79644 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____79643 uu____79644  in
                                         let_ FStar_Tests_Util.h uu____79631
                                           uu____79640
                                          in
                                       let_ FStar_Tests_Util.y uu____79619
                                         uu____79628
                                        in
                                     let_ FStar_Tests_Util.x uu____79615
                                       uu____79616
                                      in
                                   ((Prims.parse_int "15"), uu____79612, z)
                                    in
                                 let uu____79653 =
                                   let uu____79667 =
                                     let uu____79679 =
                                       let uu____79682 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____79685 =
                                         let uu____79686 =
                                           let uu____79689 =
                                             let uu____79692 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____79693 =
                                               let uu____79696 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____79696]  in
                                             uu____79692 :: uu____79693  in
                                           FStar_Tests_Util.app mul
                                             uu____79689
                                            in
                                         let uu____79697 =
                                           let uu____79698 =
                                             let uu____79701 =
                                               let uu____79704 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____79705 =
                                                 let uu____79708 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____79708]  in
                                               uu____79704 :: uu____79705  in
                                             FStar_Tests_Util.app mul
                                               uu____79701
                                              in
                                           let uu____79709 =
                                             let uu____79710 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____79711 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____79710 uu____79711
                                              in
                                           mk_let FStar_Tests_Util.h
                                             uu____79698 uu____79709
                                            in
                                         mk_let FStar_Tests_Util.y
                                           uu____79686 uu____79697
                                          in
                                       mk_let FStar_Tests_Util.x uu____79682
                                         uu____79685
                                        in
                                     ((Prims.parse_int "16"), uu____79679, z)
                                      in
                                   let uu____79720 =
                                     let uu____79734 =
                                       let uu____79746 =
                                         let uu____79749 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____79750 =
                                           let uu____79753 =
                                             let uu____79754 =
                                               let uu____79757 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____79758 =
                                                 let uu____79761 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____79761]  in
                                               uu____79757 :: uu____79758  in
                                             FStar_Tests_Util.app mul
                                               uu____79754
                                              in
                                           let uu____79762 =
                                             let uu____79765 =
                                               let uu____79766 =
                                                 let uu____79769 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____79770 =
                                                   let uu____79773 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____79773]  in
                                                 uu____79769 :: uu____79770
                                                  in
                                               FStar_Tests_Util.app mul
                                                 uu____79766
                                                in
                                             let uu____79774 =
                                               let uu____79777 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____79778 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____79777 uu____79778
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____79765 uu____79774
                                              in
                                           let_ FStar_Tests_Util.y
                                             uu____79753 uu____79762
                                            in
                                         let_ FStar_Tests_Util.x uu____79749
                                           uu____79750
                                          in
                                       ((Prims.parse_int "17"), uu____79746,
                                         z)
                                        in
                                     let uu____79787 =
                                       let uu____79801 =
                                         let uu____79813 =
                                           let uu____79816 =
                                             let uu____79819 = snat znat  in
                                             snat uu____79819  in
                                           pred_nat uu____79816  in
                                         let uu____79820 = snat znat  in
                                         ((Prims.parse_int "18"),
                                           uu____79813, uu____79820)
                                          in
                                       let uu____79829 =
                                         let uu____79843 =
                                           let uu____79855 =
                                             let uu____79858 =
                                               let uu____79859 =
                                                 let uu____79860 = snat znat
                                                    in
                                                 snat uu____79860  in
                                               let uu____79861 = snat znat
                                                  in
                                               minus_nat uu____79859
                                                 uu____79861
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____79858
                                              in
                                           let uu____79862 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____79855, uu____79862)
                                            in
                                         let uu____79871 =
                                           let uu____79885 =
                                             let uu____79897 =
                                               let uu____79900 =
                                                 let uu____79901 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 let uu____79903 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 minus_nat uu____79901
                                                   uu____79903
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____79900
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____79897, znat)
                                              in
                                           let uu____79911 =
                                             let uu____79925 =
                                               let uu____79937 =
                                                 let uu____79940 =
                                                   let uu____79941 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   let uu____79943 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   minus_nat uu____79941
                                                     uu____79943
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____79940
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____79937, znat)
                                                in
                                             let uu____79951 =
                                               let uu____79965 =
                                                 let uu____79977 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____79981 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____79977, uu____79981)
                                                  in
                                               let uu____79991 =
                                                 let uu____80005 =
                                                   let uu____80017 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____80021 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____80017,
                                                     uu____80021)
                                                    in
                                                 let uu____80031 =
                                                   let uu____80045 =
                                                     let uu____80057 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____80061 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____80057,
                                                       uu____80061)
                                                      in
                                                   let uu____80071 =
                                                     let uu____80085 =
                                                       let uu____80097 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____80101 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____80097,
                                                         uu____80101)
                                                        in
                                                     let uu____80111 =
                                                       let uu____80125 =
                                                         let uu____80137 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____80141 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____80137,
                                                           uu____80141)
                                                          in
                                                       let uu____80151 =
                                                         let uu____80165 =
                                                           let uu____80177 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____80181 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____80177,
                                                             uu____80181)
                                                            in
                                                         let uu____80191 =
                                                           let uu____80205 =
                                                             let uu____80217
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____80221
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____80217,
                                                               uu____80221)
                                                              in
                                                           let uu____80231 =
                                                             let uu____80245
                                                               =
                                                               let uu____80257
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____80261
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____80257,
                                                                 uu____80261)
                                                                in
                                                             let uu____80271
                                                               =
                                                               let uu____80285
                                                                 =
                                                                 let uu____80297
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____80301
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____80297,
                                                                   uu____80301)
                                                                  in
                                                               let uu____80311
                                                                 =
                                                                 let uu____80325
                                                                   =
                                                                   let uu____80337
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____80341
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____80337,
                                                                    uu____80341)
                                                                    in
                                                                 let uu____80351
                                                                   =
                                                                   let uu____80365
                                                                    =
                                                                    let uu____80377
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____80381
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____80377,
                                                                    uu____80381)
                                                                     in
                                                                   let uu____80391
                                                                    =
                                                                    let uu____80405
                                                                    =
                                                                    let uu____80417
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____80421
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____80417,
                                                                    uu____80421)
                                                                     in
                                                                    let uu____80431
                                                                    =
                                                                    let uu____80445
                                                                    =
                                                                    let uu____80457
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____80461
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____80457,
                                                                    uu____80461)
                                                                     in
                                                                    let uu____80471
                                                                    =
                                                                    let uu____80485
                                                                    =
                                                                    let uu____80497
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____80501
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____80497,
                                                                    uu____80501)
                                                                     in
                                                                    let uu____80511
                                                                    =
                                                                    let uu____80525
                                                                    =
                                                                    let uu____80537
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____80541
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____80537,
                                                                    uu____80541)
                                                                     in
                                                                    let uu____80551
                                                                    =
                                                                    let uu____80565
                                                                    =
                                                                    let uu____80577
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____80581
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____80577,
                                                                    uu____80581)
                                                                     in
                                                                    let uu____80591
                                                                    =
                                                                    let uu____80605
                                                                    =
                                                                    let uu____80617
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____80621
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____80617,
                                                                    uu____80621)
                                                                     in
                                                                    let uu____80631
                                                                    =
                                                                    let uu____80645
                                                                    =
                                                                    let uu____80657
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____80661
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____80657,
                                                                    uu____80661)
                                                                     in
                                                                    let uu____80671
                                                                    =
                                                                    let uu____80685
                                                                    =
                                                                    let uu____80697
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____80701
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____80697,
                                                                    uu____80701)
                                                                     in
                                                                    let uu____80711
                                                                    =
                                                                    let uu____80725
                                                                    =
                                                                    let uu____80737
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____80741
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____80737,
                                                                    uu____80741)
                                                                     in
                                                                    let uu____80751
                                                                    =
                                                                    let uu____80765
                                                                    =
                                                                    let uu____80777
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____80781
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____80777,
                                                                    uu____80781)
                                                                     in
                                                                    let uu____80791
                                                                    =
                                                                    let uu____80805
                                                                    =
                                                                    let uu____80817
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____80821
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____80817,
                                                                    uu____80821)
                                                                     in
                                                                    let uu____80831
                                                                    =
                                                                    let uu____80845
                                                                    =
                                                                    let uu____80857
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____80861
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____80857,
                                                                    uu____80861)
                                                                     in
                                                                    let uu____80871
                                                                    =
                                                                    let uu____80885
                                                                    =
                                                                    let uu____80897
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____80901
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____80897,
                                                                    uu____80901)
                                                                     in
                                                                    let uu____80911
                                                                    =
                                                                    let uu____80925
                                                                    =
                                                                    let uu____80937
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____80941
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____80937,
                                                                    uu____80941)
                                                                     in
                                                                    let uu____80951
                                                                    =
                                                                    let uu____80965
                                                                    =
                                                                    let uu____80977
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____80981
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____80977,
                                                                    uu____80981)
                                                                     in
                                                                    let uu____80991
                                                                    =
                                                                    let uu____81005
                                                                    =
                                                                    let uu____81017
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____81021
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____81017,
                                                                    uu____81021)
                                                                     in
                                                                    let uu____81031
                                                                    =
                                                                    let uu____81045
                                                                    =
                                                                    let uu____81057
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____81061
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____81057,
                                                                    uu____81061)
                                                                     in
                                                                    let uu____81071
                                                                    =
                                                                    let uu____81085
                                                                    =
                                                                    let uu____81097
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____81101
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____81097,
                                                                    uu____81101)
                                                                     in
                                                                    let uu____81111
                                                                    =
                                                                    let uu____81125
                                                                    =
                                                                    let uu____81137
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____81141
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____81137,
                                                                    uu____81141)
                                                                     in
                                                                    let uu____81151
                                                                    =
                                                                    let uu____81165
                                                                    =
                                                                    let uu____81177
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____81181
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____81177,
                                                                    uu____81181)
                                                                     in
                                                                    let uu____81191
                                                                    =
                                                                    let uu____81205
                                                                    =
                                                                    let uu____81217
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____81221
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____81217,
                                                                    uu____81221)
                                                                     in
                                                                    let uu____81231
                                                                    =
                                                                    let uu____81245
                                                                    =
                                                                    let uu____81257
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____81261
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____81257,
                                                                    uu____81261)
                                                                     in
                                                                    let uu____81271
                                                                    =
                                                                    let uu____81285
                                                                    =
                                                                    let uu____81297
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____81301
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____81297,
                                                                    uu____81301)
                                                                     in
                                                                    [uu____81285]
                                                                     in
                                                                    uu____81245
                                                                    ::
                                                                    uu____81271
                                                                     in
                                                                    uu____81205
                                                                    ::
                                                                    uu____81231
                                                                     in
                                                                    uu____81165
                                                                    ::
                                                                    uu____81191
                                                                     in
                                                                    uu____81125
                                                                    ::
                                                                    uu____81151
                                                                     in
                                                                    uu____81085
                                                                    ::
                                                                    uu____81111
                                                                     in
                                                                    uu____81045
                                                                    ::
                                                                    uu____81071
                                                                     in
                                                                    uu____81005
                                                                    ::
                                                                    uu____81031
                                                                     in
                                                                    uu____80965
                                                                    ::
                                                                    uu____80991
                                                                     in
                                                                    uu____80925
                                                                    ::
                                                                    uu____80951
                                                                     in
                                                                    uu____80885
                                                                    ::
                                                                    uu____80911
                                                                     in
                                                                    uu____80845
                                                                    ::
                                                                    uu____80871
                                                                     in
                                                                    uu____80805
                                                                    ::
                                                                    uu____80831
                                                                     in
                                                                    uu____80765
                                                                    ::
                                                                    uu____80791
                                                                     in
                                                                    uu____80725
                                                                    ::
                                                                    uu____80751
                                                                     in
                                                                    uu____80685
                                                                    ::
                                                                    uu____80711
                                                                     in
                                                                    uu____80645
                                                                    ::
                                                                    uu____80671
                                                                     in
                                                                    uu____80605
                                                                    ::
                                                                    uu____80631
                                                                     in
                                                                    uu____80565
                                                                    ::
                                                                    uu____80591
                                                                     in
                                                                    uu____80525
                                                                    ::
                                                                    uu____80551
                                                                     in
                                                                    uu____80485
                                                                    ::
                                                                    uu____80511
                                                                     in
                                                                    uu____80445
                                                                    ::
                                                                    uu____80471
                                                                     in
                                                                    uu____80405
                                                                    ::
                                                                    uu____80431
                                                                     in
                                                                   uu____80365
                                                                    ::
                                                                    uu____80391
                                                                    in
                                                                 uu____80325
                                                                   ::
                                                                   uu____80351
                                                                  in
                                                               uu____80285 ::
                                                                 uu____80311
                                                                in
                                                             uu____80245 ::
                                                               uu____80271
                                                              in
                                                           uu____80205 ::
                                                             uu____80231
                                                            in
                                                         uu____80165 ::
                                                           uu____80191
                                                          in
                                                       uu____80125 ::
                                                         uu____80151
                                                        in
                                                     uu____80085 ::
                                                       uu____80111
                                                      in
                                                   uu____80045 :: uu____80071
                                                    in
                                                 uu____80005 :: uu____80031
                                                  in
                                               uu____79965 :: uu____79991  in
                                             uu____79925 :: uu____79951  in
                                           uu____79885 :: uu____79911  in
                                         uu____79843 :: uu____79871  in
                                       uu____79801 :: uu____79829  in
                                     uu____79734 :: uu____79787  in
                                   uu____79667 :: uu____79720  in
                                 uu____79600 :: uu____79653  in
                               uu____79556 :: uu____79586  in
                             uu____79515 :: uu____79542  in
                           uu____79474 :: uu____79501  in
                         uu____79435 :: uu____79460  in
                       uu____79400 :: uu____79421  in
                     uu____79365 :: uu____79386  in
                   uu____79330 :: uu____79351  in
                 uu____79295 :: uu____79316  in
               uu____79260 :: uu____79281  in
             uu____79208 :: uu____79246  in
           uu____79144 :: uu____79194  in
         uu____79095 :: uu____79130  in
       uu____79046 :: uu____79081  in
     uu____79004 :: uu____79032  in
   uu____78956 :: uu____78990)
  
let run_either :
  'Auu____81949 .
    Prims.int ->
      'Auu____81949 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____81949 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____81987 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____81987);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____81992 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____81992 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____82015 =
               let uu____82017 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____82017 expected  in
             FStar_Tests_Util.always i uu____82015)))
  
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
        let interp uu____82096 = run_interpreter i r expected  in
        let uu____82097 =
          let uu____82098 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____82098  in
        (i, uu____82097)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____82136 = run_nbe i r expected  in
        let uu____82137 =
          let uu____82138 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____82138  in
        (i, uu____82137)
  
let run_tests :
  'Auu____82149 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
           'Auu____82149)
      -> 'Auu____82149 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___742_82201  ->
            match uu___742_82201 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____82232  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____82235 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____82244  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____82247 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____82263  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____82293  ->
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
        let nbe1 uu____82338 = run_nbe i r expected  in
        let norm1 uu____82344 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____82357  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____82360 =
       let uu____82361 = encode (Prims.parse_int "1000")  in
       let uu____82363 =
         let uu____82366 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____82367 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____82366 uu____82367  in
       let_ FStar_Tests_Util.x uu____82361 uu____82363  in
     run_both_with_time (Prims.parse_int "14") uu____82360 z)
  
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
             let uu____82443 = res1  in
             match uu____82443 with
             | (t1,time_int) ->
                 let uu____82453 = res2  in
                 (match uu____82453 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____82465 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____82465 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____82476  ->
    (let uu____82478 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____82478);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  