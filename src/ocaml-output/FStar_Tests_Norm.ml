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
      (let uu____83323 =
         let uu____83326 = encode (n1 - (Prims.parse_int "1"))  in
         [uu____83326]  in
       FStar_Tests_Util.app succ uu____83323)
  
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
        let uu____83365 =
          let uu____83368 = let uu____83369 = b x1  in [uu____83369]  in
          FStar_Syntax_Util.abs uu____83368 e' FStar_Pervasives_Native.None
           in
        FStar_Tests_Util.app uu____83365 [e]
  
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
  let uu____83439 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____83439
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____83442 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____83442
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
    let uu____83461 =
      let uu____83468 =
        let uu____83469 =
          let uu____83486 = tm_fv snat_l  in
          let uu____83489 =
            let uu____83500 = FStar_Syntax_Syntax.as_arg s  in [uu____83500]
             in
          (uu____83486, uu____83489)  in
        FStar_Syntax_Syntax.Tm_app uu____83469  in
      FStar_Syntax_Syntax.mk uu____83468  in
    uu____83461 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____83545 .
    'Auu____83545 -> 'Auu____83545 FStar_Syntax_Syntax.withinfo_t
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
      let uu____83654 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____83654, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____83698 =
        let uu____83701 =
          let uu____83702 =
            let uu____83716 =
              let uu____83726 =
                let uu____83734 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____83734, false)  in
              [uu____83726]  in
            (snat_l, uu____83716)  in
          FStar_Syntax_Syntax.Pat_cons uu____83702  in
        pat uu____83701  in
      let uu____83764 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___763_83769 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___763_83769.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___763_83769.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____83698, FStar_Pervasives_Native.None, uu____83764)  in
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
        let uu____83810 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____83829 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____83810, FStar_Pervasives_Native.None, uu____83829)  in
      let sbranch =
        let uu____83857 =
          let uu____83860 =
            let uu____83861 =
              let uu____83875 =
                let uu____83885 =
                  let uu____83893 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____83893, false)  in
                [uu____83885]  in
              (snat_l, uu____83875)  in
            FStar_Syntax_Syntax.Pat_cons uu____83861  in
          pat uu____83860  in
        let uu____83923 =
          let uu____83926 = FStar_Tests_Util.nm minus1  in
          let uu____83929 =
            let uu____83932 =
              let uu____83933 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____83933  in
            let uu____83936 =
              let uu____83939 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____83939]  in
            uu____83932 :: uu____83936  in
          FStar_Tests_Util.app uu____83926 uu____83929  in
        (uu____83857, FStar_Pervasives_Native.None, uu____83923)  in
      let lb =
        let uu____83951 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____83955 =
          let uu____83958 =
            let uu____83959 =
              let uu____83960 = b FStar_Tests_Util.x  in
              let uu____83967 =
                let uu____83976 = b FStar_Tests_Util.y  in [uu____83976]  in
              uu____83960 :: uu____83967  in
            let uu____84001 =
              let uu____84004 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____84004 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____83959 uu____84001
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____83958
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____83951;
          FStar_Syntax_Syntax.lbdef = uu____83955;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____84011 =
        let uu____84018 =
          let uu____84019 =
            let uu____84033 =
              let uu____84036 =
                let uu____84037 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____84037 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____84036
               in
            ((true, [lb]), uu____84033)  in
          FStar_Syntax_Syntax.Tm_let uu____84019  in
        FStar_Syntax_Syntax.mk uu____84018  in
      uu____84011 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____84084 = snat out  in
         aux uu____84084 (n2 - (Prims.parse_int "1")))
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
  (let uu____84150 =
     let uu____84162 =
       let uu____84165 =
         let uu____84168 =
           let uu____84171 =
             let uu____84174 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____84174]  in
           id :: uu____84171  in
         one :: uu____84168  in
       FStar_Tests_Util.app apply uu____84165  in
     let uu____84175 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____84162, uu____84175)  in
   let uu____84184 =
     let uu____84198 =
       let uu____84210 =
         let uu____84213 =
           let uu____84216 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____84216]  in
         FStar_Tests_Util.app id uu____84213  in
       let uu____84217 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____84210, uu____84217)  in
     let uu____84226 =
       let uu____84240 =
         let uu____84252 =
           let uu____84255 =
             let uu____84258 =
               let uu____84261 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____84262 =
                 let uu____84265 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____84265]  in
               uu____84261 :: uu____84262  in
             tt :: uu____84258  in
           FStar_Tests_Util.app apply uu____84255  in
         let uu____84266 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____84252, uu____84266)  in
       let uu____84275 =
         let uu____84289 =
           let uu____84301 =
             let uu____84304 =
               let uu____84307 =
                 let uu____84310 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____84311 =
                   let uu____84314 = FStar_Tests_Util.nm FStar_Tests_Util.m
                      in
                   [uu____84314]  in
                 uu____84310 :: uu____84311  in
               ff :: uu____84307  in
             FStar_Tests_Util.app apply uu____84304  in
           let uu____84315 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____84301, uu____84315)  in
         let uu____84324 =
           let uu____84338 =
             let uu____84350 =
               let uu____84353 =
                 let uu____84356 =
                   let uu____84359 =
                     let uu____84362 =
                       let uu____84365 =
                         let uu____84368 =
                           let uu____84371 =
                             let uu____84374 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____84375 =
                               let uu____84378 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____84378]  in
                             uu____84374 :: uu____84375  in
                           ff :: uu____84371  in
                         apply :: uu____84368  in
                       apply :: uu____84365  in
                     apply :: uu____84362  in
                   apply :: uu____84359  in
                 apply :: uu____84356  in
               FStar_Tests_Util.app apply uu____84353  in
             let uu____84379 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____84350, uu____84379)  in
           let uu____84388 =
             let uu____84402 =
               let uu____84414 =
                 let uu____84417 =
                   let uu____84420 =
                     let uu____84423 =
                       let uu____84426 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n  in
                       let uu____84427 =
                         let uu____84430 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____84430]  in
                       uu____84426 :: uu____84427  in
                     ff :: uu____84423  in
                   apply :: uu____84420  in
                 FStar_Tests_Util.app twice uu____84417  in
               let uu____84431 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____84414, uu____84431)  in
             let uu____84440 =
               let uu____84454 =
                 let uu____84466 = minus one z  in
                 ((Prims.parse_int "5"), uu____84466, one)  in
               let uu____84475 =
                 let uu____84489 =
                   let uu____84501 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____84501, z)  in
                 let uu____84510 =
                   let uu____84524 =
                     let uu____84536 = minus one one  in
                     ((Prims.parse_int "7"), uu____84536, z)  in
                   let uu____84545 =
                     let uu____84559 =
                       let uu____84571 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____84571, one)  in
                     let uu____84580 =
                       let uu____84594 =
                         let uu____84606 =
                           FStar_Tests_Util.app mul [two; one]  in
                         ((Prims.parse_int "9"), uu____84606, two)  in
                       let uu____84615 =
                         let uu____84629 =
                           let uu____84641 =
                             let uu____84644 =
                               let uu____84647 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____84647; one]  in
                             FStar_Tests_Util.app mul uu____84644  in
                           ((Prims.parse_int "10"), uu____84641, two)  in
                         let uu____84654 =
                           let uu____84668 =
                             let uu____84680 =
                               let uu____84683 =
                                 encode (Prims.parse_int "10")  in
                               let uu____84685 =
                                 encode (Prims.parse_int "10")  in
                               minus uu____84683 uu____84685  in
                             ((Prims.parse_int "11"), uu____84680, z)  in
                           let uu____84695 =
                             let uu____84709 =
                               let uu____84721 =
                                 let uu____84724 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____84726 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____84724 uu____84726  in
                               ((Prims.parse_int "12"), uu____84721, z)  in
                             let uu____84736 =
                               let uu____84750 =
                                 let uu____84762 =
                                   let uu____84765 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____84767 =
                                     let uu____84770 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____84771 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____84770 uu____84771  in
                                   let_ FStar_Tests_Util.x uu____84765
                                     uu____84767
                                    in
                                 ((Prims.parse_int "13"), uu____84762, z)  in
                               let uu____84780 =
                                 let uu____84794 =
                                   let uu____84806 =
                                     let uu____84809 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____84810 =
                                       let uu____84813 =
                                         let uu____84814 =
                                           let uu____84817 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____84818 =
                                             let uu____84821 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____84821]  in
                                           uu____84817 :: uu____84818  in
                                         FStar_Tests_Util.app mul uu____84814
                                          in
                                       let uu____84822 =
                                         let uu____84825 =
                                           let uu____84826 =
                                             let uu____84829 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____84830 =
                                               let uu____84833 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____84833]  in
                                             uu____84829 :: uu____84830  in
                                           FStar_Tests_Util.app mul
                                             uu____84826
                                            in
                                         let uu____84834 =
                                           let uu____84837 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____84838 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____84837 uu____84838  in
                                         let_ FStar_Tests_Util.h uu____84825
                                           uu____84834
                                          in
                                       let_ FStar_Tests_Util.y uu____84813
                                         uu____84822
                                        in
                                     let_ FStar_Tests_Util.x uu____84809
                                       uu____84810
                                      in
                                   ((Prims.parse_int "15"), uu____84806, z)
                                    in
                                 let uu____84847 =
                                   let uu____84861 =
                                     let uu____84873 =
                                       let uu____84876 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____84879 =
                                         let uu____84880 =
                                           let uu____84883 =
                                             let uu____84886 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____84887 =
                                               let uu____84890 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____84890]  in
                                             uu____84886 :: uu____84887  in
                                           FStar_Tests_Util.app mul
                                             uu____84883
                                            in
                                         let uu____84891 =
                                           let uu____84892 =
                                             let uu____84895 =
                                               let uu____84898 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____84899 =
                                                 let uu____84902 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____84902]  in
                                               uu____84898 :: uu____84899  in
                                             FStar_Tests_Util.app mul
                                               uu____84895
                                              in
                                           let uu____84903 =
                                             let uu____84904 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____84905 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____84904 uu____84905
                                              in
                                           mk_let FStar_Tests_Util.h
                                             uu____84892 uu____84903
                                            in
                                         mk_let FStar_Tests_Util.y
                                           uu____84880 uu____84891
                                          in
                                       mk_let FStar_Tests_Util.x uu____84876
                                         uu____84879
                                        in
                                     ((Prims.parse_int "16"), uu____84873, z)
                                      in
                                   let uu____84914 =
                                     let uu____84928 =
                                       let uu____84940 =
                                         let uu____84943 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____84944 =
                                           let uu____84947 =
                                             let uu____84948 =
                                               let uu____84951 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____84952 =
                                                 let uu____84955 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____84955]  in
                                               uu____84951 :: uu____84952  in
                                             FStar_Tests_Util.app mul
                                               uu____84948
                                              in
                                           let uu____84956 =
                                             let uu____84959 =
                                               let uu____84960 =
                                                 let uu____84963 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____84964 =
                                                   let uu____84967 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____84967]  in
                                                 uu____84963 :: uu____84964
                                                  in
                                               FStar_Tests_Util.app mul
                                                 uu____84960
                                                in
                                             let uu____84968 =
                                               let uu____84971 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____84972 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____84971 uu____84972
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____84959 uu____84968
                                              in
                                           let_ FStar_Tests_Util.y
                                             uu____84947 uu____84956
                                            in
                                         let_ FStar_Tests_Util.x uu____84943
                                           uu____84944
                                          in
                                       ((Prims.parse_int "17"), uu____84940,
                                         z)
                                        in
                                     let uu____84981 =
                                       let uu____84995 =
                                         let uu____85007 =
                                           let uu____85010 =
                                             let uu____85013 = snat znat  in
                                             snat uu____85013  in
                                           pred_nat uu____85010  in
                                         let uu____85014 = snat znat  in
                                         ((Prims.parse_int "18"),
                                           uu____85007, uu____85014)
                                          in
                                       let uu____85023 =
                                         let uu____85037 =
                                           let uu____85049 =
                                             let uu____85052 =
                                               let uu____85053 =
                                                 let uu____85054 = snat znat
                                                    in
                                                 snat uu____85054  in
                                               let uu____85055 = snat znat
                                                  in
                                               minus_nat uu____85053
                                                 uu____85055
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____85052
                                              in
                                           let uu____85056 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____85049, uu____85056)
                                            in
                                         let uu____85065 =
                                           let uu____85079 =
                                             let uu____85091 =
                                               let uu____85094 =
                                                 let uu____85095 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 let uu____85097 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 minus_nat uu____85095
                                                   uu____85097
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____85094
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____85091, znat)
                                              in
                                           let uu____85105 =
                                             let uu____85119 =
                                               let uu____85131 =
                                                 let uu____85134 =
                                                   let uu____85135 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   let uu____85137 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   minus_nat uu____85135
                                                     uu____85137
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____85134
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____85131, znat)
                                                in
                                             let uu____85145 =
                                               let uu____85159 =
                                                 let uu____85171 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____85175 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____85171, uu____85175)
                                                  in
                                               let uu____85185 =
                                                 let uu____85199 =
                                                   let uu____85211 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____85215 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____85211,
                                                     uu____85215)
                                                    in
                                                 let uu____85225 =
                                                   let uu____85239 =
                                                     let uu____85251 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____85255 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____85251,
                                                       uu____85255)
                                                      in
                                                   let uu____85265 =
                                                     let uu____85279 =
                                                       let uu____85291 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____85295 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____85291,
                                                         uu____85295)
                                                        in
                                                     let uu____85305 =
                                                       let uu____85319 =
                                                         let uu____85331 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____85335 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____85331,
                                                           uu____85335)
                                                          in
                                                       let uu____85345 =
                                                         let uu____85359 =
                                                           let uu____85371 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____85375 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____85371,
                                                             uu____85375)
                                                            in
                                                         let uu____85385 =
                                                           let uu____85399 =
                                                             let uu____85411
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____85415
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____85411,
                                                               uu____85415)
                                                              in
                                                           let uu____85425 =
                                                             let uu____85439
                                                               =
                                                               let uu____85451
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____85455
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____85451,
                                                                 uu____85455)
                                                                in
                                                             let uu____85465
                                                               =
                                                               let uu____85479
                                                                 =
                                                                 let uu____85491
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____85495
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____85491,
                                                                   uu____85495)
                                                                  in
                                                               let uu____85505
                                                                 =
                                                                 let uu____85519
                                                                   =
                                                                   let uu____85531
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____85535
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____85531,
                                                                    uu____85535)
                                                                    in
                                                                 let uu____85545
                                                                   =
                                                                   let uu____85559
                                                                    =
                                                                    let uu____85571
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____85575
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____85571,
                                                                    uu____85575)
                                                                     in
                                                                   let uu____85585
                                                                    =
                                                                    let uu____85599
                                                                    =
                                                                    let uu____85611
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____85615
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____85611,
                                                                    uu____85615)
                                                                     in
                                                                    let uu____85625
                                                                    =
                                                                    let uu____85639
                                                                    =
                                                                    let uu____85651
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____85655
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____85651,
                                                                    uu____85655)
                                                                     in
                                                                    let uu____85665
                                                                    =
                                                                    let uu____85679
                                                                    =
                                                                    let uu____85691
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____85695
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____85691,
                                                                    uu____85695)
                                                                     in
                                                                    let uu____85705
                                                                    =
                                                                    let uu____85719
                                                                    =
                                                                    let uu____85731
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____85735
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____85731,
                                                                    uu____85735)
                                                                     in
                                                                    let uu____85745
                                                                    =
                                                                    let uu____85759
                                                                    =
                                                                    let uu____85771
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____85775
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____85771,
                                                                    uu____85775)
                                                                     in
                                                                    let uu____85785
                                                                    =
                                                                    let uu____85799
                                                                    =
                                                                    let uu____85811
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____85815
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____85811,
                                                                    uu____85815)
                                                                     in
                                                                    let uu____85825
                                                                    =
                                                                    let uu____85839
                                                                    =
                                                                    let uu____85851
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____85855
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____85851,
                                                                    uu____85855)
                                                                     in
                                                                    let uu____85865
                                                                    =
                                                                    let uu____85879
                                                                    =
                                                                    let uu____85891
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____85895
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____85891,
                                                                    uu____85895)
                                                                     in
                                                                    let uu____85905
                                                                    =
                                                                    let uu____85919
                                                                    =
                                                                    let uu____85931
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____85935
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____85931,
                                                                    uu____85935)
                                                                     in
                                                                    let uu____85945
                                                                    =
                                                                    let uu____85959
                                                                    =
                                                                    let uu____85971
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____85975
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____85971,
                                                                    uu____85975)
                                                                     in
                                                                    let uu____85985
                                                                    =
                                                                    let uu____85999
                                                                    =
                                                                    let uu____86011
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____86015
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____86011,
                                                                    uu____86015)
                                                                     in
                                                                    let uu____86025
                                                                    =
                                                                    let uu____86039
                                                                    =
                                                                    let uu____86051
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____86055
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____86051,
                                                                    uu____86055)
                                                                     in
                                                                    let uu____86065
                                                                    =
                                                                    let uu____86079
                                                                    =
                                                                    let uu____86091
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____86095
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____86091,
                                                                    uu____86095)
                                                                     in
                                                                    let uu____86105
                                                                    =
                                                                    let uu____86119
                                                                    =
                                                                    let uu____86131
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____86135
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____86131,
                                                                    uu____86135)
                                                                     in
                                                                    let uu____86145
                                                                    =
                                                                    let uu____86159
                                                                    =
                                                                    let uu____86171
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____86175
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____86171,
                                                                    uu____86175)
                                                                     in
                                                                    let uu____86185
                                                                    =
                                                                    let uu____86199
                                                                    =
                                                                    let uu____86211
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____86215
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____86211,
                                                                    uu____86215)
                                                                     in
                                                                    let uu____86225
                                                                    =
                                                                    let uu____86239
                                                                    =
                                                                    let uu____86251
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____86255
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____86251,
                                                                    uu____86255)
                                                                     in
                                                                    let uu____86265
                                                                    =
                                                                    let uu____86279
                                                                    =
                                                                    let uu____86291
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____86295
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____86291,
                                                                    uu____86295)
                                                                     in
                                                                    let uu____86305
                                                                    =
                                                                    let uu____86319
                                                                    =
                                                                    let uu____86331
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____86335
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____86331,
                                                                    uu____86335)
                                                                     in
                                                                    let uu____86345
                                                                    =
                                                                    let uu____86359
                                                                    =
                                                                    let uu____86371
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____86375
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____86371,
                                                                    uu____86375)
                                                                     in
                                                                    let uu____86385
                                                                    =
                                                                    let uu____86399
                                                                    =
                                                                    let uu____86411
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____86415
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____86411,
                                                                    uu____86415)
                                                                     in
                                                                    let uu____86425
                                                                    =
                                                                    let uu____86439
                                                                    =
                                                                    let uu____86451
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____86455
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____86451,
                                                                    uu____86455)
                                                                     in
                                                                    let uu____86465
                                                                    =
                                                                    let uu____86479
                                                                    =
                                                                    let uu____86491
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____86495
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____86491,
                                                                    uu____86495)
                                                                     in
                                                                    [uu____86479]
                                                                     in
                                                                    uu____86439
                                                                    ::
                                                                    uu____86465
                                                                     in
                                                                    uu____86399
                                                                    ::
                                                                    uu____86425
                                                                     in
                                                                    uu____86359
                                                                    ::
                                                                    uu____86385
                                                                     in
                                                                    uu____86319
                                                                    ::
                                                                    uu____86345
                                                                     in
                                                                    uu____86279
                                                                    ::
                                                                    uu____86305
                                                                     in
                                                                    uu____86239
                                                                    ::
                                                                    uu____86265
                                                                     in
                                                                    uu____86199
                                                                    ::
                                                                    uu____86225
                                                                     in
                                                                    uu____86159
                                                                    ::
                                                                    uu____86185
                                                                     in
                                                                    uu____86119
                                                                    ::
                                                                    uu____86145
                                                                     in
                                                                    uu____86079
                                                                    ::
                                                                    uu____86105
                                                                     in
                                                                    uu____86039
                                                                    ::
                                                                    uu____86065
                                                                     in
                                                                    uu____85999
                                                                    ::
                                                                    uu____86025
                                                                     in
                                                                    uu____85959
                                                                    ::
                                                                    uu____85985
                                                                     in
                                                                    uu____85919
                                                                    ::
                                                                    uu____85945
                                                                     in
                                                                    uu____85879
                                                                    ::
                                                                    uu____85905
                                                                     in
                                                                    uu____85839
                                                                    ::
                                                                    uu____85865
                                                                     in
                                                                    uu____85799
                                                                    ::
                                                                    uu____85825
                                                                     in
                                                                    uu____85759
                                                                    ::
                                                                    uu____85785
                                                                     in
                                                                    uu____85719
                                                                    ::
                                                                    uu____85745
                                                                     in
                                                                    uu____85679
                                                                    ::
                                                                    uu____85705
                                                                     in
                                                                    uu____85639
                                                                    ::
                                                                    uu____85665
                                                                     in
                                                                    uu____85599
                                                                    ::
                                                                    uu____85625
                                                                     in
                                                                   uu____85559
                                                                    ::
                                                                    uu____85585
                                                                    in
                                                                 uu____85519
                                                                   ::
                                                                   uu____85545
                                                                  in
                                                               uu____85479 ::
                                                                 uu____85505
                                                                in
                                                             uu____85439 ::
                                                               uu____85465
                                                              in
                                                           uu____85399 ::
                                                             uu____85425
                                                            in
                                                         uu____85359 ::
                                                           uu____85385
                                                          in
                                                       uu____85319 ::
                                                         uu____85345
                                                        in
                                                     uu____85279 ::
                                                       uu____85305
                                                      in
                                                   uu____85239 :: uu____85265
                                                    in
                                                 uu____85199 :: uu____85225
                                                  in
                                               uu____85159 :: uu____85185  in
                                             uu____85119 :: uu____85145  in
                                           uu____85079 :: uu____85105  in
                                         uu____85037 :: uu____85065  in
                                       uu____84995 :: uu____85023  in
                                     uu____84928 :: uu____84981  in
                                   uu____84861 :: uu____84914  in
                                 uu____84794 :: uu____84847  in
                               uu____84750 :: uu____84780  in
                             uu____84709 :: uu____84736  in
                           uu____84668 :: uu____84695  in
                         uu____84629 :: uu____84654  in
                       uu____84594 :: uu____84615  in
                     uu____84559 :: uu____84580  in
                   uu____84524 :: uu____84545  in
                 uu____84489 :: uu____84510  in
               uu____84454 :: uu____84475  in
             uu____84402 :: uu____84440  in
           uu____84338 :: uu____84388  in
         uu____84289 :: uu____84324  in
       uu____84240 :: uu____84275  in
     uu____84198 :: uu____84226  in
   uu____84150 :: uu____84184)
  
let run_either :
  'Auu____87143 .
    Prims.int ->
      'Auu____87143 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____87143 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____87181 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____87181);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____87186 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____87186 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____87209 =
               let uu____87211 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____87211 expected  in
             FStar_Tests_Util.always i uu____87209)))
  
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
        let interp uu____87290 = run_interpreter i r expected  in
        let uu____87291 =
          let uu____87292 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____87292  in
        (i, uu____87291)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____87330 = run_nbe i r expected  in
        let uu____87331 =
          let uu____87332 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____87332  in
        (i, uu____87331)
  
let run_tests :
  'Auu____87343 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
           'Auu____87343)
      -> 'Auu____87343 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___742_87395  ->
            match uu___742_87395 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____87426  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____87429 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____87438  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____87441 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____87457  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____87487  ->
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
        let nbe1 uu____87532 = run_nbe i r expected  in
        let norm1 uu____87538 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____87551  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____87554 =
       let uu____87555 = encode (Prims.parse_int "1000")  in
       let uu____87557 =
         let uu____87560 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____87561 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____87560 uu____87561  in
       let_ FStar_Tests_Util.x uu____87555 uu____87557  in
     run_both_with_time (Prims.parse_int "14") uu____87554 z)
  
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
             let uu____87637 = res1  in
             match uu____87637 with
             | (t1,time_int) ->
                 let uu____87647 = res2  in
                 (match uu____87647 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____87659 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____87659 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____87670  ->
    (let uu____87672 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____87672);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  