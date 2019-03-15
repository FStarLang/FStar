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
      (let uu____78010 =
         let uu____78013 = encode (n1 - (Prims.parse_int "1"))  in
         [uu____78013]  in
       FStar_Tests_Util.app succ uu____78010)
  
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
        let uu____78052 =
          let uu____78055 = let uu____78056 = b x1  in [uu____78056]  in
          FStar_Syntax_Util.abs uu____78055 e' FStar_Pervasives_Native.None
           in
        FStar_Tests_Util.app uu____78052 [e]
  
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
  let uu____78126 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____78126
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____78129 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____78129
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
    let uu____78148 =
      let uu____78155 =
        let uu____78156 =
          let uu____78173 = tm_fv snat_l  in
          let uu____78176 =
            let uu____78187 = FStar_Syntax_Syntax.as_arg s  in [uu____78187]
             in
          (uu____78173, uu____78176)  in
        FStar_Syntax_Syntax.Tm_app uu____78156  in
      FStar_Syntax_Syntax.mk uu____78155  in
    uu____78148 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____78229 .
    'Auu____78229 -> 'Auu____78229 FStar_Syntax_Syntax.withinfo_t
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
      let uu____78338 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____78338, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____78382 =
        let uu____78385 =
          let uu____78386 =
            let uu____78400 =
              let uu____78410 =
                let uu____78418 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____78418, false)  in
              [uu____78410]  in
            (snat_l, uu____78400)  in
          FStar_Syntax_Syntax.Pat_cons uu____78386  in
        pat uu____78385  in
      let uu____78448 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___763_78453 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___763_78453.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___763_78453.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____78382, FStar_Pervasives_Native.None, uu____78448)  in
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
        let uu____78494 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____78513 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____78494, FStar_Pervasives_Native.None, uu____78513)  in
      let sbranch =
        let uu____78541 =
          let uu____78544 =
            let uu____78545 =
              let uu____78559 =
                let uu____78569 =
                  let uu____78577 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____78577, false)  in
                [uu____78569]  in
              (snat_l, uu____78559)  in
            FStar_Syntax_Syntax.Pat_cons uu____78545  in
          pat uu____78544  in
        let uu____78607 =
          let uu____78610 = FStar_Tests_Util.nm minus1  in
          let uu____78613 =
            let uu____78616 =
              let uu____78617 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____78617  in
            let uu____78620 =
              let uu____78623 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____78623]  in
            uu____78616 :: uu____78620  in
          FStar_Tests_Util.app uu____78610 uu____78613  in
        (uu____78541, FStar_Pervasives_Native.None, uu____78607)  in
      let lb =
        let uu____78635 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____78639 =
          let uu____78642 =
            let uu____78643 =
              let uu____78644 = b FStar_Tests_Util.x  in
              let uu____78651 =
                let uu____78660 = b FStar_Tests_Util.y  in [uu____78660]  in
              uu____78644 :: uu____78651  in
            let uu____78685 =
              let uu____78688 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____78688 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____78643 uu____78685
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____78642
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____78635;
          FStar_Syntax_Syntax.lbdef = uu____78639;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____78695 =
        let uu____78702 =
          let uu____78703 =
            let uu____78717 =
              let uu____78720 =
                let uu____78721 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____78721 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____78720
               in
            ((true, [lb]), uu____78717)  in
          FStar_Syntax_Syntax.Tm_let uu____78703  in
        FStar_Syntax_Syntax.mk uu____78702  in
      uu____78695 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____78765 = snat out  in
         aux uu____78765 (n2 - (Prims.parse_int "1")))
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
  (let uu____78831 =
     let uu____78843 =
       let uu____78846 =
         let uu____78849 =
           let uu____78852 =
             let uu____78855 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____78855]  in
           id :: uu____78852  in
         one :: uu____78849  in
       FStar_Tests_Util.app apply uu____78846  in
     let uu____78856 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____78843, uu____78856)  in
   let uu____78865 =
     let uu____78879 =
       let uu____78891 =
         let uu____78894 =
           let uu____78897 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____78897]  in
         FStar_Tests_Util.app id uu____78894  in
       let uu____78898 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____78891, uu____78898)  in
     let uu____78907 =
       let uu____78921 =
         let uu____78933 =
           let uu____78936 =
             let uu____78939 =
               let uu____78942 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____78943 =
                 let uu____78946 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____78946]  in
               uu____78942 :: uu____78943  in
             tt :: uu____78939  in
           FStar_Tests_Util.app apply uu____78936  in
         let uu____78947 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____78933, uu____78947)  in
       let uu____78956 =
         let uu____78970 =
           let uu____78982 =
             let uu____78985 =
               let uu____78988 =
                 let uu____78991 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____78992 =
                   let uu____78995 = FStar_Tests_Util.nm FStar_Tests_Util.m
                      in
                   [uu____78995]  in
                 uu____78991 :: uu____78992  in
               ff :: uu____78988  in
             FStar_Tests_Util.app apply uu____78985  in
           let uu____78996 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____78982, uu____78996)  in
         let uu____79005 =
           let uu____79019 =
             let uu____79031 =
               let uu____79034 =
                 let uu____79037 =
                   let uu____79040 =
                     let uu____79043 =
                       let uu____79046 =
                         let uu____79049 =
                           let uu____79052 =
                             let uu____79055 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____79056 =
                               let uu____79059 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____79059]  in
                             uu____79055 :: uu____79056  in
                           ff :: uu____79052  in
                         apply :: uu____79049  in
                       apply :: uu____79046  in
                     apply :: uu____79043  in
                   apply :: uu____79040  in
                 apply :: uu____79037  in
               FStar_Tests_Util.app apply uu____79034  in
             let uu____79060 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____79031, uu____79060)  in
           let uu____79069 =
             let uu____79083 =
               let uu____79095 =
                 let uu____79098 =
                   let uu____79101 =
                     let uu____79104 =
                       let uu____79107 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n  in
                       let uu____79108 =
                         let uu____79111 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____79111]  in
                       uu____79107 :: uu____79108  in
                     ff :: uu____79104  in
                   apply :: uu____79101  in
                 FStar_Tests_Util.app twice uu____79098  in
               let uu____79112 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____79095, uu____79112)  in
             let uu____79121 =
               let uu____79135 =
                 let uu____79147 = minus one z  in
                 ((Prims.parse_int "5"), uu____79147, one)  in
               let uu____79156 =
                 let uu____79170 =
                   let uu____79182 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____79182, z)  in
                 let uu____79191 =
                   let uu____79205 =
                     let uu____79217 = minus one one  in
                     ((Prims.parse_int "7"), uu____79217, z)  in
                   let uu____79226 =
                     let uu____79240 =
                       let uu____79252 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____79252, one)  in
                     let uu____79261 =
                       let uu____79275 =
                         let uu____79287 =
                           FStar_Tests_Util.app mul [two; one]  in
                         ((Prims.parse_int "9"), uu____79287, two)  in
                       let uu____79296 =
                         let uu____79310 =
                           let uu____79322 =
                             let uu____79325 =
                               let uu____79328 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____79328; one]  in
                             FStar_Tests_Util.app mul uu____79325  in
                           ((Prims.parse_int "10"), uu____79322, two)  in
                         let uu____79335 =
                           let uu____79349 =
                             let uu____79361 =
                               let uu____79364 =
                                 encode (Prims.parse_int "10")  in
                               let uu____79366 =
                                 encode (Prims.parse_int "10")  in
                               minus uu____79364 uu____79366  in
                             ((Prims.parse_int "11"), uu____79361, z)  in
                           let uu____79376 =
                             let uu____79390 =
                               let uu____79402 =
                                 let uu____79405 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____79407 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____79405 uu____79407  in
                               ((Prims.parse_int "12"), uu____79402, z)  in
                             let uu____79417 =
                               let uu____79431 =
                                 let uu____79443 =
                                   let uu____79446 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____79448 =
                                     let uu____79451 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____79452 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____79451 uu____79452  in
                                   let_ FStar_Tests_Util.x uu____79446
                                     uu____79448
                                    in
                                 ((Prims.parse_int "13"), uu____79443, z)  in
                               let uu____79461 =
                                 let uu____79475 =
                                   let uu____79487 =
                                     let uu____79490 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____79491 =
                                       let uu____79494 =
                                         let uu____79495 =
                                           let uu____79498 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____79499 =
                                             let uu____79502 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____79502]  in
                                           uu____79498 :: uu____79499  in
                                         FStar_Tests_Util.app mul uu____79495
                                          in
                                       let uu____79503 =
                                         let uu____79506 =
                                           let uu____79507 =
                                             let uu____79510 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____79511 =
                                               let uu____79514 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____79514]  in
                                             uu____79510 :: uu____79511  in
                                           FStar_Tests_Util.app mul
                                             uu____79507
                                            in
                                         let uu____79515 =
                                           let uu____79518 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____79519 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____79518 uu____79519  in
                                         let_ FStar_Tests_Util.h uu____79506
                                           uu____79515
                                          in
                                       let_ FStar_Tests_Util.y uu____79494
                                         uu____79503
                                        in
                                     let_ FStar_Tests_Util.x uu____79490
                                       uu____79491
                                      in
                                   ((Prims.parse_int "15"), uu____79487, z)
                                    in
                                 let uu____79528 =
                                   let uu____79542 =
                                     let uu____79554 =
                                       let uu____79557 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____79560 =
                                         let uu____79561 =
                                           let uu____79564 =
                                             let uu____79567 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____79568 =
                                               let uu____79571 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____79571]  in
                                             uu____79567 :: uu____79568  in
                                           FStar_Tests_Util.app mul
                                             uu____79564
                                            in
                                         let uu____79572 =
                                           let uu____79573 =
                                             let uu____79576 =
                                               let uu____79579 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____79580 =
                                                 let uu____79583 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____79583]  in
                                               uu____79579 :: uu____79580  in
                                             FStar_Tests_Util.app mul
                                               uu____79576
                                              in
                                           let uu____79584 =
                                             let uu____79585 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____79586 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____79585 uu____79586
                                              in
                                           mk_let FStar_Tests_Util.h
                                             uu____79573 uu____79584
                                            in
                                         mk_let FStar_Tests_Util.y
                                           uu____79561 uu____79572
                                          in
                                       mk_let FStar_Tests_Util.x uu____79557
                                         uu____79560
                                        in
                                     ((Prims.parse_int "16"), uu____79554, z)
                                      in
                                   let uu____79595 =
                                     let uu____79609 =
                                       let uu____79621 =
                                         let uu____79624 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____79625 =
                                           let uu____79628 =
                                             let uu____79629 =
                                               let uu____79632 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____79633 =
                                                 let uu____79636 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____79636]  in
                                               uu____79632 :: uu____79633  in
                                             FStar_Tests_Util.app mul
                                               uu____79629
                                              in
                                           let uu____79637 =
                                             let uu____79640 =
                                               let uu____79641 =
                                                 let uu____79644 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____79645 =
                                                   let uu____79648 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____79648]  in
                                                 uu____79644 :: uu____79645
                                                  in
                                               FStar_Tests_Util.app mul
                                                 uu____79641
                                                in
                                             let uu____79649 =
                                               let uu____79652 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____79653 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____79652 uu____79653
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____79640 uu____79649
                                              in
                                           let_ FStar_Tests_Util.y
                                             uu____79628 uu____79637
                                            in
                                         let_ FStar_Tests_Util.x uu____79624
                                           uu____79625
                                          in
                                       ((Prims.parse_int "17"), uu____79621,
                                         z)
                                        in
                                     let uu____79662 =
                                       let uu____79676 =
                                         let uu____79688 =
                                           let uu____79691 =
                                             let uu____79694 = snat znat  in
                                             snat uu____79694  in
                                           pred_nat uu____79691  in
                                         let uu____79695 = snat znat  in
                                         ((Prims.parse_int "18"),
                                           uu____79688, uu____79695)
                                          in
                                       let uu____79704 =
                                         let uu____79718 =
                                           let uu____79730 =
                                             let uu____79733 =
                                               let uu____79734 =
                                                 let uu____79735 = snat znat
                                                    in
                                                 snat uu____79735  in
                                               let uu____79736 = snat znat
                                                  in
                                               minus_nat uu____79734
                                                 uu____79736
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____79733
                                              in
                                           let uu____79737 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____79730, uu____79737)
                                            in
                                         let uu____79746 =
                                           let uu____79760 =
                                             let uu____79772 =
                                               let uu____79775 =
                                                 let uu____79776 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 let uu____79778 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 minus_nat uu____79776
                                                   uu____79778
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____79775
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____79772, znat)
                                              in
                                           let uu____79786 =
                                             let uu____79800 =
                                               let uu____79812 =
                                                 let uu____79815 =
                                                   let uu____79816 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   let uu____79818 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   minus_nat uu____79816
                                                     uu____79818
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____79815
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____79812, znat)
                                                in
                                             let uu____79826 =
                                               let uu____79840 =
                                                 let uu____79852 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____79856 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____79852, uu____79856)
                                                  in
                                               let uu____79866 =
                                                 let uu____79880 =
                                                   let uu____79892 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____79896 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____79892,
                                                     uu____79896)
                                                    in
                                                 let uu____79906 =
                                                   let uu____79920 =
                                                     let uu____79932 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____79936 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____79932,
                                                       uu____79936)
                                                      in
                                                   let uu____79946 =
                                                     let uu____79960 =
                                                       let uu____79972 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____79976 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____79972,
                                                         uu____79976)
                                                        in
                                                     let uu____79986 =
                                                       let uu____80000 =
                                                         let uu____80012 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____80016 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____80012,
                                                           uu____80016)
                                                          in
                                                       let uu____80026 =
                                                         let uu____80040 =
                                                           let uu____80052 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____80056 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____80052,
                                                             uu____80056)
                                                            in
                                                         let uu____80066 =
                                                           let uu____80080 =
                                                             let uu____80092
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____80096
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____80092,
                                                               uu____80096)
                                                              in
                                                           let uu____80106 =
                                                             let uu____80120
                                                               =
                                                               let uu____80132
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____80136
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____80132,
                                                                 uu____80136)
                                                                in
                                                             let uu____80146
                                                               =
                                                               let uu____80160
                                                                 =
                                                                 let uu____80172
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____80176
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____80172,
                                                                   uu____80176)
                                                                  in
                                                               let uu____80186
                                                                 =
                                                                 let uu____80200
                                                                   =
                                                                   let uu____80212
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____80216
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____80212,
                                                                    uu____80216)
                                                                    in
                                                                 let uu____80226
                                                                   =
                                                                   let uu____80240
                                                                    =
                                                                    let uu____80252
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____80256
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____80252,
                                                                    uu____80256)
                                                                     in
                                                                   let uu____80266
                                                                    =
                                                                    let uu____80280
                                                                    =
                                                                    let uu____80292
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____80296
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____80292,
                                                                    uu____80296)
                                                                     in
                                                                    let uu____80306
                                                                    =
                                                                    let uu____80320
                                                                    =
                                                                    let uu____80332
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____80336
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____80332,
                                                                    uu____80336)
                                                                     in
                                                                    let uu____80346
                                                                    =
                                                                    let uu____80360
                                                                    =
                                                                    let uu____80372
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____80376
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____80372,
                                                                    uu____80376)
                                                                     in
                                                                    let uu____80386
                                                                    =
                                                                    let uu____80400
                                                                    =
                                                                    let uu____80412
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____80416
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____80412,
                                                                    uu____80416)
                                                                     in
                                                                    let uu____80426
                                                                    =
                                                                    let uu____80440
                                                                    =
                                                                    let uu____80452
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____80456
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____80452,
                                                                    uu____80456)
                                                                     in
                                                                    let uu____80466
                                                                    =
                                                                    let uu____80480
                                                                    =
                                                                    let uu____80492
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____80496
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____80492,
                                                                    uu____80496)
                                                                     in
                                                                    let uu____80506
                                                                    =
                                                                    let uu____80520
                                                                    =
                                                                    let uu____80532
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____80536
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____80532,
                                                                    uu____80536)
                                                                     in
                                                                    let uu____80546
                                                                    =
                                                                    let uu____80560
                                                                    =
                                                                    let uu____80572
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____80576
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____80572,
                                                                    uu____80576)
                                                                     in
                                                                    let uu____80586
                                                                    =
                                                                    let uu____80600
                                                                    =
                                                                    let uu____80612
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____80616
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____80612,
                                                                    uu____80616)
                                                                     in
                                                                    let uu____80626
                                                                    =
                                                                    let uu____80640
                                                                    =
                                                                    let uu____80652
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____80656
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____80652,
                                                                    uu____80656)
                                                                     in
                                                                    let uu____80666
                                                                    =
                                                                    let uu____80680
                                                                    =
                                                                    let uu____80692
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____80696
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____80692,
                                                                    uu____80696)
                                                                     in
                                                                    let uu____80706
                                                                    =
                                                                    let uu____80720
                                                                    =
                                                                    let uu____80732
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____80736
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____80732,
                                                                    uu____80736)
                                                                     in
                                                                    let uu____80746
                                                                    =
                                                                    let uu____80760
                                                                    =
                                                                    let uu____80772
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____80776
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____80772,
                                                                    uu____80776)
                                                                     in
                                                                    let uu____80786
                                                                    =
                                                                    let uu____80800
                                                                    =
                                                                    let uu____80812
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____80816
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____80812,
                                                                    uu____80816)
                                                                     in
                                                                    let uu____80826
                                                                    =
                                                                    let uu____80840
                                                                    =
                                                                    let uu____80852
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____80856
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____80852,
                                                                    uu____80856)
                                                                     in
                                                                    let uu____80866
                                                                    =
                                                                    let uu____80880
                                                                    =
                                                                    let uu____80892
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____80896
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____80892,
                                                                    uu____80896)
                                                                     in
                                                                    let uu____80906
                                                                    =
                                                                    let uu____80920
                                                                    =
                                                                    let uu____80932
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____80936
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____80932,
                                                                    uu____80936)
                                                                     in
                                                                    let uu____80946
                                                                    =
                                                                    let uu____80960
                                                                    =
                                                                    let uu____80972
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____80976
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____80972,
                                                                    uu____80976)
                                                                     in
                                                                    let uu____80986
                                                                    =
                                                                    let uu____81000
                                                                    =
                                                                    let uu____81012
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____81016
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____81012,
                                                                    uu____81016)
                                                                     in
                                                                    let uu____81026
                                                                    =
                                                                    let uu____81040
                                                                    =
                                                                    let uu____81052
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____81056
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____81052,
                                                                    uu____81056)
                                                                     in
                                                                    let uu____81066
                                                                    =
                                                                    let uu____81080
                                                                    =
                                                                    let uu____81092
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____81096
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____81092,
                                                                    uu____81096)
                                                                     in
                                                                    let uu____81106
                                                                    =
                                                                    let uu____81120
                                                                    =
                                                                    let uu____81132
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____81136
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____81132,
                                                                    uu____81136)
                                                                     in
                                                                    let uu____81146
                                                                    =
                                                                    let uu____81160
                                                                    =
                                                                    let uu____81172
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____81176
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____81172,
                                                                    uu____81176)
                                                                     in
                                                                    [uu____81160]
                                                                     in
                                                                    uu____81120
                                                                    ::
                                                                    uu____81146
                                                                     in
                                                                    uu____81080
                                                                    ::
                                                                    uu____81106
                                                                     in
                                                                    uu____81040
                                                                    ::
                                                                    uu____81066
                                                                     in
                                                                    uu____81000
                                                                    ::
                                                                    uu____81026
                                                                     in
                                                                    uu____80960
                                                                    ::
                                                                    uu____80986
                                                                     in
                                                                    uu____80920
                                                                    ::
                                                                    uu____80946
                                                                     in
                                                                    uu____80880
                                                                    ::
                                                                    uu____80906
                                                                     in
                                                                    uu____80840
                                                                    ::
                                                                    uu____80866
                                                                     in
                                                                    uu____80800
                                                                    ::
                                                                    uu____80826
                                                                     in
                                                                    uu____80760
                                                                    ::
                                                                    uu____80786
                                                                     in
                                                                    uu____80720
                                                                    ::
                                                                    uu____80746
                                                                     in
                                                                    uu____80680
                                                                    ::
                                                                    uu____80706
                                                                     in
                                                                    uu____80640
                                                                    ::
                                                                    uu____80666
                                                                     in
                                                                    uu____80600
                                                                    ::
                                                                    uu____80626
                                                                     in
                                                                    uu____80560
                                                                    ::
                                                                    uu____80586
                                                                     in
                                                                    uu____80520
                                                                    ::
                                                                    uu____80546
                                                                     in
                                                                    uu____80480
                                                                    ::
                                                                    uu____80506
                                                                     in
                                                                    uu____80440
                                                                    ::
                                                                    uu____80466
                                                                     in
                                                                    uu____80400
                                                                    ::
                                                                    uu____80426
                                                                     in
                                                                    uu____80360
                                                                    ::
                                                                    uu____80386
                                                                     in
                                                                    uu____80320
                                                                    ::
                                                                    uu____80346
                                                                     in
                                                                    uu____80280
                                                                    ::
                                                                    uu____80306
                                                                     in
                                                                   uu____80240
                                                                    ::
                                                                    uu____80266
                                                                    in
                                                                 uu____80200
                                                                   ::
                                                                   uu____80226
                                                                  in
                                                               uu____80160 ::
                                                                 uu____80186
                                                                in
                                                             uu____80120 ::
                                                               uu____80146
                                                              in
                                                           uu____80080 ::
                                                             uu____80106
                                                            in
                                                         uu____80040 ::
                                                           uu____80066
                                                          in
                                                       uu____80000 ::
                                                         uu____80026
                                                        in
                                                     uu____79960 ::
                                                       uu____79986
                                                      in
                                                   uu____79920 :: uu____79946
                                                    in
                                                 uu____79880 :: uu____79906
                                                  in
                                               uu____79840 :: uu____79866  in
                                             uu____79800 :: uu____79826  in
                                           uu____79760 :: uu____79786  in
                                         uu____79718 :: uu____79746  in
                                       uu____79676 :: uu____79704  in
                                     uu____79609 :: uu____79662  in
                                   uu____79542 :: uu____79595  in
                                 uu____79475 :: uu____79528  in
                               uu____79431 :: uu____79461  in
                             uu____79390 :: uu____79417  in
                           uu____79349 :: uu____79376  in
                         uu____79310 :: uu____79335  in
                       uu____79275 :: uu____79296  in
                     uu____79240 :: uu____79261  in
                   uu____79205 :: uu____79226  in
                 uu____79170 :: uu____79191  in
               uu____79135 :: uu____79156  in
             uu____79083 :: uu____79121  in
           uu____79019 :: uu____79069  in
         uu____78970 :: uu____79005  in
       uu____78921 :: uu____78956  in
     uu____78879 :: uu____78907  in
   uu____78831 :: uu____78865)
  
let run_either :
  'Auu____81824 .
    Prims.int ->
      'Auu____81824 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____81824 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____81862 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____81862);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____81867 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____81867 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____81890 =
               let uu____81892 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____81892 expected  in
             FStar_Tests_Util.always i uu____81890)))
  
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
        let interp uu____81971 = run_interpreter i r expected  in
        let uu____81972 =
          let uu____81973 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____81973  in
        (i, uu____81972)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____82011 = run_nbe i r expected  in
        let uu____82012 =
          let uu____82013 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____82013  in
        (i, uu____82012)
  
let run_tests :
  'Auu____82024 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
           'Auu____82024)
      -> 'Auu____82024 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___742_82076  ->
            match uu___742_82076 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____82107  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____82110 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____82119  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____82122 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____82138  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____82168  ->
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
        let nbe1 uu____82213 = run_nbe i r expected  in
        let norm1 uu____82219 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____82232  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____82235 =
       let uu____82236 = encode (Prims.parse_int "1000")  in
       let uu____82238 =
         let uu____82241 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____82242 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____82241 uu____82242  in
       let_ FStar_Tests_Util.x uu____82236 uu____82238  in
     run_both_with_time (Prims.parse_int "14") uu____82235 z)
  
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
             let uu____82318 = res1  in
             match uu____82318 with
             | (t1,time_int) ->
                 let uu____82328 = res2  in
                 (match uu____82328 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____82340 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____82340 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____82351  ->
    (let uu____82353 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____82353);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  