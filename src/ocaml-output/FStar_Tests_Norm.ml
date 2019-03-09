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
      (let uu____78023 =
         let uu____78026 = encode (n1 - (Prims.parse_int "1"))  in
         [uu____78026]  in
       FStar_Tests_Util.app succ uu____78023)
  
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
        let uu____78065 =
          let uu____78068 = let uu____78069 = b x1  in [uu____78069]  in
          FStar_Syntax_Util.abs uu____78068 e' FStar_Pervasives_Native.None
           in
        FStar_Tests_Util.app uu____78065 [e]
  
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
  let uu____78139 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____78139
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____78142 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____78142
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
    let uu____78161 =
      let uu____78168 =
        let uu____78169 =
          let uu____78186 = tm_fv snat_l  in
          let uu____78189 =
            let uu____78200 = FStar_Syntax_Syntax.as_arg s  in [uu____78200]
             in
          (uu____78186, uu____78189)  in
        FStar_Syntax_Syntax.Tm_app uu____78169  in
      FStar_Syntax_Syntax.mk uu____78168  in
    uu____78161 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____78242 .
    'Auu____78242 -> 'Auu____78242 FStar_Syntax_Syntax.withinfo_t
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
      let uu____78351 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____78351, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____78395 =
        let uu____78398 =
          let uu____78399 =
            let uu____78413 =
              let uu____78423 =
                let uu____78431 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____78431, false)  in
              [uu____78423]  in
            (snat_l, uu____78413)  in
          FStar_Syntax_Syntax.Pat_cons uu____78399  in
        pat uu____78398  in
      let uu____78461 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___763_78466 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___763_78466.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___763_78466.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____78395, FStar_Pervasives_Native.None, uu____78461)  in
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
        let uu____78507 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____78526 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____78507, FStar_Pervasives_Native.None, uu____78526)  in
      let sbranch =
        let uu____78554 =
          let uu____78557 =
            let uu____78558 =
              let uu____78572 =
                let uu____78582 =
                  let uu____78590 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____78590, false)  in
                [uu____78582]  in
              (snat_l, uu____78572)  in
            FStar_Syntax_Syntax.Pat_cons uu____78558  in
          pat uu____78557  in
        let uu____78620 =
          let uu____78623 = FStar_Tests_Util.nm minus1  in
          let uu____78626 =
            let uu____78629 =
              let uu____78630 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____78630  in
            let uu____78633 =
              let uu____78636 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____78636]  in
            uu____78629 :: uu____78633  in
          FStar_Tests_Util.app uu____78623 uu____78626  in
        (uu____78554, FStar_Pervasives_Native.None, uu____78620)  in
      let lb =
        let uu____78648 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____78652 =
          let uu____78655 =
            let uu____78656 =
              let uu____78657 = b FStar_Tests_Util.x  in
              let uu____78664 =
                let uu____78673 = b FStar_Tests_Util.y  in [uu____78673]  in
              uu____78657 :: uu____78664  in
            let uu____78698 =
              let uu____78701 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____78701 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____78656 uu____78698
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____78655
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____78648;
          FStar_Syntax_Syntax.lbdef = uu____78652;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____78708 =
        let uu____78715 =
          let uu____78716 =
            let uu____78730 =
              let uu____78733 =
                let uu____78734 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____78734 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____78733
               in
            ((true, [lb]), uu____78730)  in
          FStar_Syntax_Syntax.Tm_let uu____78716  in
        FStar_Syntax_Syntax.mk uu____78715  in
      uu____78708 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____78778 = snat out  in
         aux uu____78778 (n2 - (Prims.parse_int "1")))
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
  (let uu____78844 =
     let uu____78856 =
       let uu____78859 =
         let uu____78862 =
           let uu____78865 =
             let uu____78868 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____78868]  in
           id :: uu____78865  in
         one :: uu____78862  in
       FStar_Tests_Util.app apply uu____78859  in
     let uu____78869 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____78856, uu____78869)  in
   let uu____78878 =
     let uu____78892 =
       let uu____78904 =
         let uu____78907 =
           let uu____78910 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____78910]  in
         FStar_Tests_Util.app id uu____78907  in
       let uu____78911 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____78904, uu____78911)  in
     let uu____78920 =
       let uu____78934 =
         let uu____78946 =
           let uu____78949 =
             let uu____78952 =
               let uu____78955 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____78956 =
                 let uu____78959 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____78959]  in
               uu____78955 :: uu____78956  in
             tt :: uu____78952  in
           FStar_Tests_Util.app apply uu____78949  in
         let uu____78960 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____78946, uu____78960)  in
       let uu____78969 =
         let uu____78983 =
           let uu____78995 =
             let uu____78998 =
               let uu____79001 =
                 let uu____79004 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____79005 =
                   let uu____79008 = FStar_Tests_Util.nm FStar_Tests_Util.m
                      in
                   [uu____79008]  in
                 uu____79004 :: uu____79005  in
               ff :: uu____79001  in
             FStar_Tests_Util.app apply uu____78998  in
           let uu____79009 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____78995, uu____79009)  in
         let uu____79018 =
           let uu____79032 =
             let uu____79044 =
               let uu____79047 =
                 let uu____79050 =
                   let uu____79053 =
                     let uu____79056 =
                       let uu____79059 =
                         let uu____79062 =
                           let uu____79065 =
                             let uu____79068 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____79069 =
                               let uu____79072 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____79072]  in
                             uu____79068 :: uu____79069  in
                           ff :: uu____79065  in
                         apply :: uu____79062  in
                       apply :: uu____79059  in
                     apply :: uu____79056  in
                   apply :: uu____79053  in
                 apply :: uu____79050  in
               FStar_Tests_Util.app apply uu____79047  in
             let uu____79073 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____79044, uu____79073)  in
           let uu____79082 =
             let uu____79096 =
               let uu____79108 =
                 let uu____79111 =
                   let uu____79114 =
                     let uu____79117 =
                       let uu____79120 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n  in
                       let uu____79121 =
                         let uu____79124 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____79124]  in
                       uu____79120 :: uu____79121  in
                     ff :: uu____79117  in
                   apply :: uu____79114  in
                 FStar_Tests_Util.app twice uu____79111  in
               let uu____79125 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____79108, uu____79125)  in
             let uu____79134 =
               let uu____79148 =
                 let uu____79160 = minus one z  in
                 ((Prims.parse_int "5"), uu____79160, one)  in
               let uu____79169 =
                 let uu____79183 =
                   let uu____79195 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____79195, z)  in
                 let uu____79204 =
                   let uu____79218 =
                     let uu____79230 = minus one one  in
                     ((Prims.parse_int "7"), uu____79230, z)  in
                   let uu____79239 =
                     let uu____79253 =
                       let uu____79265 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____79265, one)  in
                     let uu____79274 =
                       let uu____79288 =
                         let uu____79300 =
                           FStar_Tests_Util.app mul [two; one]  in
                         ((Prims.parse_int "9"), uu____79300, two)  in
                       let uu____79309 =
                         let uu____79323 =
                           let uu____79335 =
                             let uu____79338 =
                               let uu____79341 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____79341; one]  in
                             FStar_Tests_Util.app mul uu____79338  in
                           ((Prims.parse_int "10"), uu____79335, two)  in
                         let uu____79348 =
                           let uu____79362 =
                             let uu____79374 =
                               let uu____79377 =
                                 encode (Prims.parse_int "10")  in
                               let uu____79379 =
                                 encode (Prims.parse_int "10")  in
                               minus uu____79377 uu____79379  in
                             ((Prims.parse_int "11"), uu____79374, z)  in
                           let uu____79389 =
                             let uu____79403 =
                               let uu____79415 =
                                 let uu____79418 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____79420 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____79418 uu____79420  in
                               ((Prims.parse_int "12"), uu____79415, z)  in
                             let uu____79430 =
                               let uu____79444 =
                                 let uu____79456 =
                                   let uu____79459 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____79461 =
                                     let uu____79464 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____79465 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____79464 uu____79465  in
                                   let_ FStar_Tests_Util.x uu____79459
                                     uu____79461
                                    in
                                 ((Prims.parse_int "13"), uu____79456, z)  in
                               let uu____79474 =
                                 let uu____79488 =
                                   let uu____79500 =
                                     let uu____79503 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____79504 =
                                       let uu____79507 =
                                         let uu____79508 =
                                           let uu____79511 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____79512 =
                                             let uu____79515 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____79515]  in
                                           uu____79511 :: uu____79512  in
                                         FStar_Tests_Util.app mul uu____79508
                                          in
                                       let uu____79516 =
                                         let uu____79519 =
                                           let uu____79520 =
                                             let uu____79523 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____79524 =
                                               let uu____79527 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____79527]  in
                                             uu____79523 :: uu____79524  in
                                           FStar_Tests_Util.app mul
                                             uu____79520
                                            in
                                         let uu____79528 =
                                           let uu____79531 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____79532 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____79531 uu____79532  in
                                         let_ FStar_Tests_Util.h uu____79519
                                           uu____79528
                                          in
                                       let_ FStar_Tests_Util.y uu____79507
                                         uu____79516
                                        in
                                     let_ FStar_Tests_Util.x uu____79503
                                       uu____79504
                                      in
                                   ((Prims.parse_int "15"), uu____79500, z)
                                    in
                                 let uu____79541 =
                                   let uu____79555 =
                                     let uu____79567 =
                                       let uu____79570 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____79573 =
                                         let uu____79574 =
                                           let uu____79577 =
                                             let uu____79580 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____79581 =
                                               let uu____79584 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____79584]  in
                                             uu____79580 :: uu____79581  in
                                           FStar_Tests_Util.app mul
                                             uu____79577
                                            in
                                         let uu____79585 =
                                           let uu____79586 =
                                             let uu____79589 =
                                               let uu____79592 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____79593 =
                                                 let uu____79596 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____79596]  in
                                               uu____79592 :: uu____79593  in
                                             FStar_Tests_Util.app mul
                                               uu____79589
                                              in
                                           let uu____79597 =
                                             let uu____79598 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____79599 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____79598 uu____79599
                                              in
                                           mk_let FStar_Tests_Util.h
                                             uu____79586 uu____79597
                                            in
                                         mk_let FStar_Tests_Util.y
                                           uu____79574 uu____79585
                                          in
                                       mk_let FStar_Tests_Util.x uu____79570
                                         uu____79573
                                        in
                                     ((Prims.parse_int "16"), uu____79567, z)
                                      in
                                   let uu____79608 =
                                     let uu____79622 =
                                       let uu____79634 =
                                         let uu____79637 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____79638 =
                                           let uu____79641 =
                                             let uu____79642 =
                                               let uu____79645 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____79646 =
                                                 let uu____79649 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____79649]  in
                                               uu____79645 :: uu____79646  in
                                             FStar_Tests_Util.app mul
                                               uu____79642
                                              in
                                           let uu____79650 =
                                             let uu____79653 =
                                               let uu____79654 =
                                                 let uu____79657 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____79658 =
                                                   let uu____79661 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____79661]  in
                                                 uu____79657 :: uu____79658
                                                  in
                                               FStar_Tests_Util.app mul
                                                 uu____79654
                                                in
                                             let uu____79662 =
                                               let uu____79665 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____79666 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____79665 uu____79666
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____79653 uu____79662
                                              in
                                           let_ FStar_Tests_Util.y
                                             uu____79641 uu____79650
                                            in
                                         let_ FStar_Tests_Util.x uu____79637
                                           uu____79638
                                          in
                                       ((Prims.parse_int "17"), uu____79634,
                                         z)
                                        in
                                     let uu____79675 =
                                       let uu____79689 =
                                         let uu____79701 =
                                           let uu____79704 =
                                             let uu____79707 = snat znat  in
                                             snat uu____79707  in
                                           pred_nat uu____79704  in
                                         let uu____79708 = snat znat  in
                                         ((Prims.parse_int "18"),
                                           uu____79701, uu____79708)
                                          in
                                       let uu____79717 =
                                         let uu____79731 =
                                           let uu____79743 =
                                             let uu____79746 =
                                               let uu____79747 =
                                                 let uu____79748 = snat znat
                                                    in
                                                 snat uu____79748  in
                                               let uu____79749 = snat znat
                                                  in
                                               minus_nat uu____79747
                                                 uu____79749
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____79746
                                              in
                                           let uu____79750 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____79743, uu____79750)
                                            in
                                         let uu____79759 =
                                           let uu____79773 =
                                             let uu____79785 =
                                               let uu____79788 =
                                                 let uu____79789 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 let uu____79791 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 minus_nat uu____79789
                                                   uu____79791
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____79788
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____79785, znat)
                                              in
                                           let uu____79799 =
                                             let uu____79813 =
                                               let uu____79825 =
                                                 let uu____79828 =
                                                   let uu____79829 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   let uu____79831 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   minus_nat uu____79829
                                                     uu____79831
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____79828
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____79825, znat)
                                                in
                                             let uu____79839 =
                                               let uu____79853 =
                                                 let uu____79865 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____79869 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____79865, uu____79869)
                                                  in
                                               let uu____79879 =
                                                 let uu____79893 =
                                                   let uu____79905 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____79909 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____79905,
                                                     uu____79909)
                                                    in
                                                 let uu____79919 =
                                                   let uu____79933 =
                                                     let uu____79945 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____79949 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____79945,
                                                       uu____79949)
                                                      in
                                                   let uu____79959 =
                                                     let uu____79973 =
                                                       let uu____79985 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____79989 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____79985,
                                                         uu____79989)
                                                        in
                                                     let uu____79999 =
                                                       let uu____80013 =
                                                         let uu____80025 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____80029 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____80025,
                                                           uu____80029)
                                                          in
                                                       let uu____80039 =
                                                         let uu____80053 =
                                                           let uu____80065 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____80069 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____80065,
                                                             uu____80069)
                                                            in
                                                         let uu____80079 =
                                                           let uu____80093 =
                                                             let uu____80105
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____80109
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____80105,
                                                               uu____80109)
                                                              in
                                                           let uu____80119 =
                                                             let uu____80133
                                                               =
                                                               let uu____80145
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____80149
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____80145,
                                                                 uu____80149)
                                                                in
                                                             let uu____80159
                                                               =
                                                               let uu____80173
                                                                 =
                                                                 let uu____80185
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____80189
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____80185,
                                                                   uu____80189)
                                                                  in
                                                               let uu____80199
                                                                 =
                                                                 let uu____80213
                                                                   =
                                                                   let uu____80225
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____80229
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____80225,
                                                                    uu____80229)
                                                                    in
                                                                 let uu____80239
                                                                   =
                                                                   let uu____80253
                                                                    =
                                                                    let uu____80265
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____80269
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____80265,
                                                                    uu____80269)
                                                                     in
                                                                   let uu____80279
                                                                    =
                                                                    let uu____80293
                                                                    =
                                                                    let uu____80305
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____80309
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____80305,
                                                                    uu____80309)
                                                                     in
                                                                    let uu____80319
                                                                    =
                                                                    let uu____80333
                                                                    =
                                                                    let uu____80345
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____80349
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____80345,
                                                                    uu____80349)
                                                                     in
                                                                    let uu____80359
                                                                    =
                                                                    let uu____80373
                                                                    =
                                                                    let uu____80385
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____80389
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____80385,
                                                                    uu____80389)
                                                                     in
                                                                    let uu____80399
                                                                    =
                                                                    let uu____80413
                                                                    =
                                                                    let uu____80425
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____80429
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____80425,
                                                                    uu____80429)
                                                                     in
                                                                    let uu____80439
                                                                    =
                                                                    let uu____80453
                                                                    =
                                                                    let uu____80465
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____80469
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____80465,
                                                                    uu____80469)
                                                                     in
                                                                    let uu____80479
                                                                    =
                                                                    let uu____80493
                                                                    =
                                                                    let uu____80505
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____80509
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____80505,
                                                                    uu____80509)
                                                                     in
                                                                    let uu____80519
                                                                    =
                                                                    let uu____80533
                                                                    =
                                                                    let uu____80545
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____80549
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____80545,
                                                                    uu____80549)
                                                                     in
                                                                    let uu____80559
                                                                    =
                                                                    let uu____80573
                                                                    =
                                                                    let uu____80585
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____80589
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____80585,
                                                                    uu____80589)
                                                                     in
                                                                    let uu____80599
                                                                    =
                                                                    let uu____80613
                                                                    =
                                                                    let uu____80625
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____80629
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____80625,
                                                                    uu____80629)
                                                                     in
                                                                    let uu____80639
                                                                    =
                                                                    let uu____80653
                                                                    =
                                                                    let uu____80665
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____80669
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____80665,
                                                                    uu____80669)
                                                                     in
                                                                    let uu____80679
                                                                    =
                                                                    let uu____80693
                                                                    =
                                                                    let uu____80705
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____80709
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____80705,
                                                                    uu____80709)
                                                                     in
                                                                    let uu____80719
                                                                    =
                                                                    let uu____80733
                                                                    =
                                                                    let uu____80745
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____80749
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____80745,
                                                                    uu____80749)
                                                                     in
                                                                    let uu____80759
                                                                    =
                                                                    let uu____80773
                                                                    =
                                                                    let uu____80785
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____80789
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____80785,
                                                                    uu____80789)
                                                                     in
                                                                    let uu____80799
                                                                    =
                                                                    let uu____80813
                                                                    =
                                                                    let uu____80825
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____80829
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____80825,
                                                                    uu____80829)
                                                                     in
                                                                    let uu____80839
                                                                    =
                                                                    let uu____80853
                                                                    =
                                                                    let uu____80865
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____80869
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____80865,
                                                                    uu____80869)
                                                                     in
                                                                    let uu____80879
                                                                    =
                                                                    let uu____80893
                                                                    =
                                                                    let uu____80905
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____80909
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____80905,
                                                                    uu____80909)
                                                                     in
                                                                    let uu____80919
                                                                    =
                                                                    let uu____80933
                                                                    =
                                                                    let uu____80945
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____80949
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____80945,
                                                                    uu____80949)
                                                                     in
                                                                    let uu____80959
                                                                    =
                                                                    let uu____80973
                                                                    =
                                                                    let uu____80985
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____80989
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____80985,
                                                                    uu____80989)
                                                                     in
                                                                    let uu____80999
                                                                    =
                                                                    let uu____81013
                                                                    =
                                                                    let uu____81025
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____81029
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____81025,
                                                                    uu____81029)
                                                                     in
                                                                    let uu____81039
                                                                    =
                                                                    let uu____81053
                                                                    =
                                                                    let uu____81065
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____81069
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____81065,
                                                                    uu____81069)
                                                                     in
                                                                    let uu____81079
                                                                    =
                                                                    let uu____81093
                                                                    =
                                                                    let uu____81105
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____81109
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____81105,
                                                                    uu____81109)
                                                                     in
                                                                    let uu____81119
                                                                    =
                                                                    let uu____81133
                                                                    =
                                                                    let uu____81145
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____81149
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____81145,
                                                                    uu____81149)
                                                                     in
                                                                    let uu____81159
                                                                    =
                                                                    let uu____81173
                                                                    =
                                                                    let uu____81185
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____81189
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____81185,
                                                                    uu____81189)
                                                                     in
                                                                    [uu____81173]
                                                                     in
                                                                    uu____81133
                                                                    ::
                                                                    uu____81159
                                                                     in
                                                                    uu____81093
                                                                    ::
                                                                    uu____81119
                                                                     in
                                                                    uu____81053
                                                                    ::
                                                                    uu____81079
                                                                     in
                                                                    uu____81013
                                                                    ::
                                                                    uu____81039
                                                                     in
                                                                    uu____80973
                                                                    ::
                                                                    uu____80999
                                                                     in
                                                                    uu____80933
                                                                    ::
                                                                    uu____80959
                                                                     in
                                                                    uu____80893
                                                                    ::
                                                                    uu____80919
                                                                     in
                                                                    uu____80853
                                                                    ::
                                                                    uu____80879
                                                                     in
                                                                    uu____80813
                                                                    ::
                                                                    uu____80839
                                                                     in
                                                                    uu____80773
                                                                    ::
                                                                    uu____80799
                                                                     in
                                                                    uu____80733
                                                                    ::
                                                                    uu____80759
                                                                     in
                                                                    uu____80693
                                                                    ::
                                                                    uu____80719
                                                                     in
                                                                    uu____80653
                                                                    ::
                                                                    uu____80679
                                                                     in
                                                                    uu____80613
                                                                    ::
                                                                    uu____80639
                                                                     in
                                                                    uu____80573
                                                                    ::
                                                                    uu____80599
                                                                     in
                                                                    uu____80533
                                                                    ::
                                                                    uu____80559
                                                                     in
                                                                    uu____80493
                                                                    ::
                                                                    uu____80519
                                                                     in
                                                                    uu____80453
                                                                    ::
                                                                    uu____80479
                                                                     in
                                                                    uu____80413
                                                                    ::
                                                                    uu____80439
                                                                     in
                                                                    uu____80373
                                                                    ::
                                                                    uu____80399
                                                                     in
                                                                    uu____80333
                                                                    ::
                                                                    uu____80359
                                                                     in
                                                                    uu____80293
                                                                    ::
                                                                    uu____80319
                                                                     in
                                                                   uu____80253
                                                                    ::
                                                                    uu____80279
                                                                    in
                                                                 uu____80213
                                                                   ::
                                                                   uu____80239
                                                                  in
                                                               uu____80173 ::
                                                                 uu____80199
                                                                in
                                                             uu____80133 ::
                                                               uu____80159
                                                              in
                                                           uu____80093 ::
                                                             uu____80119
                                                            in
                                                         uu____80053 ::
                                                           uu____80079
                                                          in
                                                       uu____80013 ::
                                                         uu____80039
                                                        in
                                                     uu____79973 ::
                                                       uu____79999
                                                      in
                                                   uu____79933 :: uu____79959
                                                    in
                                                 uu____79893 :: uu____79919
                                                  in
                                               uu____79853 :: uu____79879  in
                                             uu____79813 :: uu____79839  in
                                           uu____79773 :: uu____79799  in
                                         uu____79731 :: uu____79759  in
                                       uu____79689 :: uu____79717  in
                                     uu____79622 :: uu____79675  in
                                   uu____79555 :: uu____79608  in
                                 uu____79488 :: uu____79541  in
                               uu____79444 :: uu____79474  in
                             uu____79403 :: uu____79430  in
                           uu____79362 :: uu____79389  in
                         uu____79323 :: uu____79348  in
                       uu____79288 :: uu____79309  in
                     uu____79253 :: uu____79274  in
                   uu____79218 :: uu____79239  in
                 uu____79183 :: uu____79204  in
               uu____79148 :: uu____79169  in
             uu____79096 :: uu____79134  in
           uu____79032 :: uu____79082  in
         uu____78983 :: uu____79018  in
       uu____78934 :: uu____78969  in
     uu____78892 :: uu____78920  in
   uu____78844 :: uu____78878)
  
let run_either :
  'Auu____81837 .
    Prims.int ->
      'Auu____81837 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____81837 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____81875 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____81875);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____81880 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____81880 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____81903 =
               let uu____81905 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____81905 expected  in
             FStar_Tests_Util.always i uu____81903)))
  
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
        let interp uu____81984 = run_interpreter i r expected  in
        let uu____81985 =
          let uu____81986 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____81986  in
        (i, uu____81985)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____82024 = run_nbe i r expected  in
        let uu____82025 =
          let uu____82026 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____82026  in
        (i, uu____82025)
  
let run_tests :
  'Auu____82037 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
           'Auu____82037)
      -> 'Auu____82037 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___742_82089  ->
            match uu___742_82089 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____82120  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____82123 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____82132  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____82135 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____82151  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____82181  ->
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
        let nbe1 uu____82226 = run_nbe i r expected  in
        let norm1 uu____82232 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____82245  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____82248 =
       let uu____82249 = encode (Prims.parse_int "1000")  in
       let uu____82251 =
         let uu____82254 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____82255 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____82254 uu____82255  in
       let_ FStar_Tests_Util.x uu____82249 uu____82251  in
     run_both_with_time (Prims.parse_int "14") uu____82248 z)
  
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
             let uu____82331 = res1  in
             match uu____82331 with
             | (t1,time_int) ->
                 let uu____82341 = res2  in
                 (match uu____82341 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____82353 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____82353 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____82364  ->
    (let uu____82366 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____82366);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  