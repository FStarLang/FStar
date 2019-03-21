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
      (let uu____77967 =
         let uu____77970 = encode (n1 - (Prims.parse_int "1"))  in
         [uu____77970]  in
       FStar_Tests_Util.app succ uu____77967)
  
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
        let uu____78009 =
          let uu____78012 = let uu____78013 = b x1  in [uu____78013]  in
          FStar_Syntax_Util.abs uu____78012 e' FStar_Pervasives_Native.None
           in
        FStar_Tests_Util.app uu____78009 [e]
  
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
  let uu____78083 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____78083
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____78086 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____78086
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
    let uu____78105 =
      let uu____78112 =
        let uu____78113 =
          let uu____78130 = tm_fv snat_l  in
          let uu____78133 =
            let uu____78144 = FStar_Syntax_Syntax.as_arg s  in [uu____78144]
             in
          (uu____78130, uu____78133)  in
        FStar_Syntax_Syntax.Tm_app uu____78113  in
      FStar_Syntax_Syntax.mk uu____78112  in
    uu____78105 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____78186 .
    'Auu____78186 -> 'Auu____78186 FStar_Syntax_Syntax.withinfo_t
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
      let uu____78295 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____78295, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____78339 =
        let uu____78342 =
          let uu____78343 =
            let uu____78357 =
              let uu____78367 =
                let uu____78375 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____78375, false)  in
              [uu____78367]  in
            (snat_l, uu____78357)  in
          FStar_Syntax_Syntax.Pat_cons uu____78343  in
        pat uu____78342  in
      let uu____78405 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___763_78410 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___763_78410.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___763_78410.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____78339, FStar_Pervasives_Native.None, uu____78405)  in
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
        let uu____78451 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____78470 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____78451, FStar_Pervasives_Native.None, uu____78470)  in
      let sbranch =
        let uu____78498 =
          let uu____78501 =
            let uu____78502 =
              let uu____78516 =
                let uu____78526 =
                  let uu____78534 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____78534, false)  in
                [uu____78526]  in
              (snat_l, uu____78516)  in
            FStar_Syntax_Syntax.Pat_cons uu____78502  in
          pat uu____78501  in
        let uu____78564 =
          let uu____78567 = FStar_Tests_Util.nm minus1  in
          let uu____78570 =
            let uu____78573 =
              let uu____78574 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____78574  in
            let uu____78577 =
              let uu____78580 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____78580]  in
            uu____78573 :: uu____78577  in
          FStar_Tests_Util.app uu____78567 uu____78570  in
        (uu____78498, FStar_Pervasives_Native.None, uu____78564)  in
      let lb =
        let uu____78592 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____78596 =
          let uu____78599 =
            let uu____78600 =
              let uu____78601 = b FStar_Tests_Util.x  in
              let uu____78608 =
                let uu____78617 = b FStar_Tests_Util.y  in [uu____78617]  in
              uu____78601 :: uu____78608  in
            let uu____78642 =
              let uu____78645 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____78645 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____78600 uu____78642
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____78599
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____78592;
          FStar_Syntax_Syntax.lbdef = uu____78596;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____78652 =
        let uu____78659 =
          let uu____78660 =
            let uu____78674 =
              let uu____78677 =
                let uu____78678 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____78678 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____78677
               in
            ((true, [lb]), uu____78674)  in
          FStar_Syntax_Syntax.Tm_let uu____78660  in
        FStar_Syntax_Syntax.mk uu____78659  in
      uu____78652 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____78722 = snat out  in
         aux uu____78722 (n2 - (Prims.parse_int "1")))
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
  (let uu____78788 =
     let uu____78800 =
       let uu____78803 =
         let uu____78806 =
           let uu____78809 =
             let uu____78812 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____78812]  in
           id :: uu____78809  in
         one :: uu____78806  in
       FStar_Tests_Util.app apply uu____78803  in
     let uu____78813 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____78800, uu____78813)  in
   let uu____78822 =
     let uu____78836 =
       let uu____78848 =
         let uu____78851 =
           let uu____78854 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____78854]  in
         FStar_Tests_Util.app id uu____78851  in
       let uu____78855 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____78848, uu____78855)  in
     let uu____78864 =
       let uu____78878 =
         let uu____78890 =
           let uu____78893 =
             let uu____78896 =
               let uu____78899 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____78900 =
                 let uu____78903 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____78903]  in
               uu____78899 :: uu____78900  in
             tt :: uu____78896  in
           FStar_Tests_Util.app apply uu____78893  in
         let uu____78904 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____78890, uu____78904)  in
       let uu____78913 =
         let uu____78927 =
           let uu____78939 =
             let uu____78942 =
               let uu____78945 =
                 let uu____78948 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____78949 =
                   let uu____78952 = FStar_Tests_Util.nm FStar_Tests_Util.m
                      in
                   [uu____78952]  in
                 uu____78948 :: uu____78949  in
               ff :: uu____78945  in
             FStar_Tests_Util.app apply uu____78942  in
           let uu____78953 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____78939, uu____78953)  in
         let uu____78962 =
           let uu____78976 =
             let uu____78988 =
               let uu____78991 =
                 let uu____78994 =
                   let uu____78997 =
                     let uu____79000 =
                       let uu____79003 =
                         let uu____79006 =
                           let uu____79009 =
                             let uu____79012 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____79013 =
                               let uu____79016 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____79016]  in
                             uu____79012 :: uu____79013  in
                           ff :: uu____79009  in
                         apply :: uu____79006  in
                       apply :: uu____79003  in
                     apply :: uu____79000  in
                   apply :: uu____78997  in
                 apply :: uu____78994  in
               FStar_Tests_Util.app apply uu____78991  in
             let uu____79017 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____78988, uu____79017)  in
           let uu____79026 =
             let uu____79040 =
               let uu____79052 =
                 let uu____79055 =
                   let uu____79058 =
                     let uu____79061 =
                       let uu____79064 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n  in
                       let uu____79065 =
                         let uu____79068 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____79068]  in
                       uu____79064 :: uu____79065  in
                     ff :: uu____79061  in
                   apply :: uu____79058  in
                 FStar_Tests_Util.app twice uu____79055  in
               let uu____79069 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____79052, uu____79069)  in
             let uu____79078 =
               let uu____79092 =
                 let uu____79104 = minus one z  in
                 ((Prims.parse_int "5"), uu____79104, one)  in
               let uu____79113 =
                 let uu____79127 =
                   let uu____79139 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____79139, z)  in
                 let uu____79148 =
                   let uu____79162 =
                     let uu____79174 = minus one one  in
                     ((Prims.parse_int "7"), uu____79174, z)  in
                   let uu____79183 =
                     let uu____79197 =
                       let uu____79209 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____79209, one)  in
                     let uu____79218 =
                       let uu____79232 =
                         let uu____79244 =
                           FStar_Tests_Util.app mul [two; one]  in
                         ((Prims.parse_int "9"), uu____79244, two)  in
                       let uu____79253 =
                         let uu____79267 =
                           let uu____79279 =
                             let uu____79282 =
                               let uu____79285 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____79285; one]  in
                             FStar_Tests_Util.app mul uu____79282  in
                           ((Prims.parse_int "10"), uu____79279, two)  in
                         let uu____79292 =
                           let uu____79306 =
                             let uu____79318 =
                               let uu____79321 =
                                 encode (Prims.parse_int "10")  in
                               let uu____79323 =
                                 encode (Prims.parse_int "10")  in
                               minus uu____79321 uu____79323  in
                             ((Prims.parse_int "11"), uu____79318, z)  in
                           let uu____79333 =
                             let uu____79347 =
                               let uu____79359 =
                                 let uu____79362 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____79364 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____79362 uu____79364  in
                               ((Prims.parse_int "12"), uu____79359, z)  in
                             let uu____79374 =
                               let uu____79388 =
                                 let uu____79400 =
                                   let uu____79403 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____79405 =
                                     let uu____79408 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____79409 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____79408 uu____79409  in
                                   let_ FStar_Tests_Util.x uu____79403
                                     uu____79405
                                    in
                                 ((Prims.parse_int "13"), uu____79400, z)  in
                               let uu____79418 =
                                 let uu____79432 =
                                   let uu____79444 =
                                     let uu____79447 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____79448 =
                                       let uu____79451 =
                                         let uu____79452 =
                                           let uu____79455 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____79456 =
                                             let uu____79459 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____79459]  in
                                           uu____79455 :: uu____79456  in
                                         FStar_Tests_Util.app mul uu____79452
                                          in
                                       let uu____79460 =
                                         let uu____79463 =
                                           let uu____79464 =
                                             let uu____79467 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____79468 =
                                               let uu____79471 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____79471]  in
                                             uu____79467 :: uu____79468  in
                                           FStar_Tests_Util.app mul
                                             uu____79464
                                            in
                                         let uu____79472 =
                                           let uu____79475 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____79476 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____79475 uu____79476  in
                                         let_ FStar_Tests_Util.h uu____79463
                                           uu____79472
                                          in
                                       let_ FStar_Tests_Util.y uu____79451
                                         uu____79460
                                        in
                                     let_ FStar_Tests_Util.x uu____79447
                                       uu____79448
                                      in
                                   ((Prims.parse_int "15"), uu____79444, z)
                                    in
                                 let uu____79485 =
                                   let uu____79499 =
                                     let uu____79511 =
                                       let uu____79514 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____79517 =
                                         let uu____79518 =
                                           let uu____79521 =
                                             let uu____79524 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____79525 =
                                               let uu____79528 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____79528]  in
                                             uu____79524 :: uu____79525  in
                                           FStar_Tests_Util.app mul
                                             uu____79521
                                            in
                                         let uu____79529 =
                                           let uu____79530 =
                                             let uu____79533 =
                                               let uu____79536 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____79537 =
                                                 let uu____79540 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____79540]  in
                                               uu____79536 :: uu____79537  in
                                             FStar_Tests_Util.app mul
                                               uu____79533
                                              in
                                           let uu____79541 =
                                             let uu____79542 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____79543 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____79542 uu____79543
                                              in
                                           mk_let FStar_Tests_Util.h
                                             uu____79530 uu____79541
                                            in
                                         mk_let FStar_Tests_Util.y
                                           uu____79518 uu____79529
                                          in
                                       mk_let FStar_Tests_Util.x uu____79514
                                         uu____79517
                                        in
                                     ((Prims.parse_int "16"), uu____79511, z)
                                      in
                                   let uu____79552 =
                                     let uu____79566 =
                                       let uu____79578 =
                                         let uu____79581 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____79582 =
                                           let uu____79585 =
                                             let uu____79586 =
                                               let uu____79589 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____79590 =
                                                 let uu____79593 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____79593]  in
                                               uu____79589 :: uu____79590  in
                                             FStar_Tests_Util.app mul
                                               uu____79586
                                              in
                                           let uu____79594 =
                                             let uu____79597 =
                                               let uu____79598 =
                                                 let uu____79601 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____79602 =
                                                   let uu____79605 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____79605]  in
                                                 uu____79601 :: uu____79602
                                                  in
                                               FStar_Tests_Util.app mul
                                                 uu____79598
                                                in
                                             let uu____79606 =
                                               let uu____79609 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____79610 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____79609 uu____79610
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____79597 uu____79606
                                              in
                                           let_ FStar_Tests_Util.y
                                             uu____79585 uu____79594
                                            in
                                         let_ FStar_Tests_Util.x uu____79581
                                           uu____79582
                                          in
                                       ((Prims.parse_int "17"), uu____79578,
                                         z)
                                        in
                                     let uu____79619 =
                                       let uu____79633 =
                                         let uu____79645 =
                                           let uu____79648 =
                                             let uu____79651 = snat znat  in
                                             snat uu____79651  in
                                           pred_nat uu____79648  in
                                         let uu____79652 = snat znat  in
                                         ((Prims.parse_int "18"),
                                           uu____79645, uu____79652)
                                          in
                                       let uu____79661 =
                                         let uu____79675 =
                                           let uu____79687 =
                                             let uu____79690 =
                                               let uu____79691 =
                                                 let uu____79692 = snat znat
                                                    in
                                                 snat uu____79692  in
                                               let uu____79693 = snat znat
                                                  in
                                               minus_nat uu____79691
                                                 uu____79693
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____79690
                                              in
                                           let uu____79694 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____79687, uu____79694)
                                            in
                                         let uu____79703 =
                                           let uu____79717 =
                                             let uu____79729 =
                                               let uu____79732 =
                                                 let uu____79733 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 let uu____79735 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 minus_nat uu____79733
                                                   uu____79735
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____79732
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____79729, znat)
                                              in
                                           let uu____79743 =
                                             let uu____79757 =
                                               let uu____79769 =
                                                 let uu____79772 =
                                                   let uu____79773 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   let uu____79775 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   minus_nat uu____79773
                                                     uu____79775
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____79772
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____79769, znat)
                                                in
                                             let uu____79783 =
                                               let uu____79797 =
                                                 let uu____79809 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____79813 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____79809, uu____79813)
                                                  in
                                               let uu____79823 =
                                                 let uu____79837 =
                                                   let uu____79849 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____79853 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____79849,
                                                     uu____79853)
                                                    in
                                                 let uu____79863 =
                                                   let uu____79877 =
                                                     let uu____79889 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____79893 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____79889,
                                                       uu____79893)
                                                      in
                                                   let uu____79903 =
                                                     let uu____79917 =
                                                       let uu____79929 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____79933 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____79929,
                                                         uu____79933)
                                                        in
                                                     let uu____79943 =
                                                       let uu____79957 =
                                                         let uu____79969 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____79973 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____79969,
                                                           uu____79973)
                                                          in
                                                       let uu____79983 =
                                                         let uu____79997 =
                                                           let uu____80009 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____80013 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____80009,
                                                             uu____80013)
                                                            in
                                                         let uu____80023 =
                                                           let uu____80037 =
                                                             let uu____80049
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____80053
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____80049,
                                                               uu____80053)
                                                              in
                                                           let uu____80063 =
                                                             let uu____80077
                                                               =
                                                               let uu____80089
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____80093
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____80089,
                                                                 uu____80093)
                                                                in
                                                             let uu____80103
                                                               =
                                                               let uu____80117
                                                                 =
                                                                 let uu____80129
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____80133
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____80129,
                                                                   uu____80133)
                                                                  in
                                                               let uu____80143
                                                                 =
                                                                 let uu____80157
                                                                   =
                                                                   let uu____80169
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____80173
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____80169,
                                                                    uu____80173)
                                                                    in
                                                                 let uu____80183
                                                                   =
                                                                   let uu____80197
                                                                    =
                                                                    let uu____80209
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____80213
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____80209,
                                                                    uu____80213)
                                                                     in
                                                                   let uu____80223
                                                                    =
                                                                    let uu____80237
                                                                    =
                                                                    let uu____80249
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____80253
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____80249,
                                                                    uu____80253)
                                                                     in
                                                                    let uu____80263
                                                                    =
                                                                    let uu____80277
                                                                    =
                                                                    let uu____80289
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____80293
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____80289,
                                                                    uu____80293)
                                                                     in
                                                                    let uu____80303
                                                                    =
                                                                    let uu____80317
                                                                    =
                                                                    let uu____80329
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____80333
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____80329,
                                                                    uu____80333)
                                                                     in
                                                                    let uu____80343
                                                                    =
                                                                    let uu____80357
                                                                    =
                                                                    let uu____80369
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____80373
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____80369,
                                                                    uu____80373)
                                                                     in
                                                                    let uu____80383
                                                                    =
                                                                    let uu____80397
                                                                    =
                                                                    let uu____80409
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____80413
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____80409,
                                                                    uu____80413)
                                                                     in
                                                                    let uu____80423
                                                                    =
                                                                    let uu____80437
                                                                    =
                                                                    let uu____80449
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____80453
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____80449,
                                                                    uu____80453)
                                                                     in
                                                                    let uu____80463
                                                                    =
                                                                    let uu____80477
                                                                    =
                                                                    let uu____80489
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____80493
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____80489,
                                                                    uu____80493)
                                                                     in
                                                                    let uu____80503
                                                                    =
                                                                    let uu____80517
                                                                    =
                                                                    let uu____80529
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____80533
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____80529,
                                                                    uu____80533)
                                                                     in
                                                                    let uu____80543
                                                                    =
                                                                    let uu____80557
                                                                    =
                                                                    let uu____80569
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____80573
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____80569,
                                                                    uu____80573)
                                                                     in
                                                                    let uu____80583
                                                                    =
                                                                    let uu____80597
                                                                    =
                                                                    let uu____80609
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____80613
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____80609,
                                                                    uu____80613)
                                                                     in
                                                                    let uu____80623
                                                                    =
                                                                    let uu____80637
                                                                    =
                                                                    let uu____80649
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____80653
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____80649,
                                                                    uu____80653)
                                                                     in
                                                                    let uu____80663
                                                                    =
                                                                    let uu____80677
                                                                    =
                                                                    let uu____80689
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____80693
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____80689,
                                                                    uu____80693)
                                                                     in
                                                                    let uu____80703
                                                                    =
                                                                    let uu____80717
                                                                    =
                                                                    let uu____80729
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____80733
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____80729,
                                                                    uu____80733)
                                                                     in
                                                                    let uu____80743
                                                                    =
                                                                    let uu____80757
                                                                    =
                                                                    let uu____80769
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____80773
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____80769,
                                                                    uu____80773)
                                                                     in
                                                                    let uu____80783
                                                                    =
                                                                    let uu____80797
                                                                    =
                                                                    let uu____80809
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____80813
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____80809,
                                                                    uu____80813)
                                                                     in
                                                                    let uu____80823
                                                                    =
                                                                    let uu____80837
                                                                    =
                                                                    let uu____80849
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____80853
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____80849,
                                                                    uu____80853)
                                                                     in
                                                                    let uu____80863
                                                                    =
                                                                    let uu____80877
                                                                    =
                                                                    let uu____80889
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____80893
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____80889,
                                                                    uu____80893)
                                                                     in
                                                                    let uu____80903
                                                                    =
                                                                    let uu____80917
                                                                    =
                                                                    let uu____80929
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____80933
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____80929,
                                                                    uu____80933)
                                                                     in
                                                                    let uu____80943
                                                                    =
                                                                    let uu____80957
                                                                    =
                                                                    let uu____80969
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____80973
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____80969,
                                                                    uu____80973)
                                                                     in
                                                                    let uu____80983
                                                                    =
                                                                    let uu____80997
                                                                    =
                                                                    let uu____81009
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____81013
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____81009,
                                                                    uu____81013)
                                                                     in
                                                                    let uu____81023
                                                                    =
                                                                    let uu____81037
                                                                    =
                                                                    let uu____81049
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____81053
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____81049,
                                                                    uu____81053)
                                                                     in
                                                                    let uu____81063
                                                                    =
                                                                    let uu____81077
                                                                    =
                                                                    let uu____81089
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____81093
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____81089,
                                                                    uu____81093)
                                                                     in
                                                                    let uu____81103
                                                                    =
                                                                    let uu____81117
                                                                    =
                                                                    let uu____81129
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____81133
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____81129,
                                                                    uu____81133)
                                                                     in
                                                                    [uu____81117]
                                                                     in
                                                                    uu____81077
                                                                    ::
                                                                    uu____81103
                                                                     in
                                                                    uu____81037
                                                                    ::
                                                                    uu____81063
                                                                     in
                                                                    uu____80997
                                                                    ::
                                                                    uu____81023
                                                                     in
                                                                    uu____80957
                                                                    ::
                                                                    uu____80983
                                                                     in
                                                                    uu____80917
                                                                    ::
                                                                    uu____80943
                                                                     in
                                                                    uu____80877
                                                                    ::
                                                                    uu____80903
                                                                     in
                                                                    uu____80837
                                                                    ::
                                                                    uu____80863
                                                                     in
                                                                    uu____80797
                                                                    ::
                                                                    uu____80823
                                                                     in
                                                                    uu____80757
                                                                    ::
                                                                    uu____80783
                                                                     in
                                                                    uu____80717
                                                                    ::
                                                                    uu____80743
                                                                     in
                                                                    uu____80677
                                                                    ::
                                                                    uu____80703
                                                                     in
                                                                    uu____80637
                                                                    ::
                                                                    uu____80663
                                                                     in
                                                                    uu____80597
                                                                    ::
                                                                    uu____80623
                                                                     in
                                                                    uu____80557
                                                                    ::
                                                                    uu____80583
                                                                     in
                                                                    uu____80517
                                                                    ::
                                                                    uu____80543
                                                                     in
                                                                    uu____80477
                                                                    ::
                                                                    uu____80503
                                                                     in
                                                                    uu____80437
                                                                    ::
                                                                    uu____80463
                                                                     in
                                                                    uu____80397
                                                                    ::
                                                                    uu____80423
                                                                     in
                                                                    uu____80357
                                                                    ::
                                                                    uu____80383
                                                                     in
                                                                    uu____80317
                                                                    ::
                                                                    uu____80343
                                                                     in
                                                                    uu____80277
                                                                    ::
                                                                    uu____80303
                                                                     in
                                                                    uu____80237
                                                                    ::
                                                                    uu____80263
                                                                     in
                                                                   uu____80197
                                                                    ::
                                                                    uu____80223
                                                                    in
                                                                 uu____80157
                                                                   ::
                                                                   uu____80183
                                                                  in
                                                               uu____80117 ::
                                                                 uu____80143
                                                                in
                                                             uu____80077 ::
                                                               uu____80103
                                                              in
                                                           uu____80037 ::
                                                             uu____80063
                                                            in
                                                         uu____79997 ::
                                                           uu____80023
                                                          in
                                                       uu____79957 ::
                                                         uu____79983
                                                        in
                                                     uu____79917 ::
                                                       uu____79943
                                                      in
                                                   uu____79877 :: uu____79903
                                                    in
                                                 uu____79837 :: uu____79863
                                                  in
                                               uu____79797 :: uu____79823  in
                                             uu____79757 :: uu____79783  in
                                           uu____79717 :: uu____79743  in
                                         uu____79675 :: uu____79703  in
                                       uu____79633 :: uu____79661  in
                                     uu____79566 :: uu____79619  in
                                   uu____79499 :: uu____79552  in
                                 uu____79432 :: uu____79485  in
                               uu____79388 :: uu____79418  in
                             uu____79347 :: uu____79374  in
                           uu____79306 :: uu____79333  in
                         uu____79267 :: uu____79292  in
                       uu____79232 :: uu____79253  in
                     uu____79197 :: uu____79218  in
                   uu____79162 :: uu____79183  in
                 uu____79127 :: uu____79148  in
               uu____79092 :: uu____79113  in
             uu____79040 :: uu____79078  in
           uu____78976 :: uu____79026  in
         uu____78927 :: uu____78962  in
       uu____78878 :: uu____78913  in
     uu____78836 :: uu____78864  in
   uu____78788 :: uu____78822)
  
let run_either :
  'Auu____81781 .
    Prims.int ->
      'Auu____81781 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____81781 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____81819 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____81819);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____81824 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____81824 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____81847 =
               let uu____81849 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____81849 expected  in
             FStar_Tests_Util.always i uu____81847)))
  
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
        let interp uu____81928 = run_interpreter i r expected  in
        let uu____81929 =
          let uu____81930 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____81930  in
        (i, uu____81929)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____81968 = run_nbe i r expected  in
        let uu____81969 =
          let uu____81970 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____81970  in
        (i, uu____81969)
  
let run_tests :
  'Auu____81981 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
           'Auu____81981)
      -> 'Auu____81981 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___742_82033  ->
            match uu___742_82033 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____82064  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____82067 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____82076  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____82079 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____82095  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____82125  ->
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
        let nbe1 uu____82170 = run_nbe i r expected  in
        let norm1 uu____82176 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____82189  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____82192 =
       let uu____82193 = encode (Prims.parse_int "1000")  in
       let uu____82195 =
         let uu____82198 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____82199 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____82198 uu____82199  in
       let_ FStar_Tests_Util.x uu____82193 uu____82195  in
     run_both_with_time (Prims.parse_int "14") uu____82192 z)
  
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
             let uu____82275 = res1  in
             match uu____82275 with
             | (t1,time_int) ->
                 let uu____82285 = res2  in
                 (match uu____82285 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____82297 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____82297 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____82308  ->
    (let uu____82310 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____82310);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  