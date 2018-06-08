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
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term)
  =
  fun x1  ->
    fun e  ->
      fun e'  ->
        let uu____50 =
          let uu____53 = let uu____54 = b x1  in [uu____54]  in
          FStar_Syntax_Util.abs uu____53 e' FStar_Pervasives_Native.None  in
        FStar_Tests_Util.app uu____50 [e]
  
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
  let uu____104 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____104 FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____105 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____105 FStar_Syntax_Syntax.delta_constant
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
    let uu____120 =
      let uu____127 =
        let uu____128 =
          let uu____143 = tm_fv snat_l  in
          let uu____146 =
            let uu____155 = FStar_Syntax_Syntax.as_arg s  in [uu____155]  in
          (uu____143, uu____146)  in
        FStar_Syntax_Syntax.Tm_app uu____128  in
      FStar_Syntax_Syntax.mk uu____127  in
    uu____120 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____191 . 'Auu____191 -> 'Auu____191 FStar_Syntax_Syntax.withinfo_t =
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
      let uu____298 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____298, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____340 =
        let uu____343 =
          let uu____344 =
            let uu____357 =
              let uu____366 =
                let uu____373 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____373, false)  in
              [uu____366]  in
            (snat_l, uu____357)  in
          FStar_Syntax_Syntax.Pat_cons uu____344  in
        pat uu____343  in
      let uu____398 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___454_403 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___454_403.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___454_403.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____340, FStar_Pervasives_Native.None, uu____398)  in
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
        let uu____442 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____459 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____442, FStar_Pervasives_Native.None, uu____459)  in
      let sbranch =
        let uu____487 =
          let uu____490 =
            let uu____491 =
              let uu____504 =
                let uu____513 =
                  let uu____520 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____520, false)  in
                [uu____513]  in
              (snat_l, uu____504)  in
            FStar_Syntax_Syntax.Pat_cons uu____491  in
          pat uu____490  in
        let uu____545 =
          let uu____548 = FStar_Tests_Util.nm minus1  in
          let uu____551 =
            let uu____554 =
              let uu____555 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____555  in
            let uu____558 =
              let uu____561 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____561]  in
            uu____554 :: uu____558  in
          FStar_Tests_Util.app uu____548 uu____551  in
        (uu____487, FStar_Pervasives_Native.None, uu____545)  in
      let lb =
        let uu____573 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____574 =
          let uu____577 =
            let uu____578 =
              let uu____579 = b FStar_Tests_Util.x  in
              let uu____584 =
                let uu____591 = b FStar_Tests_Util.y  in [uu____591]  in
              uu____579 :: uu____584  in
            let uu____608 =
              let uu____611 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____611 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____578 uu____608
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____577
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____573;
          FStar_Syntax_Syntax.lbdef = uu____574;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____616 =
        let uu____623 =
          let uu____624 =
            let uu____637 =
              let uu____640 =
                let uu____641 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____641 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____640
               in
            ((true, [lb]), uu____637)  in
          FStar_Syntax_Syntax.Tm_let uu____624  in
        FStar_Syntax_Syntax.mk uu____623  in
      uu____616 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____674 = snat out  in
         aux uu____674 (n2 - (Prims.parse_int "1")))
       in
    aux znat n1
  
let (tests :
  (Prims.int,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                                    FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 Prims.list)
  =
  FStar_Tests_Pars.pars_and_tc_fragment
    "let rec copy (x:list int) : Tot (list int) = match x with | [] -> []  | hd::tl -> hd::copy tl";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let recons (x:list 'a) : Tot (list 'a) = match x with | [] -> []  | hd::tl -> hd::tl";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let rev (x:list 'a) : Tot (list 'a) = let rec aux (x:list 'a) (out:list 'a) : Tot (list 'a) = match x with | [] -> out | hd::tl -> aux tl (hd::out) in aux x []";
  FStar_Tests_Pars.pars_and_tc_fragment
    "type t = | A : int -> int -> t | B : int -> int -> t let f = function | A x y | B y x -> y - x";
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
  FStar_Tests_Pars.pars_and_tc_fragment "let idd (x: 'a) = x";
  FStar_Tests_Pars.pars_and_tc_fragment
    "let revtb (x: tb) = match x with | T -> F | F -> T";
  FStar_Tests_Pars.pars_and_tc_fragment "let id_tb (x: tb) = x";
  FStar_Tests_Pars.pars_and_tc_fragment "let fst_a (x: 'a) (y: 'a) = x";
  FStar_Tests_Pars.pars_and_tc_fragment "let id_list (x: list 'a) = x";
  FStar_Tests_Pars.pars_and_tc_fragment "let id_list_m (x: list tb) = x";
  (let uu____707 =
     let uu____718 =
       let uu____721 =
         let uu____724 =
           let uu____727 =
             let uu____730 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____730]  in
           id :: uu____727  in
         one :: uu____724  in
       FStar_Tests_Util.app apply uu____721  in
     let uu____731 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____718, uu____731)  in
   let uu____738 =
     let uu____751 =
       let uu____762 =
         let uu____765 =
           let uu____768 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____768]  in
         FStar_Tests_Util.app id uu____765  in
       let uu____769 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____762, uu____769)  in
     let uu____776 =
       let uu____789 =
         let uu____800 =
           let uu____803 =
             let uu____806 =
               let uu____809 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____810 =
                 let uu____813 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____813]  in
               uu____809 :: uu____810  in
             tt :: uu____806  in
           FStar_Tests_Util.app apply uu____803  in
         let uu____814 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____800, uu____814)  in
       let uu____821 =
         let uu____834 =
           let uu____845 =
             let uu____848 =
               let uu____851 =
                 let uu____854 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____855 =
                   let uu____858 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                   [uu____858]  in
                 uu____854 :: uu____855  in
               ff :: uu____851  in
             FStar_Tests_Util.app apply uu____848  in
           let uu____859 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____845, uu____859)  in
         let uu____866 =
           let uu____879 =
             let uu____890 =
               let uu____893 =
                 let uu____896 =
                   let uu____899 =
                     let uu____902 =
                       let uu____905 =
                         let uu____908 =
                           let uu____911 =
                             let uu____914 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____915 =
                               let uu____918 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____918]  in
                             uu____914 :: uu____915  in
                           ff :: uu____911  in
                         apply :: uu____908  in
                       apply :: uu____905  in
                     apply :: uu____902  in
                   apply :: uu____899  in
                 apply :: uu____896  in
               FStar_Tests_Util.app apply uu____893  in
             let uu____919 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____890, uu____919)  in
           let uu____926 =
             let uu____939 =
               let uu____950 =
                 let uu____953 =
                   let uu____956 =
                     let uu____959 =
                       let uu____962 = FStar_Tests_Util.nm FStar_Tests_Util.n
                          in
                       let uu____963 =
                         let uu____966 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____966]  in
                       uu____962 :: uu____963  in
                     ff :: uu____959  in
                   apply :: uu____956  in
                 FStar_Tests_Util.app twice uu____953  in
               let uu____967 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____950, uu____967)  in
             let uu____974 =
               let uu____987 =
                 let uu____998 = minus one z  in
                 ((Prims.parse_int "5"), uu____998, one)  in
               let uu____1005 =
                 let uu____1018 =
                   let uu____1029 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____1029, z)  in
                 let uu____1036 =
                   let uu____1049 =
                     let uu____1060 = minus one one  in
                     ((Prims.parse_int "7"), uu____1060, z)  in
                   let uu____1067 =
                     let uu____1080 =
                       let uu____1091 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____1091, one)  in
                     let uu____1098 =
                       let uu____1111 =
                         let uu____1122 = FStar_Tests_Util.app mul [two; one]
                            in
                         ((Prims.parse_int "9"), uu____1122, two)  in
                       let uu____1129 =
                         let uu____1142 =
                           let uu____1153 =
                             let uu____1156 =
                               let uu____1159 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____1159; one]  in
                             FStar_Tests_Util.app mul uu____1156  in
                           ((Prims.parse_int "10"), uu____1153, two)  in
                         let uu____1164 =
                           let uu____1177 =
                             let uu____1188 =
                               let uu____1191 = encode (Prims.parse_int "10")
                                  in
                               let uu____1192 = encode (Prims.parse_int "10")
                                  in
                               minus uu____1191 uu____1192  in
                             ((Prims.parse_int "11"), uu____1188, z)  in
                           let uu____1199 =
                             let uu____1212 =
                               let uu____1223 =
                                 let uu____1226 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____1227 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____1226 uu____1227  in
                               ((Prims.parse_int "12"), uu____1223, z)  in
                             let uu____1234 =
                               let uu____1247 =
                                 let uu____1258 =
                                   let uu____1261 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____1262 =
                                     let uu____1265 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____1266 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____1265 uu____1266  in
                                   let_ FStar_Tests_Util.x uu____1261
                                     uu____1262
                                    in
                                 ((Prims.parse_int "13"), uu____1258, z)  in
                               let uu____1273 =
                                 let uu____1286 =
                                   let uu____1297 =
                                     let uu____1300 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____1301 =
                                       let uu____1304 =
                                         let uu____1305 =
                                           let uu____1308 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____1309 =
                                             let uu____1312 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____1312]  in
                                           uu____1308 :: uu____1309  in
                                         FStar_Tests_Util.app mul uu____1305
                                          in
                                       let uu____1313 =
                                         let uu____1316 =
                                           let uu____1317 =
                                             let uu____1320 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____1321 =
                                               let uu____1324 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____1324]  in
                                             uu____1320 :: uu____1321  in
                                           FStar_Tests_Util.app mul
                                             uu____1317
                                            in
                                         let uu____1325 =
                                           let uu____1328 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____1329 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____1328 uu____1329  in
                                         let_ FStar_Tests_Util.h uu____1316
                                           uu____1325
                                          in
                                       let_ FStar_Tests_Util.y uu____1304
                                         uu____1313
                                        in
                                     let_ FStar_Tests_Util.x uu____1300
                                       uu____1301
                                      in
                                   ((Prims.parse_int "15"), uu____1297, z)
                                    in
                                 let uu____1336 =
                                   let uu____1349 =
                                     let uu____1360 =
                                       let uu____1363 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____1366 =
                                         let uu____1367 =
                                           let uu____1370 =
                                             let uu____1373 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____1374 =
                                               let uu____1377 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____1377]  in
                                             uu____1373 :: uu____1374  in
                                           FStar_Tests_Util.app mul
                                             uu____1370
                                            in
                                         let uu____1378 =
                                           let uu____1379 =
                                             let uu____1382 =
                                               let uu____1385 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____1386 =
                                                 let uu____1389 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____1389]  in
                                               uu____1385 :: uu____1386  in
                                             FStar_Tests_Util.app mul
                                               uu____1382
                                              in
                                           let uu____1390 =
                                             let uu____1391 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____1392 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____1391 uu____1392  in
                                           mk_let FStar_Tests_Util.h
                                             uu____1379 uu____1390
                                            in
                                         mk_let FStar_Tests_Util.y uu____1367
                                           uu____1378
                                          in
                                       mk_let FStar_Tests_Util.x uu____1363
                                         uu____1366
                                        in
                                     ((Prims.parse_int "16"), uu____1360, z)
                                      in
                                   let uu____1399 =
                                     let uu____1412 =
                                       let uu____1423 =
                                         let uu____1426 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____1427 =
                                           let uu____1430 =
                                             let uu____1431 =
                                               let uu____1434 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____1435 =
                                                 let uu____1438 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____1438]  in
                                               uu____1434 :: uu____1435  in
                                             FStar_Tests_Util.app mul
                                               uu____1431
                                              in
                                           let uu____1439 =
                                             let uu____1442 =
                                               let uu____1443 =
                                                 let uu____1446 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____1447 =
                                                   let uu____1450 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____1450]  in
                                                 uu____1446 :: uu____1447  in
                                               FStar_Tests_Util.app mul
                                                 uu____1443
                                                in
                                             let uu____1451 =
                                               let uu____1454 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____1455 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____1454 uu____1455
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____1442 uu____1451
                                              in
                                           let_ FStar_Tests_Util.y uu____1430
                                             uu____1439
                                            in
                                         let_ FStar_Tests_Util.x uu____1426
                                           uu____1427
                                          in
                                       ((Prims.parse_int "17"), uu____1423,
                                         z)
                                        in
                                     let uu____1462 =
                                       let uu____1475 =
                                         let uu____1486 =
                                           let uu____1489 =
                                             let uu____1492 = snat znat  in
                                             snat uu____1492  in
                                           pred_nat uu____1489  in
                                         let uu____1493 = snat znat  in
                                         ((Prims.parse_int "18"), uu____1486,
                                           uu____1493)
                                          in
                                       let uu____1500 =
                                         let uu____1513 =
                                           let uu____1524 =
                                             let uu____1527 =
                                               let uu____1528 = snat znat  in
                                               snat uu____1528  in
                                             let uu____1529 = snat znat  in
                                             minus_nat uu____1527 uu____1529
                                              in
                                           let uu____1530 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____1524, uu____1530)
                                            in
                                         let uu____1537 =
                                           let uu____1550 =
                                             let uu____1561 =
                                               let uu____1564 =
                                                 encode_nat
                                                   (Prims.parse_int "10")
                                                  in
                                               let uu____1565 =
                                                 encode_nat
                                                   (Prims.parse_int "10")
                                                  in
                                               minus_nat uu____1564
                                                 uu____1565
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____1561, znat)
                                              in
                                           let uu____1570 =
                                             let uu____1583 =
                                               let uu____1594 =
                                                 let uu____1597 =
                                                   encode_nat
                                                     (Prims.parse_int "100")
                                                    in
                                                 let uu____1598 =
                                                   encode_nat
                                                     (Prims.parse_int "100")
                                                    in
                                                 minus_nat uu____1597
                                                   uu____1598
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____1594, znat)
                                                in
                                             let uu____1603 =
                                               let uu____1616 =
                                                 let uu____1627 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____1630 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____1627, uu____1630)
                                                  in
                                               let uu____1637 =
                                                 let uu____1650 =
                                                   let uu____1661 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____1664 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____1661, uu____1664)
                                                    in
                                                 let uu____1671 =
                                                   let uu____1684 =
                                                     let uu____1695 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____1698 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____1695,
                                                       uu____1698)
                                                      in
                                                   let uu____1705 =
                                                     let uu____1718 =
                                                       let uu____1729 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____1732 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____1729,
                                                         uu____1732)
                                                        in
                                                     let uu____1739 =
                                                       let uu____1752 =
                                                         let uu____1763 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____1766 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____1763,
                                                           uu____1766)
                                                          in
                                                       let uu____1773 =
                                                         let uu____1786 =
                                                           let uu____1797 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____1800 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____1797,
                                                             uu____1800)
                                                            in
                                                         let uu____1807 =
                                                           let uu____1820 =
                                                             let uu____1831 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____1834 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____1831,
                                                               uu____1834)
                                                              in
                                                           let uu____1841 =
                                                             let uu____1854 =
                                                               let uu____1865
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____1868
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____1865,
                                                                 uu____1868)
                                                                in
                                                             let uu____1875 =
                                                               let uu____1888
                                                                 =
                                                                 let uu____1899
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____1902
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____1899,
                                                                   uu____1902)
                                                                  in
                                                               let uu____1909
                                                                 =
                                                                 let uu____1922
                                                                   =
                                                                   let uu____1933
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____1936
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____1933,
                                                                    uu____1936)
                                                                    in
                                                                 let uu____1943
                                                                   =
                                                                   let uu____1956
                                                                    =
                                                                    let uu____1967
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____1970
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____1967,
                                                                    uu____1970)
                                                                     in
                                                                   let uu____1977
                                                                    =
                                                                    let uu____1990
                                                                    =
                                                                    let uu____2001
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____2004
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____2001,
                                                                    uu____2004)
                                                                     in
                                                                    let uu____2011
                                                                    =
                                                                    let uu____2024
                                                                    =
                                                                    let uu____2035
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____2038
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____2035,
                                                                    uu____2038)
                                                                     in
                                                                    let uu____2045
                                                                    =
                                                                    let uu____2058
                                                                    =
                                                                    let uu____2069
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____2072
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____2069,
                                                                    uu____2072)
                                                                     in
                                                                    let uu____2079
                                                                    =
                                                                    let uu____2092
                                                                    =
                                                                    let uu____2103
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____2106
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____2103,
                                                                    uu____2106)
                                                                     in
                                                                    let uu____2113
                                                                    =
                                                                    let uu____2126
                                                                    =
                                                                    let uu____2137
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____2140
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____2137,
                                                                    uu____2140)
                                                                     in
                                                                    let uu____2147
                                                                    =
                                                                    let uu____2160
                                                                    =
                                                                    let uu____2171
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____2174
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____2171,
                                                                    uu____2174)
                                                                     in
                                                                    let uu____2181
                                                                    =
                                                                    let uu____2194
                                                                    =
                                                                    let uu____2205
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____2208
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____2205,
                                                                    uu____2208)
                                                                     in
                                                                    let uu____2215
                                                                    =
                                                                    let uu____2228
                                                                    =
                                                                    let uu____2239
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____2242
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____2239,
                                                                    uu____2242)
                                                                     in
                                                                    let uu____2249
                                                                    =
                                                                    let uu____2262
                                                                    =
                                                                    let uu____2273
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____2276
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____2273,
                                                                    uu____2276)
                                                                     in
                                                                    let uu____2283
                                                                    =
                                                                    let uu____2296
                                                                    =
                                                                    let uu____2307
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____2310
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____2307,
                                                                    uu____2310)
                                                                     in
                                                                    let uu____2317
                                                                    =
                                                                    let uu____2330
                                                                    =
                                                                    let uu____2341
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____2344
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____2341,
                                                                    uu____2344)
                                                                     in
                                                                    let uu____2351
                                                                    =
                                                                    let uu____2364
                                                                    =
                                                                    let uu____2375
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____2378
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____2375,
                                                                    uu____2378)
                                                                     in
                                                                    let uu____2385
                                                                    =
                                                                    let uu____2398
                                                                    =
                                                                    let uu____2409
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____2412
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____2409,
                                                                    uu____2412)
                                                                     in
                                                                    let uu____2419
                                                                    =
                                                                    let uu____2432
                                                                    =
                                                                    let uu____2443
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____2446
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____2443,
                                                                    uu____2446)
                                                                     in
                                                                    let uu____2453
                                                                    =
                                                                    let uu____2466
                                                                    =
                                                                    let uu____2477
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____2480
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____2477,
                                                                    uu____2480)
                                                                     in
                                                                    let uu____2487
                                                                    =
                                                                    let uu____2500
                                                                    =
                                                                    let uu____2511
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____2514
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____2511,
                                                                    uu____2514)
                                                                     in
                                                                    let uu____2521
                                                                    =
                                                                    let uu____2534
                                                                    =
                                                                    let uu____2545
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____2548
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____2545,
                                                                    uu____2548)
                                                                     in
                                                                    [uu____2534]
                                                                     in
                                                                    uu____2500
                                                                    ::
                                                                    uu____2521
                                                                     in
                                                                    uu____2466
                                                                    ::
                                                                    uu____2487
                                                                     in
                                                                    uu____2432
                                                                    ::
                                                                    uu____2453
                                                                     in
                                                                    uu____2398
                                                                    ::
                                                                    uu____2419
                                                                     in
                                                                    uu____2364
                                                                    ::
                                                                    uu____2385
                                                                     in
                                                                    uu____2330
                                                                    ::
                                                                    uu____2351
                                                                     in
                                                                    uu____2296
                                                                    ::
                                                                    uu____2317
                                                                     in
                                                                    uu____2262
                                                                    ::
                                                                    uu____2283
                                                                     in
                                                                    uu____2228
                                                                    ::
                                                                    uu____2249
                                                                     in
                                                                    uu____2194
                                                                    ::
                                                                    uu____2215
                                                                     in
                                                                    uu____2160
                                                                    ::
                                                                    uu____2181
                                                                     in
                                                                    uu____2126
                                                                    ::
                                                                    uu____2147
                                                                     in
                                                                    uu____2092
                                                                    ::
                                                                    uu____2113
                                                                     in
                                                                    uu____2058
                                                                    ::
                                                                    uu____2079
                                                                     in
                                                                    uu____2024
                                                                    ::
                                                                    uu____2045
                                                                     in
                                                                    uu____1990
                                                                    ::
                                                                    uu____2011
                                                                     in
                                                                   uu____1956
                                                                    ::
                                                                    uu____1977
                                                                    in
                                                                 uu____1922
                                                                   ::
                                                                   uu____1943
                                                                  in
                                                               uu____1888 ::
                                                                 uu____1909
                                                                in
                                                             uu____1854 ::
                                                               uu____1875
                                                              in
                                                           uu____1820 ::
                                                             uu____1841
                                                            in
                                                         uu____1786 ::
                                                           uu____1807
                                                          in
                                                       uu____1752 ::
                                                         uu____1773
                                                        in
                                                     uu____1718 :: uu____1739
                                                      in
                                                   uu____1684 :: uu____1705
                                                    in
                                                 uu____1650 :: uu____1671  in
                                               uu____1616 :: uu____1637  in
                                             uu____1583 :: uu____1603  in
                                           uu____1550 :: uu____1570  in
                                         uu____1513 :: uu____1537  in
                                       uu____1475 :: uu____1500  in
                                     uu____1412 :: uu____1462  in
                                   uu____1349 :: uu____1399  in
                                 uu____1286 :: uu____1336  in
                               uu____1247 :: uu____1273  in
                             uu____1212 :: uu____1234  in
                           uu____1177 :: uu____1199  in
                         uu____1142 :: uu____1164  in
                       uu____1111 :: uu____1129  in
                     uu____1080 :: uu____1098  in
                   uu____1049 :: uu____1067  in
                 uu____1018 :: uu____1036  in
               uu____987 :: uu____1005  in
             uu____939 :: uu____974  in
           uu____879 :: uu____926  in
         uu____834 :: uu____866  in
       uu____789 :: uu____821  in
     uu____751 :: uu____776  in
   uu____707 :: uu____738)
  
let run_either :
  'Auu____3075 .
    Prims.int ->
      'Auu____3075 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____3075 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____3111 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____3111);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____3114 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____3114 (fun a243  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____3131 =
               let uu____3132 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____3132 expected  in
             FStar_Tests_Util.always i uu____3131)))
  
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
             [FStar_TypeChecker_Normalize.Beta;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.delta_constant;
             FStar_TypeChecker_Normalize.Primops])
  
let (run_nbe :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        run_either i r expected
          (FStar_TypeChecker_NBE.normalize
             [FStar_TypeChecker_NBE.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant])
  
let (run_interpreter_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let interp uu____3201 = run_interpreter i r expected  in
        let uu____3202 =
          let uu____3203 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____3203  in
        (i, uu____3202)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe uu____3236 = run_nbe i r expected  in
        let uu____3237 =
          let uu____3238 = FStar_Util.return_execution_time nbe  in
          FStar_Pervasives_Native.snd uu____3238  in
        (i, uu____3237)
  
let run_tests :
  'Auu____3247 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____3247)
      -> 'Auu____3247 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___453_3296  ->
            match uu___453_3296 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____3323  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____3325 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____3332  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____3334 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____3347  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____3371  ->
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
        let nbe uu____3409 = run_nbe i r expected  in
        let norm1 uu____3415 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____3423  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____3425 =
       let uu____3426 = encode (Prims.parse_int "1000")  in
       let uu____3427 =
         let uu____3430 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____3431 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____3430 uu____3431  in
       let_ FStar_Tests_Util.x uu____3426 uu____3427  in
     run_both_with_time (Prims.parse_int "14") uu____3425 z)
  
let (compare_times :
  (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2 Prims.list
    ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list -> unit)
  =
  fun l_int  ->
    fun l_nbe  ->
      FStar_Util.print_string "Comparing times for normalization and nbe\n";
      FStar_List.iter2
        (fun res1  ->
           fun res2  ->
             let uu____3496 = res1  in
             match uu____3496 with
             | (t1,time_int) ->
                 let uu____3503 = res2  in
                 (match uu____3503 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____3510 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____3510 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____3516  ->
    let l_int = run_all_interpreter_with_time ()  in
    let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe
  