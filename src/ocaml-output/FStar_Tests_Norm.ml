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
             (let uu___455_403 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___455_403.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___455_403.FStar_Syntax_Syntax.sort)
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
  (let uu____711 =
     let uu____722 =
       let uu____725 =
         let uu____728 =
           let uu____731 =
             let uu____734 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____734]  in
           id :: uu____731  in
         one :: uu____728  in
       FStar_Tests_Util.app apply uu____725  in
     let uu____735 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____722, uu____735)  in
   let uu____742 =
     let uu____755 =
       let uu____766 =
         let uu____769 =
           let uu____772 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____772]  in
         FStar_Tests_Util.app id uu____769  in
       let uu____773 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____766, uu____773)  in
     let uu____780 =
       let uu____793 =
         let uu____804 =
           let uu____807 =
             let uu____810 =
               let uu____813 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____814 =
                 let uu____817 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____817]  in
               uu____813 :: uu____814  in
             tt :: uu____810  in
           FStar_Tests_Util.app apply uu____807  in
         let uu____818 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____804, uu____818)  in
       let uu____825 =
         let uu____838 =
           let uu____849 =
             let uu____852 =
               let uu____855 =
                 let uu____858 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____859 =
                   let uu____862 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                   [uu____862]  in
                 uu____858 :: uu____859  in
               ff :: uu____855  in
             FStar_Tests_Util.app apply uu____852  in
           let uu____863 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____849, uu____863)  in
         let uu____870 =
           let uu____883 =
             let uu____894 =
               let uu____897 =
                 let uu____900 =
                   let uu____903 =
                     let uu____906 =
                       let uu____909 =
                         let uu____912 =
                           let uu____915 =
                             let uu____918 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____919 =
                               let uu____922 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____922]  in
                             uu____918 :: uu____919  in
                           ff :: uu____915  in
                         apply :: uu____912  in
                       apply :: uu____909  in
                     apply :: uu____906  in
                   apply :: uu____903  in
                 apply :: uu____900  in
               FStar_Tests_Util.app apply uu____897  in
             let uu____923 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____894, uu____923)  in
           let uu____930 =
             let uu____943 =
               let uu____954 =
                 let uu____957 =
                   let uu____960 =
                     let uu____963 =
                       let uu____966 = FStar_Tests_Util.nm FStar_Tests_Util.n
                          in
                       let uu____967 =
                         let uu____970 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____970]  in
                       uu____966 :: uu____967  in
                     ff :: uu____963  in
                   apply :: uu____960  in
                 FStar_Tests_Util.app twice uu____957  in
               let uu____971 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____954, uu____971)  in
             let uu____978 =
               let uu____991 =
                 let uu____1002 = minus one z  in
                 ((Prims.parse_int "5"), uu____1002, one)  in
               let uu____1009 =
                 let uu____1022 =
                   let uu____1033 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____1033, z)  in
                 let uu____1040 =
                   let uu____1053 =
                     let uu____1064 = minus one one  in
                     ((Prims.parse_int "7"), uu____1064, z)  in
                   let uu____1071 =
                     let uu____1084 =
                       let uu____1095 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____1095, one)  in
                     let uu____1102 =
                       let uu____1115 =
                         let uu____1126 = FStar_Tests_Util.app mul [two; one]
                            in
                         ((Prims.parse_int "9"), uu____1126, two)  in
                       let uu____1133 =
                         let uu____1146 =
                           let uu____1157 =
                             let uu____1160 =
                               let uu____1163 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____1163; one]  in
                             FStar_Tests_Util.app mul uu____1160  in
                           ((Prims.parse_int "10"), uu____1157, two)  in
                         let uu____1168 =
                           let uu____1181 =
                             let uu____1192 =
                               let uu____1195 = encode (Prims.parse_int "10")
                                  in
                               let uu____1196 = encode (Prims.parse_int "10")
                                  in
                               minus uu____1195 uu____1196  in
                             ((Prims.parse_int "11"), uu____1192, z)  in
                           let uu____1203 =
                             let uu____1216 =
                               let uu____1227 =
                                 let uu____1230 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____1231 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____1230 uu____1231  in
                               ((Prims.parse_int "12"), uu____1227, z)  in
                             let uu____1238 =
                               let uu____1251 =
                                 let uu____1262 =
                                   let uu____1265 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____1266 =
                                     let uu____1269 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____1270 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____1269 uu____1270  in
                                   let_ FStar_Tests_Util.x uu____1265
                                     uu____1266
                                    in
                                 ((Prims.parse_int "13"), uu____1262, z)  in
                               let uu____1277 =
                                 let uu____1290 =
                                   let uu____1301 =
                                     let uu____1304 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____1305 =
                                       let uu____1308 =
                                         let uu____1309 =
                                           let uu____1312 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____1313 =
                                             let uu____1316 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____1316]  in
                                           uu____1312 :: uu____1313  in
                                         FStar_Tests_Util.app mul uu____1309
                                          in
                                       let uu____1317 =
                                         let uu____1320 =
                                           let uu____1321 =
                                             let uu____1324 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____1325 =
                                               let uu____1328 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____1328]  in
                                             uu____1324 :: uu____1325  in
                                           FStar_Tests_Util.app mul
                                             uu____1321
                                            in
                                         let uu____1329 =
                                           let uu____1332 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____1333 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____1332 uu____1333  in
                                         let_ FStar_Tests_Util.h uu____1320
                                           uu____1329
                                          in
                                       let_ FStar_Tests_Util.y uu____1308
                                         uu____1317
                                        in
                                     let_ FStar_Tests_Util.x uu____1304
                                       uu____1305
                                      in
                                   ((Prims.parse_int "15"), uu____1301, z)
                                    in
                                 let uu____1340 =
                                   let uu____1353 =
                                     let uu____1364 =
                                       let uu____1367 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____1370 =
                                         let uu____1371 =
                                           let uu____1374 =
                                             let uu____1377 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____1378 =
                                               let uu____1381 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____1381]  in
                                             uu____1377 :: uu____1378  in
                                           FStar_Tests_Util.app mul
                                             uu____1374
                                            in
                                         let uu____1382 =
                                           let uu____1383 =
                                             let uu____1386 =
                                               let uu____1389 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____1390 =
                                                 let uu____1393 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____1393]  in
                                               uu____1389 :: uu____1390  in
                                             FStar_Tests_Util.app mul
                                               uu____1386
                                              in
                                           let uu____1394 =
                                             let uu____1395 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____1396 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____1395 uu____1396  in
                                           mk_let FStar_Tests_Util.h
                                             uu____1383 uu____1394
                                            in
                                         mk_let FStar_Tests_Util.y uu____1371
                                           uu____1382
                                          in
                                       mk_let FStar_Tests_Util.x uu____1367
                                         uu____1370
                                        in
                                     ((Prims.parse_int "16"), uu____1364, z)
                                      in
                                   let uu____1403 =
                                     let uu____1416 =
                                       let uu____1427 =
                                         let uu____1430 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____1431 =
                                           let uu____1434 =
                                             let uu____1435 =
                                               let uu____1438 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____1439 =
                                                 let uu____1442 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____1442]  in
                                               uu____1438 :: uu____1439  in
                                             FStar_Tests_Util.app mul
                                               uu____1435
                                              in
                                           let uu____1443 =
                                             let uu____1446 =
                                               let uu____1447 =
                                                 let uu____1450 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____1451 =
                                                   let uu____1454 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____1454]  in
                                                 uu____1450 :: uu____1451  in
                                               FStar_Tests_Util.app mul
                                                 uu____1447
                                                in
                                             let uu____1455 =
                                               let uu____1458 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____1459 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____1458 uu____1459
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____1446 uu____1455
                                              in
                                           let_ FStar_Tests_Util.y uu____1434
                                             uu____1443
                                            in
                                         let_ FStar_Tests_Util.x uu____1430
                                           uu____1431
                                          in
                                       ((Prims.parse_int "17"), uu____1427,
                                         z)
                                        in
                                     let uu____1466 =
                                       let uu____1479 =
                                         let uu____1490 =
                                           let uu____1493 =
                                             let uu____1496 = snat znat  in
                                             snat uu____1496  in
                                           pred_nat uu____1493  in
                                         let uu____1497 = snat znat  in
                                         ((Prims.parse_int "18"), uu____1490,
                                           uu____1497)
                                          in
                                       let uu____1504 =
                                         let uu____1517 =
                                           let uu____1528 =
                                             let uu____1531 =
                                               let uu____1532 = snat znat  in
                                               snat uu____1532  in
                                             let uu____1533 = snat znat  in
                                             minus_nat uu____1531 uu____1533
                                              in
                                           let uu____1534 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____1528, uu____1534)
                                            in
                                         let uu____1541 =
                                           let uu____1554 =
                                             let uu____1565 =
                                               let uu____1568 =
                                                 encode_nat
                                                   (Prims.parse_int "10")
                                                  in
                                               let uu____1569 =
                                                 encode_nat
                                                   (Prims.parse_int "10")
                                                  in
                                               minus_nat uu____1568
                                                 uu____1569
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____1565, znat)
                                              in
                                           let uu____1574 =
                                             let uu____1587 =
                                               let uu____1598 =
                                                 let uu____1601 =
                                                   encode_nat
                                                     (Prims.parse_int "100")
                                                    in
                                                 let uu____1602 =
                                                   encode_nat
                                                     (Prims.parse_int "100")
                                                    in
                                                 minus_nat uu____1601
                                                   uu____1602
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____1598, znat)
                                                in
                                             let uu____1607 =
                                               let uu____1620 =
                                                 let uu____1631 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____1634 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____1631, uu____1634)
                                                  in
                                               let uu____1641 =
                                                 let uu____1654 =
                                                   let uu____1665 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____1668 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____1665, uu____1668)
                                                    in
                                                 let uu____1675 =
                                                   let uu____1688 =
                                                     let uu____1699 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____1702 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____1699,
                                                       uu____1702)
                                                      in
                                                   let uu____1709 =
                                                     let uu____1722 =
                                                       let uu____1733 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____1736 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____1733,
                                                         uu____1736)
                                                        in
                                                     let uu____1743 =
                                                       let uu____1756 =
                                                         let uu____1767 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____1770 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____1767,
                                                           uu____1770)
                                                          in
                                                       let uu____1777 =
                                                         let uu____1790 =
                                                           let uu____1801 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____1804 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____1801,
                                                             uu____1804)
                                                            in
                                                         let uu____1811 =
                                                           let uu____1824 =
                                                             let uu____1835 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____1838 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____1835,
                                                               uu____1838)
                                                              in
                                                           let uu____1845 =
                                                             let uu____1858 =
                                                               let uu____1869
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____1872
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____1869,
                                                                 uu____1872)
                                                                in
                                                             let uu____1879 =
                                                               let uu____1892
                                                                 =
                                                                 let uu____1903
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____1906
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____1903,
                                                                   uu____1906)
                                                                  in
                                                               let uu____1913
                                                                 =
                                                                 let uu____1926
                                                                   =
                                                                   let uu____1937
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____1940
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____1937,
                                                                    uu____1940)
                                                                    in
                                                                 let uu____1947
                                                                   =
                                                                   let uu____1960
                                                                    =
                                                                    let uu____1971
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____1974
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____1971,
                                                                    uu____1974)
                                                                     in
                                                                   let uu____1981
                                                                    =
                                                                    let uu____1994
                                                                    =
                                                                    let uu____2005
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____2008
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____2005,
                                                                    uu____2008)
                                                                     in
                                                                    let uu____2015
                                                                    =
                                                                    let uu____2028
                                                                    =
                                                                    let uu____2039
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____2042
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____2039,
                                                                    uu____2042)
                                                                     in
                                                                    let uu____2049
                                                                    =
                                                                    let uu____2062
                                                                    =
                                                                    let uu____2073
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____2076
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____2073,
                                                                    uu____2076)
                                                                     in
                                                                    let uu____2083
                                                                    =
                                                                    let uu____2096
                                                                    =
                                                                    let uu____2107
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____2110
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____2107,
                                                                    uu____2110)
                                                                     in
                                                                    let uu____2117
                                                                    =
                                                                    let uu____2130
                                                                    =
                                                                    let uu____2141
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____2144
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____2141,
                                                                    uu____2144)
                                                                     in
                                                                    let uu____2151
                                                                    =
                                                                    let uu____2164
                                                                    =
                                                                    let uu____2175
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____2178
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____2175,
                                                                    uu____2178)
                                                                     in
                                                                    let uu____2185
                                                                    =
                                                                    let uu____2198
                                                                    =
                                                                    let uu____2209
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____2212
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____2209,
                                                                    uu____2212)
                                                                     in
                                                                    let uu____2219
                                                                    =
                                                                    let uu____2232
                                                                    =
                                                                    let uu____2243
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____2246
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____2243,
                                                                    uu____2246)
                                                                     in
                                                                    let uu____2253
                                                                    =
                                                                    let uu____2266
                                                                    =
                                                                    let uu____2277
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____2280
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____2277,
                                                                    uu____2280)
                                                                     in
                                                                    let uu____2287
                                                                    =
                                                                    let uu____2300
                                                                    =
                                                                    let uu____2311
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____2314
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____2311,
                                                                    uu____2314)
                                                                     in
                                                                    let uu____2321
                                                                    =
                                                                    let uu____2334
                                                                    =
                                                                    let uu____2345
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____2348
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____2345,
                                                                    uu____2348)
                                                                     in
                                                                    let uu____2355
                                                                    =
                                                                    let uu____2368
                                                                    =
                                                                    let uu____2379
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____2382
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____2379,
                                                                    uu____2382)
                                                                     in
                                                                    let uu____2389
                                                                    =
                                                                    let uu____2402
                                                                    =
                                                                    let uu____2413
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____2416
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____2413,
                                                                    uu____2416)
                                                                     in
                                                                    let uu____2423
                                                                    =
                                                                    let uu____2436
                                                                    =
                                                                    let uu____2447
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____2450
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____2447,
                                                                    uu____2450)
                                                                     in
                                                                    let uu____2457
                                                                    =
                                                                    let uu____2470
                                                                    =
                                                                    let uu____2481
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____2484
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____2481,
                                                                    uu____2484)
                                                                     in
                                                                    let uu____2491
                                                                    =
                                                                    let uu____2504
                                                                    =
                                                                    let uu____2515
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____2518
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____2515,
                                                                    uu____2518)
                                                                     in
                                                                    let uu____2525
                                                                    =
                                                                    let uu____2538
                                                                    =
                                                                    let uu____2549
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____2552
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____2549,
                                                                    uu____2552)
                                                                     in
                                                                    let uu____2559
                                                                    =
                                                                    let uu____2572
                                                                    =
                                                                    let uu____2583
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____2586
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____2583,
                                                                    uu____2586)
                                                                     in
                                                                    let uu____2593
                                                                    =
                                                                    let uu____2606
                                                                    =
                                                                    let uu____2617
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____2620
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____2617,
                                                                    uu____2620)
                                                                     in
                                                                    let uu____2627
                                                                    =
                                                                    let uu____2640
                                                                    =
                                                                    let uu____2651
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____2654
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____2651,
                                                                    uu____2654)
                                                                     in
                                                                    let uu____2661
                                                                    =
                                                                    let uu____2674
                                                                    =
                                                                    let uu____2685
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____2688
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____2685,
                                                                    uu____2688)
                                                                     in
                                                                    let uu____2695
                                                                    =
                                                                    let uu____2708
                                                                    =
                                                                    let uu____2719
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____2722
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____2719,
                                                                    uu____2722)
                                                                     in
                                                                    let uu____2729
                                                                    =
                                                                    let uu____2742
                                                                    =
                                                                    let uu____2753
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____2756
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____2753,
                                                                    uu____2756)
                                                                     in
                                                                    [uu____2742]
                                                                     in
                                                                    uu____2708
                                                                    ::
                                                                    uu____2729
                                                                     in
                                                                    uu____2674
                                                                    ::
                                                                    uu____2695
                                                                     in
                                                                    uu____2640
                                                                    ::
                                                                    uu____2661
                                                                     in
                                                                    uu____2606
                                                                    ::
                                                                    uu____2627
                                                                     in
                                                                    uu____2572
                                                                    ::
                                                                    uu____2593
                                                                     in
                                                                    uu____2538
                                                                    ::
                                                                    uu____2559
                                                                     in
                                                                    uu____2504
                                                                    ::
                                                                    uu____2525
                                                                     in
                                                                    uu____2470
                                                                    ::
                                                                    uu____2491
                                                                     in
                                                                    uu____2436
                                                                    ::
                                                                    uu____2457
                                                                     in
                                                                    uu____2402
                                                                    ::
                                                                    uu____2423
                                                                     in
                                                                    uu____2368
                                                                    ::
                                                                    uu____2389
                                                                     in
                                                                    uu____2334
                                                                    ::
                                                                    uu____2355
                                                                     in
                                                                    uu____2300
                                                                    ::
                                                                    uu____2321
                                                                     in
                                                                    uu____2266
                                                                    ::
                                                                    uu____2287
                                                                     in
                                                                    uu____2232
                                                                    ::
                                                                    uu____2253
                                                                     in
                                                                    uu____2198
                                                                    ::
                                                                    uu____2219
                                                                     in
                                                                    uu____2164
                                                                    ::
                                                                    uu____2185
                                                                     in
                                                                    uu____2130
                                                                    ::
                                                                    uu____2151
                                                                     in
                                                                    uu____2096
                                                                    ::
                                                                    uu____2117
                                                                     in
                                                                    uu____2062
                                                                    ::
                                                                    uu____2083
                                                                     in
                                                                    uu____2028
                                                                    ::
                                                                    uu____2049
                                                                     in
                                                                    uu____1994
                                                                    ::
                                                                    uu____2015
                                                                     in
                                                                   uu____1960
                                                                    ::
                                                                    uu____1981
                                                                    in
                                                                 uu____1926
                                                                   ::
                                                                   uu____1947
                                                                  in
                                                               uu____1892 ::
                                                                 uu____1913
                                                                in
                                                             uu____1858 ::
                                                               uu____1879
                                                              in
                                                           uu____1824 ::
                                                             uu____1845
                                                            in
                                                         uu____1790 ::
                                                           uu____1811
                                                          in
                                                       uu____1756 ::
                                                         uu____1777
                                                        in
                                                     uu____1722 :: uu____1743
                                                      in
                                                   uu____1688 :: uu____1709
                                                    in
                                                 uu____1654 :: uu____1675  in
                                               uu____1620 :: uu____1641  in
                                             uu____1587 :: uu____1607  in
                                           uu____1554 :: uu____1574  in
                                         uu____1517 :: uu____1541  in
                                       uu____1479 :: uu____1504  in
                                     uu____1416 :: uu____1466  in
                                   uu____1353 :: uu____1403  in
                                 uu____1290 :: uu____1340  in
                               uu____1251 :: uu____1277  in
                             uu____1216 :: uu____1238  in
                           uu____1181 :: uu____1203  in
                         uu____1146 :: uu____1168  in
                       uu____1115 :: uu____1133  in
                     uu____1084 :: uu____1102  in
                   uu____1053 :: uu____1071  in
                 uu____1022 :: uu____1040  in
               uu____991 :: uu____1009  in
             uu____943 :: uu____978  in
           uu____883 :: uu____930  in
         uu____838 :: uu____870  in
       uu____793 :: uu____825  in
     uu____755 :: uu____780  in
   uu____711 :: uu____742)
  
let run_either :
  'Auu____3343 .
    Prims.int ->
      'Auu____3343 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____3343 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____3379 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____3379);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____3382 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____3382 (fun a243  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____3399 =
               let uu____3400 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____3400 expected  in
             FStar_Tests_Util.always i uu____3399)))
  
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
        let interp uu____3469 = run_interpreter i r expected  in
        let uu____3470 =
          let uu____3471 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____3471  in
        (i, uu____3470)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____3504 = run_nbe i r expected  in
        let uu____3505 =
          let uu____3506 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____3506  in
        (i, uu____3505)
  
let run_tests :
  'Auu____3515 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____3515)
      -> 'Auu____3515 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___454_3564  ->
            match uu___454_3564 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____3591  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____3593 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____3600  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____3602 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____3615  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____3639  ->
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
        let nbe1 uu____3677 = run_nbe i r expected  in
        let norm1 uu____3683 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____3691  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____3693 =
       let uu____3694 = encode (Prims.parse_int "1000")  in
       let uu____3695 =
         let uu____3698 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____3699 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____3698 uu____3699  in
       let_ FStar_Tests_Util.x uu____3694 uu____3695  in
     run_both_with_time (Prims.parse_int "14") uu____3693 z)
  
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
             let uu____3764 = res1  in
             match uu____3764 with
             | (t1,time_int) ->
                 let uu____3771 = res2  in
                 (match uu____3771 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____3778 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____3778 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____3784  ->
    let l_int = run_all_interpreter_with_time ()  in
    let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe
  