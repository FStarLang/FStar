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
  fun x1  -> FStar_Ident.lid_of_path ["Norm"; x1] FStar_Range.dummyRange 
let (znat_l : FStar_Syntax_Syntax.fv) =
  let uu____110 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____110 FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____111 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____111 FStar_Syntax_Syntax.delta_constant
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
    let uu____126 =
      let uu____133 =
        let uu____134 =
          let uu____151 = tm_fv snat_l  in
          let uu____154 =
            let uu____165 = FStar_Syntax_Syntax.as_arg s  in [uu____165]  in
          (uu____151, uu____154)  in
        FStar_Syntax_Syntax.Tm_app uu____134  in
      FStar_Syntax_Syntax.mk uu____133  in
    uu____126 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____209 . 'Auu____209 -> 'Auu____209 FStar_Syntax_Syntax.withinfo_t =
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
      let uu____316 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____316, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____358 =
        let uu____361 =
          let uu____362 =
            let uu____375 =
              let uu____384 =
                let uu____391 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____391, false)  in
              [uu____384]  in
            (snat_l, uu____375)  in
          FStar_Syntax_Syntax.Pat_cons uu____362  in
        pat uu____361  in
      let uu____416 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___460_421 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___460_421.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___460_421.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____358, FStar_Pervasives_Native.None, uu____416)  in
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
        let uu____460 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____477 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____460, FStar_Pervasives_Native.None, uu____477)  in
      let sbranch =
        let uu____505 =
          let uu____508 =
            let uu____509 =
              let uu____522 =
                let uu____531 =
                  let uu____538 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____538, false)  in
                [uu____531]  in
              (snat_l, uu____522)  in
            FStar_Syntax_Syntax.Pat_cons uu____509  in
          pat uu____508  in
        let uu____563 =
          let uu____566 = FStar_Tests_Util.nm minus1  in
          let uu____569 =
            let uu____572 =
              let uu____573 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____573  in
            let uu____576 =
              let uu____579 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____579]  in
            uu____572 :: uu____576  in
          FStar_Tests_Util.app uu____566 uu____569  in
        (uu____505, FStar_Pervasives_Native.None, uu____563)  in
      let lb =
        let uu____591 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____592 =
          let uu____595 =
            let uu____596 =
              let uu____597 = b FStar_Tests_Util.x  in
              let uu____604 =
                let uu____613 = b FStar_Tests_Util.y  in [uu____613]  in
              uu____597 :: uu____604  in
            let uu____638 =
              let uu____641 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____641 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____596 uu____638
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____595
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____591;
          FStar_Syntax_Syntax.lbdef = uu____592;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____646 =
        let uu____653 =
          let uu____654 =
            let uu____667 =
              let uu____670 =
                let uu____671 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____671 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____670
               in
            ((true, [lb]), uu____667)  in
          FStar_Syntax_Syntax.Tm_let uu____654  in
        FStar_Syntax_Syntax.mk uu____653  in
      uu____646 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____704 = snat out  in
         aux uu____704 (n2 - (Prims.parse_int "1")))
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
  (let uu____741 =
     let uu____752 =
       let uu____755 =
         let uu____758 =
           let uu____761 =
             let uu____764 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____764]  in
           id :: uu____761  in
         one :: uu____758  in
       FStar_Tests_Util.app apply uu____755  in
     let uu____765 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____752, uu____765)  in
   let uu____772 =
     let uu____785 =
       let uu____796 =
         let uu____799 =
           let uu____802 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____802]  in
         FStar_Tests_Util.app id uu____799  in
       let uu____803 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____796, uu____803)  in
     let uu____810 =
       let uu____823 =
         let uu____834 =
           let uu____837 =
             let uu____840 =
               let uu____843 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____844 =
                 let uu____847 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____847]  in
               uu____843 :: uu____844  in
             tt :: uu____840  in
           FStar_Tests_Util.app apply uu____837  in
         let uu____848 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____834, uu____848)  in
       let uu____855 =
         let uu____868 =
           let uu____879 =
             let uu____882 =
               let uu____885 =
                 let uu____888 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____889 =
                   let uu____892 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                   [uu____892]  in
                 uu____888 :: uu____889  in
               ff :: uu____885  in
             FStar_Tests_Util.app apply uu____882  in
           let uu____893 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____879, uu____893)  in
         let uu____900 =
           let uu____913 =
             let uu____924 =
               let uu____927 =
                 let uu____930 =
                   let uu____933 =
                     let uu____936 =
                       let uu____939 =
                         let uu____942 =
                           let uu____945 =
                             let uu____948 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____949 =
                               let uu____952 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____952]  in
                             uu____948 :: uu____949  in
                           ff :: uu____945  in
                         apply :: uu____942  in
                       apply :: uu____939  in
                     apply :: uu____936  in
                   apply :: uu____933  in
                 apply :: uu____930  in
               FStar_Tests_Util.app apply uu____927  in
             let uu____953 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____924, uu____953)  in
           let uu____960 =
             let uu____973 =
               let uu____984 =
                 let uu____987 =
                   let uu____990 =
                     let uu____993 =
                       let uu____996 = FStar_Tests_Util.nm FStar_Tests_Util.n
                          in
                       let uu____997 =
                         let uu____1000 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____1000]  in
                       uu____996 :: uu____997  in
                     ff :: uu____993  in
                   apply :: uu____990  in
                 FStar_Tests_Util.app twice uu____987  in
               let uu____1001 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____984, uu____1001)  in
             let uu____1008 =
               let uu____1021 =
                 let uu____1032 = minus one z  in
                 ((Prims.parse_int "5"), uu____1032, one)  in
               let uu____1039 =
                 let uu____1052 =
                   let uu____1063 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____1063, z)  in
                 let uu____1070 =
                   let uu____1083 =
                     let uu____1094 = minus one one  in
                     ((Prims.parse_int "7"), uu____1094, z)  in
                   let uu____1101 =
                     let uu____1114 =
                       let uu____1125 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____1125, one)  in
                     let uu____1132 =
                       let uu____1145 =
                         let uu____1156 = FStar_Tests_Util.app mul [two; one]
                            in
                         ((Prims.parse_int "9"), uu____1156, two)  in
                       let uu____1163 =
                         let uu____1176 =
                           let uu____1187 =
                             let uu____1190 =
                               let uu____1193 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____1193; one]  in
                             FStar_Tests_Util.app mul uu____1190  in
                           ((Prims.parse_int "10"), uu____1187, two)  in
                         let uu____1198 =
                           let uu____1211 =
                             let uu____1222 =
                               let uu____1225 = encode (Prims.parse_int "10")
                                  in
                               let uu____1226 = encode (Prims.parse_int "10")
                                  in
                               minus uu____1225 uu____1226  in
                             ((Prims.parse_int "11"), uu____1222, z)  in
                           let uu____1233 =
                             let uu____1246 =
                               let uu____1257 =
                                 let uu____1260 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____1261 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____1260 uu____1261  in
                               ((Prims.parse_int "12"), uu____1257, z)  in
                             let uu____1268 =
                               let uu____1281 =
                                 let uu____1292 =
                                   let uu____1295 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____1296 =
                                     let uu____1299 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____1300 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____1299 uu____1300  in
                                   let_ FStar_Tests_Util.x uu____1295
                                     uu____1296
                                    in
                                 ((Prims.parse_int "13"), uu____1292, z)  in
                               let uu____1307 =
                                 let uu____1320 =
                                   let uu____1331 =
                                     let uu____1334 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____1335 =
                                       let uu____1338 =
                                         let uu____1339 =
                                           let uu____1342 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____1343 =
                                             let uu____1346 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____1346]  in
                                           uu____1342 :: uu____1343  in
                                         FStar_Tests_Util.app mul uu____1339
                                          in
                                       let uu____1347 =
                                         let uu____1350 =
                                           let uu____1351 =
                                             let uu____1354 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____1355 =
                                               let uu____1358 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____1358]  in
                                             uu____1354 :: uu____1355  in
                                           FStar_Tests_Util.app mul
                                             uu____1351
                                            in
                                         let uu____1359 =
                                           let uu____1362 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____1363 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____1362 uu____1363  in
                                         let_ FStar_Tests_Util.h uu____1350
                                           uu____1359
                                          in
                                       let_ FStar_Tests_Util.y uu____1338
                                         uu____1347
                                        in
                                     let_ FStar_Tests_Util.x uu____1334
                                       uu____1335
                                      in
                                   ((Prims.parse_int "15"), uu____1331, z)
                                    in
                                 let uu____1370 =
                                   let uu____1383 =
                                     let uu____1394 =
                                       let uu____1397 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____1400 =
                                         let uu____1401 =
                                           let uu____1404 =
                                             let uu____1407 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____1408 =
                                               let uu____1411 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____1411]  in
                                             uu____1407 :: uu____1408  in
                                           FStar_Tests_Util.app mul
                                             uu____1404
                                            in
                                         let uu____1412 =
                                           let uu____1413 =
                                             let uu____1416 =
                                               let uu____1419 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____1420 =
                                                 let uu____1423 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____1423]  in
                                               uu____1419 :: uu____1420  in
                                             FStar_Tests_Util.app mul
                                               uu____1416
                                              in
                                           let uu____1424 =
                                             let uu____1425 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____1426 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____1425 uu____1426  in
                                           mk_let FStar_Tests_Util.h
                                             uu____1413 uu____1424
                                            in
                                         mk_let FStar_Tests_Util.y uu____1401
                                           uu____1412
                                          in
                                       mk_let FStar_Tests_Util.x uu____1397
                                         uu____1400
                                        in
                                     ((Prims.parse_int "16"), uu____1394, z)
                                      in
                                   let uu____1433 =
                                     let uu____1446 =
                                       let uu____1457 =
                                         let uu____1460 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____1461 =
                                           let uu____1464 =
                                             let uu____1465 =
                                               let uu____1468 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____1469 =
                                                 let uu____1472 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____1472]  in
                                               uu____1468 :: uu____1469  in
                                             FStar_Tests_Util.app mul
                                               uu____1465
                                              in
                                           let uu____1473 =
                                             let uu____1476 =
                                               let uu____1477 =
                                                 let uu____1480 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____1481 =
                                                   let uu____1484 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____1484]  in
                                                 uu____1480 :: uu____1481  in
                                               FStar_Tests_Util.app mul
                                                 uu____1477
                                                in
                                             let uu____1485 =
                                               let uu____1488 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____1489 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____1488 uu____1489
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____1476 uu____1485
                                              in
                                           let_ FStar_Tests_Util.y uu____1464
                                             uu____1473
                                            in
                                         let_ FStar_Tests_Util.x uu____1460
                                           uu____1461
                                          in
                                       ((Prims.parse_int "17"), uu____1457,
                                         z)
                                        in
                                     let uu____1496 =
                                       let uu____1509 =
                                         let uu____1520 =
                                           let uu____1523 =
                                             let uu____1526 = snat znat  in
                                             snat uu____1526  in
                                           pred_nat uu____1523  in
                                         let uu____1527 = snat znat  in
                                         ((Prims.parse_int "18"), uu____1520,
                                           uu____1527)
                                          in
                                       let uu____1534 =
                                         let uu____1547 =
                                           let uu____1558 =
                                             let uu____1561 =
                                               let uu____1562 = snat znat  in
                                               snat uu____1562  in
                                             let uu____1563 = snat znat  in
                                             minus_nat uu____1561 uu____1563
                                              in
                                           let uu____1564 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____1558, uu____1564)
                                            in
                                         let uu____1571 =
                                           let uu____1584 =
                                             let uu____1595 =
                                               let uu____1598 =
                                                 encode_nat
                                                   (Prims.parse_int "10")
                                                  in
                                               let uu____1599 =
                                                 encode_nat
                                                   (Prims.parse_int "10")
                                                  in
                                               minus_nat uu____1598
                                                 uu____1599
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____1595, znat)
                                              in
                                           let uu____1604 =
                                             let uu____1617 =
                                               let uu____1628 =
                                                 let uu____1631 =
                                                   encode_nat
                                                     (Prims.parse_int "100")
                                                    in
                                                 let uu____1632 =
                                                   encode_nat
                                                     (Prims.parse_int "100")
                                                    in
                                                 minus_nat uu____1631
                                                   uu____1632
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____1628, znat)
                                                in
                                             let uu____1637 =
                                               let uu____1650 =
                                                 let uu____1661 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____1664 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____1661, uu____1664)
                                                  in
                                               let uu____1671 =
                                                 let uu____1684 =
                                                   let uu____1695 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____1698 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____1695, uu____1698)
                                                    in
                                                 let uu____1705 =
                                                   let uu____1718 =
                                                     let uu____1729 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____1732 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____1729,
                                                       uu____1732)
                                                      in
                                                   let uu____1739 =
                                                     let uu____1752 =
                                                       let uu____1763 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____1766 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____1763,
                                                         uu____1766)
                                                        in
                                                     let uu____1773 =
                                                       let uu____1786 =
                                                         let uu____1797 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____1800 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____1797,
                                                           uu____1800)
                                                          in
                                                       let uu____1807 =
                                                         let uu____1820 =
                                                           let uu____1831 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____1834 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____1831,
                                                             uu____1834)
                                                            in
                                                         let uu____1841 =
                                                           let uu____1854 =
                                                             let uu____1865 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____1868 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____1865,
                                                               uu____1868)
                                                              in
                                                           let uu____1875 =
                                                             let uu____1888 =
                                                               let uu____1899
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____1902
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____1899,
                                                                 uu____1902)
                                                                in
                                                             let uu____1909 =
                                                               let uu____1922
                                                                 =
                                                                 let uu____1933
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____1936
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
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
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____1970
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
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
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____2004
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
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
                                                                    "idd T"
                                                                     in
                                                                    let uu____2038
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
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
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____2072
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
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
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____2106
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
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
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____2140
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
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
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____2174
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
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
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____2208
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
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
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____2242
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
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
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____2276
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
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
                                                                    "[5]"  in
                                                                    let uu____2310
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
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
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____2344
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
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
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____2378
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
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
                                                                    "idd T"
                                                                     in
                                                                    let uu____2412
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
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
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____2446
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
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
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____2480
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
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
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____2514
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
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
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____2548
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____2545,
                                                                    uu____2548)
                                                                     in
                                                                    let uu____2555
                                                                    =
                                                                    let uu____2568
                                                                    =
                                                                    let uu____2579
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____2582
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____2579,
                                                                    uu____2582)
                                                                     in
                                                                    let uu____2589
                                                                    =
                                                                    let uu____2602
                                                                    =
                                                                    let uu____2613
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____2616
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____2613,
                                                                    uu____2616)
                                                                     in
                                                                    let uu____2623
                                                                    =
                                                                    let uu____2636
                                                                    =
                                                                    let uu____2647
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____2650
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____2647,
                                                                    uu____2650)
                                                                     in
                                                                    let uu____2657
                                                                    =
                                                                    let uu____2670
                                                                    =
                                                                    let uu____2681
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____2684
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____2681,
                                                                    uu____2684)
                                                                     in
                                                                    let uu____2691
                                                                    =
                                                                    let uu____2704
                                                                    =
                                                                    let uu____2715
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____2718
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____2715,
                                                                    uu____2718)
                                                                     in
                                                                    let uu____2725
                                                                    =
                                                                    let uu____2738
                                                                    =
                                                                    let uu____2749
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____2752
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____2749,
                                                                    uu____2752)
                                                                     in
                                                                    let uu____2759
                                                                    =
                                                                    let uu____2772
                                                                    =
                                                                    let uu____2783
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____2786
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____2783,
                                                                    uu____2786)
                                                                     in
                                                                    [uu____2772]
                                                                     in
                                                                    uu____2738
                                                                    ::
                                                                    uu____2759
                                                                     in
                                                                    uu____2704
                                                                    ::
                                                                    uu____2725
                                                                     in
                                                                    uu____2670
                                                                    ::
                                                                    uu____2691
                                                                     in
                                                                    uu____2636
                                                                    ::
                                                                    uu____2657
                                                                     in
                                                                    uu____2602
                                                                    ::
                                                                    uu____2623
                                                                     in
                                                                    uu____2568
                                                                    ::
                                                                    uu____2589
                                                                     in
                                                                    uu____2534
                                                                    ::
                                                                    uu____2555
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
                                                               uu____1922 ::
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
                                                     uu____1752 :: uu____1773
                                                      in
                                                   uu____1718 :: uu____1739
                                                    in
                                                 uu____1684 :: uu____1705  in
                                               uu____1650 :: uu____1671  in
                                             uu____1617 :: uu____1637  in
                                           uu____1584 :: uu____1604  in
                                         uu____1547 :: uu____1571  in
                                       uu____1509 :: uu____1534  in
                                     uu____1446 :: uu____1496  in
                                   uu____1383 :: uu____1433  in
                                 uu____1320 :: uu____1370  in
                               uu____1281 :: uu____1307  in
                             uu____1246 :: uu____1268  in
                           uu____1211 :: uu____1233  in
                         uu____1176 :: uu____1198  in
                       uu____1145 :: uu____1163  in
                     uu____1114 :: uu____1132  in
                   uu____1083 :: uu____1101  in
                 uu____1052 :: uu____1070  in
               uu____1021 :: uu____1039  in
             uu____973 :: uu____1008  in
           uu____913 :: uu____960  in
         uu____868 :: uu____900  in
       uu____823 :: uu____855  in
     uu____785 :: uu____810  in
   uu____741 :: uu____772)
  
let run_either :
  'Auu____3373 .
    Prims.int ->
      'Auu____3373 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____3373 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____3409 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____3409);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____3412 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____3412 (fun a242  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____3429 =
               let uu____3430 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____3430 expected  in
             FStar_Tests_Util.always i uu____3429)))
  
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
          (FStar_TypeChecker_NBE.test_normalize
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
        let interp uu____3499 = run_interpreter i r expected  in
        let uu____3500 =
          let uu____3501 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____3501  in
        (i, uu____3500)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____3534 = run_nbe i r expected  in
        let uu____3535 =
          let uu____3536 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____3536  in
        (i, uu____3535)
  
let run_tests :
  'Auu____3545 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____3545)
      -> 'Auu____3545 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___459_3594  ->
            match uu___459_3594 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____3621  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____3623 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____3630  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____3632 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____3645  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____3669  ->
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
        let nbe1 uu____3707 = run_nbe i r expected  in
        let norm1 uu____3713 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____3721  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____3723 =
       let uu____3724 = encode (Prims.parse_int "1000")  in
       let uu____3725 =
         let uu____3728 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____3729 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____3728 uu____3729  in
       let_ FStar_Tests_Util.x uu____3724 uu____3725  in
     run_both_with_time (Prims.parse_int "14") uu____3723 z)
  
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
             let uu____3794 = res1  in
             match uu____3794 with
             | (t1,time_int) ->
                 let uu____3801 = res2  in
                 (match uu____3801 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____3808 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____3808 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____3814  ->
    (let uu____3816 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____3816);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  