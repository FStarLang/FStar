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
  fun x1  -> FStar_Ident.lid_of_path ["Test"; x1] FStar_Range.dummyRange 
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
             (let uu___473_421 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___473_421.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___473_421.FStar_Syntax_Syntax.sort)
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
  (let uu____742 =
     let uu____753 =
       let uu____756 =
         let uu____759 =
           let uu____762 =
             let uu____765 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____765]  in
           id :: uu____762  in
         one :: uu____759  in
       FStar_Tests_Util.app apply uu____756  in
     let uu____766 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____753, uu____766)  in
   let uu____773 =
     let uu____786 =
       let uu____797 =
         let uu____800 =
           let uu____803 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____803]  in
         FStar_Tests_Util.app id uu____800  in
       let uu____804 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____797, uu____804)  in
     let uu____811 =
       let uu____824 =
         let uu____835 =
           let uu____838 =
             let uu____841 =
               let uu____844 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____845 =
                 let uu____848 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____848]  in
               uu____844 :: uu____845  in
             tt :: uu____841  in
           FStar_Tests_Util.app apply uu____838  in
         let uu____849 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____835, uu____849)  in
       let uu____856 =
         let uu____869 =
           let uu____880 =
             let uu____883 =
               let uu____886 =
                 let uu____889 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____890 =
                   let uu____893 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                   [uu____893]  in
                 uu____889 :: uu____890  in
               ff :: uu____886  in
             FStar_Tests_Util.app apply uu____883  in
           let uu____894 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____880, uu____894)  in
         let uu____901 =
           let uu____914 =
             let uu____925 =
               let uu____928 =
                 let uu____931 =
                   let uu____934 =
                     let uu____937 =
                       let uu____940 =
                         let uu____943 =
                           let uu____946 =
                             let uu____949 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____950 =
                               let uu____953 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____953]  in
                             uu____949 :: uu____950  in
                           ff :: uu____946  in
                         apply :: uu____943  in
                       apply :: uu____940  in
                     apply :: uu____937  in
                   apply :: uu____934  in
                 apply :: uu____931  in
               FStar_Tests_Util.app apply uu____928  in
             let uu____954 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____925, uu____954)  in
           let uu____961 =
             let uu____974 =
               let uu____985 =
                 let uu____988 =
                   let uu____991 =
                     let uu____994 =
                       let uu____997 = FStar_Tests_Util.nm FStar_Tests_Util.n
                          in
                       let uu____998 =
                         let uu____1001 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____1001]  in
                       uu____997 :: uu____998  in
                     ff :: uu____994  in
                   apply :: uu____991  in
                 FStar_Tests_Util.app twice uu____988  in
               let uu____1002 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____985, uu____1002)  in
             let uu____1009 =
               let uu____1022 =
                 let uu____1033 = minus one z  in
                 ((Prims.parse_int "5"), uu____1033, one)  in
               let uu____1040 =
                 let uu____1053 =
                   let uu____1064 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____1064, z)  in
                 let uu____1071 =
                   let uu____1084 =
                     let uu____1095 = minus one one  in
                     ((Prims.parse_int "7"), uu____1095, z)  in
                   let uu____1102 =
                     let uu____1115 =
                       let uu____1126 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____1126, one)  in
                     let uu____1133 =
                       let uu____1146 =
                         let uu____1157 = FStar_Tests_Util.app mul [two; one]
                            in
                         ((Prims.parse_int "9"), uu____1157, two)  in
                       let uu____1164 =
                         let uu____1177 =
                           let uu____1188 =
                             let uu____1191 =
                               let uu____1194 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____1194; one]  in
                             FStar_Tests_Util.app mul uu____1191  in
                           ((Prims.parse_int "10"), uu____1188, two)  in
                         let uu____1199 =
                           let uu____1212 =
                             let uu____1223 =
                               let uu____1226 = encode (Prims.parse_int "10")
                                  in
                               let uu____1227 = encode (Prims.parse_int "10")
                                  in
                               minus uu____1226 uu____1227  in
                             ((Prims.parse_int "11"), uu____1223, z)  in
                           let uu____1234 =
                             let uu____1247 =
                               let uu____1258 =
                                 let uu____1261 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____1262 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____1261 uu____1262  in
                               ((Prims.parse_int "12"), uu____1258, z)  in
                             let uu____1269 =
                               let uu____1282 =
                                 let uu____1293 =
                                   let uu____1296 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____1297 =
                                     let uu____1300 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____1301 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____1300 uu____1301  in
                                   let_ FStar_Tests_Util.x uu____1296
                                     uu____1297
                                    in
                                 ((Prims.parse_int "13"), uu____1293, z)  in
                               let uu____1308 =
                                 let uu____1321 =
                                   let uu____1332 =
                                     let uu____1335 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____1336 =
                                       let uu____1339 =
                                         let uu____1340 =
                                           let uu____1343 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____1344 =
                                             let uu____1347 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____1347]  in
                                           uu____1343 :: uu____1344  in
                                         FStar_Tests_Util.app mul uu____1340
                                          in
                                       let uu____1348 =
                                         let uu____1351 =
                                           let uu____1352 =
                                             let uu____1355 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____1356 =
                                               let uu____1359 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____1359]  in
                                             uu____1355 :: uu____1356  in
                                           FStar_Tests_Util.app mul
                                             uu____1352
                                            in
                                         let uu____1360 =
                                           let uu____1363 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____1364 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____1363 uu____1364  in
                                         let_ FStar_Tests_Util.h uu____1351
                                           uu____1360
                                          in
                                       let_ FStar_Tests_Util.y uu____1339
                                         uu____1348
                                        in
                                     let_ FStar_Tests_Util.x uu____1335
                                       uu____1336
                                      in
                                   ((Prims.parse_int "15"), uu____1332, z)
                                    in
                                 let uu____1371 =
                                   let uu____1384 =
                                     let uu____1395 =
                                       let uu____1398 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____1401 =
                                         let uu____1402 =
                                           let uu____1405 =
                                             let uu____1408 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____1409 =
                                               let uu____1412 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____1412]  in
                                             uu____1408 :: uu____1409  in
                                           FStar_Tests_Util.app mul
                                             uu____1405
                                            in
                                         let uu____1413 =
                                           let uu____1414 =
                                             let uu____1417 =
                                               let uu____1420 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____1421 =
                                                 let uu____1424 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____1424]  in
                                               uu____1420 :: uu____1421  in
                                             FStar_Tests_Util.app mul
                                               uu____1417
                                              in
                                           let uu____1425 =
                                             let uu____1426 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____1427 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____1426 uu____1427  in
                                           mk_let FStar_Tests_Util.h
                                             uu____1414 uu____1425
                                            in
                                         mk_let FStar_Tests_Util.y uu____1402
                                           uu____1413
                                          in
                                       mk_let FStar_Tests_Util.x uu____1398
                                         uu____1401
                                        in
                                     ((Prims.parse_int "16"), uu____1395, z)
                                      in
                                   let uu____1434 =
                                     let uu____1447 =
                                       let uu____1458 =
                                         let uu____1461 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____1462 =
                                           let uu____1465 =
                                             let uu____1466 =
                                               let uu____1469 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____1470 =
                                                 let uu____1473 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____1473]  in
                                               uu____1469 :: uu____1470  in
                                             FStar_Tests_Util.app mul
                                               uu____1466
                                              in
                                           let uu____1474 =
                                             let uu____1477 =
                                               let uu____1478 =
                                                 let uu____1481 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____1482 =
                                                   let uu____1485 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____1485]  in
                                                 uu____1481 :: uu____1482  in
                                               FStar_Tests_Util.app mul
                                                 uu____1478
                                                in
                                             let uu____1486 =
                                               let uu____1489 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____1490 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____1489 uu____1490
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____1477 uu____1486
                                              in
                                           let_ FStar_Tests_Util.y uu____1465
                                             uu____1474
                                            in
                                         let_ FStar_Tests_Util.x uu____1461
                                           uu____1462
                                          in
                                       ((Prims.parse_int "17"), uu____1458,
                                         z)
                                        in
                                     let uu____1497 =
                                       let uu____1510 =
                                         let uu____1521 =
                                           let uu____1524 =
                                             let uu____1527 = snat znat  in
                                             snat uu____1527  in
                                           pred_nat uu____1524  in
                                         let uu____1528 = snat znat  in
                                         ((Prims.parse_int "18"), uu____1521,
                                           uu____1528)
                                          in
                                       let uu____1535 =
                                         let uu____1548 =
                                           let uu____1559 =
                                             let uu____1562 =
                                               let uu____1563 =
                                                 let uu____1564 = snat znat
                                                    in
                                                 snat uu____1564  in
                                               let uu____1565 = snat znat  in
                                               minus_nat uu____1563
                                                 uu____1565
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____1562
                                              in
                                           let uu____1566 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____1559, uu____1566)
                                            in
                                         let uu____1573 =
                                           let uu____1586 =
                                             let uu____1597 =
                                               let uu____1600 =
                                                 let uu____1601 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 let uu____1602 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 minus_nat uu____1601
                                                   uu____1602
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____1600
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____1597, znat)
                                              in
                                           let uu____1607 =
                                             let uu____1620 =
                                               let uu____1631 =
                                                 let uu____1634 =
                                                   let uu____1635 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   let uu____1636 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   minus_nat uu____1635
                                                     uu____1636
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____1634
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____1631, znat)
                                                in
                                             let uu____1641 =
                                               let uu____1654 =
                                                 let uu____1665 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____1668 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____1665, uu____1668)
                                                  in
                                               let uu____1675 =
                                                 let uu____1688 =
                                                   let uu____1699 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____1702 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____1699, uu____1702)
                                                    in
                                                 let uu____1709 =
                                                   let uu____1722 =
                                                     let uu____1733 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____1736 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____1733,
                                                       uu____1736)
                                                      in
                                                   let uu____1743 =
                                                     let uu____1756 =
                                                       let uu____1767 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____1770 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____1767,
                                                         uu____1770)
                                                        in
                                                     let uu____1777 =
                                                       let uu____1790 =
                                                         let uu____1801 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____1804 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____1801,
                                                           uu____1804)
                                                          in
                                                       let uu____1811 =
                                                         let uu____1824 =
                                                           let uu____1835 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____1838 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____1835,
                                                             uu____1838)
                                                            in
                                                         let uu____1845 =
                                                           let uu____1858 =
                                                             let uu____1869 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____1872 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____1869,
                                                               uu____1872)
                                                              in
                                                           let uu____1879 =
                                                             let uu____1892 =
                                                               let uu____1903
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____1906
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____1903,
                                                                 uu____1906)
                                                                in
                                                             let uu____1913 =
                                                               let uu____1926
                                                                 =
                                                                 let uu____1937
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____1940
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
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
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____1974
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
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
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____2008
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
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
                                                                    "idd T"
                                                                     in
                                                                    let uu____2042
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
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
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____2076
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
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
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____2110
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
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
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____2144
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
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
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____2178
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
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
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____2212
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
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
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____2246
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
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
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____2280
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
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
                                                                    "[5]"  in
                                                                    let uu____2314
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
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
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____2348
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
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
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____2382
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
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
                                                                    "idd T"
                                                                     in
                                                                    let uu____2416
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
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
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____2450
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
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
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____2484
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
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
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____2518
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
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
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____2552
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
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
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____2586
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
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
                                                                    "x1"  in
                                                                    let uu____2620
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
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
                                                                    "x2"  in
                                                                    let uu____2654
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
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
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____2688
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
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
                                                                    "true && false"
                                                                     in
                                                                    let uu____2722
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
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
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____2756
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____2753,
                                                                    uu____2756)
                                                                     in
                                                                    let uu____2763
                                                                    =
                                                                    let uu____2776
                                                                    =
                                                                    let uu____2787
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____2790
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____2787,
                                                                    uu____2790)
                                                                     in
                                                                    [uu____2776]
                                                                     in
                                                                    uu____2742
                                                                    ::
                                                                    uu____2763
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
                                                               uu____1926 ::
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
                                                     uu____1756 :: uu____1777
                                                      in
                                                   uu____1722 :: uu____1743
                                                    in
                                                 uu____1688 :: uu____1709  in
                                               uu____1654 :: uu____1675  in
                                             uu____1620 :: uu____1641  in
                                           uu____1586 :: uu____1607  in
                                         uu____1548 :: uu____1573  in
                                       uu____1510 :: uu____1535  in
                                     uu____1447 :: uu____1497  in
                                   uu____1384 :: uu____1434  in
                                 uu____1321 :: uu____1371  in
                               uu____1282 :: uu____1308  in
                             uu____1247 :: uu____1269  in
                           uu____1212 :: uu____1234  in
                         uu____1177 :: uu____1199  in
                       uu____1146 :: uu____1164  in
                     uu____1115 :: uu____1133  in
                   uu____1084 :: uu____1102  in
                 uu____1053 :: uu____1071  in
               uu____1022 :: uu____1040  in
             uu____974 :: uu____1009  in
           uu____914 :: uu____961  in
         uu____869 :: uu____901  in
       uu____824 :: uu____856  in
     uu____786 :: uu____811  in
   uu____742 :: uu____773)
  
let run_either :
  'Auu____3377 .
    Prims.int ->
      'Auu____3377 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____3377 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____3413 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____3413);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____3416 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____3416 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____3433 =
               let uu____3434 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____3434 expected  in
             FStar_Tests_Util.always i uu____3433)))
  
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
        (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let interp uu____3503 = run_interpreter i r expected  in
        let uu____3504 =
          let uu____3505 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____3505  in
        (i, uu____3504)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____3538 = run_nbe i r expected  in
        let uu____3539 =
          let uu____3540 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____3540  in
        (i, uu____3539)
  
let run_tests :
  'Auu____3549 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____3549)
      -> 'Auu____3549 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___472_3598  ->
            match uu___472_3598 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____3625  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____3627 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____3634  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____3636 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____3649  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____3673  ->
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
        let nbe1 uu____3711 = run_nbe i r expected  in
        let norm1 uu____3717 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____3725  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____3727 =
       let uu____3728 = encode (Prims.parse_int "1000")  in
       let uu____3729 =
         let uu____3732 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____3733 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____3732 uu____3733  in
       let_ FStar_Tests_Util.x uu____3728 uu____3729  in
     run_both_with_time (Prims.parse_int "14") uu____3727 z)
  
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
             let uu____3798 = res1  in
             match uu____3798 with
             | (t1,time_int) ->
                 let uu____3805 = res2  in
                 (match uu____3805 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____3812 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____3812 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____3818  ->
    (let uu____3820 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____3820);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  