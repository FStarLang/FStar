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
      (let uu____83254 =
         let uu____83257 = encode (n1 - (Prims.parse_int "1"))  in
         [uu____83257]  in
       FStar_Tests_Util.app succ uu____83254)
  
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
        let uu____83296 =
          let uu____83299 = let uu____83300 = b x1  in [uu____83300]  in
          FStar_Syntax_Util.abs uu____83299 e' FStar_Pervasives_Native.None
           in
        FStar_Tests_Util.app uu____83296 [e]
  
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
  let uu____83370 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____83370
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____83373 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____83373
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
    let uu____83392 =
      let uu____83399 =
        let uu____83400 =
          let uu____83417 = tm_fv snat_l  in
          let uu____83420 =
            let uu____83431 = FStar_Syntax_Syntax.as_arg s  in [uu____83431]
             in
          (uu____83417, uu____83420)  in
        FStar_Syntax_Syntax.Tm_app uu____83400  in
      FStar_Syntax_Syntax.mk uu____83399  in
    uu____83392 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____83476 .
    'Auu____83476 -> 'Auu____83476 FStar_Syntax_Syntax.withinfo_t
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
      let uu____83585 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____83585, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____83629 =
        let uu____83632 =
          let uu____83633 =
            let uu____83647 =
              let uu____83657 =
                let uu____83665 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____83665, false)  in
              [uu____83657]  in
            (snat_l, uu____83647)  in
          FStar_Syntax_Syntax.Pat_cons uu____83633  in
        pat uu____83632  in
      let uu____83695 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___763_83700 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___763_83700.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___763_83700.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____83629, FStar_Pervasives_Native.None, uu____83695)  in
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
        let uu____83741 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____83760 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____83741, FStar_Pervasives_Native.None, uu____83760)  in
      let sbranch =
        let uu____83788 =
          let uu____83791 =
            let uu____83792 =
              let uu____83806 =
                let uu____83816 =
                  let uu____83824 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____83824, false)  in
                [uu____83816]  in
              (snat_l, uu____83806)  in
            FStar_Syntax_Syntax.Pat_cons uu____83792  in
          pat uu____83791  in
        let uu____83854 =
          let uu____83857 = FStar_Tests_Util.nm minus1  in
          let uu____83860 =
            let uu____83863 =
              let uu____83864 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____83864  in
            let uu____83867 =
              let uu____83870 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____83870]  in
            uu____83863 :: uu____83867  in
          FStar_Tests_Util.app uu____83857 uu____83860  in
        (uu____83788, FStar_Pervasives_Native.None, uu____83854)  in
      let lb =
        let uu____83882 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____83886 =
          let uu____83889 =
            let uu____83890 =
              let uu____83891 = b FStar_Tests_Util.x  in
              let uu____83898 =
                let uu____83907 = b FStar_Tests_Util.y  in [uu____83907]  in
              uu____83891 :: uu____83898  in
            let uu____83932 =
              let uu____83935 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____83935 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____83890 uu____83932
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____83889
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____83882;
          FStar_Syntax_Syntax.lbdef = uu____83886;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____83942 =
        let uu____83949 =
          let uu____83950 =
            let uu____83964 =
              let uu____83967 =
                let uu____83968 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____83968 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____83967
               in
            ((true, [lb]), uu____83964)  in
          FStar_Syntax_Syntax.Tm_let uu____83950  in
        FStar_Syntax_Syntax.mk uu____83949  in
      uu____83942 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____84015 = snat out  in
         aux uu____84015 (n2 - (Prims.parse_int "1")))
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
  (let uu____84081 =
     let uu____84093 =
       let uu____84096 =
         let uu____84099 =
           let uu____84102 =
             let uu____84105 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____84105]  in
           id :: uu____84102  in
         one :: uu____84099  in
       FStar_Tests_Util.app apply uu____84096  in
     let uu____84106 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____84093, uu____84106)  in
   let uu____84115 =
     let uu____84129 =
       let uu____84141 =
         let uu____84144 =
           let uu____84147 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____84147]  in
         FStar_Tests_Util.app id uu____84144  in
       let uu____84148 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____84141, uu____84148)  in
     let uu____84157 =
       let uu____84171 =
         let uu____84183 =
           let uu____84186 =
             let uu____84189 =
               let uu____84192 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____84193 =
                 let uu____84196 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____84196]  in
               uu____84192 :: uu____84193  in
             tt :: uu____84189  in
           FStar_Tests_Util.app apply uu____84186  in
         let uu____84197 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____84183, uu____84197)  in
       let uu____84206 =
         let uu____84220 =
           let uu____84232 =
             let uu____84235 =
               let uu____84238 =
                 let uu____84241 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____84242 =
                   let uu____84245 = FStar_Tests_Util.nm FStar_Tests_Util.m
                      in
                   [uu____84245]  in
                 uu____84241 :: uu____84242  in
               ff :: uu____84238  in
             FStar_Tests_Util.app apply uu____84235  in
           let uu____84246 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____84232, uu____84246)  in
         let uu____84255 =
           let uu____84269 =
             let uu____84281 =
               let uu____84284 =
                 let uu____84287 =
                   let uu____84290 =
                     let uu____84293 =
                       let uu____84296 =
                         let uu____84299 =
                           let uu____84302 =
                             let uu____84305 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____84306 =
                               let uu____84309 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____84309]  in
                             uu____84305 :: uu____84306  in
                           ff :: uu____84302  in
                         apply :: uu____84299  in
                       apply :: uu____84296  in
                     apply :: uu____84293  in
                   apply :: uu____84290  in
                 apply :: uu____84287  in
               FStar_Tests_Util.app apply uu____84284  in
             let uu____84310 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____84281, uu____84310)  in
           let uu____84319 =
             let uu____84333 =
               let uu____84345 =
                 let uu____84348 =
                   let uu____84351 =
                     let uu____84354 =
                       let uu____84357 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n  in
                       let uu____84358 =
                         let uu____84361 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____84361]  in
                       uu____84357 :: uu____84358  in
                     ff :: uu____84354  in
                   apply :: uu____84351  in
                 FStar_Tests_Util.app twice uu____84348  in
               let uu____84362 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____84345, uu____84362)  in
             let uu____84371 =
               let uu____84385 =
                 let uu____84397 = minus one z  in
                 ((Prims.parse_int "5"), uu____84397, one)  in
               let uu____84406 =
                 let uu____84420 =
                   let uu____84432 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____84432, z)  in
                 let uu____84441 =
                   let uu____84455 =
                     let uu____84467 = minus one one  in
                     ((Prims.parse_int "7"), uu____84467, z)  in
                   let uu____84476 =
                     let uu____84490 =
                       let uu____84502 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____84502, one)  in
                     let uu____84511 =
                       let uu____84525 =
                         let uu____84537 =
                           FStar_Tests_Util.app mul [two; one]  in
                         ((Prims.parse_int "9"), uu____84537, two)  in
                       let uu____84546 =
                         let uu____84560 =
                           let uu____84572 =
                             let uu____84575 =
                               let uu____84578 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____84578; one]  in
                             FStar_Tests_Util.app mul uu____84575  in
                           ((Prims.parse_int "10"), uu____84572, two)  in
                         let uu____84585 =
                           let uu____84599 =
                             let uu____84611 =
                               let uu____84614 =
                                 encode (Prims.parse_int "10")  in
                               let uu____84616 =
                                 encode (Prims.parse_int "10")  in
                               minus uu____84614 uu____84616  in
                             ((Prims.parse_int "11"), uu____84611, z)  in
                           let uu____84626 =
                             let uu____84640 =
                               let uu____84652 =
                                 let uu____84655 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____84657 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____84655 uu____84657  in
                               ((Prims.parse_int "12"), uu____84652, z)  in
                             let uu____84667 =
                               let uu____84681 =
                                 let uu____84693 =
                                   let uu____84696 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____84698 =
                                     let uu____84701 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____84702 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____84701 uu____84702  in
                                   let_ FStar_Tests_Util.x uu____84696
                                     uu____84698
                                    in
                                 ((Prims.parse_int "13"), uu____84693, z)  in
                               let uu____84711 =
                                 let uu____84725 =
                                   let uu____84737 =
                                     let uu____84740 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____84741 =
                                       let uu____84744 =
                                         let uu____84745 =
                                           let uu____84748 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____84749 =
                                             let uu____84752 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____84752]  in
                                           uu____84748 :: uu____84749  in
                                         FStar_Tests_Util.app mul uu____84745
                                          in
                                       let uu____84753 =
                                         let uu____84756 =
                                           let uu____84757 =
                                             let uu____84760 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____84761 =
                                               let uu____84764 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____84764]  in
                                             uu____84760 :: uu____84761  in
                                           FStar_Tests_Util.app mul
                                             uu____84757
                                            in
                                         let uu____84765 =
                                           let uu____84768 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____84769 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____84768 uu____84769  in
                                         let_ FStar_Tests_Util.h uu____84756
                                           uu____84765
                                          in
                                       let_ FStar_Tests_Util.y uu____84744
                                         uu____84753
                                        in
                                     let_ FStar_Tests_Util.x uu____84740
                                       uu____84741
                                      in
                                   ((Prims.parse_int "15"), uu____84737, z)
                                    in
                                 let uu____84778 =
                                   let uu____84792 =
                                     let uu____84804 =
                                       let uu____84807 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____84810 =
                                         let uu____84811 =
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
                                           FStar_Tests_Util.app mul
                                             uu____84814
                                            in
                                         let uu____84822 =
                                           let uu____84823 =
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
                                             let uu____84835 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____84836 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____84835 uu____84836
                                              in
                                           mk_let FStar_Tests_Util.h
                                             uu____84823 uu____84834
                                            in
                                         mk_let FStar_Tests_Util.y
                                           uu____84811 uu____84822
                                          in
                                       mk_let FStar_Tests_Util.x uu____84807
                                         uu____84810
                                        in
                                     ((Prims.parse_int "16"), uu____84804, z)
                                      in
                                   let uu____84845 =
                                     let uu____84859 =
                                       let uu____84871 =
                                         let uu____84874 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____84875 =
                                           let uu____84878 =
                                             let uu____84879 =
                                               let uu____84882 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____84883 =
                                                 let uu____84886 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____84886]  in
                                               uu____84882 :: uu____84883  in
                                             FStar_Tests_Util.app mul
                                               uu____84879
                                              in
                                           let uu____84887 =
                                             let uu____84890 =
                                               let uu____84891 =
                                                 let uu____84894 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____84895 =
                                                   let uu____84898 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____84898]  in
                                                 uu____84894 :: uu____84895
                                                  in
                                               FStar_Tests_Util.app mul
                                                 uu____84891
                                                in
                                             let uu____84899 =
                                               let uu____84902 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____84903 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____84902 uu____84903
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____84890 uu____84899
                                              in
                                           let_ FStar_Tests_Util.y
                                             uu____84878 uu____84887
                                            in
                                         let_ FStar_Tests_Util.x uu____84874
                                           uu____84875
                                          in
                                       ((Prims.parse_int "17"), uu____84871,
                                         z)
                                        in
                                     let uu____84912 =
                                       let uu____84926 =
                                         let uu____84938 =
                                           let uu____84941 =
                                             let uu____84944 = snat znat  in
                                             snat uu____84944  in
                                           pred_nat uu____84941  in
                                         let uu____84945 = snat znat  in
                                         ((Prims.parse_int "18"),
                                           uu____84938, uu____84945)
                                          in
                                       let uu____84954 =
                                         let uu____84968 =
                                           let uu____84980 =
                                             let uu____84983 =
                                               let uu____84984 =
                                                 let uu____84985 = snat znat
                                                    in
                                                 snat uu____84985  in
                                               let uu____84986 = snat znat
                                                  in
                                               minus_nat uu____84984
                                                 uu____84986
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____84983
                                              in
                                           let uu____84987 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____84980, uu____84987)
                                            in
                                         let uu____84996 =
                                           let uu____85010 =
                                             let uu____85022 =
                                               let uu____85025 =
                                                 let uu____85026 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 let uu____85028 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 minus_nat uu____85026
                                                   uu____85028
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____85025
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____85022, znat)
                                              in
                                           let uu____85036 =
                                             let uu____85050 =
                                               let uu____85062 =
                                                 let uu____85065 =
                                                   let uu____85066 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   let uu____85068 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   minus_nat uu____85066
                                                     uu____85068
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____85065
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____85062, znat)
                                                in
                                             let uu____85076 =
                                               let uu____85090 =
                                                 let uu____85102 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____85106 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____85102, uu____85106)
                                                  in
                                               let uu____85116 =
                                                 let uu____85130 =
                                                   let uu____85142 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____85146 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____85142,
                                                     uu____85146)
                                                    in
                                                 let uu____85156 =
                                                   let uu____85170 =
                                                     let uu____85182 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____85186 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____85182,
                                                       uu____85186)
                                                      in
                                                   let uu____85196 =
                                                     let uu____85210 =
                                                       let uu____85222 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____85226 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____85222,
                                                         uu____85226)
                                                        in
                                                     let uu____85236 =
                                                       let uu____85250 =
                                                         let uu____85262 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____85266 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____85262,
                                                           uu____85266)
                                                          in
                                                       let uu____85276 =
                                                         let uu____85290 =
                                                           let uu____85302 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____85306 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____85302,
                                                             uu____85306)
                                                            in
                                                         let uu____85316 =
                                                           let uu____85330 =
                                                             let uu____85342
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____85346
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____85342,
                                                               uu____85346)
                                                              in
                                                           let uu____85356 =
                                                             let uu____85370
                                                               =
                                                               let uu____85382
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____85386
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____85382,
                                                                 uu____85386)
                                                                in
                                                             let uu____85396
                                                               =
                                                               let uu____85410
                                                                 =
                                                                 let uu____85422
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____85426
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____85422,
                                                                   uu____85426)
                                                                  in
                                                               let uu____85436
                                                                 =
                                                                 let uu____85450
                                                                   =
                                                                   let uu____85462
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____85466
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____85462,
                                                                    uu____85466)
                                                                    in
                                                                 let uu____85476
                                                                   =
                                                                   let uu____85490
                                                                    =
                                                                    let uu____85502
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____85506
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____85502,
                                                                    uu____85506)
                                                                     in
                                                                   let uu____85516
                                                                    =
                                                                    let uu____85530
                                                                    =
                                                                    let uu____85542
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____85546
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____85542,
                                                                    uu____85546)
                                                                     in
                                                                    let uu____85556
                                                                    =
                                                                    let uu____85570
                                                                    =
                                                                    let uu____85582
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____85586
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____85582,
                                                                    uu____85586)
                                                                     in
                                                                    let uu____85596
                                                                    =
                                                                    let uu____85610
                                                                    =
                                                                    let uu____85622
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____85626
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____85622,
                                                                    uu____85626)
                                                                     in
                                                                    let uu____85636
                                                                    =
                                                                    let uu____85650
                                                                    =
                                                                    let uu____85662
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____85666
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____85662,
                                                                    uu____85666)
                                                                     in
                                                                    let uu____85676
                                                                    =
                                                                    let uu____85690
                                                                    =
                                                                    let uu____85702
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____85706
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____85702,
                                                                    uu____85706)
                                                                     in
                                                                    let uu____85716
                                                                    =
                                                                    let uu____85730
                                                                    =
                                                                    let uu____85742
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____85746
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____85742,
                                                                    uu____85746)
                                                                     in
                                                                    let uu____85756
                                                                    =
                                                                    let uu____85770
                                                                    =
                                                                    let uu____85782
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____85786
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____85782,
                                                                    uu____85786)
                                                                     in
                                                                    let uu____85796
                                                                    =
                                                                    let uu____85810
                                                                    =
                                                                    let uu____85822
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____85826
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____85822,
                                                                    uu____85826)
                                                                     in
                                                                    let uu____85836
                                                                    =
                                                                    let uu____85850
                                                                    =
                                                                    let uu____85862
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____85866
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____85862,
                                                                    uu____85866)
                                                                     in
                                                                    let uu____85876
                                                                    =
                                                                    let uu____85890
                                                                    =
                                                                    let uu____85902
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____85906
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____85902,
                                                                    uu____85906)
                                                                     in
                                                                    let uu____85916
                                                                    =
                                                                    let uu____85930
                                                                    =
                                                                    let uu____85942
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____85946
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____85942,
                                                                    uu____85946)
                                                                     in
                                                                    let uu____85956
                                                                    =
                                                                    let uu____85970
                                                                    =
                                                                    let uu____85982
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____85986
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____85982,
                                                                    uu____85986)
                                                                     in
                                                                    let uu____85996
                                                                    =
                                                                    let uu____86010
                                                                    =
                                                                    let uu____86022
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____86026
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____86022,
                                                                    uu____86026)
                                                                     in
                                                                    let uu____86036
                                                                    =
                                                                    let uu____86050
                                                                    =
                                                                    let uu____86062
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____86066
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____86062,
                                                                    uu____86066)
                                                                     in
                                                                    let uu____86076
                                                                    =
                                                                    let uu____86090
                                                                    =
                                                                    let uu____86102
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____86106
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____86102,
                                                                    uu____86106)
                                                                     in
                                                                    let uu____86116
                                                                    =
                                                                    let uu____86130
                                                                    =
                                                                    let uu____86142
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____86146
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____86142,
                                                                    uu____86146)
                                                                     in
                                                                    let uu____86156
                                                                    =
                                                                    let uu____86170
                                                                    =
                                                                    let uu____86182
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____86186
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____86182,
                                                                    uu____86186)
                                                                     in
                                                                    let uu____86196
                                                                    =
                                                                    let uu____86210
                                                                    =
                                                                    let uu____86222
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____86226
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____86222,
                                                                    uu____86226)
                                                                     in
                                                                    let uu____86236
                                                                    =
                                                                    let uu____86250
                                                                    =
                                                                    let uu____86262
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____86266
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____86262,
                                                                    uu____86266)
                                                                     in
                                                                    let uu____86276
                                                                    =
                                                                    let uu____86290
                                                                    =
                                                                    let uu____86302
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____86306
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____86302,
                                                                    uu____86306)
                                                                     in
                                                                    let uu____86316
                                                                    =
                                                                    let uu____86330
                                                                    =
                                                                    let uu____86342
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____86346
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____86342,
                                                                    uu____86346)
                                                                     in
                                                                    let uu____86356
                                                                    =
                                                                    let uu____86370
                                                                    =
                                                                    let uu____86382
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____86386
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____86382,
                                                                    uu____86386)
                                                                     in
                                                                    let uu____86396
                                                                    =
                                                                    let uu____86410
                                                                    =
                                                                    let uu____86422
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____86426
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____86422,
                                                                    uu____86426)
                                                                     in
                                                                    [uu____86410]
                                                                     in
                                                                    uu____86370
                                                                    ::
                                                                    uu____86396
                                                                     in
                                                                    uu____86330
                                                                    ::
                                                                    uu____86356
                                                                     in
                                                                    uu____86290
                                                                    ::
                                                                    uu____86316
                                                                     in
                                                                    uu____86250
                                                                    ::
                                                                    uu____86276
                                                                     in
                                                                    uu____86210
                                                                    ::
                                                                    uu____86236
                                                                     in
                                                                    uu____86170
                                                                    ::
                                                                    uu____86196
                                                                     in
                                                                    uu____86130
                                                                    ::
                                                                    uu____86156
                                                                     in
                                                                    uu____86090
                                                                    ::
                                                                    uu____86116
                                                                     in
                                                                    uu____86050
                                                                    ::
                                                                    uu____86076
                                                                     in
                                                                    uu____86010
                                                                    ::
                                                                    uu____86036
                                                                     in
                                                                    uu____85970
                                                                    ::
                                                                    uu____85996
                                                                     in
                                                                    uu____85930
                                                                    ::
                                                                    uu____85956
                                                                     in
                                                                    uu____85890
                                                                    ::
                                                                    uu____85916
                                                                     in
                                                                    uu____85850
                                                                    ::
                                                                    uu____85876
                                                                     in
                                                                    uu____85810
                                                                    ::
                                                                    uu____85836
                                                                     in
                                                                    uu____85770
                                                                    ::
                                                                    uu____85796
                                                                     in
                                                                    uu____85730
                                                                    ::
                                                                    uu____85756
                                                                     in
                                                                    uu____85690
                                                                    ::
                                                                    uu____85716
                                                                     in
                                                                    uu____85650
                                                                    ::
                                                                    uu____85676
                                                                     in
                                                                    uu____85610
                                                                    ::
                                                                    uu____85636
                                                                     in
                                                                    uu____85570
                                                                    ::
                                                                    uu____85596
                                                                     in
                                                                    uu____85530
                                                                    ::
                                                                    uu____85556
                                                                     in
                                                                   uu____85490
                                                                    ::
                                                                    uu____85516
                                                                    in
                                                                 uu____85450
                                                                   ::
                                                                   uu____85476
                                                                  in
                                                               uu____85410 ::
                                                                 uu____85436
                                                                in
                                                             uu____85370 ::
                                                               uu____85396
                                                              in
                                                           uu____85330 ::
                                                             uu____85356
                                                            in
                                                         uu____85290 ::
                                                           uu____85316
                                                          in
                                                       uu____85250 ::
                                                         uu____85276
                                                        in
                                                     uu____85210 ::
                                                       uu____85236
                                                      in
                                                   uu____85170 :: uu____85196
                                                    in
                                                 uu____85130 :: uu____85156
                                                  in
                                               uu____85090 :: uu____85116  in
                                             uu____85050 :: uu____85076  in
                                           uu____85010 :: uu____85036  in
                                         uu____84968 :: uu____84996  in
                                       uu____84926 :: uu____84954  in
                                     uu____84859 :: uu____84912  in
                                   uu____84792 :: uu____84845  in
                                 uu____84725 :: uu____84778  in
                               uu____84681 :: uu____84711  in
                             uu____84640 :: uu____84667  in
                           uu____84599 :: uu____84626  in
                         uu____84560 :: uu____84585  in
                       uu____84525 :: uu____84546  in
                     uu____84490 :: uu____84511  in
                   uu____84455 :: uu____84476  in
                 uu____84420 :: uu____84441  in
               uu____84385 :: uu____84406  in
             uu____84333 :: uu____84371  in
           uu____84269 :: uu____84319  in
         uu____84220 :: uu____84255  in
       uu____84171 :: uu____84206  in
     uu____84129 :: uu____84157  in
   uu____84081 :: uu____84115)
  
let run_either :
  'Auu____87074 .
    Prims.int ->
      'Auu____87074 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____87074 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____87112 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____87112);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____87117 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____87117 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____87140 =
               let uu____87142 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____87142 expected  in
             FStar_Tests_Util.always i uu____87140)))
  
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
        let interp uu____87221 = run_interpreter i r expected  in
        let uu____87222 =
          let uu____87223 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____87223  in
        (i, uu____87222)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____87261 = run_nbe i r expected  in
        let uu____87262 =
          let uu____87263 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____87263  in
        (i, uu____87262)
  
let run_tests :
  'Auu____87274 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
           'Auu____87274)
      -> 'Auu____87274 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___742_87326  ->
            match uu___742_87326 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____87357  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____87360 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____87369  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____87372 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____87388  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____87418  ->
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
        let nbe1 uu____87463 = run_nbe i r expected  in
        let norm1 uu____87469 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____87482  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____87485 =
       let uu____87486 = encode (Prims.parse_int "1000")  in
       let uu____87488 =
         let uu____87491 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____87492 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____87491 uu____87492  in
       let_ FStar_Tests_Util.x uu____87486 uu____87488  in
     run_both_with_time (Prims.parse_int "14") uu____87485 z)
  
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
             let uu____87568 = res1  in
             match uu____87568 with
             | (t1,time_int) ->
                 let uu____87578 = res2  in
                 (match uu____87578 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____87590 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____87590 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____87601  ->
    (let uu____87603 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____87603);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  