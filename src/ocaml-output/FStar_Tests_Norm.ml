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
      (let uu____83361 =
         let uu____83364 = encode (n1 - (Prims.parse_int "1"))  in
         [uu____83364]  in
       FStar_Tests_Util.app succ uu____83361)
  
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
        let uu____83403 =
          let uu____83406 = let uu____83407 = b x1  in [uu____83407]  in
          FStar_Syntax_Util.abs uu____83406 e' FStar_Pervasives_Native.None
           in
        FStar_Tests_Util.app uu____83403 [e]
  
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
  let uu____83477 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____83477
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____83480 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____83480
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
    let uu____83499 =
      let uu____83506 =
        let uu____83507 =
          let uu____83524 = tm_fv snat_l  in
          let uu____83527 =
            let uu____83538 = FStar_Syntax_Syntax.as_arg s  in [uu____83538]
             in
          (uu____83524, uu____83527)  in
        FStar_Syntax_Syntax.Tm_app uu____83507  in
      FStar_Syntax_Syntax.mk uu____83506  in
    uu____83499 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____83583 .
    'Auu____83583 -> 'Auu____83583 FStar_Syntax_Syntax.withinfo_t
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
      let uu____83692 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____83692, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____83736 =
        let uu____83739 =
          let uu____83740 =
            let uu____83754 =
              let uu____83764 =
                let uu____83772 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____83772, false)  in
              [uu____83764]  in
            (snat_l, uu____83754)  in
          FStar_Syntax_Syntax.Pat_cons uu____83740  in
        pat uu____83739  in
      let uu____83802 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___763_83807 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___763_83807.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___763_83807.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____83736, FStar_Pervasives_Native.None, uu____83802)  in
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
        let uu____83848 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____83867 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____83848, FStar_Pervasives_Native.None, uu____83867)  in
      let sbranch =
        let uu____83895 =
          let uu____83898 =
            let uu____83899 =
              let uu____83913 =
                let uu____83923 =
                  let uu____83931 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____83931, false)  in
                [uu____83923]  in
              (snat_l, uu____83913)  in
            FStar_Syntax_Syntax.Pat_cons uu____83899  in
          pat uu____83898  in
        let uu____83961 =
          let uu____83964 = FStar_Tests_Util.nm minus1  in
          let uu____83967 =
            let uu____83970 =
              let uu____83971 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____83971  in
            let uu____83974 =
              let uu____83977 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____83977]  in
            uu____83970 :: uu____83974  in
          FStar_Tests_Util.app uu____83964 uu____83967  in
        (uu____83895, FStar_Pervasives_Native.None, uu____83961)  in
      let lb =
        let uu____83989 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____83993 =
          let uu____83996 =
            let uu____83997 =
              let uu____83998 = b FStar_Tests_Util.x  in
              let uu____84005 =
                let uu____84014 = b FStar_Tests_Util.y  in [uu____84014]  in
              uu____83998 :: uu____84005  in
            let uu____84039 =
              let uu____84042 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____84042 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____83997 uu____84039
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____83996
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____83989;
          FStar_Syntax_Syntax.lbdef = uu____83993;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____84049 =
        let uu____84056 =
          let uu____84057 =
            let uu____84071 =
              let uu____84074 =
                let uu____84075 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____84075 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____84074
               in
            ((true, [lb]), uu____84071)  in
          FStar_Syntax_Syntax.Tm_let uu____84057  in
        FStar_Syntax_Syntax.mk uu____84056  in
      uu____84049 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____84122 = snat out  in
         aux uu____84122 (n2 - (Prims.parse_int "1")))
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
  (let uu____84188 =
     let uu____84200 =
       let uu____84203 =
         let uu____84206 =
           let uu____84209 =
             let uu____84212 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____84212]  in
           id :: uu____84209  in
         one :: uu____84206  in
       FStar_Tests_Util.app apply uu____84203  in
     let uu____84213 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____84200, uu____84213)  in
   let uu____84222 =
     let uu____84236 =
       let uu____84248 =
         let uu____84251 =
           let uu____84254 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____84254]  in
         FStar_Tests_Util.app id uu____84251  in
       let uu____84255 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____84248, uu____84255)  in
     let uu____84264 =
       let uu____84278 =
         let uu____84290 =
           let uu____84293 =
             let uu____84296 =
               let uu____84299 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____84300 =
                 let uu____84303 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____84303]  in
               uu____84299 :: uu____84300  in
             tt :: uu____84296  in
           FStar_Tests_Util.app apply uu____84293  in
         let uu____84304 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____84290, uu____84304)  in
       let uu____84313 =
         let uu____84327 =
           let uu____84339 =
             let uu____84342 =
               let uu____84345 =
                 let uu____84348 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____84349 =
                   let uu____84352 = FStar_Tests_Util.nm FStar_Tests_Util.m
                      in
                   [uu____84352]  in
                 uu____84348 :: uu____84349  in
               ff :: uu____84345  in
             FStar_Tests_Util.app apply uu____84342  in
           let uu____84353 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____84339, uu____84353)  in
         let uu____84362 =
           let uu____84376 =
             let uu____84388 =
               let uu____84391 =
                 let uu____84394 =
                   let uu____84397 =
                     let uu____84400 =
                       let uu____84403 =
                         let uu____84406 =
                           let uu____84409 =
                             let uu____84412 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____84413 =
                               let uu____84416 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____84416]  in
                             uu____84412 :: uu____84413  in
                           ff :: uu____84409  in
                         apply :: uu____84406  in
                       apply :: uu____84403  in
                     apply :: uu____84400  in
                   apply :: uu____84397  in
                 apply :: uu____84394  in
               FStar_Tests_Util.app apply uu____84391  in
             let uu____84417 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____84388, uu____84417)  in
           let uu____84426 =
             let uu____84440 =
               let uu____84452 =
                 let uu____84455 =
                   let uu____84458 =
                     let uu____84461 =
                       let uu____84464 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n  in
                       let uu____84465 =
                         let uu____84468 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____84468]  in
                       uu____84464 :: uu____84465  in
                     ff :: uu____84461  in
                   apply :: uu____84458  in
                 FStar_Tests_Util.app twice uu____84455  in
               let uu____84469 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____84452, uu____84469)  in
             let uu____84478 =
               let uu____84492 =
                 let uu____84504 = minus one z  in
                 ((Prims.parse_int "5"), uu____84504, one)  in
               let uu____84513 =
                 let uu____84527 =
                   let uu____84539 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____84539, z)  in
                 let uu____84548 =
                   let uu____84562 =
                     let uu____84574 = minus one one  in
                     ((Prims.parse_int "7"), uu____84574, z)  in
                   let uu____84583 =
                     let uu____84597 =
                       let uu____84609 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____84609, one)  in
                     let uu____84618 =
                       let uu____84632 =
                         let uu____84644 =
                           FStar_Tests_Util.app mul [two; one]  in
                         ((Prims.parse_int "9"), uu____84644, two)  in
                       let uu____84653 =
                         let uu____84667 =
                           let uu____84679 =
                             let uu____84682 =
                               let uu____84685 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____84685; one]  in
                             FStar_Tests_Util.app mul uu____84682  in
                           ((Prims.parse_int "10"), uu____84679, two)  in
                         let uu____84692 =
                           let uu____84706 =
                             let uu____84718 =
                               let uu____84721 =
                                 encode (Prims.parse_int "10")  in
                               let uu____84723 =
                                 encode (Prims.parse_int "10")  in
                               minus uu____84721 uu____84723  in
                             ((Prims.parse_int "11"), uu____84718, z)  in
                           let uu____84733 =
                             let uu____84747 =
                               let uu____84759 =
                                 let uu____84762 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____84764 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____84762 uu____84764  in
                               ((Prims.parse_int "12"), uu____84759, z)  in
                             let uu____84774 =
                               let uu____84788 =
                                 let uu____84800 =
                                   let uu____84803 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____84805 =
                                     let uu____84808 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____84809 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____84808 uu____84809  in
                                   let_ FStar_Tests_Util.x uu____84803
                                     uu____84805
                                    in
                                 ((Prims.parse_int "13"), uu____84800, z)  in
                               let uu____84818 =
                                 let uu____84832 =
                                   let uu____84844 =
                                     let uu____84847 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____84848 =
                                       let uu____84851 =
                                         let uu____84852 =
                                           let uu____84855 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____84856 =
                                             let uu____84859 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____84859]  in
                                           uu____84855 :: uu____84856  in
                                         FStar_Tests_Util.app mul uu____84852
                                          in
                                       let uu____84860 =
                                         let uu____84863 =
                                           let uu____84864 =
                                             let uu____84867 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____84868 =
                                               let uu____84871 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____84871]  in
                                             uu____84867 :: uu____84868  in
                                           FStar_Tests_Util.app mul
                                             uu____84864
                                            in
                                         let uu____84872 =
                                           let uu____84875 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____84876 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____84875 uu____84876  in
                                         let_ FStar_Tests_Util.h uu____84863
                                           uu____84872
                                          in
                                       let_ FStar_Tests_Util.y uu____84851
                                         uu____84860
                                        in
                                     let_ FStar_Tests_Util.x uu____84847
                                       uu____84848
                                      in
                                   ((Prims.parse_int "15"), uu____84844, z)
                                    in
                                 let uu____84885 =
                                   let uu____84899 =
                                     let uu____84911 =
                                       let uu____84914 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____84917 =
                                         let uu____84918 =
                                           let uu____84921 =
                                             let uu____84924 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____84925 =
                                               let uu____84928 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____84928]  in
                                             uu____84924 :: uu____84925  in
                                           FStar_Tests_Util.app mul
                                             uu____84921
                                            in
                                         let uu____84929 =
                                           let uu____84930 =
                                             let uu____84933 =
                                               let uu____84936 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____84937 =
                                                 let uu____84940 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____84940]  in
                                               uu____84936 :: uu____84937  in
                                             FStar_Tests_Util.app mul
                                               uu____84933
                                              in
                                           let uu____84941 =
                                             let uu____84942 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____84943 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____84942 uu____84943
                                              in
                                           mk_let FStar_Tests_Util.h
                                             uu____84930 uu____84941
                                            in
                                         mk_let FStar_Tests_Util.y
                                           uu____84918 uu____84929
                                          in
                                       mk_let FStar_Tests_Util.x uu____84914
                                         uu____84917
                                        in
                                     ((Prims.parse_int "16"), uu____84911, z)
                                      in
                                   let uu____84952 =
                                     let uu____84966 =
                                       let uu____84978 =
                                         let uu____84981 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____84982 =
                                           let uu____84985 =
                                             let uu____84986 =
                                               let uu____84989 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____84990 =
                                                 let uu____84993 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____84993]  in
                                               uu____84989 :: uu____84990  in
                                             FStar_Tests_Util.app mul
                                               uu____84986
                                              in
                                           let uu____84994 =
                                             let uu____84997 =
                                               let uu____84998 =
                                                 let uu____85001 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____85002 =
                                                   let uu____85005 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____85005]  in
                                                 uu____85001 :: uu____85002
                                                  in
                                               FStar_Tests_Util.app mul
                                                 uu____84998
                                                in
                                             let uu____85006 =
                                               let uu____85009 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____85010 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____85009 uu____85010
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____84997 uu____85006
                                              in
                                           let_ FStar_Tests_Util.y
                                             uu____84985 uu____84994
                                            in
                                         let_ FStar_Tests_Util.x uu____84981
                                           uu____84982
                                          in
                                       ((Prims.parse_int "17"), uu____84978,
                                         z)
                                        in
                                     let uu____85019 =
                                       let uu____85033 =
                                         let uu____85045 =
                                           let uu____85048 =
                                             let uu____85051 = snat znat  in
                                             snat uu____85051  in
                                           pred_nat uu____85048  in
                                         let uu____85052 = snat znat  in
                                         ((Prims.parse_int "18"),
                                           uu____85045, uu____85052)
                                          in
                                       let uu____85061 =
                                         let uu____85075 =
                                           let uu____85087 =
                                             let uu____85090 =
                                               let uu____85091 =
                                                 let uu____85092 = snat znat
                                                    in
                                                 snat uu____85092  in
                                               let uu____85093 = snat znat
                                                  in
                                               minus_nat uu____85091
                                                 uu____85093
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____85090
                                              in
                                           let uu____85094 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____85087, uu____85094)
                                            in
                                         let uu____85103 =
                                           let uu____85117 =
                                             let uu____85129 =
                                               let uu____85132 =
                                                 let uu____85133 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 let uu____85135 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 minus_nat uu____85133
                                                   uu____85135
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____85132
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____85129, znat)
                                              in
                                           let uu____85143 =
                                             let uu____85157 =
                                               let uu____85169 =
                                                 let uu____85172 =
                                                   let uu____85173 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   let uu____85175 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   minus_nat uu____85173
                                                     uu____85175
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____85172
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____85169, znat)
                                                in
                                             let uu____85183 =
                                               let uu____85197 =
                                                 let uu____85209 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____85213 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____85209, uu____85213)
                                                  in
                                               let uu____85223 =
                                                 let uu____85237 =
                                                   let uu____85249 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____85253 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____85249,
                                                     uu____85253)
                                                    in
                                                 let uu____85263 =
                                                   let uu____85277 =
                                                     let uu____85289 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____85293 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____85289,
                                                       uu____85293)
                                                      in
                                                   let uu____85303 =
                                                     let uu____85317 =
                                                       let uu____85329 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____85333 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____85329,
                                                         uu____85333)
                                                        in
                                                     let uu____85343 =
                                                       let uu____85357 =
                                                         let uu____85369 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____85373 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____85369,
                                                           uu____85373)
                                                          in
                                                       let uu____85383 =
                                                         let uu____85397 =
                                                           let uu____85409 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____85413 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____85409,
                                                             uu____85413)
                                                            in
                                                         let uu____85423 =
                                                           let uu____85437 =
                                                             let uu____85449
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____85453
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____85449,
                                                               uu____85453)
                                                              in
                                                           let uu____85463 =
                                                             let uu____85477
                                                               =
                                                               let uu____85489
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____85493
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____85489,
                                                                 uu____85493)
                                                                in
                                                             let uu____85503
                                                               =
                                                               let uu____85517
                                                                 =
                                                                 let uu____85529
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____85533
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____85529,
                                                                   uu____85533)
                                                                  in
                                                               let uu____85543
                                                                 =
                                                                 let uu____85557
                                                                   =
                                                                   let uu____85569
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____85573
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____85569,
                                                                    uu____85573)
                                                                    in
                                                                 let uu____85583
                                                                   =
                                                                   let uu____85597
                                                                    =
                                                                    let uu____85609
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____85613
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____85609,
                                                                    uu____85613)
                                                                     in
                                                                   let uu____85623
                                                                    =
                                                                    let uu____85637
                                                                    =
                                                                    let uu____85649
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____85653
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____85649,
                                                                    uu____85653)
                                                                     in
                                                                    let uu____85663
                                                                    =
                                                                    let uu____85677
                                                                    =
                                                                    let uu____85689
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____85693
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____85689,
                                                                    uu____85693)
                                                                     in
                                                                    let uu____85703
                                                                    =
                                                                    let uu____85717
                                                                    =
                                                                    let uu____85729
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____85733
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____85729,
                                                                    uu____85733)
                                                                     in
                                                                    let uu____85743
                                                                    =
                                                                    let uu____85757
                                                                    =
                                                                    let uu____85769
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____85773
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____85769,
                                                                    uu____85773)
                                                                     in
                                                                    let uu____85783
                                                                    =
                                                                    let uu____85797
                                                                    =
                                                                    let uu____85809
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____85813
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____85809,
                                                                    uu____85813)
                                                                     in
                                                                    let uu____85823
                                                                    =
                                                                    let uu____85837
                                                                    =
                                                                    let uu____85849
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____85853
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____85849,
                                                                    uu____85853)
                                                                     in
                                                                    let uu____85863
                                                                    =
                                                                    let uu____85877
                                                                    =
                                                                    let uu____85889
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____85893
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____85889,
                                                                    uu____85893)
                                                                     in
                                                                    let uu____85903
                                                                    =
                                                                    let uu____85917
                                                                    =
                                                                    let uu____85929
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____85933
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____85929,
                                                                    uu____85933)
                                                                     in
                                                                    let uu____85943
                                                                    =
                                                                    let uu____85957
                                                                    =
                                                                    let uu____85969
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____85973
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____85969,
                                                                    uu____85973)
                                                                     in
                                                                    let uu____85983
                                                                    =
                                                                    let uu____85997
                                                                    =
                                                                    let uu____86009
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____86013
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____86009,
                                                                    uu____86013)
                                                                     in
                                                                    let uu____86023
                                                                    =
                                                                    let uu____86037
                                                                    =
                                                                    let uu____86049
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____86053
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____86049,
                                                                    uu____86053)
                                                                     in
                                                                    let uu____86063
                                                                    =
                                                                    let uu____86077
                                                                    =
                                                                    let uu____86089
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____86093
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____86089,
                                                                    uu____86093)
                                                                     in
                                                                    let uu____86103
                                                                    =
                                                                    let uu____86117
                                                                    =
                                                                    let uu____86129
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____86133
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____86129,
                                                                    uu____86133)
                                                                     in
                                                                    let uu____86143
                                                                    =
                                                                    let uu____86157
                                                                    =
                                                                    let uu____86169
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____86173
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____86169,
                                                                    uu____86173)
                                                                     in
                                                                    let uu____86183
                                                                    =
                                                                    let uu____86197
                                                                    =
                                                                    let uu____86209
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____86213
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____86209,
                                                                    uu____86213)
                                                                     in
                                                                    let uu____86223
                                                                    =
                                                                    let uu____86237
                                                                    =
                                                                    let uu____86249
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____86253
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____86249,
                                                                    uu____86253)
                                                                     in
                                                                    let uu____86263
                                                                    =
                                                                    let uu____86277
                                                                    =
                                                                    let uu____86289
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____86293
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____86289,
                                                                    uu____86293)
                                                                     in
                                                                    let uu____86303
                                                                    =
                                                                    let uu____86317
                                                                    =
                                                                    let uu____86329
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____86333
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____86329,
                                                                    uu____86333)
                                                                     in
                                                                    let uu____86343
                                                                    =
                                                                    let uu____86357
                                                                    =
                                                                    let uu____86369
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____86373
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____86369,
                                                                    uu____86373)
                                                                     in
                                                                    let uu____86383
                                                                    =
                                                                    let uu____86397
                                                                    =
                                                                    let uu____86409
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____86413
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____86409,
                                                                    uu____86413)
                                                                     in
                                                                    let uu____86423
                                                                    =
                                                                    let uu____86437
                                                                    =
                                                                    let uu____86449
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____86453
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____86449,
                                                                    uu____86453)
                                                                     in
                                                                    let uu____86463
                                                                    =
                                                                    let uu____86477
                                                                    =
                                                                    let uu____86489
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____86493
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____86489,
                                                                    uu____86493)
                                                                     in
                                                                    let uu____86503
                                                                    =
                                                                    let uu____86517
                                                                    =
                                                                    let uu____86529
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____86533
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____86529,
                                                                    uu____86533)
                                                                     in
                                                                    [uu____86517]
                                                                     in
                                                                    uu____86477
                                                                    ::
                                                                    uu____86503
                                                                     in
                                                                    uu____86437
                                                                    ::
                                                                    uu____86463
                                                                     in
                                                                    uu____86397
                                                                    ::
                                                                    uu____86423
                                                                     in
                                                                    uu____86357
                                                                    ::
                                                                    uu____86383
                                                                     in
                                                                    uu____86317
                                                                    ::
                                                                    uu____86343
                                                                     in
                                                                    uu____86277
                                                                    ::
                                                                    uu____86303
                                                                     in
                                                                    uu____86237
                                                                    ::
                                                                    uu____86263
                                                                     in
                                                                    uu____86197
                                                                    ::
                                                                    uu____86223
                                                                     in
                                                                    uu____86157
                                                                    ::
                                                                    uu____86183
                                                                     in
                                                                    uu____86117
                                                                    ::
                                                                    uu____86143
                                                                     in
                                                                    uu____86077
                                                                    ::
                                                                    uu____86103
                                                                     in
                                                                    uu____86037
                                                                    ::
                                                                    uu____86063
                                                                     in
                                                                    uu____85997
                                                                    ::
                                                                    uu____86023
                                                                     in
                                                                    uu____85957
                                                                    ::
                                                                    uu____85983
                                                                     in
                                                                    uu____85917
                                                                    ::
                                                                    uu____85943
                                                                     in
                                                                    uu____85877
                                                                    ::
                                                                    uu____85903
                                                                     in
                                                                    uu____85837
                                                                    ::
                                                                    uu____85863
                                                                     in
                                                                    uu____85797
                                                                    ::
                                                                    uu____85823
                                                                     in
                                                                    uu____85757
                                                                    ::
                                                                    uu____85783
                                                                     in
                                                                    uu____85717
                                                                    ::
                                                                    uu____85743
                                                                     in
                                                                    uu____85677
                                                                    ::
                                                                    uu____85703
                                                                     in
                                                                    uu____85637
                                                                    ::
                                                                    uu____85663
                                                                     in
                                                                   uu____85597
                                                                    ::
                                                                    uu____85623
                                                                    in
                                                                 uu____85557
                                                                   ::
                                                                   uu____85583
                                                                  in
                                                               uu____85517 ::
                                                                 uu____85543
                                                                in
                                                             uu____85477 ::
                                                               uu____85503
                                                              in
                                                           uu____85437 ::
                                                             uu____85463
                                                            in
                                                         uu____85397 ::
                                                           uu____85423
                                                          in
                                                       uu____85357 ::
                                                         uu____85383
                                                        in
                                                     uu____85317 ::
                                                       uu____85343
                                                      in
                                                   uu____85277 :: uu____85303
                                                    in
                                                 uu____85237 :: uu____85263
                                                  in
                                               uu____85197 :: uu____85223  in
                                             uu____85157 :: uu____85183  in
                                           uu____85117 :: uu____85143  in
                                         uu____85075 :: uu____85103  in
                                       uu____85033 :: uu____85061  in
                                     uu____84966 :: uu____85019  in
                                   uu____84899 :: uu____84952  in
                                 uu____84832 :: uu____84885  in
                               uu____84788 :: uu____84818  in
                             uu____84747 :: uu____84774  in
                           uu____84706 :: uu____84733  in
                         uu____84667 :: uu____84692  in
                       uu____84632 :: uu____84653  in
                     uu____84597 :: uu____84618  in
                   uu____84562 :: uu____84583  in
                 uu____84527 :: uu____84548  in
               uu____84492 :: uu____84513  in
             uu____84440 :: uu____84478  in
           uu____84376 :: uu____84426  in
         uu____84327 :: uu____84362  in
       uu____84278 :: uu____84313  in
     uu____84236 :: uu____84264  in
   uu____84188 :: uu____84222)
  
let run_either :
  'Auu____87181 .
    Prims.int ->
      'Auu____87181 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____87181 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____87219 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____87219);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____87224 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____87224 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____87247 =
               let uu____87249 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____87249 expected  in
             FStar_Tests_Util.always i uu____87247)))
  
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
        let interp uu____87328 = run_interpreter i r expected  in
        let uu____87329 =
          let uu____87330 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____87330  in
        (i, uu____87329)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____87368 = run_nbe i r expected  in
        let uu____87369 =
          let uu____87370 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____87370  in
        (i, uu____87369)
  
let run_tests :
  'Auu____87381 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
           'Auu____87381)
      -> 'Auu____87381 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___742_87433  ->
            match uu___742_87433 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____87464  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____87467 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____87476  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____87479 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____87495  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____87525  ->
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
        let nbe1 uu____87570 = run_nbe i r expected  in
        let norm1 uu____87576 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____87589  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____87592 =
       let uu____87593 = encode (Prims.parse_int "1000")  in
       let uu____87595 =
         let uu____87598 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____87599 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____87598 uu____87599  in
       let_ FStar_Tests_Util.x uu____87593 uu____87595  in
     run_both_with_time (Prims.parse_int "14") uu____87592 z)
  
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
             let uu____87675 = res1  in
             match uu____87675 with
             | (t1,time_int) ->
                 let uu____87685 = res2  in
                 (match uu____87685 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____87697 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____87697 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____87708  ->
    (let uu____87710 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____87710);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  