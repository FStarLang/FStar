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
      (let uu____83264 =
         let uu____83267 = encode (n1 - (Prims.parse_int "1"))  in
         [uu____83267]  in
       FStar_Tests_Util.app succ uu____83264)
  
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
        let uu____83306 =
          let uu____83309 = let uu____83310 = b x1  in [uu____83310]  in
          FStar_Syntax_Util.abs uu____83309 e' FStar_Pervasives_Native.None
           in
        FStar_Tests_Util.app uu____83306 [e]
  
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
  let uu____83380 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____83380
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____83383 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____83383
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
    let uu____83402 =
      let uu____83409 =
        let uu____83410 =
          let uu____83427 = tm_fv snat_l  in
          let uu____83430 =
            let uu____83441 = FStar_Syntax_Syntax.as_arg s  in [uu____83441]
             in
          (uu____83427, uu____83430)  in
        FStar_Syntax_Syntax.Tm_app uu____83410  in
      FStar_Syntax_Syntax.mk uu____83409  in
    uu____83402 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____83486 .
    'Auu____83486 -> 'Auu____83486 FStar_Syntax_Syntax.withinfo_t
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
      let uu____83595 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____83595, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____83639 =
        let uu____83642 =
          let uu____83643 =
            let uu____83657 =
              let uu____83667 =
                let uu____83675 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____83675, false)  in
              [uu____83667]  in
            (snat_l, uu____83657)  in
          FStar_Syntax_Syntax.Pat_cons uu____83643  in
        pat uu____83642  in
      let uu____83705 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___763_83710 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___763_83710.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___763_83710.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____83639, FStar_Pervasives_Native.None, uu____83705)  in
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
        let uu____83751 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____83770 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____83751, FStar_Pervasives_Native.None, uu____83770)  in
      let sbranch =
        let uu____83798 =
          let uu____83801 =
            let uu____83802 =
              let uu____83816 =
                let uu____83826 =
                  let uu____83834 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____83834, false)  in
                [uu____83826]  in
              (snat_l, uu____83816)  in
            FStar_Syntax_Syntax.Pat_cons uu____83802  in
          pat uu____83801  in
        let uu____83864 =
          let uu____83867 = FStar_Tests_Util.nm minus1  in
          let uu____83870 =
            let uu____83873 =
              let uu____83874 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____83874  in
            let uu____83877 =
              let uu____83880 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____83880]  in
            uu____83873 :: uu____83877  in
          FStar_Tests_Util.app uu____83867 uu____83870  in
        (uu____83798, FStar_Pervasives_Native.None, uu____83864)  in
      let lb =
        let uu____83892 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____83896 =
          let uu____83899 =
            let uu____83900 =
              let uu____83901 = b FStar_Tests_Util.x  in
              let uu____83908 =
                let uu____83917 = b FStar_Tests_Util.y  in [uu____83917]  in
              uu____83901 :: uu____83908  in
            let uu____83942 =
              let uu____83945 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____83945 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____83900 uu____83942
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____83899
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____83892;
          FStar_Syntax_Syntax.lbdef = uu____83896;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____83952 =
        let uu____83959 =
          let uu____83960 =
            let uu____83974 =
              let uu____83977 =
                let uu____83978 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____83978 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____83977
               in
            ((true, [lb]), uu____83974)  in
          FStar_Syntax_Syntax.Tm_let uu____83960  in
        FStar_Syntax_Syntax.mk uu____83959  in
      uu____83952 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____84025 = snat out  in
         aux uu____84025 (n2 - (Prims.parse_int "1")))
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
  (let uu____84091 =
     let uu____84103 =
       let uu____84106 =
         let uu____84109 =
           let uu____84112 =
             let uu____84115 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____84115]  in
           id :: uu____84112  in
         one :: uu____84109  in
       FStar_Tests_Util.app apply uu____84106  in
     let uu____84116 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____84103, uu____84116)  in
   let uu____84125 =
     let uu____84139 =
       let uu____84151 =
         let uu____84154 =
           let uu____84157 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____84157]  in
         FStar_Tests_Util.app id uu____84154  in
       let uu____84158 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____84151, uu____84158)  in
     let uu____84167 =
       let uu____84181 =
         let uu____84193 =
           let uu____84196 =
             let uu____84199 =
               let uu____84202 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____84203 =
                 let uu____84206 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____84206]  in
               uu____84202 :: uu____84203  in
             tt :: uu____84199  in
           FStar_Tests_Util.app apply uu____84196  in
         let uu____84207 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____84193, uu____84207)  in
       let uu____84216 =
         let uu____84230 =
           let uu____84242 =
             let uu____84245 =
               let uu____84248 =
                 let uu____84251 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____84252 =
                   let uu____84255 = FStar_Tests_Util.nm FStar_Tests_Util.m
                      in
                   [uu____84255]  in
                 uu____84251 :: uu____84252  in
               ff :: uu____84248  in
             FStar_Tests_Util.app apply uu____84245  in
           let uu____84256 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____84242, uu____84256)  in
         let uu____84265 =
           let uu____84279 =
             let uu____84291 =
               let uu____84294 =
                 let uu____84297 =
                   let uu____84300 =
                     let uu____84303 =
                       let uu____84306 =
                         let uu____84309 =
                           let uu____84312 =
                             let uu____84315 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____84316 =
                               let uu____84319 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____84319]  in
                             uu____84315 :: uu____84316  in
                           ff :: uu____84312  in
                         apply :: uu____84309  in
                       apply :: uu____84306  in
                     apply :: uu____84303  in
                   apply :: uu____84300  in
                 apply :: uu____84297  in
               FStar_Tests_Util.app apply uu____84294  in
             let uu____84320 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____84291, uu____84320)  in
           let uu____84329 =
             let uu____84343 =
               let uu____84355 =
                 let uu____84358 =
                   let uu____84361 =
                     let uu____84364 =
                       let uu____84367 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n  in
                       let uu____84368 =
                         let uu____84371 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____84371]  in
                       uu____84367 :: uu____84368  in
                     ff :: uu____84364  in
                   apply :: uu____84361  in
                 FStar_Tests_Util.app twice uu____84358  in
               let uu____84372 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____84355, uu____84372)  in
             let uu____84381 =
               let uu____84395 =
                 let uu____84407 = minus one z  in
                 ((Prims.parse_int "5"), uu____84407, one)  in
               let uu____84416 =
                 let uu____84430 =
                   let uu____84442 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____84442, z)  in
                 let uu____84451 =
                   let uu____84465 =
                     let uu____84477 = minus one one  in
                     ((Prims.parse_int "7"), uu____84477, z)  in
                   let uu____84486 =
                     let uu____84500 =
                       let uu____84512 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____84512, one)  in
                     let uu____84521 =
                       let uu____84535 =
                         let uu____84547 =
                           FStar_Tests_Util.app mul [two; one]  in
                         ((Prims.parse_int "9"), uu____84547, two)  in
                       let uu____84556 =
                         let uu____84570 =
                           let uu____84582 =
                             let uu____84585 =
                               let uu____84588 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____84588; one]  in
                             FStar_Tests_Util.app mul uu____84585  in
                           ((Prims.parse_int "10"), uu____84582, two)  in
                         let uu____84595 =
                           let uu____84609 =
                             let uu____84621 =
                               let uu____84624 =
                                 encode (Prims.parse_int "10")  in
                               let uu____84626 =
                                 encode (Prims.parse_int "10")  in
                               minus uu____84624 uu____84626  in
                             ((Prims.parse_int "11"), uu____84621, z)  in
                           let uu____84636 =
                             let uu____84650 =
                               let uu____84662 =
                                 let uu____84665 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____84667 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____84665 uu____84667  in
                               ((Prims.parse_int "12"), uu____84662, z)  in
                             let uu____84677 =
                               let uu____84691 =
                                 let uu____84703 =
                                   let uu____84706 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____84708 =
                                     let uu____84711 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____84712 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____84711 uu____84712  in
                                   let_ FStar_Tests_Util.x uu____84706
                                     uu____84708
                                    in
                                 ((Prims.parse_int "13"), uu____84703, z)  in
                               let uu____84721 =
                                 let uu____84735 =
                                   let uu____84747 =
                                     let uu____84750 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____84751 =
                                       let uu____84754 =
                                         let uu____84755 =
                                           let uu____84758 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____84759 =
                                             let uu____84762 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____84762]  in
                                           uu____84758 :: uu____84759  in
                                         FStar_Tests_Util.app mul uu____84755
                                          in
                                       let uu____84763 =
                                         let uu____84766 =
                                           let uu____84767 =
                                             let uu____84770 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____84771 =
                                               let uu____84774 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____84774]  in
                                             uu____84770 :: uu____84771  in
                                           FStar_Tests_Util.app mul
                                             uu____84767
                                            in
                                         let uu____84775 =
                                           let uu____84778 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____84779 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____84778 uu____84779  in
                                         let_ FStar_Tests_Util.h uu____84766
                                           uu____84775
                                          in
                                       let_ FStar_Tests_Util.y uu____84754
                                         uu____84763
                                        in
                                     let_ FStar_Tests_Util.x uu____84750
                                       uu____84751
                                      in
                                   ((Prims.parse_int "15"), uu____84747, z)
                                    in
                                 let uu____84788 =
                                   let uu____84802 =
                                     let uu____84814 =
                                       let uu____84817 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____84820 =
                                         let uu____84821 =
                                           let uu____84824 =
                                             let uu____84827 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____84828 =
                                               let uu____84831 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____84831]  in
                                             uu____84827 :: uu____84828  in
                                           FStar_Tests_Util.app mul
                                             uu____84824
                                            in
                                         let uu____84832 =
                                           let uu____84833 =
                                             let uu____84836 =
                                               let uu____84839 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____84840 =
                                                 let uu____84843 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____84843]  in
                                               uu____84839 :: uu____84840  in
                                             FStar_Tests_Util.app mul
                                               uu____84836
                                              in
                                           let uu____84844 =
                                             let uu____84845 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____84846 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____84845 uu____84846
                                              in
                                           mk_let FStar_Tests_Util.h
                                             uu____84833 uu____84844
                                            in
                                         mk_let FStar_Tests_Util.y
                                           uu____84821 uu____84832
                                          in
                                       mk_let FStar_Tests_Util.x uu____84817
                                         uu____84820
                                        in
                                     ((Prims.parse_int "16"), uu____84814, z)
                                      in
                                   let uu____84855 =
                                     let uu____84869 =
                                       let uu____84881 =
                                         let uu____84884 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____84885 =
                                           let uu____84888 =
                                             let uu____84889 =
                                               let uu____84892 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____84893 =
                                                 let uu____84896 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____84896]  in
                                               uu____84892 :: uu____84893  in
                                             FStar_Tests_Util.app mul
                                               uu____84889
                                              in
                                           let uu____84897 =
                                             let uu____84900 =
                                               let uu____84901 =
                                                 let uu____84904 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____84905 =
                                                   let uu____84908 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____84908]  in
                                                 uu____84904 :: uu____84905
                                                  in
                                               FStar_Tests_Util.app mul
                                                 uu____84901
                                                in
                                             let uu____84909 =
                                               let uu____84912 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____84913 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____84912 uu____84913
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____84900 uu____84909
                                              in
                                           let_ FStar_Tests_Util.y
                                             uu____84888 uu____84897
                                            in
                                         let_ FStar_Tests_Util.x uu____84884
                                           uu____84885
                                          in
                                       ((Prims.parse_int "17"), uu____84881,
                                         z)
                                        in
                                     let uu____84922 =
                                       let uu____84936 =
                                         let uu____84948 =
                                           let uu____84951 =
                                             let uu____84954 = snat znat  in
                                             snat uu____84954  in
                                           pred_nat uu____84951  in
                                         let uu____84955 = snat znat  in
                                         ((Prims.parse_int "18"),
                                           uu____84948, uu____84955)
                                          in
                                       let uu____84964 =
                                         let uu____84978 =
                                           let uu____84990 =
                                             let uu____84993 =
                                               let uu____84994 =
                                                 let uu____84995 = snat znat
                                                    in
                                                 snat uu____84995  in
                                               let uu____84996 = snat znat
                                                  in
                                               minus_nat uu____84994
                                                 uu____84996
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____84993
                                              in
                                           let uu____84997 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____84990, uu____84997)
                                            in
                                         let uu____85006 =
                                           let uu____85020 =
                                             let uu____85032 =
                                               let uu____85035 =
                                                 let uu____85036 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 let uu____85038 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 minus_nat uu____85036
                                                   uu____85038
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____85035
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____85032, znat)
                                              in
                                           let uu____85046 =
                                             let uu____85060 =
                                               let uu____85072 =
                                                 let uu____85075 =
                                                   let uu____85076 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   let uu____85078 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   minus_nat uu____85076
                                                     uu____85078
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____85075
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____85072, znat)
                                                in
                                             let uu____85086 =
                                               let uu____85100 =
                                                 let uu____85112 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____85116 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____85112, uu____85116)
                                                  in
                                               let uu____85126 =
                                                 let uu____85140 =
                                                   let uu____85152 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____85156 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____85152,
                                                     uu____85156)
                                                    in
                                                 let uu____85166 =
                                                   let uu____85180 =
                                                     let uu____85192 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____85196 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____85192,
                                                       uu____85196)
                                                      in
                                                   let uu____85206 =
                                                     let uu____85220 =
                                                       let uu____85232 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____85236 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____85232,
                                                         uu____85236)
                                                        in
                                                     let uu____85246 =
                                                       let uu____85260 =
                                                         let uu____85272 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____85276 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____85272,
                                                           uu____85276)
                                                          in
                                                       let uu____85286 =
                                                         let uu____85300 =
                                                           let uu____85312 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____85316 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____85312,
                                                             uu____85316)
                                                            in
                                                         let uu____85326 =
                                                           let uu____85340 =
                                                             let uu____85352
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____85356
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____85352,
                                                               uu____85356)
                                                              in
                                                           let uu____85366 =
                                                             let uu____85380
                                                               =
                                                               let uu____85392
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____85396
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____85392,
                                                                 uu____85396)
                                                                in
                                                             let uu____85406
                                                               =
                                                               let uu____85420
                                                                 =
                                                                 let uu____85432
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____85436
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____85432,
                                                                   uu____85436)
                                                                  in
                                                               let uu____85446
                                                                 =
                                                                 let uu____85460
                                                                   =
                                                                   let uu____85472
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____85476
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____85472,
                                                                    uu____85476)
                                                                    in
                                                                 let uu____85486
                                                                   =
                                                                   let uu____85500
                                                                    =
                                                                    let uu____85512
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____85516
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____85512,
                                                                    uu____85516)
                                                                     in
                                                                   let uu____85526
                                                                    =
                                                                    let uu____85540
                                                                    =
                                                                    let uu____85552
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____85556
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____85552,
                                                                    uu____85556)
                                                                     in
                                                                    let uu____85566
                                                                    =
                                                                    let uu____85580
                                                                    =
                                                                    let uu____85592
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____85596
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____85592,
                                                                    uu____85596)
                                                                     in
                                                                    let uu____85606
                                                                    =
                                                                    let uu____85620
                                                                    =
                                                                    let uu____85632
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____85636
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____85632,
                                                                    uu____85636)
                                                                     in
                                                                    let uu____85646
                                                                    =
                                                                    let uu____85660
                                                                    =
                                                                    let uu____85672
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____85676
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____85672,
                                                                    uu____85676)
                                                                     in
                                                                    let uu____85686
                                                                    =
                                                                    let uu____85700
                                                                    =
                                                                    let uu____85712
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____85716
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____85712,
                                                                    uu____85716)
                                                                     in
                                                                    let uu____85726
                                                                    =
                                                                    let uu____85740
                                                                    =
                                                                    let uu____85752
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____85756
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____85752,
                                                                    uu____85756)
                                                                     in
                                                                    let uu____85766
                                                                    =
                                                                    let uu____85780
                                                                    =
                                                                    let uu____85792
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____85796
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____85792,
                                                                    uu____85796)
                                                                     in
                                                                    let uu____85806
                                                                    =
                                                                    let uu____85820
                                                                    =
                                                                    let uu____85832
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____85836
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____85832,
                                                                    uu____85836)
                                                                     in
                                                                    let uu____85846
                                                                    =
                                                                    let uu____85860
                                                                    =
                                                                    let uu____85872
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____85876
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____85872,
                                                                    uu____85876)
                                                                     in
                                                                    let uu____85886
                                                                    =
                                                                    let uu____85900
                                                                    =
                                                                    let uu____85912
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____85916
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____85912,
                                                                    uu____85916)
                                                                     in
                                                                    let uu____85926
                                                                    =
                                                                    let uu____85940
                                                                    =
                                                                    let uu____85952
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____85956
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____85952,
                                                                    uu____85956)
                                                                     in
                                                                    let uu____85966
                                                                    =
                                                                    let uu____85980
                                                                    =
                                                                    let uu____85992
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____85996
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____85992,
                                                                    uu____85996)
                                                                     in
                                                                    let uu____86006
                                                                    =
                                                                    let uu____86020
                                                                    =
                                                                    let uu____86032
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____86036
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____86032,
                                                                    uu____86036)
                                                                     in
                                                                    let uu____86046
                                                                    =
                                                                    let uu____86060
                                                                    =
                                                                    let uu____86072
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____86076
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____86072,
                                                                    uu____86076)
                                                                     in
                                                                    let uu____86086
                                                                    =
                                                                    let uu____86100
                                                                    =
                                                                    let uu____86112
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____86116
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____86112,
                                                                    uu____86116)
                                                                     in
                                                                    let uu____86126
                                                                    =
                                                                    let uu____86140
                                                                    =
                                                                    let uu____86152
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____86156
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____86152,
                                                                    uu____86156)
                                                                     in
                                                                    let uu____86166
                                                                    =
                                                                    let uu____86180
                                                                    =
                                                                    let uu____86192
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____86196
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____86192,
                                                                    uu____86196)
                                                                     in
                                                                    let uu____86206
                                                                    =
                                                                    let uu____86220
                                                                    =
                                                                    let uu____86232
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____86236
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____86232,
                                                                    uu____86236)
                                                                     in
                                                                    let uu____86246
                                                                    =
                                                                    let uu____86260
                                                                    =
                                                                    let uu____86272
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____86276
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____86272,
                                                                    uu____86276)
                                                                     in
                                                                    let uu____86286
                                                                    =
                                                                    let uu____86300
                                                                    =
                                                                    let uu____86312
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____86316
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____86312,
                                                                    uu____86316)
                                                                     in
                                                                    let uu____86326
                                                                    =
                                                                    let uu____86340
                                                                    =
                                                                    let uu____86352
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____86356
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____86352,
                                                                    uu____86356)
                                                                     in
                                                                    let uu____86366
                                                                    =
                                                                    let uu____86380
                                                                    =
                                                                    let uu____86392
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____86396
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____86392,
                                                                    uu____86396)
                                                                     in
                                                                    let uu____86406
                                                                    =
                                                                    let uu____86420
                                                                    =
                                                                    let uu____86432
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____86436
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____86432,
                                                                    uu____86436)
                                                                     in
                                                                    [uu____86420]
                                                                     in
                                                                    uu____86380
                                                                    ::
                                                                    uu____86406
                                                                     in
                                                                    uu____86340
                                                                    ::
                                                                    uu____86366
                                                                     in
                                                                    uu____86300
                                                                    ::
                                                                    uu____86326
                                                                     in
                                                                    uu____86260
                                                                    ::
                                                                    uu____86286
                                                                     in
                                                                    uu____86220
                                                                    ::
                                                                    uu____86246
                                                                     in
                                                                    uu____86180
                                                                    ::
                                                                    uu____86206
                                                                     in
                                                                    uu____86140
                                                                    ::
                                                                    uu____86166
                                                                     in
                                                                    uu____86100
                                                                    ::
                                                                    uu____86126
                                                                     in
                                                                    uu____86060
                                                                    ::
                                                                    uu____86086
                                                                     in
                                                                    uu____86020
                                                                    ::
                                                                    uu____86046
                                                                     in
                                                                    uu____85980
                                                                    ::
                                                                    uu____86006
                                                                     in
                                                                    uu____85940
                                                                    ::
                                                                    uu____85966
                                                                     in
                                                                    uu____85900
                                                                    ::
                                                                    uu____85926
                                                                     in
                                                                    uu____85860
                                                                    ::
                                                                    uu____85886
                                                                     in
                                                                    uu____85820
                                                                    ::
                                                                    uu____85846
                                                                     in
                                                                    uu____85780
                                                                    ::
                                                                    uu____85806
                                                                     in
                                                                    uu____85740
                                                                    ::
                                                                    uu____85766
                                                                     in
                                                                    uu____85700
                                                                    ::
                                                                    uu____85726
                                                                     in
                                                                    uu____85660
                                                                    ::
                                                                    uu____85686
                                                                     in
                                                                    uu____85620
                                                                    ::
                                                                    uu____85646
                                                                     in
                                                                    uu____85580
                                                                    ::
                                                                    uu____85606
                                                                     in
                                                                    uu____85540
                                                                    ::
                                                                    uu____85566
                                                                     in
                                                                   uu____85500
                                                                    ::
                                                                    uu____85526
                                                                    in
                                                                 uu____85460
                                                                   ::
                                                                   uu____85486
                                                                  in
                                                               uu____85420 ::
                                                                 uu____85446
                                                                in
                                                             uu____85380 ::
                                                               uu____85406
                                                              in
                                                           uu____85340 ::
                                                             uu____85366
                                                            in
                                                         uu____85300 ::
                                                           uu____85326
                                                          in
                                                       uu____85260 ::
                                                         uu____85286
                                                        in
                                                     uu____85220 ::
                                                       uu____85246
                                                      in
                                                   uu____85180 :: uu____85206
                                                    in
                                                 uu____85140 :: uu____85166
                                                  in
                                               uu____85100 :: uu____85126  in
                                             uu____85060 :: uu____85086  in
                                           uu____85020 :: uu____85046  in
                                         uu____84978 :: uu____85006  in
                                       uu____84936 :: uu____84964  in
                                     uu____84869 :: uu____84922  in
                                   uu____84802 :: uu____84855  in
                                 uu____84735 :: uu____84788  in
                               uu____84691 :: uu____84721  in
                             uu____84650 :: uu____84677  in
                           uu____84609 :: uu____84636  in
                         uu____84570 :: uu____84595  in
                       uu____84535 :: uu____84556  in
                     uu____84500 :: uu____84521  in
                   uu____84465 :: uu____84486  in
                 uu____84430 :: uu____84451  in
               uu____84395 :: uu____84416  in
             uu____84343 :: uu____84381  in
           uu____84279 :: uu____84329  in
         uu____84230 :: uu____84265  in
       uu____84181 :: uu____84216  in
     uu____84139 :: uu____84167  in
   uu____84091 :: uu____84125)
  
let run_either :
  'Auu____87084 .
    Prims.int ->
      'Auu____87084 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____87084 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____87122 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____87122);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____87127 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____87127 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____87150 =
               let uu____87152 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____87152 expected  in
             FStar_Tests_Util.always i uu____87150)))
  
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
        let interp uu____87231 = run_interpreter i r expected  in
        let uu____87232 =
          let uu____87233 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____87233  in
        (i, uu____87232)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____87271 = run_nbe i r expected  in
        let uu____87272 =
          let uu____87273 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____87273  in
        (i, uu____87272)
  
let run_tests :
  'Auu____87284 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
           'Auu____87284)
      -> 'Auu____87284 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___742_87336  ->
            match uu___742_87336 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____87367  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____87370 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____87379  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____87382 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____87398  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____87428  ->
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
        let nbe1 uu____87473 = run_nbe i r expected  in
        let norm1 uu____87479 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____87492  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____87495 =
       let uu____87496 = encode (Prims.parse_int "1000")  in
       let uu____87498 =
         let uu____87501 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____87502 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____87501 uu____87502  in
       let_ FStar_Tests_Util.x uu____87496 uu____87498  in
     run_both_with_time (Prims.parse_int "14") uu____87495 z)
  
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
             let uu____87578 = res1  in
             match uu____87578 with
             | (t1,time_int) ->
                 let uu____87588 = res2  in
                 (match uu____87588 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____87600 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____87600 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____87611  ->
    (let uu____87613 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____87613);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  