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
      (let uu____83236 =
         let uu____83239 = encode (n1 - (Prims.parse_int "1"))  in
         [uu____83239]  in
       FStar_Tests_Util.app succ uu____83236)
  
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
        let uu____83278 =
          let uu____83281 = let uu____83282 = b x1  in [uu____83282]  in
          FStar_Syntax_Util.abs uu____83281 e' FStar_Pervasives_Native.None
           in
        FStar_Tests_Util.app uu____83278 [e]
  
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
  let uu____83352 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____83352
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____83355 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____83355
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
    let uu____83374 =
      let uu____83381 =
        let uu____83382 =
          let uu____83399 = tm_fv snat_l  in
          let uu____83402 =
            let uu____83413 = FStar_Syntax_Syntax.as_arg s  in [uu____83413]
             in
          (uu____83399, uu____83402)  in
        FStar_Syntax_Syntax.Tm_app uu____83382  in
      FStar_Syntax_Syntax.mk uu____83381  in
    uu____83374 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____83458 .
    'Auu____83458 -> 'Auu____83458 FStar_Syntax_Syntax.withinfo_t
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
      let uu____83567 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____83567, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____83611 =
        let uu____83614 =
          let uu____83615 =
            let uu____83629 =
              let uu____83639 =
                let uu____83647 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____83647, false)  in
              [uu____83639]  in
            (snat_l, uu____83629)  in
          FStar_Syntax_Syntax.Pat_cons uu____83615  in
        pat uu____83614  in
      let uu____83677 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___763_83682 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___763_83682.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___763_83682.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____83611, FStar_Pervasives_Native.None, uu____83677)  in
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
        let uu____83723 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____83742 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____83723, FStar_Pervasives_Native.None, uu____83742)  in
      let sbranch =
        let uu____83770 =
          let uu____83773 =
            let uu____83774 =
              let uu____83788 =
                let uu____83798 =
                  let uu____83806 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____83806, false)  in
                [uu____83798]  in
              (snat_l, uu____83788)  in
            FStar_Syntax_Syntax.Pat_cons uu____83774  in
          pat uu____83773  in
        let uu____83836 =
          let uu____83839 = FStar_Tests_Util.nm minus1  in
          let uu____83842 =
            let uu____83845 =
              let uu____83846 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____83846  in
            let uu____83849 =
              let uu____83852 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____83852]  in
            uu____83845 :: uu____83849  in
          FStar_Tests_Util.app uu____83839 uu____83842  in
        (uu____83770, FStar_Pervasives_Native.None, uu____83836)  in
      let lb =
        let uu____83864 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____83868 =
          let uu____83871 =
            let uu____83872 =
              let uu____83873 = b FStar_Tests_Util.x  in
              let uu____83880 =
                let uu____83889 = b FStar_Tests_Util.y  in [uu____83889]  in
              uu____83873 :: uu____83880  in
            let uu____83914 =
              let uu____83917 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____83917 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____83872 uu____83914
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____83871
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____83864;
          FStar_Syntax_Syntax.lbdef = uu____83868;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____83924 =
        let uu____83931 =
          let uu____83932 =
            let uu____83946 =
              let uu____83949 =
                let uu____83950 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____83950 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____83949
               in
            ((true, [lb]), uu____83946)  in
          FStar_Syntax_Syntax.Tm_let uu____83932  in
        FStar_Syntax_Syntax.mk uu____83931  in
      uu____83924 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____83997 = snat out  in
         aux uu____83997 (n2 - (Prims.parse_int "1")))
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
  (let uu____84063 =
     let uu____84075 =
       let uu____84078 =
         let uu____84081 =
           let uu____84084 =
             let uu____84087 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____84087]  in
           id :: uu____84084  in
         one :: uu____84081  in
       FStar_Tests_Util.app apply uu____84078  in
     let uu____84088 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____84075, uu____84088)  in
   let uu____84097 =
     let uu____84111 =
       let uu____84123 =
         let uu____84126 =
           let uu____84129 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____84129]  in
         FStar_Tests_Util.app id uu____84126  in
       let uu____84130 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____84123, uu____84130)  in
     let uu____84139 =
       let uu____84153 =
         let uu____84165 =
           let uu____84168 =
             let uu____84171 =
               let uu____84174 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____84175 =
                 let uu____84178 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____84178]  in
               uu____84174 :: uu____84175  in
             tt :: uu____84171  in
           FStar_Tests_Util.app apply uu____84168  in
         let uu____84179 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____84165, uu____84179)  in
       let uu____84188 =
         let uu____84202 =
           let uu____84214 =
             let uu____84217 =
               let uu____84220 =
                 let uu____84223 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____84224 =
                   let uu____84227 = FStar_Tests_Util.nm FStar_Tests_Util.m
                      in
                   [uu____84227]  in
                 uu____84223 :: uu____84224  in
               ff :: uu____84220  in
             FStar_Tests_Util.app apply uu____84217  in
           let uu____84228 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____84214, uu____84228)  in
         let uu____84237 =
           let uu____84251 =
             let uu____84263 =
               let uu____84266 =
                 let uu____84269 =
                   let uu____84272 =
                     let uu____84275 =
                       let uu____84278 =
                         let uu____84281 =
                           let uu____84284 =
                             let uu____84287 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____84288 =
                               let uu____84291 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____84291]  in
                             uu____84287 :: uu____84288  in
                           ff :: uu____84284  in
                         apply :: uu____84281  in
                       apply :: uu____84278  in
                     apply :: uu____84275  in
                   apply :: uu____84272  in
                 apply :: uu____84269  in
               FStar_Tests_Util.app apply uu____84266  in
             let uu____84292 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____84263, uu____84292)  in
           let uu____84301 =
             let uu____84315 =
               let uu____84327 =
                 let uu____84330 =
                   let uu____84333 =
                     let uu____84336 =
                       let uu____84339 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n  in
                       let uu____84340 =
                         let uu____84343 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____84343]  in
                       uu____84339 :: uu____84340  in
                     ff :: uu____84336  in
                   apply :: uu____84333  in
                 FStar_Tests_Util.app twice uu____84330  in
               let uu____84344 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____84327, uu____84344)  in
             let uu____84353 =
               let uu____84367 =
                 let uu____84379 = minus one z  in
                 ((Prims.parse_int "5"), uu____84379, one)  in
               let uu____84388 =
                 let uu____84402 =
                   let uu____84414 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____84414, z)  in
                 let uu____84423 =
                   let uu____84437 =
                     let uu____84449 = minus one one  in
                     ((Prims.parse_int "7"), uu____84449, z)  in
                   let uu____84458 =
                     let uu____84472 =
                       let uu____84484 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____84484, one)  in
                     let uu____84493 =
                       let uu____84507 =
                         let uu____84519 =
                           FStar_Tests_Util.app mul [two; one]  in
                         ((Prims.parse_int "9"), uu____84519, two)  in
                       let uu____84528 =
                         let uu____84542 =
                           let uu____84554 =
                             let uu____84557 =
                               let uu____84560 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____84560; one]  in
                             FStar_Tests_Util.app mul uu____84557  in
                           ((Prims.parse_int "10"), uu____84554, two)  in
                         let uu____84567 =
                           let uu____84581 =
                             let uu____84593 =
                               let uu____84596 =
                                 encode (Prims.parse_int "10")  in
                               let uu____84598 =
                                 encode (Prims.parse_int "10")  in
                               minus uu____84596 uu____84598  in
                             ((Prims.parse_int "11"), uu____84593, z)  in
                           let uu____84608 =
                             let uu____84622 =
                               let uu____84634 =
                                 let uu____84637 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____84639 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____84637 uu____84639  in
                               ((Prims.parse_int "12"), uu____84634, z)  in
                             let uu____84649 =
                               let uu____84663 =
                                 let uu____84675 =
                                   let uu____84678 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____84680 =
                                     let uu____84683 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____84684 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____84683 uu____84684  in
                                   let_ FStar_Tests_Util.x uu____84678
                                     uu____84680
                                    in
                                 ((Prims.parse_int "13"), uu____84675, z)  in
                               let uu____84693 =
                                 let uu____84707 =
                                   let uu____84719 =
                                     let uu____84722 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____84723 =
                                       let uu____84726 =
                                         let uu____84727 =
                                           let uu____84730 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____84731 =
                                             let uu____84734 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____84734]  in
                                           uu____84730 :: uu____84731  in
                                         FStar_Tests_Util.app mul uu____84727
                                          in
                                       let uu____84735 =
                                         let uu____84738 =
                                           let uu____84739 =
                                             let uu____84742 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____84743 =
                                               let uu____84746 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____84746]  in
                                             uu____84742 :: uu____84743  in
                                           FStar_Tests_Util.app mul
                                             uu____84739
                                            in
                                         let uu____84747 =
                                           let uu____84750 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____84751 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____84750 uu____84751  in
                                         let_ FStar_Tests_Util.h uu____84738
                                           uu____84747
                                          in
                                       let_ FStar_Tests_Util.y uu____84726
                                         uu____84735
                                        in
                                     let_ FStar_Tests_Util.x uu____84722
                                       uu____84723
                                      in
                                   ((Prims.parse_int "15"), uu____84719, z)
                                    in
                                 let uu____84760 =
                                   let uu____84774 =
                                     let uu____84786 =
                                       let uu____84789 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____84792 =
                                         let uu____84793 =
                                           let uu____84796 =
                                             let uu____84799 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____84800 =
                                               let uu____84803 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____84803]  in
                                             uu____84799 :: uu____84800  in
                                           FStar_Tests_Util.app mul
                                             uu____84796
                                            in
                                         let uu____84804 =
                                           let uu____84805 =
                                             let uu____84808 =
                                               let uu____84811 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____84812 =
                                                 let uu____84815 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____84815]  in
                                               uu____84811 :: uu____84812  in
                                             FStar_Tests_Util.app mul
                                               uu____84808
                                              in
                                           let uu____84816 =
                                             let uu____84817 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____84818 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____84817 uu____84818
                                              in
                                           mk_let FStar_Tests_Util.h
                                             uu____84805 uu____84816
                                            in
                                         mk_let FStar_Tests_Util.y
                                           uu____84793 uu____84804
                                          in
                                       mk_let FStar_Tests_Util.x uu____84789
                                         uu____84792
                                        in
                                     ((Prims.parse_int "16"), uu____84786, z)
                                      in
                                   let uu____84827 =
                                     let uu____84841 =
                                       let uu____84853 =
                                         let uu____84856 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____84857 =
                                           let uu____84860 =
                                             let uu____84861 =
                                               let uu____84864 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____84865 =
                                                 let uu____84868 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____84868]  in
                                               uu____84864 :: uu____84865  in
                                             FStar_Tests_Util.app mul
                                               uu____84861
                                              in
                                           let uu____84869 =
                                             let uu____84872 =
                                               let uu____84873 =
                                                 let uu____84876 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____84877 =
                                                   let uu____84880 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____84880]  in
                                                 uu____84876 :: uu____84877
                                                  in
                                               FStar_Tests_Util.app mul
                                                 uu____84873
                                                in
                                             let uu____84881 =
                                               let uu____84884 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____84885 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____84884 uu____84885
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____84872 uu____84881
                                              in
                                           let_ FStar_Tests_Util.y
                                             uu____84860 uu____84869
                                            in
                                         let_ FStar_Tests_Util.x uu____84856
                                           uu____84857
                                          in
                                       ((Prims.parse_int "17"), uu____84853,
                                         z)
                                        in
                                     let uu____84894 =
                                       let uu____84908 =
                                         let uu____84920 =
                                           let uu____84923 =
                                             let uu____84926 = snat znat  in
                                             snat uu____84926  in
                                           pred_nat uu____84923  in
                                         let uu____84927 = snat znat  in
                                         ((Prims.parse_int "18"),
                                           uu____84920, uu____84927)
                                          in
                                       let uu____84936 =
                                         let uu____84950 =
                                           let uu____84962 =
                                             let uu____84965 =
                                               let uu____84966 =
                                                 let uu____84967 = snat znat
                                                    in
                                                 snat uu____84967  in
                                               let uu____84968 = snat znat
                                                  in
                                               minus_nat uu____84966
                                                 uu____84968
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____84965
                                              in
                                           let uu____84969 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____84962, uu____84969)
                                            in
                                         let uu____84978 =
                                           let uu____84992 =
                                             let uu____85004 =
                                               let uu____85007 =
                                                 let uu____85008 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 let uu____85010 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 minus_nat uu____85008
                                                   uu____85010
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____85007
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____85004, znat)
                                              in
                                           let uu____85018 =
                                             let uu____85032 =
                                               let uu____85044 =
                                                 let uu____85047 =
                                                   let uu____85048 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   let uu____85050 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   minus_nat uu____85048
                                                     uu____85050
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____85047
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____85044, znat)
                                                in
                                             let uu____85058 =
                                               let uu____85072 =
                                                 let uu____85084 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____85088 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____85084, uu____85088)
                                                  in
                                               let uu____85098 =
                                                 let uu____85112 =
                                                   let uu____85124 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____85128 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____85124,
                                                     uu____85128)
                                                    in
                                                 let uu____85138 =
                                                   let uu____85152 =
                                                     let uu____85164 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____85168 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____85164,
                                                       uu____85168)
                                                      in
                                                   let uu____85178 =
                                                     let uu____85192 =
                                                       let uu____85204 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____85208 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____85204,
                                                         uu____85208)
                                                        in
                                                     let uu____85218 =
                                                       let uu____85232 =
                                                         let uu____85244 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____85248 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____85244,
                                                           uu____85248)
                                                          in
                                                       let uu____85258 =
                                                         let uu____85272 =
                                                           let uu____85284 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____85288 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____85284,
                                                             uu____85288)
                                                            in
                                                         let uu____85298 =
                                                           let uu____85312 =
                                                             let uu____85324
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____85328
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____85324,
                                                               uu____85328)
                                                              in
                                                           let uu____85338 =
                                                             let uu____85352
                                                               =
                                                               let uu____85364
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____85368
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____85364,
                                                                 uu____85368)
                                                                in
                                                             let uu____85378
                                                               =
                                                               let uu____85392
                                                                 =
                                                                 let uu____85404
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____85408
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____85404,
                                                                   uu____85408)
                                                                  in
                                                               let uu____85418
                                                                 =
                                                                 let uu____85432
                                                                   =
                                                                   let uu____85444
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____85448
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____85444,
                                                                    uu____85448)
                                                                    in
                                                                 let uu____85458
                                                                   =
                                                                   let uu____85472
                                                                    =
                                                                    let uu____85484
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____85488
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____85484,
                                                                    uu____85488)
                                                                     in
                                                                   let uu____85498
                                                                    =
                                                                    let uu____85512
                                                                    =
                                                                    let uu____85524
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____85528
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____85524,
                                                                    uu____85528)
                                                                     in
                                                                    let uu____85538
                                                                    =
                                                                    let uu____85552
                                                                    =
                                                                    let uu____85564
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____85568
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____85564,
                                                                    uu____85568)
                                                                     in
                                                                    let uu____85578
                                                                    =
                                                                    let uu____85592
                                                                    =
                                                                    let uu____85604
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____85608
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____85604,
                                                                    uu____85608)
                                                                     in
                                                                    let uu____85618
                                                                    =
                                                                    let uu____85632
                                                                    =
                                                                    let uu____85644
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____85648
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____85644,
                                                                    uu____85648)
                                                                     in
                                                                    let uu____85658
                                                                    =
                                                                    let uu____85672
                                                                    =
                                                                    let uu____85684
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____85688
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____85684,
                                                                    uu____85688)
                                                                     in
                                                                    let uu____85698
                                                                    =
                                                                    let uu____85712
                                                                    =
                                                                    let uu____85724
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____85728
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____85724,
                                                                    uu____85728)
                                                                     in
                                                                    let uu____85738
                                                                    =
                                                                    let uu____85752
                                                                    =
                                                                    let uu____85764
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____85768
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____85764,
                                                                    uu____85768)
                                                                     in
                                                                    let uu____85778
                                                                    =
                                                                    let uu____85792
                                                                    =
                                                                    let uu____85804
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____85808
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____85804,
                                                                    uu____85808)
                                                                     in
                                                                    let uu____85818
                                                                    =
                                                                    let uu____85832
                                                                    =
                                                                    let uu____85844
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____85848
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____85844,
                                                                    uu____85848)
                                                                     in
                                                                    let uu____85858
                                                                    =
                                                                    let uu____85872
                                                                    =
                                                                    let uu____85884
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____85888
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____85884,
                                                                    uu____85888)
                                                                     in
                                                                    let uu____85898
                                                                    =
                                                                    let uu____85912
                                                                    =
                                                                    let uu____85924
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____85928
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____85924,
                                                                    uu____85928)
                                                                     in
                                                                    let uu____85938
                                                                    =
                                                                    let uu____85952
                                                                    =
                                                                    let uu____85964
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____85968
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____85964,
                                                                    uu____85968)
                                                                     in
                                                                    let uu____85978
                                                                    =
                                                                    let uu____85992
                                                                    =
                                                                    let uu____86004
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____86008
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____86004,
                                                                    uu____86008)
                                                                     in
                                                                    let uu____86018
                                                                    =
                                                                    let uu____86032
                                                                    =
                                                                    let uu____86044
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____86048
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____86044,
                                                                    uu____86048)
                                                                     in
                                                                    let uu____86058
                                                                    =
                                                                    let uu____86072
                                                                    =
                                                                    let uu____86084
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____86088
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____86084,
                                                                    uu____86088)
                                                                     in
                                                                    let uu____86098
                                                                    =
                                                                    let uu____86112
                                                                    =
                                                                    let uu____86124
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____86128
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____86124,
                                                                    uu____86128)
                                                                     in
                                                                    let uu____86138
                                                                    =
                                                                    let uu____86152
                                                                    =
                                                                    let uu____86164
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____86168
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____86164,
                                                                    uu____86168)
                                                                     in
                                                                    let uu____86178
                                                                    =
                                                                    let uu____86192
                                                                    =
                                                                    let uu____86204
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____86208
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____86204,
                                                                    uu____86208)
                                                                     in
                                                                    let uu____86218
                                                                    =
                                                                    let uu____86232
                                                                    =
                                                                    let uu____86244
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____86248
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____86244,
                                                                    uu____86248)
                                                                     in
                                                                    let uu____86258
                                                                    =
                                                                    let uu____86272
                                                                    =
                                                                    let uu____86284
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____86288
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____86284,
                                                                    uu____86288)
                                                                     in
                                                                    let uu____86298
                                                                    =
                                                                    let uu____86312
                                                                    =
                                                                    let uu____86324
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____86328
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____86324,
                                                                    uu____86328)
                                                                     in
                                                                    let uu____86338
                                                                    =
                                                                    let uu____86352
                                                                    =
                                                                    let uu____86364
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____86368
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____86364,
                                                                    uu____86368)
                                                                     in
                                                                    let uu____86378
                                                                    =
                                                                    let uu____86392
                                                                    =
                                                                    let uu____86404
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____86408
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____86404,
                                                                    uu____86408)
                                                                     in
                                                                    [uu____86392]
                                                                     in
                                                                    uu____86352
                                                                    ::
                                                                    uu____86378
                                                                     in
                                                                    uu____86312
                                                                    ::
                                                                    uu____86338
                                                                     in
                                                                    uu____86272
                                                                    ::
                                                                    uu____86298
                                                                     in
                                                                    uu____86232
                                                                    ::
                                                                    uu____86258
                                                                     in
                                                                    uu____86192
                                                                    ::
                                                                    uu____86218
                                                                     in
                                                                    uu____86152
                                                                    ::
                                                                    uu____86178
                                                                     in
                                                                    uu____86112
                                                                    ::
                                                                    uu____86138
                                                                     in
                                                                    uu____86072
                                                                    ::
                                                                    uu____86098
                                                                     in
                                                                    uu____86032
                                                                    ::
                                                                    uu____86058
                                                                     in
                                                                    uu____85992
                                                                    ::
                                                                    uu____86018
                                                                     in
                                                                    uu____85952
                                                                    ::
                                                                    uu____85978
                                                                     in
                                                                    uu____85912
                                                                    ::
                                                                    uu____85938
                                                                     in
                                                                    uu____85872
                                                                    ::
                                                                    uu____85898
                                                                     in
                                                                    uu____85832
                                                                    ::
                                                                    uu____85858
                                                                     in
                                                                    uu____85792
                                                                    ::
                                                                    uu____85818
                                                                     in
                                                                    uu____85752
                                                                    ::
                                                                    uu____85778
                                                                     in
                                                                    uu____85712
                                                                    ::
                                                                    uu____85738
                                                                     in
                                                                    uu____85672
                                                                    ::
                                                                    uu____85698
                                                                     in
                                                                    uu____85632
                                                                    ::
                                                                    uu____85658
                                                                     in
                                                                    uu____85592
                                                                    ::
                                                                    uu____85618
                                                                     in
                                                                    uu____85552
                                                                    ::
                                                                    uu____85578
                                                                     in
                                                                    uu____85512
                                                                    ::
                                                                    uu____85538
                                                                     in
                                                                   uu____85472
                                                                    ::
                                                                    uu____85498
                                                                    in
                                                                 uu____85432
                                                                   ::
                                                                   uu____85458
                                                                  in
                                                               uu____85392 ::
                                                                 uu____85418
                                                                in
                                                             uu____85352 ::
                                                               uu____85378
                                                              in
                                                           uu____85312 ::
                                                             uu____85338
                                                            in
                                                         uu____85272 ::
                                                           uu____85298
                                                          in
                                                       uu____85232 ::
                                                         uu____85258
                                                        in
                                                     uu____85192 ::
                                                       uu____85218
                                                      in
                                                   uu____85152 :: uu____85178
                                                    in
                                                 uu____85112 :: uu____85138
                                                  in
                                               uu____85072 :: uu____85098  in
                                             uu____85032 :: uu____85058  in
                                           uu____84992 :: uu____85018  in
                                         uu____84950 :: uu____84978  in
                                       uu____84908 :: uu____84936  in
                                     uu____84841 :: uu____84894  in
                                   uu____84774 :: uu____84827  in
                                 uu____84707 :: uu____84760  in
                               uu____84663 :: uu____84693  in
                             uu____84622 :: uu____84649  in
                           uu____84581 :: uu____84608  in
                         uu____84542 :: uu____84567  in
                       uu____84507 :: uu____84528  in
                     uu____84472 :: uu____84493  in
                   uu____84437 :: uu____84458  in
                 uu____84402 :: uu____84423  in
               uu____84367 :: uu____84388  in
             uu____84315 :: uu____84353  in
           uu____84251 :: uu____84301  in
         uu____84202 :: uu____84237  in
       uu____84153 :: uu____84188  in
     uu____84111 :: uu____84139  in
   uu____84063 :: uu____84097)
  
let run_either :
  'Auu____87056 .
    Prims.int ->
      'Auu____87056 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____87056 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____87094 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____87094);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____87099 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____87099 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____87122 =
               let uu____87124 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____87124 expected  in
             FStar_Tests_Util.always i uu____87122)))
  
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
        let interp uu____87203 = run_interpreter i r expected  in
        let uu____87204 =
          let uu____87205 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____87205  in
        (i, uu____87204)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____87243 = run_nbe i r expected  in
        let uu____87244 =
          let uu____87245 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____87245  in
        (i, uu____87244)
  
let run_tests :
  'Auu____87256 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
           'Auu____87256)
      -> 'Auu____87256 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___742_87308  ->
            match uu___742_87308 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____87339  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____87342 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____87351  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____87354 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____87370  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____87400  ->
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
        let nbe1 uu____87445 = run_nbe i r expected  in
        let norm1 uu____87451 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____87464  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____87467 =
       let uu____87468 = encode (Prims.parse_int "1000")  in
       let uu____87470 =
         let uu____87473 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____87474 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____87473 uu____87474  in
       let_ FStar_Tests_Util.x uu____87468 uu____87470  in
     run_both_with_time (Prims.parse_int "14") uu____87467 z)
  
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
             let uu____87550 = res1  in
             match uu____87550 with
             | (t1,time_int) ->
                 let uu____87560 = res2  in
                 (match uu____87560 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____87572 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____87572 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____87583  ->
    (let uu____87585 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____87585);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  