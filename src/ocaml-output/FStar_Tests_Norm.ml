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
      (let uu____78043 =
         let uu____78046 = encode (n1 - (Prims.parse_int "1"))  in
         [uu____78046]  in
       FStar_Tests_Util.app succ uu____78043)
  
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
        let uu____78085 =
          let uu____78088 = let uu____78089 = b x1  in [uu____78089]  in
          FStar_Syntax_Util.abs uu____78088 e' FStar_Pervasives_Native.None
           in
        FStar_Tests_Util.app uu____78085 [e]
  
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
  let uu____78159 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____78159
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____78162 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____78162
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
    let uu____78181 =
      let uu____78188 =
        let uu____78189 =
          let uu____78206 = tm_fv snat_l  in
          let uu____78209 =
            let uu____78220 = FStar_Syntax_Syntax.as_arg s  in [uu____78220]
             in
          (uu____78206, uu____78209)  in
        FStar_Syntax_Syntax.Tm_app uu____78189  in
      FStar_Syntax_Syntax.mk uu____78188  in
    uu____78181 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____78262 .
    'Auu____78262 -> 'Auu____78262 FStar_Syntax_Syntax.withinfo_t
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
      let uu____78371 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____78371, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____78415 =
        let uu____78418 =
          let uu____78419 =
            let uu____78433 =
              let uu____78443 =
                let uu____78451 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____78451, false)  in
              [uu____78443]  in
            (snat_l, uu____78433)  in
          FStar_Syntax_Syntax.Pat_cons uu____78419  in
        pat uu____78418  in
      let uu____78481 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___763_78486 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___763_78486.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___763_78486.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____78415, FStar_Pervasives_Native.None, uu____78481)  in
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
        let uu____78527 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____78546 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____78527, FStar_Pervasives_Native.None, uu____78546)  in
      let sbranch =
        let uu____78574 =
          let uu____78577 =
            let uu____78578 =
              let uu____78592 =
                let uu____78602 =
                  let uu____78610 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____78610, false)  in
                [uu____78602]  in
              (snat_l, uu____78592)  in
            FStar_Syntax_Syntax.Pat_cons uu____78578  in
          pat uu____78577  in
        let uu____78640 =
          let uu____78643 = FStar_Tests_Util.nm minus1  in
          let uu____78646 =
            let uu____78649 =
              let uu____78650 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____78650  in
            let uu____78653 =
              let uu____78656 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____78656]  in
            uu____78649 :: uu____78653  in
          FStar_Tests_Util.app uu____78643 uu____78646  in
        (uu____78574, FStar_Pervasives_Native.None, uu____78640)  in
      let lb =
        let uu____78668 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____78672 =
          let uu____78675 =
            let uu____78676 =
              let uu____78677 = b FStar_Tests_Util.x  in
              let uu____78684 =
                let uu____78693 = b FStar_Tests_Util.y  in [uu____78693]  in
              uu____78677 :: uu____78684  in
            let uu____78718 =
              let uu____78721 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____78721 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____78676 uu____78718
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____78675
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____78668;
          FStar_Syntax_Syntax.lbdef = uu____78672;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____78728 =
        let uu____78735 =
          let uu____78736 =
            let uu____78750 =
              let uu____78753 =
                let uu____78754 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____78754 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____78753
               in
            ((true, [lb]), uu____78750)  in
          FStar_Syntax_Syntax.Tm_let uu____78736  in
        FStar_Syntax_Syntax.mk uu____78735  in
      uu____78728 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____78798 = snat out  in
         aux uu____78798 (n2 - (Prims.parse_int "1")))
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
  (let uu____78864 =
     let uu____78876 =
       let uu____78879 =
         let uu____78882 =
           let uu____78885 =
             let uu____78888 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____78888]  in
           id :: uu____78885  in
         one :: uu____78882  in
       FStar_Tests_Util.app apply uu____78879  in
     let uu____78889 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____78876, uu____78889)  in
   let uu____78898 =
     let uu____78912 =
       let uu____78924 =
         let uu____78927 =
           let uu____78930 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____78930]  in
         FStar_Tests_Util.app id uu____78927  in
       let uu____78931 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____78924, uu____78931)  in
     let uu____78940 =
       let uu____78954 =
         let uu____78966 =
           let uu____78969 =
             let uu____78972 =
               let uu____78975 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____78976 =
                 let uu____78979 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____78979]  in
               uu____78975 :: uu____78976  in
             tt :: uu____78972  in
           FStar_Tests_Util.app apply uu____78969  in
         let uu____78980 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____78966, uu____78980)  in
       let uu____78989 =
         let uu____79003 =
           let uu____79015 =
             let uu____79018 =
               let uu____79021 =
                 let uu____79024 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____79025 =
                   let uu____79028 = FStar_Tests_Util.nm FStar_Tests_Util.m
                      in
                   [uu____79028]  in
                 uu____79024 :: uu____79025  in
               ff :: uu____79021  in
             FStar_Tests_Util.app apply uu____79018  in
           let uu____79029 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____79015, uu____79029)  in
         let uu____79038 =
           let uu____79052 =
             let uu____79064 =
               let uu____79067 =
                 let uu____79070 =
                   let uu____79073 =
                     let uu____79076 =
                       let uu____79079 =
                         let uu____79082 =
                           let uu____79085 =
                             let uu____79088 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____79089 =
                               let uu____79092 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____79092]  in
                             uu____79088 :: uu____79089  in
                           ff :: uu____79085  in
                         apply :: uu____79082  in
                       apply :: uu____79079  in
                     apply :: uu____79076  in
                   apply :: uu____79073  in
                 apply :: uu____79070  in
               FStar_Tests_Util.app apply uu____79067  in
             let uu____79093 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____79064, uu____79093)  in
           let uu____79102 =
             let uu____79116 =
               let uu____79128 =
                 let uu____79131 =
                   let uu____79134 =
                     let uu____79137 =
                       let uu____79140 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n  in
                       let uu____79141 =
                         let uu____79144 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____79144]  in
                       uu____79140 :: uu____79141  in
                     ff :: uu____79137  in
                   apply :: uu____79134  in
                 FStar_Tests_Util.app twice uu____79131  in
               let uu____79145 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____79128, uu____79145)  in
             let uu____79154 =
               let uu____79168 =
                 let uu____79180 = minus one z  in
                 ((Prims.parse_int "5"), uu____79180, one)  in
               let uu____79189 =
                 let uu____79203 =
                   let uu____79215 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____79215, z)  in
                 let uu____79224 =
                   let uu____79238 =
                     let uu____79250 = minus one one  in
                     ((Prims.parse_int "7"), uu____79250, z)  in
                   let uu____79259 =
                     let uu____79273 =
                       let uu____79285 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____79285, one)  in
                     let uu____79294 =
                       let uu____79308 =
                         let uu____79320 =
                           FStar_Tests_Util.app mul [two; one]  in
                         ((Prims.parse_int "9"), uu____79320, two)  in
                       let uu____79329 =
                         let uu____79343 =
                           let uu____79355 =
                             let uu____79358 =
                               let uu____79361 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____79361; one]  in
                             FStar_Tests_Util.app mul uu____79358  in
                           ((Prims.parse_int "10"), uu____79355, two)  in
                         let uu____79368 =
                           let uu____79382 =
                             let uu____79394 =
                               let uu____79397 =
                                 encode (Prims.parse_int "10")  in
                               let uu____79399 =
                                 encode (Prims.parse_int "10")  in
                               minus uu____79397 uu____79399  in
                             ((Prims.parse_int "11"), uu____79394, z)  in
                           let uu____79409 =
                             let uu____79423 =
                               let uu____79435 =
                                 let uu____79438 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____79440 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____79438 uu____79440  in
                               ((Prims.parse_int "12"), uu____79435, z)  in
                             let uu____79450 =
                               let uu____79464 =
                                 let uu____79476 =
                                   let uu____79479 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____79481 =
                                     let uu____79484 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____79485 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____79484 uu____79485  in
                                   let_ FStar_Tests_Util.x uu____79479
                                     uu____79481
                                    in
                                 ((Prims.parse_int "13"), uu____79476, z)  in
                               let uu____79494 =
                                 let uu____79508 =
                                   let uu____79520 =
                                     let uu____79523 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____79524 =
                                       let uu____79527 =
                                         let uu____79528 =
                                           let uu____79531 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____79532 =
                                             let uu____79535 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____79535]  in
                                           uu____79531 :: uu____79532  in
                                         FStar_Tests_Util.app mul uu____79528
                                          in
                                       let uu____79536 =
                                         let uu____79539 =
                                           let uu____79540 =
                                             let uu____79543 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____79544 =
                                               let uu____79547 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____79547]  in
                                             uu____79543 :: uu____79544  in
                                           FStar_Tests_Util.app mul
                                             uu____79540
                                            in
                                         let uu____79548 =
                                           let uu____79551 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____79552 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____79551 uu____79552  in
                                         let_ FStar_Tests_Util.h uu____79539
                                           uu____79548
                                          in
                                       let_ FStar_Tests_Util.y uu____79527
                                         uu____79536
                                        in
                                     let_ FStar_Tests_Util.x uu____79523
                                       uu____79524
                                      in
                                   ((Prims.parse_int "15"), uu____79520, z)
                                    in
                                 let uu____79561 =
                                   let uu____79575 =
                                     let uu____79587 =
                                       let uu____79590 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____79593 =
                                         let uu____79594 =
                                           let uu____79597 =
                                             let uu____79600 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____79601 =
                                               let uu____79604 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____79604]  in
                                             uu____79600 :: uu____79601  in
                                           FStar_Tests_Util.app mul
                                             uu____79597
                                            in
                                         let uu____79605 =
                                           let uu____79606 =
                                             let uu____79609 =
                                               let uu____79612 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____79613 =
                                                 let uu____79616 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____79616]  in
                                               uu____79612 :: uu____79613  in
                                             FStar_Tests_Util.app mul
                                               uu____79609
                                              in
                                           let uu____79617 =
                                             let uu____79618 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____79619 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____79618 uu____79619
                                              in
                                           mk_let FStar_Tests_Util.h
                                             uu____79606 uu____79617
                                            in
                                         mk_let FStar_Tests_Util.y
                                           uu____79594 uu____79605
                                          in
                                       mk_let FStar_Tests_Util.x uu____79590
                                         uu____79593
                                        in
                                     ((Prims.parse_int "16"), uu____79587, z)
                                      in
                                   let uu____79628 =
                                     let uu____79642 =
                                       let uu____79654 =
                                         let uu____79657 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____79658 =
                                           let uu____79661 =
                                             let uu____79662 =
                                               let uu____79665 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____79666 =
                                                 let uu____79669 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____79669]  in
                                               uu____79665 :: uu____79666  in
                                             FStar_Tests_Util.app mul
                                               uu____79662
                                              in
                                           let uu____79670 =
                                             let uu____79673 =
                                               let uu____79674 =
                                                 let uu____79677 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____79678 =
                                                   let uu____79681 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____79681]  in
                                                 uu____79677 :: uu____79678
                                                  in
                                               FStar_Tests_Util.app mul
                                                 uu____79674
                                                in
                                             let uu____79682 =
                                               let uu____79685 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____79686 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____79685 uu____79686
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____79673 uu____79682
                                              in
                                           let_ FStar_Tests_Util.y
                                             uu____79661 uu____79670
                                            in
                                         let_ FStar_Tests_Util.x uu____79657
                                           uu____79658
                                          in
                                       ((Prims.parse_int "17"), uu____79654,
                                         z)
                                        in
                                     let uu____79695 =
                                       let uu____79709 =
                                         let uu____79721 =
                                           let uu____79724 =
                                             let uu____79727 = snat znat  in
                                             snat uu____79727  in
                                           pred_nat uu____79724  in
                                         let uu____79728 = snat znat  in
                                         ((Prims.parse_int "18"),
                                           uu____79721, uu____79728)
                                          in
                                       let uu____79737 =
                                         let uu____79751 =
                                           let uu____79763 =
                                             let uu____79766 =
                                               let uu____79767 =
                                                 let uu____79768 = snat znat
                                                    in
                                                 snat uu____79768  in
                                               let uu____79769 = snat znat
                                                  in
                                               minus_nat uu____79767
                                                 uu____79769
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____79766
                                              in
                                           let uu____79770 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____79763, uu____79770)
                                            in
                                         let uu____79779 =
                                           let uu____79793 =
                                             let uu____79805 =
                                               let uu____79808 =
                                                 let uu____79809 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 let uu____79811 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 minus_nat uu____79809
                                                   uu____79811
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____79808
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____79805, znat)
                                              in
                                           let uu____79819 =
                                             let uu____79833 =
                                               let uu____79845 =
                                                 let uu____79848 =
                                                   let uu____79849 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   let uu____79851 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   minus_nat uu____79849
                                                     uu____79851
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____79848
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____79845, znat)
                                                in
                                             let uu____79859 =
                                               let uu____79873 =
                                                 let uu____79885 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____79889 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____79885, uu____79889)
                                                  in
                                               let uu____79899 =
                                                 let uu____79913 =
                                                   let uu____79925 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____79929 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____79925,
                                                     uu____79929)
                                                    in
                                                 let uu____79939 =
                                                   let uu____79953 =
                                                     let uu____79965 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____79969 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____79965,
                                                       uu____79969)
                                                      in
                                                   let uu____79979 =
                                                     let uu____79993 =
                                                       let uu____80005 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____80009 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____80005,
                                                         uu____80009)
                                                        in
                                                     let uu____80019 =
                                                       let uu____80033 =
                                                         let uu____80045 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____80049 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____80045,
                                                           uu____80049)
                                                          in
                                                       let uu____80059 =
                                                         let uu____80073 =
                                                           let uu____80085 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____80089 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____80085,
                                                             uu____80089)
                                                            in
                                                         let uu____80099 =
                                                           let uu____80113 =
                                                             let uu____80125
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____80129
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____80125,
                                                               uu____80129)
                                                              in
                                                           let uu____80139 =
                                                             let uu____80153
                                                               =
                                                               let uu____80165
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____80169
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____80165,
                                                                 uu____80169)
                                                                in
                                                             let uu____80179
                                                               =
                                                               let uu____80193
                                                                 =
                                                                 let uu____80205
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____80209
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____80205,
                                                                   uu____80209)
                                                                  in
                                                               let uu____80219
                                                                 =
                                                                 let uu____80233
                                                                   =
                                                                   let uu____80245
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____80249
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____80245,
                                                                    uu____80249)
                                                                    in
                                                                 let uu____80259
                                                                   =
                                                                   let uu____80273
                                                                    =
                                                                    let uu____80285
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____80289
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____80285,
                                                                    uu____80289)
                                                                     in
                                                                   let uu____80299
                                                                    =
                                                                    let uu____80313
                                                                    =
                                                                    let uu____80325
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____80329
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____80325,
                                                                    uu____80329)
                                                                     in
                                                                    let uu____80339
                                                                    =
                                                                    let uu____80353
                                                                    =
                                                                    let uu____80365
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____80369
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____80365,
                                                                    uu____80369)
                                                                     in
                                                                    let uu____80379
                                                                    =
                                                                    let uu____80393
                                                                    =
                                                                    let uu____80405
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____80409
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____80405,
                                                                    uu____80409)
                                                                     in
                                                                    let uu____80419
                                                                    =
                                                                    let uu____80433
                                                                    =
                                                                    let uu____80445
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____80449
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____80445,
                                                                    uu____80449)
                                                                     in
                                                                    let uu____80459
                                                                    =
                                                                    let uu____80473
                                                                    =
                                                                    let uu____80485
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____80489
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____80485,
                                                                    uu____80489)
                                                                     in
                                                                    let uu____80499
                                                                    =
                                                                    let uu____80513
                                                                    =
                                                                    let uu____80525
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____80529
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____80525,
                                                                    uu____80529)
                                                                     in
                                                                    let uu____80539
                                                                    =
                                                                    let uu____80553
                                                                    =
                                                                    let uu____80565
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____80569
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____80565,
                                                                    uu____80569)
                                                                     in
                                                                    let uu____80579
                                                                    =
                                                                    let uu____80593
                                                                    =
                                                                    let uu____80605
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____80609
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____80605,
                                                                    uu____80609)
                                                                     in
                                                                    let uu____80619
                                                                    =
                                                                    let uu____80633
                                                                    =
                                                                    let uu____80645
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____80649
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____80645,
                                                                    uu____80649)
                                                                     in
                                                                    let uu____80659
                                                                    =
                                                                    let uu____80673
                                                                    =
                                                                    let uu____80685
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____80689
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____80685,
                                                                    uu____80689)
                                                                     in
                                                                    let uu____80699
                                                                    =
                                                                    let uu____80713
                                                                    =
                                                                    let uu____80725
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____80729
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____80725,
                                                                    uu____80729)
                                                                     in
                                                                    let uu____80739
                                                                    =
                                                                    let uu____80753
                                                                    =
                                                                    let uu____80765
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____80769
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____80765,
                                                                    uu____80769)
                                                                     in
                                                                    let uu____80779
                                                                    =
                                                                    let uu____80793
                                                                    =
                                                                    let uu____80805
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____80809
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____80805,
                                                                    uu____80809)
                                                                     in
                                                                    let uu____80819
                                                                    =
                                                                    let uu____80833
                                                                    =
                                                                    let uu____80845
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____80849
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____80845,
                                                                    uu____80849)
                                                                     in
                                                                    let uu____80859
                                                                    =
                                                                    let uu____80873
                                                                    =
                                                                    let uu____80885
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____80889
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____80885,
                                                                    uu____80889)
                                                                     in
                                                                    let uu____80899
                                                                    =
                                                                    let uu____80913
                                                                    =
                                                                    let uu____80925
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____80929
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____80925,
                                                                    uu____80929)
                                                                     in
                                                                    let uu____80939
                                                                    =
                                                                    let uu____80953
                                                                    =
                                                                    let uu____80965
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____80969
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____80965,
                                                                    uu____80969)
                                                                     in
                                                                    let uu____80979
                                                                    =
                                                                    let uu____80993
                                                                    =
                                                                    let uu____81005
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____81009
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____81005,
                                                                    uu____81009)
                                                                     in
                                                                    let uu____81019
                                                                    =
                                                                    let uu____81033
                                                                    =
                                                                    let uu____81045
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____81049
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____81045,
                                                                    uu____81049)
                                                                     in
                                                                    let uu____81059
                                                                    =
                                                                    let uu____81073
                                                                    =
                                                                    let uu____81085
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____81089
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____81085,
                                                                    uu____81089)
                                                                     in
                                                                    let uu____81099
                                                                    =
                                                                    let uu____81113
                                                                    =
                                                                    let uu____81125
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____81129
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____81125,
                                                                    uu____81129)
                                                                     in
                                                                    let uu____81139
                                                                    =
                                                                    let uu____81153
                                                                    =
                                                                    let uu____81165
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____81169
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____81165,
                                                                    uu____81169)
                                                                     in
                                                                    let uu____81179
                                                                    =
                                                                    let uu____81193
                                                                    =
                                                                    let uu____81205
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____81209
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____81205,
                                                                    uu____81209)
                                                                     in
                                                                    [uu____81193]
                                                                     in
                                                                    uu____81153
                                                                    ::
                                                                    uu____81179
                                                                     in
                                                                    uu____81113
                                                                    ::
                                                                    uu____81139
                                                                     in
                                                                    uu____81073
                                                                    ::
                                                                    uu____81099
                                                                     in
                                                                    uu____81033
                                                                    ::
                                                                    uu____81059
                                                                     in
                                                                    uu____80993
                                                                    ::
                                                                    uu____81019
                                                                     in
                                                                    uu____80953
                                                                    ::
                                                                    uu____80979
                                                                     in
                                                                    uu____80913
                                                                    ::
                                                                    uu____80939
                                                                     in
                                                                    uu____80873
                                                                    ::
                                                                    uu____80899
                                                                     in
                                                                    uu____80833
                                                                    ::
                                                                    uu____80859
                                                                     in
                                                                    uu____80793
                                                                    ::
                                                                    uu____80819
                                                                     in
                                                                    uu____80753
                                                                    ::
                                                                    uu____80779
                                                                     in
                                                                    uu____80713
                                                                    ::
                                                                    uu____80739
                                                                     in
                                                                    uu____80673
                                                                    ::
                                                                    uu____80699
                                                                     in
                                                                    uu____80633
                                                                    ::
                                                                    uu____80659
                                                                     in
                                                                    uu____80593
                                                                    ::
                                                                    uu____80619
                                                                     in
                                                                    uu____80553
                                                                    ::
                                                                    uu____80579
                                                                     in
                                                                    uu____80513
                                                                    ::
                                                                    uu____80539
                                                                     in
                                                                    uu____80473
                                                                    ::
                                                                    uu____80499
                                                                     in
                                                                    uu____80433
                                                                    ::
                                                                    uu____80459
                                                                     in
                                                                    uu____80393
                                                                    ::
                                                                    uu____80419
                                                                     in
                                                                    uu____80353
                                                                    ::
                                                                    uu____80379
                                                                     in
                                                                    uu____80313
                                                                    ::
                                                                    uu____80339
                                                                     in
                                                                   uu____80273
                                                                    ::
                                                                    uu____80299
                                                                    in
                                                                 uu____80233
                                                                   ::
                                                                   uu____80259
                                                                  in
                                                               uu____80193 ::
                                                                 uu____80219
                                                                in
                                                             uu____80153 ::
                                                               uu____80179
                                                              in
                                                           uu____80113 ::
                                                             uu____80139
                                                            in
                                                         uu____80073 ::
                                                           uu____80099
                                                          in
                                                       uu____80033 ::
                                                         uu____80059
                                                        in
                                                     uu____79993 ::
                                                       uu____80019
                                                      in
                                                   uu____79953 :: uu____79979
                                                    in
                                                 uu____79913 :: uu____79939
                                                  in
                                               uu____79873 :: uu____79899  in
                                             uu____79833 :: uu____79859  in
                                           uu____79793 :: uu____79819  in
                                         uu____79751 :: uu____79779  in
                                       uu____79709 :: uu____79737  in
                                     uu____79642 :: uu____79695  in
                                   uu____79575 :: uu____79628  in
                                 uu____79508 :: uu____79561  in
                               uu____79464 :: uu____79494  in
                             uu____79423 :: uu____79450  in
                           uu____79382 :: uu____79409  in
                         uu____79343 :: uu____79368  in
                       uu____79308 :: uu____79329  in
                     uu____79273 :: uu____79294  in
                   uu____79238 :: uu____79259  in
                 uu____79203 :: uu____79224  in
               uu____79168 :: uu____79189  in
             uu____79116 :: uu____79154  in
           uu____79052 :: uu____79102  in
         uu____79003 :: uu____79038  in
       uu____78954 :: uu____78989  in
     uu____78912 :: uu____78940  in
   uu____78864 :: uu____78898)
  
let run_either :
  'Auu____81857 .
    Prims.int ->
      'Auu____81857 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____81857 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____81895 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____81895);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____81900 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____81900 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____81923 =
               let uu____81925 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____81925 expected  in
             FStar_Tests_Util.always i uu____81923)))
  
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
        let interp uu____82004 = run_interpreter i r expected  in
        let uu____82005 =
          let uu____82006 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____82006  in
        (i, uu____82005)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____82044 = run_nbe i r expected  in
        let uu____82045 =
          let uu____82046 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____82046  in
        (i, uu____82045)
  
let run_tests :
  'Auu____82057 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
           'Auu____82057)
      -> 'Auu____82057 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___742_82109  ->
            match uu___742_82109 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____82140  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____82143 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____82152  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____82155 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____82171  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____82201  ->
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
        let nbe1 uu____82246 = run_nbe i r expected  in
        let norm1 uu____82252 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____82265  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____82268 =
       let uu____82269 = encode (Prims.parse_int "1000")  in
       let uu____82271 =
         let uu____82274 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____82275 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____82274 uu____82275  in
       let_ FStar_Tests_Util.x uu____82269 uu____82271  in
     run_both_with_time (Prims.parse_int "14") uu____82268 z)
  
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
             let uu____82351 = res1  in
             match uu____82351 with
             | (t1,time_int) ->
                 let uu____82361 = res2  in
                 (match uu____82361 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____82373 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____82373 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____82384  ->
    (let uu____82386 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____82386);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  