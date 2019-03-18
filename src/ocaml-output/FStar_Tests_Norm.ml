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
      (let uu____77981 =
         let uu____77984 = encode (n1 - (Prims.parse_int "1"))  in
         [uu____77984]  in
       FStar_Tests_Util.app succ uu____77981)
  
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
        let uu____78023 =
          let uu____78026 = let uu____78027 = b x1  in [uu____78027]  in
          FStar_Syntax_Util.abs uu____78026 e' FStar_Pervasives_Native.None
           in
        FStar_Tests_Util.app uu____78023 [e]
  
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
  let uu____78097 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____78097
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____78100 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____78100
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
    let uu____78119 =
      let uu____78126 =
        let uu____78127 =
          let uu____78144 = tm_fv snat_l  in
          let uu____78147 =
            let uu____78158 = FStar_Syntax_Syntax.as_arg s  in [uu____78158]
             in
          (uu____78144, uu____78147)  in
        FStar_Syntax_Syntax.Tm_app uu____78127  in
      FStar_Syntax_Syntax.mk uu____78126  in
    uu____78119 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____78200 .
    'Auu____78200 -> 'Auu____78200 FStar_Syntax_Syntax.withinfo_t
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
      let uu____78309 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____78309, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____78353 =
        let uu____78356 =
          let uu____78357 =
            let uu____78371 =
              let uu____78381 =
                let uu____78389 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____78389, false)  in
              [uu____78381]  in
            (snat_l, uu____78371)  in
          FStar_Syntax_Syntax.Pat_cons uu____78357  in
        pat uu____78356  in
      let uu____78419 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___763_78424 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___763_78424.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___763_78424.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____78353, FStar_Pervasives_Native.None, uu____78419)  in
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
        let uu____78465 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____78484 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____78465, FStar_Pervasives_Native.None, uu____78484)  in
      let sbranch =
        let uu____78512 =
          let uu____78515 =
            let uu____78516 =
              let uu____78530 =
                let uu____78540 =
                  let uu____78548 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____78548, false)  in
                [uu____78540]  in
              (snat_l, uu____78530)  in
            FStar_Syntax_Syntax.Pat_cons uu____78516  in
          pat uu____78515  in
        let uu____78578 =
          let uu____78581 = FStar_Tests_Util.nm minus1  in
          let uu____78584 =
            let uu____78587 =
              let uu____78588 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____78588  in
            let uu____78591 =
              let uu____78594 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____78594]  in
            uu____78587 :: uu____78591  in
          FStar_Tests_Util.app uu____78581 uu____78584  in
        (uu____78512, FStar_Pervasives_Native.None, uu____78578)  in
      let lb =
        let uu____78606 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____78610 =
          let uu____78613 =
            let uu____78614 =
              let uu____78615 = b FStar_Tests_Util.x  in
              let uu____78622 =
                let uu____78631 = b FStar_Tests_Util.y  in [uu____78631]  in
              uu____78615 :: uu____78622  in
            let uu____78656 =
              let uu____78659 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____78659 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____78614 uu____78656
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____78613
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____78606;
          FStar_Syntax_Syntax.lbdef = uu____78610;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____78666 =
        let uu____78673 =
          let uu____78674 =
            let uu____78688 =
              let uu____78691 =
                let uu____78692 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____78692 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____78691
               in
            ((true, [lb]), uu____78688)  in
          FStar_Syntax_Syntax.Tm_let uu____78674  in
        FStar_Syntax_Syntax.mk uu____78673  in
      uu____78666 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____78736 = snat out  in
         aux uu____78736 (n2 - (Prims.parse_int "1")))
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
  (let uu____78802 =
     let uu____78814 =
       let uu____78817 =
         let uu____78820 =
           let uu____78823 =
             let uu____78826 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____78826]  in
           id :: uu____78823  in
         one :: uu____78820  in
       FStar_Tests_Util.app apply uu____78817  in
     let uu____78827 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____78814, uu____78827)  in
   let uu____78836 =
     let uu____78850 =
       let uu____78862 =
         let uu____78865 =
           let uu____78868 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____78868]  in
         FStar_Tests_Util.app id uu____78865  in
       let uu____78869 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____78862, uu____78869)  in
     let uu____78878 =
       let uu____78892 =
         let uu____78904 =
           let uu____78907 =
             let uu____78910 =
               let uu____78913 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____78914 =
                 let uu____78917 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____78917]  in
               uu____78913 :: uu____78914  in
             tt :: uu____78910  in
           FStar_Tests_Util.app apply uu____78907  in
         let uu____78918 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____78904, uu____78918)  in
       let uu____78927 =
         let uu____78941 =
           let uu____78953 =
             let uu____78956 =
               let uu____78959 =
                 let uu____78962 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____78963 =
                   let uu____78966 = FStar_Tests_Util.nm FStar_Tests_Util.m
                      in
                   [uu____78966]  in
                 uu____78962 :: uu____78963  in
               ff :: uu____78959  in
             FStar_Tests_Util.app apply uu____78956  in
           let uu____78967 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____78953, uu____78967)  in
         let uu____78976 =
           let uu____78990 =
             let uu____79002 =
               let uu____79005 =
                 let uu____79008 =
                   let uu____79011 =
                     let uu____79014 =
                       let uu____79017 =
                         let uu____79020 =
                           let uu____79023 =
                             let uu____79026 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____79027 =
                               let uu____79030 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____79030]  in
                             uu____79026 :: uu____79027  in
                           ff :: uu____79023  in
                         apply :: uu____79020  in
                       apply :: uu____79017  in
                     apply :: uu____79014  in
                   apply :: uu____79011  in
                 apply :: uu____79008  in
               FStar_Tests_Util.app apply uu____79005  in
             let uu____79031 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____79002, uu____79031)  in
           let uu____79040 =
             let uu____79054 =
               let uu____79066 =
                 let uu____79069 =
                   let uu____79072 =
                     let uu____79075 =
                       let uu____79078 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n  in
                       let uu____79079 =
                         let uu____79082 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____79082]  in
                       uu____79078 :: uu____79079  in
                     ff :: uu____79075  in
                   apply :: uu____79072  in
                 FStar_Tests_Util.app twice uu____79069  in
               let uu____79083 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____79066, uu____79083)  in
             let uu____79092 =
               let uu____79106 =
                 let uu____79118 = minus one z  in
                 ((Prims.parse_int "5"), uu____79118, one)  in
               let uu____79127 =
                 let uu____79141 =
                   let uu____79153 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____79153, z)  in
                 let uu____79162 =
                   let uu____79176 =
                     let uu____79188 = minus one one  in
                     ((Prims.parse_int "7"), uu____79188, z)  in
                   let uu____79197 =
                     let uu____79211 =
                       let uu____79223 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____79223, one)  in
                     let uu____79232 =
                       let uu____79246 =
                         let uu____79258 =
                           FStar_Tests_Util.app mul [two; one]  in
                         ((Prims.parse_int "9"), uu____79258, two)  in
                       let uu____79267 =
                         let uu____79281 =
                           let uu____79293 =
                             let uu____79296 =
                               let uu____79299 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____79299; one]  in
                             FStar_Tests_Util.app mul uu____79296  in
                           ((Prims.parse_int "10"), uu____79293, two)  in
                         let uu____79306 =
                           let uu____79320 =
                             let uu____79332 =
                               let uu____79335 =
                                 encode (Prims.parse_int "10")  in
                               let uu____79337 =
                                 encode (Prims.parse_int "10")  in
                               minus uu____79335 uu____79337  in
                             ((Prims.parse_int "11"), uu____79332, z)  in
                           let uu____79347 =
                             let uu____79361 =
                               let uu____79373 =
                                 let uu____79376 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____79378 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____79376 uu____79378  in
                               ((Prims.parse_int "12"), uu____79373, z)  in
                             let uu____79388 =
                               let uu____79402 =
                                 let uu____79414 =
                                   let uu____79417 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____79419 =
                                     let uu____79422 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____79423 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____79422 uu____79423  in
                                   let_ FStar_Tests_Util.x uu____79417
                                     uu____79419
                                    in
                                 ((Prims.parse_int "13"), uu____79414, z)  in
                               let uu____79432 =
                                 let uu____79446 =
                                   let uu____79458 =
                                     let uu____79461 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____79462 =
                                       let uu____79465 =
                                         let uu____79466 =
                                           let uu____79469 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____79470 =
                                             let uu____79473 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____79473]  in
                                           uu____79469 :: uu____79470  in
                                         FStar_Tests_Util.app mul uu____79466
                                          in
                                       let uu____79474 =
                                         let uu____79477 =
                                           let uu____79478 =
                                             let uu____79481 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____79482 =
                                               let uu____79485 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____79485]  in
                                             uu____79481 :: uu____79482  in
                                           FStar_Tests_Util.app mul
                                             uu____79478
                                            in
                                         let uu____79486 =
                                           let uu____79489 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____79490 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____79489 uu____79490  in
                                         let_ FStar_Tests_Util.h uu____79477
                                           uu____79486
                                          in
                                       let_ FStar_Tests_Util.y uu____79465
                                         uu____79474
                                        in
                                     let_ FStar_Tests_Util.x uu____79461
                                       uu____79462
                                      in
                                   ((Prims.parse_int "15"), uu____79458, z)
                                    in
                                 let uu____79499 =
                                   let uu____79513 =
                                     let uu____79525 =
                                       let uu____79528 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____79531 =
                                         let uu____79532 =
                                           let uu____79535 =
                                             let uu____79538 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____79539 =
                                               let uu____79542 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____79542]  in
                                             uu____79538 :: uu____79539  in
                                           FStar_Tests_Util.app mul
                                             uu____79535
                                            in
                                         let uu____79543 =
                                           let uu____79544 =
                                             let uu____79547 =
                                               let uu____79550 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____79551 =
                                                 let uu____79554 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____79554]  in
                                               uu____79550 :: uu____79551  in
                                             FStar_Tests_Util.app mul
                                               uu____79547
                                              in
                                           let uu____79555 =
                                             let uu____79556 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____79557 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____79556 uu____79557
                                              in
                                           mk_let FStar_Tests_Util.h
                                             uu____79544 uu____79555
                                            in
                                         mk_let FStar_Tests_Util.y
                                           uu____79532 uu____79543
                                          in
                                       mk_let FStar_Tests_Util.x uu____79528
                                         uu____79531
                                        in
                                     ((Prims.parse_int "16"), uu____79525, z)
                                      in
                                   let uu____79566 =
                                     let uu____79580 =
                                       let uu____79592 =
                                         let uu____79595 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____79596 =
                                           let uu____79599 =
                                             let uu____79600 =
                                               let uu____79603 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____79604 =
                                                 let uu____79607 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____79607]  in
                                               uu____79603 :: uu____79604  in
                                             FStar_Tests_Util.app mul
                                               uu____79600
                                              in
                                           let uu____79608 =
                                             let uu____79611 =
                                               let uu____79612 =
                                                 let uu____79615 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____79616 =
                                                   let uu____79619 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____79619]  in
                                                 uu____79615 :: uu____79616
                                                  in
                                               FStar_Tests_Util.app mul
                                                 uu____79612
                                                in
                                             let uu____79620 =
                                               let uu____79623 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____79624 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____79623 uu____79624
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____79611 uu____79620
                                              in
                                           let_ FStar_Tests_Util.y
                                             uu____79599 uu____79608
                                            in
                                         let_ FStar_Tests_Util.x uu____79595
                                           uu____79596
                                          in
                                       ((Prims.parse_int "17"), uu____79592,
                                         z)
                                        in
                                     let uu____79633 =
                                       let uu____79647 =
                                         let uu____79659 =
                                           let uu____79662 =
                                             let uu____79665 = snat znat  in
                                             snat uu____79665  in
                                           pred_nat uu____79662  in
                                         let uu____79666 = snat znat  in
                                         ((Prims.parse_int "18"),
                                           uu____79659, uu____79666)
                                          in
                                       let uu____79675 =
                                         let uu____79689 =
                                           let uu____79701 =
                                             let uu____79704 =
                                               let uu____79705 =
                                                 let uu____79706 = snat znat
                                                    in
                                                 snat uu____79706  in
                                               let uu____79707 = snat znat
                                                  in
                                               minus_nat uu____79705
                                                 uu____79707
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____79704
                                              in
                                           let uu____79708 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____79701, uu____79708)
                                            in
                                         let uu____79717 =
                                           let uu____79731 =
                                             let uu____79743 =
                                               let uu____79746 =
                                                 let uu____79747 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 let uu____79749 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 minus_nat uu____79747
                                                   uu____79749
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____79746
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____79743, znat)
                                              in
                                           let uu____79757 =
                                             let uu____79771 =
                                               let uu____79783 =
                                                 let uu____79786 =
                                                   let uu____79787 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   let uu____79789 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   minus_nat uu____79787
                                                     uu____79789
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____79786
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____79783, znat)
                                                in
                                             let uu____79797 =
                                               let uu____79811 =
                                                 let uu____79823 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____79827 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____79823, uu____79827)
                                                  in
                                               let uu____79837 =
                                                 let uu____79851 =
                                                   let uu____79863 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____79867 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____79863,
                                                     uu____79867)
                                                    in
                                                 let uu____79877 =
                                                   let uu____79891 =
                                                     let uu____79903 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____79907 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____79903,
                                                       uu____79907)
                                                      in
                                                   let uu____79917 =
                                                     let uu____79931 =
                                                       let uu____79943 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____79947 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____79943,
                                                         uu____79947)
                                                        in
                                                     let uu____79957 =
                                                       let uu____79971 =
                                                         let uu____79983 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____79987 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____79983,
                                                           uu____79987)
                                                          in
                                                       let uu____79997 =
                                                         let uu____80011 =
                                                           let uu____80023 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____80027 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____80023,
                                                             uu____80027)
                                                            in
                                                         let uu____80037 =
                                                           let uu____80051 =
                                                             let uu____80063
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____80067
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____80063,
                                                               uu____80067)
                                                              in
                                                           let uu____80077 =
                                                             let uu____80091
                                                               =
                                                               let uu____80103
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____80107
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____80103,
                                                                 uu____80107)
                                                                in
                                                             let uu____80117
                                                               =
                                                               let uu____80131
                                                                 =
                                                                 let uu____80143
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____80147
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____80143,
                                                                   uu____80147)
                                                                  in
                                                               let uu____80157
                                                                 =
                                                                 let uu____80171
                                                                   =
                                                                   let uu____80183
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____80187
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____80183,
                                                                    uu____80187)
                                                                    in
                                                                 let uu____80197
                                                                   =
                                                                   let uu____80211
                                                                    =
                                                                    let uu____80223
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____80227
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____80223,
                                                                    uu____80227)
                                                                     in
                                                                   let uu____80237
                                                                    =
                                                                    let uu____80251
                                                                    =
                                                                    let uu____80263
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____80267
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____80263,
                                                                    uu____80267)
                                                                     in
                                                                    let uu____80277
                                                                    =
                                                                    let uu____80291
                                                                    =
                                                                    let uu____80303
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____80307
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____80303,
                                                                    uu____80307)
                                                                     in
                                                                    let uu____80317
                                                                    =
                                                                    let uu____80331
                                                                    =
                                                                    let uu____80343
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____80347
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____80343,
                                                                    uu____80347)
                                                                     in
                                                                    let uu____80357
                                                                    =
                                                                    let uu____80371
                                                                    =
                                                                    let uu____80383
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____80387
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____80383,
                                                                    uu____80387)
                                                                     in
                                                                    let uu____80397
                                                                    =
                                                                    let uu____80411
                                                                    =
                                                                    let uu____80423
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____80427
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____80423,
                                                                    uu____80427)
                                                                     in
                                                                    let uu____80437
                                                                    =
                                                                    let uu____80451
                                                                    =
                                                                    let uu____80463
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____80467
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____80463,
                                                                    uu____80467)
                                                                     in
                                                                    let uu____80477
                                                                    =
                                                                    let uu____80491
                                                                    =
                                                                    let uu____80503
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____80507
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____80503,
                                                                    uu____80507)
                                                                     in
                                                                    let uu____80517
                                                                    =
                                                                    let uu____80531
                                                                    =
                                                                    let uu____80543
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____80547
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____80543,
                                                                    uu____80547)
                                                                     in
                                                                    let uu____80557
                                                                    =
                                                                    let uu____80571
                                                                    =
                                                                    let uu____80583
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____80587
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____80583,
                                                                    uu____80587)
                                                                     in
                                                                    let uu____80597
                                                                    =
                                                                    let uu____80611
                                                                    =
                                                                    let uu____80623
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____80627
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____80623,
                                                                    uu____80627)
                                                                     in
                                                                    let uu____80637
                                                                    =
                                                                    let uu____80651
                                                                    =
                                                                    let uu____80663
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____80667
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____80663,
                                                                    uu____80667)
                                                                     in
                                                                    let uu____80677
                                                                    =
                                                                    let uu____80691
                                                                    =
                                                                    let uu____80703
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____80707
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____80703,
                                                                    uu____80707)
                                                                     in
                                                                    let uu____80717
                                                                    =
                                                                    let uu____80731
                                                                    =
                                                                    let uu____80743
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____80747
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____80743,
                                                                    uu____80747)
                                                                     in
                                                                    let uu____80757
                                                                    =
                                                                    let uu____80771
                                                                    =
                                                                    let uu____80783
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____80787
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____80783,
                                                                    uu____80787)
                                                                     in
                                                                    let uu____80797
                                                                    =
                                                                    let uu____80811
                                                                    =
                                                                    let uu____80823
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____80827
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____80823,
                                                                    uu____80827)
                                                                     in
                                                                    let uu____80837
                                                                    =
                                                                    let uu____80851
                                                                    =
                                                                    let uu____80863
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____80867
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____80863,
                                                                    uu____80867)
                                                                     in
                                                                    let uu____80877
                                                                    =
                                                                    let uu____80891
                                                                    =
                                                                    let uu____80903
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____80907
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____80903,
                                                                    uu____80907)
                                                                     in
                                                                    let uu____80917
                                                                    =
                                                                    let uu____80931
                                                                    =
                                                                    let uu____80943
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____80947
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____80943,
                                                                    uu____80947)
                                                                     in
                                                                    let uu____80957
                                                                    =
                                                                    let uu____80971
                                                                    =
                                                                    let uu____80983
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____80987
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____80983,
                                                                    uu____80987)
                                                                     in
                                                                    let uu____80997
                                                                    =
                                                                    let uu____81011
                                                                    =
                                                                    let uu____81023
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____81027
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____81023,
                                                                    uu____81027)
                                                                     in
                                                                    let uu____81037
                                                                    =
                                                                    let uu____81051
                                                                    =
                                                                    let uu____81063
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____81067
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____81063,
                                                                    uu____81067)
                                                                     in
                                                                    let uu____81077
                                                                    =
                                                                    let uu____81091
                                                                    =
                                                                    let uu____81103
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____81107
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____81103,
                                                                    uu____81107)
                                                                     in
                                                                    let uu____81117
                                                                    =
                                                                    let uu____81131
                                                                    =
                                                                    let uu____81143
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____81147
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____81143,
                                                                    uu____81147)
                                                                     in
                                                                    [uu____81131]
                                                                     in
                                                                    uu____81091
                                                                    ::
                                                                    uu____81117
                                                                     in
                                                                    uu____81051
                                                                    ::
                                                                    uu____81077
                                                                     in
                                                                    uu____81011
                                                                    ::
                                                                    uu____81037
                                                                     in
                                                                    uu____80971
                                                                    ::
                                                                    uu____80997
                                                                     in
                                                                    uu____80931
                                                                    ::
                                                                    uu____80957
                                                                     in
                                                                    uu____80891
                                                                    ::
                                                                    uu____80917
                                                                     in
                                                                    uu____80851
                                                                    ::
                                                                    uu____80877
                                                                     in
                                                                    uu____80811
                                                                    ::
                                                                    uu____80837
                                                                     in
                                                                    uu____80771
                                                                    ::
                                                                    uu____80797
                                                                     in
                                                                    uu____80731
                                                                    ::
                                                                    uu____80757
                                                                     in
                                                                    uu____80691
                                                                    ::
                                                                    uu____80717
                                                                     in
                                                                    uu____80651
                                                                    ::
                                                                    uu____80677
                                                                     in
                                                                    uu____80611
                                                                    ::
                                                                    uu____80637
                                                                     in
                                                                    uu____80571
                                                                    ::
                                                                    uu____80597
                                                                     in
                                                                    uu____80531
                                                                    ::
                                                                    uu____80557
                                                                     in
                                                                    uu____80491
                                                                    ::
                                                                    uu____80517
                                                                     in
                                                                    uu____80451
                                                                    ::
                                                                    uu____80477
                                                                     in
                                                                    uu____80411
                                                                    ::
                                                                    uu____80437
                                                                     in
                                                                    uu____80371
                                                                    ::
                                                                    uu____80397
                                                                     in
                                                                    uu____80331
                                                                    ::
                                                                    uu____80357
                                                                     in
                                                                    uu____80291
                                                                    ::
                                                                    uu____80317
                                                                     in
                                                                    uu____80251
                                                                    ::
                                                                    uu____80277
                                                                     in
                                                                   uu____80211
                                                                    ::
                                                                    uu____80237
                                                                    in
                                                                 uu____80171
                                                                   ::
                                                                   uu____80197
                                                                  in
                                                               uu____80131 ::
                                                                 uu____80157
                                                                in
                                                             uu____80091 ::
                                                               uu____80117
                                                              in
                                                           uu____80051 ::
                                                             uu____80077
                                                            in
                                                         uu____80011 ::
                                                           uu____80037
                                                          in
                                                       uu____79971 ::
                                                         uu____79997
                                                        in
                                                     uu____79931 ::
                                                       uu____79957
                                                      in
                                                   uu____79891 :: uu____79917
                                                    in
                                                 uu____79851 :: uu____79877
                                                  in
                                               uu____79811 :: uu____79837  in
                                             uu____79771 :: uu____79797  in
                                           uu____79731 :: uu____79757  in
                                         uu____79689 :: uu____79717  in
                                       uu____79647 :: uu____79675  in
                                     uu____79580 :: uu____79633  in
                                   uu____79513 :: uu____79566  in
                                 uu____79446 :: uu____79499  in
                               uu____79402 :: uu____79432  in
                             uu____79361 :: uu____79388  in
                           uu____79320 :: uu____79347  in
                         uu____79281 :: uu____79306  in
                       uu____79246 :: uu____79267  in
                     uu____79211 :: uu____79232  in
                   uu____79176 :: uu____79197  in
                 uu____79141 :: uu____79162  in
               uu____79106 :: uu____79127  in
             uu____79054 :: uu____79092  in
           uu____78990 :: uu____79040  in
         uu____78941 :: uu____78976  in
       uu____78892 :: uu____78927  in
     uu____78850 :: uu____78878  in
   uu____78802 :: uu____78836)
  
let run_either :
  'Auu____81795 .
    Prims.int ->
      'Auu____81795 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____81795 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____81833 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____81833);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____81838 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____81838 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____81861 =
               let uu____81863 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____81863 expected  in
             FStar_Tests_Util.always i uu____81861)))
  
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
        let interp uu____81942 = run_interpreter i r expected  in
        let uu____81943 =
          let uu____81944 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____81944  in
        (i, uu____81943)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____81982 = run_nbe i r expected  in
        let uu____81983 =
          let uu____81984 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____81984  in
        (i, uu____81983)
  
let run_tests :
  'Auu____81995 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
           'Auu____81995)
      -> 'Auu____81995 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___742_82047  ->
            match uu___742_82047 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____82078  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____82081 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____82090  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____82093 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____82109  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____82139  ->
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
        let nbe1 uu____82184 = run_nbe i r expected  in
        let norm1 uu____82190 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____82203  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____82206 =
       let uu____82207 = encode (Prims.parse_int "1000")  in
       let uu____82209 =
         let uu____82212 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____82213 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____82212 uu____82213  in
       let_ FStar_Tests_Util.x uu____82207 uu____82209  in
     run_both_with_time (Prims.parse_int "14") uu____82206 z)
  
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
             let uu____82289 = res1  in
             match uu____82289 with
             | (t1,time_int) ->
                 let uu____82299 = res2  in
                 (match uu____82299 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____82311 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____82311 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____82322  ->
    (let uu____82324 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____82324);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  