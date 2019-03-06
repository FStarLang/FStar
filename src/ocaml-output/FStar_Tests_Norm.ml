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
      (let uu____78939 =
         let uu____78942 = encode (n1 - (Prims.parse_int "1"))  in
         [uu____78942]  in
       FStar_Tests_Util.app succ uu____78939)
  
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
        let uu____78981 =
          let uu____78984 = let uu____78985 = b x1  in [uu____78985]  in
          FStar_Syntax_Util.abs uu____78984 e' FStar_Pervasives_Native.None
           in
        FStar_Tests_Util.app uu____78981 [e]
  
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
  let uu____79055 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____79055
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____79058 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____79058
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
    let uu____79077 =
      let uu____79084 =
        let uu____79085 =
          let uu____79102 = tm_fv snat_l  in
          let uu____79105 =
            let uu____79116 = FStar_Syntax_Syntax.as_arg s  in [uu____79116]
             in
          (uu____79102, uu____79105)  in
        FStar_Syntax_Syntax.Tm_app uu____79085  in
      FStar_Syntax_Syntax.mk uu____79084  in
    uu____79077 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____79158 .
    'Auu____79158 -> 'Auu____79158 FStar_Syntax_Syntax.withinfo_t
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
      let uu____79267 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____79267, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____79311 =
        let uu____79314 =
          let uu____79315 =
            let uu____79329 =
              let uu____79339 =
                let uu____79347 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____79347, false)  in
              [uu____79339]  in
            (snat_l, uu____79329)  in
          FStar_Syntax_Syntax.Pat_cons uu____79315  in
        pat uu____79314  in
      let uu____79377 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___763_79382 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___763_79382.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___763_79382.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____79311, FStar_Pervasives_Native.None, uu____79377)  in
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
        let uu____79423 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____79442 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____79423, FStar_Pervasives_Native.None, uu____79442)  in
      let sbranch =
        let uu____79470 =
          let uu____79473 =
            let uu____79474 =
              let uu____79488 =
                let uu____79498 =
                  let uu____79506 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____79506, false)  in
                [uu____79498]  in
              (snat_l, uu____79488)  in
            FStar_Syntax_Syntax.Pat_cons uu____79474  in
          pat uu____79473  in
        let uu____79536 =
          let uu____79539 = FStar_Tests_Util.nm minus1  in
          let uu____79542 =
            let uu____79545 =
              let uu____79546 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____79546  in
            let uu____79549 =
              let uu____79552 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____79552]  in
            uu____79545 :: uu____79549  in
          FStar_Tests_Util.app uu____79539 uu____79542  in
        (uu____79470, FStar_Pervasives_Native.None, uu____79536)  in
      let lb =
        let uu____79564 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____79568 =
          let uu____79571 =
            let uu____79572 =
              let uu____79573 = b FStar_Tests_Util.x  in
              let uu____79580 =
                let uu____79589 = b FStar_Tests_Util.y  in [uu____79589]  in
              uu____79573 :: uu____79580  in
            let uu____79614 =
              let uu____79617 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____79617 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____79572 uu____79614
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____79571
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____79564;
          FStar_Syntax_Syntax.lbdef = uu____79568;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        }  in
      let uu____79624 =
        let uu____79631 =
          let uu____79632 =
            let uu____79646 =
              let uu____79649 =
                let uu____79650 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____79650 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____79649
               in
            ((true, [lb]), uu____79646)  in
          FStar_Syntax_Syntax.Tm_let uu____79632  in
        FStar_Syntax_Syntax.mk uu____79631  in
      uu____79624 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____79694 = snat out  in
         aux uu____79694 (n2 - (Prims.parse_int "1")))
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
  (let uu____79760 =
     let uu____79772 =
       let uu____79775 =
         let uu____79778 =
           let uu____79781 =
             let uu____79784 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____79784]  in
           id :: uu____79781  in
         one :: uu____79778  in
       FStar_Tests_Util.app apply uu____79775  in
     let uu____79785 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____79772, uu____79785)  in
   let uu____79794 =
     let uu____79808 =
       let uu____79820 =
         let uu____79823 =
           let uu____79826 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
           [uu____79826]  in
         FStar_Tests_Util.app id uu____79823  in
       let uu____79827 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
       ((Prims.parse_int "1"), uu____79820, uu____79827)  in
     let uu____79836 =
       let uu____79850 =
         let uu____79862 =
           let uu____79865 =
             let uu____79868 =
               let uu____79871 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
               let uu____79872 =
                 let uu____79875 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
                 [uu____79875]  in
               uu____79871 :: uu____79872  in
             tt :: uu____79868  in
           FStar_Tests_Util.app apply uu____79865  in
         let uu____79876 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
         ((Prims.parse_int "1"), uu____79862, uu____79876)  in
       let uu____79885 =
         let uu____79899 =
           let uu____79911 =
             let uu____79914 =
               let uu____79917 =
                 let uu____79920 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
                 let uu____79921 =
                   let uu____79924 = FStar_Tests_Util.nm FStar_Tests_Util.m
                      in
                   [uu____79924]  in
                 uu____79920 :: uu____79921  in
               ff :: uu____79917  in
             FStar_Tests_Util.app apply uu____79914  in
           let uu____79925 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
           ((Prims.parse_int "2"), uu____79911, uu____79925)  in
         let uu____79934 =
           let uu____79948 =
             let uu____79960 =
               let uu____79963 =
                 let uu____79966 =
                   let uu____79969 =
                     let uu____79972 =
                       let uu____79975 =
                         let uu____79978 =
                           let uu____79981 =
                             let uu____79984 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n  in
                             let uu____79985 =
                               let uu____79988 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m  in
                               [uu____79988]  in
                             uu____79984 :: uu____79985  in
                           ff :: uu____79981  in
                         apply :: uu____79978  in
                       apply :: uu____79975  in
                     apply :: uu____79972  in
                   apply :: uu____79969  in
                 apply :: uu____79966  in
               FStar_Tests_Util.app apply uu____79963  in
             let uu____79989 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
             ((Prims.parse_int "3"), uu____79960, uu____79989)  in
           let uu____79998 =
             let uu____80012 =
               let uu____80024 =
                 let uu____80027 =
                   let uu____80030 =
                     let uu____80033 =
                       let uu____80036 =
                         FStar_Tests_Util.nm FStar_Tests_Util.n  in
                       let uu____80037 =
                         let uu____80040 =
                           FStar_Tests_Util.nm FStar_Tests_Util.m  in
                         [uu____80040]  in
                       uu____80036 :: uu____80037  in
                     ff :: uu____80033  in
                   apply :: uu____80030  in
                 FStar_Tests_Util.app twice uu____80027  in
               let uu____80041 = FStar_Tests_Util.nm FStar_Tests_Util.m  in
               ((Prims.parse_int "4"), uu____80024, uu____80041)  in
             let uu____80050 =
               let uu____80064 =
                 let uu____80076 = minus one z  in
                 ((Prims.parse_int "5"), uu____80076, one)  in
               let uu____80085 =
                 let uu____80099 =
                   let uu____80111 = FStar_Tests_Util.app pred [one]  in
                   ((Prims.parse_int "6"), uu____80111, z)  in
                 let uu____80120 =
                   let uu____80134 =
                     let uu____80146 = minus one one  in
                     ((Prims.parse_int "7"), uu____80146, z)  in
                   let uu____80155 =
                     let uu____80169 =
                       let uu____80181 = FStar_Tests_Util.app mul [one; one]
                          in
                       ((Prims.parse_int "8"), uu____80181, one)  in
                     let uu____80190 =
                       let uu____80204 =
                         let uu____80216 =
                           FStar_Tests_Util.app mul [two; one]  in
                         ((Prims.parse_int "9"), uu____80216, two)  in
                       let uu____80225 =
                         let uu____80239 =
                           let uu____80251 =
                             let uu____80254 =
                               let uu____80257 =
                                 FStar_Tests_Util.app succ [one]  in
                               [uu____80257; one]  in
                             FStar_Tests_Util.app mul uu____80254  in
                           ((Prims.parse_int "10"), uu____80251, two)  in
                         let uu____80264 =
                           let uu____80278 =
                             let uu____80290 =
                               let uu____80293 =
                                 encode (Prims.parse_int "10")  in
                               let uu____80295 =
                                 encode (Prims.parse_int "10")  in
                               minus uu____80293 uu____80295  in
                             ((Prims.parse_int "11"), uu____80290, z)  in
                           let uu____80305 =
                             let uu____80319 =
                               let uu____80331 =
                                 let uu____80334 =
                                   encode (Prims.parse_int "100")  in
                                 let uu____80336 =
                                   encode (Prims.parse_int "100")  in
                                 minus uu____80334 uu____80336  in
                               ((Prims.parse_int "12"), uu____80331, z)  in
                             let uu____80346 =
                               let uu____80360 =
                                 let uu____80372 =
                                   let uu____80375 =
                                     encode (Prims.parse_int "100")  in
                                   let uu____80377 =
                                     let uu____80380 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     let uu____80381 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x
                                        in
                                     minus uu____80380 uu____80381  in
                                   let_ FStar_Tests_Util.x uu____80375
                                     uu____80377
                                    in
                                 ((Prims.parse_int "13"), uu____80372, z)  in
                               let uu____80390 =
                                 let uu____80404 =
                                   let uu____80416 =
                                     let uu____80419 =
                                       FStar_Tests_Util.app succ [one]  in
                                     let uu____80420 =
                                       let uu____80423 =
                                         let uu____80424 =
                                           let uu____80427 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x
                                              in
                                           let uu____80428 =
                                             let uu____80431 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             [uu____80431]  in
                                           uu____80427 :: uu____80428  in
                                         FStar_Tests_Util.app mul uu____80424
                                          in
                                       let uu____80432 =
                                         let uu____80435 =
                                           let uu____80436 =
                                             let uu____80439 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y
                                                in
                                             let uu____80440 =
                                               let uu____80443 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               [uu____80443]  in
                                             uu____80439 :: uu____80440  in
                                           FStar_Tests_Util.app mul
                                             uu____80436
                                            in
                                         let uu____80444 =
                                           let uu____80447 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           let uu____80448 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h
                                              in
                                           minus uu____80447 uu____80448  in
                                         let_ FStar_Tests_Util.h uu____80435
                                           uu____80444
                                          in
                                       let_ FStar_Tests_Util.y uu____80423
                                         uu____80432
                                        in
                                     let_ FStar_Tests_Util.x uu____80419
                                       uu____80420
                                      in
                                   ((Prims.parse_int "15"), uu____80416, z)
                                    in
                                 let uu____80457 =
                                   let uu____80471 =
                                     let uu____80483 =
                                       let uu____80486 =
                                         FStar_Tests_Util.app succ [one]  in
                                       let uu____80489 =
                                         let uu____80490 =
                                           let uu____80493 =
                                             let uu____80496 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x
                                                in
                                             let uu____80497 =
                                               let uu____80500 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               [uu____80500]  in
                                             uu____80496 :: uu____80497  in
                                           FStar_Tests_Util.app mul
                                             uu____80493
                                            in
                                         let uu____80501 =
                                           let uu____80502 =
                                             let uu____80505 =
                                               let uu____80508 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y
                                                  in
                                               let uu____80509 =
                                                 let uu____80512 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 [uu____80512]  in
                                               uu____80508 :: uu____80509  in
                                             FStar_Tests_Util.app mul
                                               uu____80505
                                              in
                                           let uu____80513 =
                                             let uu____80514 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             let uu____80515 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h
                                                in
                                             minus uu____80514 uu____80515
                                              in
                                           mk_let FStar_Tests_Util.h
                                             uu____80502 uu____80513
                                            in
                                         mk_let FStar_Tests_Util.y
                                           uu____80490 uu____80501
                                          in
                                       mk_let FStar_Tests_Util.x uu____80486
                                         uu____80489
                                        in
                                     ((Prims.parse_int "16"), uu____80483, z)
                                      in
                                   let uu____80524 =
                                     let uu____80538 =
                                       let uu____80550 =
                                         let uu____80553 =
                                           FStar_Tests_Util.app succ [one]
                                            in
                                         let uu____80554 =
                                           let uu____80557 =
                                             let uu____80558 =
                                               let uu____80561 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x
                                                  in
                                               let uu____80562 =
                                                 let uu____80565 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x
                                                    in
                                                 [uu____80565]  in
                                               uu____80561 :: uu____80562  in
                                             FStar_Tests_Util.app mul
                                               uu____80558
                                              in
                                           let uu____80566 =
                                             let uu____80569 =
                                               let uu____80570 =
                                                 let uu____80573 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y
                                                    in
                                                 let uu____80574 =
                                                   let uu____80577 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y
                                                      in
                                                   [uu____80577]  in
                                                 uu____80573 :: uu____80574
                                                  in
                                               FStar_Tests_Util.app mul
                                                 uu____80570
                                                in
                                             let uu____80578 =
                                               let uu____80581 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               let uu____80582 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h
                                                  in
                                               minus uu____80581 uu____80582
                                                in
                                             let_ FStar_Tests_Util.h
                                               uu____80569 uu____80578
                                              in
                                           let_ FStar_Tests_Util.y
                                             uu____80557 uu____80566
                                            in
                                         let_ FStar_Tests_Util.x uu____80553
                                           uu____80554
                                          in
                                       ((Prims.parse_int "17"), uu____80550,
                                         z)
                                        in
                                     let uu____80591 =
                                       let uu____80605 =
                                         let uu____80617 =
                                           let uu____80620 =
                                             let uu____80623 = snat znat  in
                                             snat uu____80623  in
                                           pred_nat uu____80620  in
                                         let uu____80624 = snat znat  in
                                         ((Prims.parse_int "18"),
                                           uu____80617, uu____80624)
                                          in
                                       let uu____80633 =
                                         let uu____80647 =
                                           let uu____80659 =
                                             let uu____80662 =
                                               let uu____80663 =
                                                 let uu____80664 = snat znat
                                                    in
                                                 snat uu____80664  in
                                               let uu____80665 = snat znat
                                                  in
                                               minus_nat uu____80663
                                                 uu____80665
                                                in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu____80662
                                              in
                                           let uu____80666 = snat znat  in
                                           ((Prims.parse_int "19"),
                                             uu____80659, uu____80666)
                                            in
                                         let uu____80675 =
                                           let uu____80689 =
                                             let uu____80701 =
                                               let uu____80704 =
                                                 let uu____80705 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 let uu____80707 =
                                                   encode_nat
                                                     (Prims.parse_int "10")
                                                    in
                                                 minus_nat uu____80705
                                                   uu____80707
                                                  in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu____80704
                                                in
                                             ((Prims.parse_int "20"),
                                               uu____80701, znat)
                                              in
                                           let uu____80715 =
                                             let uu____80729 =
                                               let uu____80741 =
                                                 let uu____80744 =
                                                   let uu____80745 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   let uu____80747 =
                                                     encode_nat
                                                       (Prims.parse_int "100")
                                                      in
                                                   minus_nat uu____80745
                                                     uu____80747
                                                    in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu____80744
                                                  in
                                               ((Prims.parse_int "21"),
                                                 uu____80741, znat)
                                                in
                                             let uu____80755 =
                                               let uu____80769 =
                                                 let uu____80781 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]"
                                                    in
                                                 let uu____80785 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]"
                                                    in
                                                 ((Prims.parse_int "24"),
                                                   uu____80781, uu____80785)
                                                  in
                                               let uu____80795 =
                                                 let uu____80809 =
                                                   let uu____80821 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]"
                                                      in
                                                   let uu____80825 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]"
                                                      in
                                                   ((Prims.parse_int "241"),
                                                     uu____80821,
                                                     uu____80825)
                                                    in
                                                 let uu____80835 =
                                                   let uu____80849 =
                                                     let uu____80861 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]"
                                                        in
                                                     let uu____80865 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]"
                                                        in
                                                     ((Prims.parse_int "25"),
                                                       uu____80861,
                                                       uu____80865)
                                                      in
                                                   let uu____80875 =
                                                     let uu____80889 =
                                                       let uu____80901 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]"
                                                          in
                                                       let uu____80905 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]"
                                                          in
                                                       ((Prims.parse_int "26"),
                                                         uu____80901,
                                                         uu____80905)
                                                        in
                                                     let uu____80915 =
                                                       let uu____80929 =
                                                         let uu____80941 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T"
                                                            in
                                                         let uu____80945 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F"
                                                            in
                                                         ((Prims.parse_int "28"),
                                                           uu____80941,
                                                           uu____80945)
                                                          in
                                                       let uu____80955 =
                                                         let uu____80969 =
                                                           let uu____80981 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           let uu____80985 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]"
                                                              in
                                                           ((Prims.parse_int "29"),
                                                             uu____80981,
                                                             uu____80985)
                                                            in
                                                         let uu____80995 =
                                                           let uu____81009 =
                                                             let uu____81021
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T"
                                                                in
                                                             let uu____81025
                                                               =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T"
                                                                in
                                                             ((Prims.parse_int "31"),
                                                               uu____81021,
                                                               uu____81025)
                                                              in
                                                           let uu____81035 =
                                                             let uu____81049
                                                               =
                                                               let uu____81061
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T"
                                                                  in
                                                               let uu____81065
                                                                 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T"
                                                                  in
                                                               ((Prims.parse_int "32"),
                                                                 uu____81061,
                                                                 uu____81065)
                                                                in
                                                             let uu____81075
                                                               =
                                                               let uu____81089
                                                                 =
                                                                 let uu____81101
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T"
                                                                    in
                                                                 let uu____81105
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F"
                                                                    in
                                                                 ((Prims.parse_int "33"),
                                                                   uu____81101,
                                                                   uu____81105)
                                                                  in
                                                               let uu____81115
                                                                 =
                                                                 let uu____81129
                                                                   =
                                                                   let uu____81141
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F"
                                                                     in
                                                                   let uu____81145
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                   ((Prims.parse_int "34"),
                                                                    uu____81141,
                                                                    uu____81145)
                                                                    in
                                                                 let uu____81155
                                                                   =
                                                                   let uu____81169
                                                                    =
                                                                    let uu____81181
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F"
                                                                     in
                                                                    let uu____81185
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "35"),
                                                                    uu____81181,
                                                                    uu____81185)
                                                                     in
                                                                   let uu____81195
                                                                    =
                                                                    let uu____81209
                                                                    =
                                                                    let uu____81221
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____81225
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "36"),
                                                                    uu____81221,
                                                                    uu____81225)
                                                                     in
                                                                    let uu____81235
                                                                    =
                                                                    let uu____81249
                                                                    =
                                                                    let uu____81261
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]"
                                                                     in
                                                                    let uu____81265
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "301"),
                                                                    uu____81261,
                                                                    uu____81265)
                                                                     in
                                                                    let uu____81275
                                                                    =
                                                                    let uu____81289
                                                                    =
                                                                    let uu____81301
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]"
                                                                     in
                                                                    let uu____81305
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "3012"),
                                                                    uu____81301,
                                                                    uu____81305)
                                                                     in
                                                                    let uu____81315
                                                                    =
                                                                    let uu____81329
                                                                    =
                                                                    let uu____81341
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]"
                                                                     in
                                                                    let uu____81345
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]"
                                                                     in
                                                                    ((Prims.parse_int "302"),
                                                                    uu____81341,
                                                                    uu____81345)
                                                                     in
                                                                    let uu____81355
                                                                    =
                                                                    let uu____81369
                                                                    =
                                                                    let uu____81381
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3"
                                                                     in
                                                                    let uu____81385
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1"  in
                                                                    ((Prims.parse_int "303"),
                                                                    uu____81381,
                                                                    uu____81385)
                                                                     in
                                                                    let uu____81395
                                                                    =
                                                                    let uu____81409
                                                                    =
                                                                    let uu____81421
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4"
                                                                     in
                                                                    let uu____81425
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3"  in
                                                                    ((Prims.parse_int "3031"),
                                                                    uu____81421,
                                                                    uu____81425)
                                                                     in
                                                                    let uu____81435
                                                                    =
                                                                    let uu____81449
                                                                    =
                                                                    let uu____81461
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4"
                                                                     in
                                                                    let uu____81465
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4"  in
                                                                    ((Prims.parse_int "3032"),
                                                                    uu____81461,
                                                                    uu____81465)
                                                                     in
                                                                    let uu____81475
                                                                    =
                                                                    let uu____81489
                                                                    =
                                                                    let uu____81501
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9"
                                                                     in
                                                                    let uu____81505
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8"  in
                                                                    ((Prims.parse_int "3033"),
                                                                    uu____81501,
                                                                    uu____81505)
                                                                     in
                                                                    let uu____81515
                                                                    =
                                                                    let uu____81529
                                                                    =
                                                                    let uu____81541
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    let uu____81545
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]"  in
                                                                    ((Prims.parse_int "3034"),
                                                                    uu____81541,
                                                                    uu____81545)
                                                                     in
                                                                    let uu____81555
                                                                    =
                                                                    let uu____81569
                                                                    =
                                                                    let uu____81581
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    let uu____81585
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]"
                                                                     in
                                                                    ((Prims.parse_int "3035"),
                                                                    uu____81581,
                                                                    uu____81585)
                                                                     in
                                                                    let uu____81595
                                                                    =
                                                                    let uu____81609
                                                                    =
                                                                    let uu____81621
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7"
                                                                     in
                                                                    let uu____81625
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "3036"),
                                                                    uu____81621,
                                                                    uu____81625)
                                                                     in
                                                                    let uu____81635
                                                                    =
                                                                    let uu____81649
                                                                    =
                                                                    let uu____81661
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T"
                                                                     in
                                                                    let uu____81665
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T"  in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____81661,
                                                                    uu____81665)
                                                                     in
                                                                    let uu____81675
                                                                    =
                                                                    let uu____81689
                                                                    =
                                                                    let uu____81701
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]"
                                                                     in
                                                                    let uu____81705
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]"  in
                                                                    ((Prims.parse_int "306"),
                                                                    uu____81701,
                                                                    uu____81705)
                                                                     in
                                                                    let uu____81715
                                                                    =
                                                                    let uu____81729
                                                                    =
                                                                    let uu____81741
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____81745
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "307"),
                                                                    uu____81741,
                                                                    uu____81745)
                                                                     in
                                                                    let uu____81755
                                                                    =
                                                                    let uu____81769
                                                                    =
                                                                    let uu____81781
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]"
                                                                     in
                                                                    let uu____81785
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]"
                                                                     in
                                                                    ((Prims.parse_int "308"),
                                                                    uu____81781,
                                                                    uu____81785)
                                                                     in
                                                                    let uu____81795
                                                                    =
                                                                    let uu____81809
                                                                    =
                                                                    let uu____81821
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]"
                                                                     in
                                                                    let uu____81825
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]"
                                                                     in
                                                                    ((Prims.parse_int "304"),
                                                                    uu____81821,
                                                                    uu____81825)
                                                                     in
                                                                    let uu____81835
                                                                    =
                                                                    let uu____81849
                                                                    =
                                                                    let uu____81861
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]"
                                                                     in
                                                                    let uu____81865
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]"
                                                                     in
                                                                    ((Prims.parse_int "305"),
                                                                    uu____81861,
                                                                    uu____81865)
                                                                     in
                                                                    let uu____81875
                                                                    =
                                                                    let uu____81889
                                                                    =
                                                                    let uu____81901
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1"  in
                                                                    let uu____81905
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6"  in
                                                                    ((Prims.parse_int "309"),
                                                                    uu____81901,
                                                                    uu____81905)
                                                                     in
                                                                    let uu____81915
                                                                    =
                                                                    let uu____81929
                                                                    =
                                                                    let uu____81941
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2"  in
                                                                    let uu____81945
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2"  in
                                                                    ((Prims.parse_int "310"),
                                                                    uu____81941,
                                                                    uu____81945)
                                                                     in
                                                                    let uu____81955
                                                                    =
                                                                    let uu____81969
                                                                    =
                                                                    let uu____81981
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3"
                                                                     in
                                                                    let uu____81985
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10"  in
                                                                    ((Prims.parse_int "401"),
                                                                    uu____81981,
                                                                    uu____81985)
                                                                     in
                                                                    let uu____81995
                                                                    =
                                                                    let uu____82009
                                                                    =
                                                                    let uu____82021
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false"
                                                                     in
                                                                    let uu____82025
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "402"),
                                                                    uu____82021,
                                                                    uu____82025)
                                                                     in
                                                                    let uu____82035
                                                                    =
                                                                    let uu____82049
                                                                    =
                                                                    let uu____82061
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5"
                                                                     in
                                                                    let uu____82065
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false"
                                                                     in
                                                                    ((Prims.parse_int "403"),
                                                                    uu____82061,
                                                                    uu____82065)
                                                                     in
                                                                    let uu____82075
                                                                    =
                                                                    let uu____82089
                                                                    =
                                                                    let uu____82101
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\""
                                                                     in
                                                                    let uu____82105
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\""
                                                                     in
                                                                    ((Prims.parse_int "404"),
                                                                    uu____82101,
                                                                    uu____82105)
                                                                     in
                                                                    [uu____82089]
                                                                     in
                                                                    uu____82049
                                                                    ::
                                                                    uu____82075
                                                                     in
                                                                    uu____82009
                                                                    ::
                                                                    uu____82035
                                                                     in
                                                                    uu____81969
                                                                    ::
                                                                    uu____81995
                                                                     in
                                                                    uu____81929
                                                                    ::
                                                                    uu____81955
                                                                     in
                                                                    uu____81889
                                                                    ::
                                                                    uu____81915
                                                                     in
                                                                    uu____81849
                                                                    ::
                                                                    uu____81875
                                                                     in
                                                                    uu____81809
                                                                    ::
                                                                    uu____81835
                                                                     in
                                                                    uu____81769
                                                                    ::
                                                                    uu____81795
                                                                     in
                                                                    uu____81729
                                                                    ::
                                                                    uu____81755
                                                                     in
                                                                    uu____81689
                                                                    ::
                                                                    uu____81715
                                                                     in
                                                                    uu____81649
                                                                    ::
                                                                    uu____81675
                                                                     in
                                                                    uu____81609
                                                                    ::
                                                                    uu____81635
                                                                     in
                                                                    uu____81569
                                                                    ::
                                                                    uu____81595
                                                                     in
                                                                    uu____81529
                                                                    ::
                                                                    uu____81555
                                                                     in
                                                                    uu____81489
                                                                    ::
                                                                    uu____81515
                                                                     in
                                                                    uu____81449
                                                                    ::
                                                                    uu____81475
                                                                     in
                                                                    uu____81409
                                                                    ::
                                                                    uu____81435
                                                                     in
                                                                    uu____81369
                                                                    ::
                                                                    uu____81395
                                                                     in
                                                                    uu____81329
                                                                    ::
                                                                    uu____81355
                                                                     in
                                                                    uu____81289
                                                                    ::
                                                                    uu____81315
                                                                     in
                                                                    uu____81249
                                                                    ::
                                                                    uu____81275
                                                                     in
                                                                    uu____81209
                                                                    ::
                                                                    uu____81235
                                                                     in
                                                                   uu____81169
                                                                    ::
                                                                    uu____81195
                                                                    in
                                                                 uu____81129
                                                                   ::
                                                                   uu____81155
                                                                  in
                                                               uu____81089 ::
                                                                 uu____81115
                                                                in
                                                             uu____81049 ::
                                                               uu____81075
                                                              in
                                                           uu____81009 ::
                                                             uu____81035
                                                            in
                                                         uu____80969 ::
                                                           uu____80995
                                                          in
                                                       uu____80929 ::
                                                         uu____80955
                                                        in
                                                     uu____80889 ::
                                                       uu____80915
                                                      in
                                                   uu____80849 :: uu____80875
                                                    in
                                                 uu____80809 :: uu____80835
                                                  in
                                               uu____80769 :: uu____80795  in
                                             uu____80729 :: uu____80755  in
                                           uu____80689 :: uu____80715  in
                                         uu____80647 :: uu____80675  in
                                       uu____80605 :: uu____80633  in
                                     uu____80538 :: uu____80591  in
                                   uu____80471 :: uu____80524  in
                                 uu____80404 :: uu____80457  in
                               uu____80360 :: uu____80390  in
                             uu____80319 :: uu____80346  in
                           uu____80278 :: uu____80305  in
                         uu____80239 :: uu____80264  in
                       uu____80204 :: uu____80225  in
                     uu____80169 :: uu____80190  in
                   uu____80134 :: uu____80155  in
                 uu____80099 :: uu____80120  in
               uu____80064 :: uu____80085  in
             uu____80012 :: uu____80050  in
           uu____79948 :: uu____79998  in
         uu____79899 :: uu____79934  in
       uu____79850 :: uu____79885  in
     uu____79808 :: uu____79836  in
   uu____79760 :: uu____79794)
  
let run_either :
  'Auu____82753 .
    Prims.int ->
      'Auu____82753 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env ->
             'Auu____82753 -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____82791 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____82791);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____82796 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____82796 (fun a1  -> ()));
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____82819 =
               let uu____82821 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____82821 expected  in
             FStar_Tests_Util.always i uu____82819)))
  
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
        let interp uu____82900 = run_interpreter i r expected  in
        let uu____82901 =
          let uu____82902 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____82902  in
        (i, uu____82901)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe1 uu____82940 = run_nbe i r expected  in
        let uu____82941 =
          let uu____82942 = FStar_Util.return_execution_time nbe1  in
          FStar_Pervasives_Native.snd uu____82942  in
        (i, uu____82941)
  
let run_tests :
  'Auu____82953 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
           'Auu____82953)
      -> 'Auu____82953 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___742_83005  ->
            match uu___742_83005 with | (no,test,res) -> run1 no test res)
         tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : unit -> unit) =
  fun uu____83036  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____83039 = run_tests run_nbe  in
     FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : unit -> unit) =
  fun uu____83048  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____83051 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____83067  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu____83097  ->
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
        let nbe1 uu____83142 = run_nbe i r expected  in
        let norm1 uu____83148 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe1;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : unit -> unit) =
  fun uu____83161  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____83164 =
       let uu____83165 = encode (Prims.parse_int "1000")  in
       let uu____83167 =
         let uu____83170 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____83171 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____83170 uu____83171  in
       let_ FStar_Tests_Util.x uu____83165 uu____83167  in
     run_both_with_time (Prims.parse_int "14") uu____83164 z)
  
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
             let uu____83247 = res1  in
             match uu____83247 with
             | (t1,time_int) ->
                 let uu____83257 = res2  in
                 (match uu____83257 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____83269 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____83269 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : unit -> unit) =
  fun uu____83280  ->
    (let uu____83282 = FStar_Syntax_Print.term_to_string znat  in
     FStar_Util.print1 "%s" uu____83282);
    (let l_int = run_all_interpreter_with_time ()  in
     let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe)
  