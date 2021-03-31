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
  fun n ->
    if n = Prims.int_zero
    then z
    else
      (let uu___1 = let uu___2 = encode (n - Prims.int_one) in [uu___2] in
       FStar_Tests_Util.app succ uu___1)
let (minus :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun m -> fun n -> FStar_Tests_Util.app n [pred; m]
let (let_ :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term)
  =
  fun x ->
    fun e ->
      fun e' ->
        let uu___ =
          let uu___1 = let uu___2 = b x in [uu___2] in
          FStar_Syntax_Util.abs uu___1 e' FStar_Pervasives_Native.None in
        FStar_Tests_Util.app uu___ [e]
let (mk_let :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun x ->
    fun e ->
      fun e' ->
        let e'1 =
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (x, Prims.int_zero)] e' in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_let
             ((false,
                [{
                   FStar_Syntax_Syntax.lbname = (FStar_Pervasives.Inl x);
                   FStar_Syntax_Syntax.lbunivs = [];
                   FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
                   FStar_Syntax_Syntax.lbeff =
                     FStar_Parser_Const.effect_Tot_lid;
                   FStar_Syntax_Syntax.lbdef = e;
                   FStar_Syntax_Syntax.lbattrs = [];
                   FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
                 }]), e'1)) FStar_Range.dummyRange
let (lid : Prims.string -> FStar_Ident.lident) =
  fun x -> FStar_Ident.lid_of_path ["Test"; x] FStar_Range.dummyRange
let (znat_l : FStar_Syntax_Syntax.fv) =
  let uu___ = lid "Z" in
  FStar_Syntax_Syntax.lid_as_fv uu___ FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu___ = lid "S" in
  FStar_Syntax_Syntax.lid_as_fv uu___ FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
let (tm_fv :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun fv ->
    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
      FStar_Range.dummyRange
let (znat : FStar_Syntax_Syntax.term) = tm_fv znat_l
let (snat :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s ->
    let uu___ =
      let uu___1 =
        let uu___2 = tm_fv snat_l in
        let uu___3 = let uu___4 = FStar_Syntax_Syntax.as_arg s in [uu___4] in
        (uu___2, uu___3) in
      FStar_Syntax_Syntax.Tm_app uu___1 in
    FStar_Syntax_Syntax.mk uu___ FStar_Range.dummyRange
let pat : 'uuuuu . 'uuuuu -> 'uuuuu FStar_Syntax_Syntax.withinfo_t =
  fun p -> FStar_Syntax_Syntax.withinfo p FStar_Range.dummyRange
let (snat_type : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  let uu___ =
    let uu___1 = lid "snat" in
    FStar_Syntax_Syntax.lid_as_fv uu___1 FStar_Syntax_Syntax.delta_constant
      FStar_Pervasives_Native.None in
  tm_fv uu___
let (mk_match :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun h ->
    fun branches ->
      let branches1 =
        FStar_All.pipe_right branches
          (FStar_List.map FStar_Syntax_Util.branch) in
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_match
           (h, FStar_Pervasives_Native.None, branches1))
        FStar_Range.dummyRange
let (pred_nat :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s ->
    let zbranch =
      let uu___ = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, [])) in
      (uu___, FStar_Pervasives_Native.None, znat) in
    let sbranch =
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x) in
                (uu___5, false) in
              [uu___4] in
            (snat_l, uu___3) in
          FStar_Syntax_Syntax.Pat_cons uu___2 in
        pat uu___1 in
      let uu___1 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___2 = FStar_Tests_Util.x in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = Prims.int_zero;
                FStar_Syntax_Syntax.sort = (uu___2.FStar_Syntax_Syntax.sort)
              })) FStar_Range.dummyRange in
      (uu___, FStar_Pervasives_Native.None, uu___1) in
    mk_match s [zbranch; sbranch]
let (minus_nat :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1 ->
    fun t2 ->
      let minus1 = FStar_Tests_Util.m in
      let x =
        let uu___ = FStar_Tests_Util.x in
        {
          FStar_Syntax_Syntax.ppname = (uu___.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = snat_type
        } in
      let y =
        let uu___ = FStar_Tests_Util.y in
        {
          FStar_Syntax_Syntax.ppname = (uu___.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = snat_type
        } in
      let zbranch =
        let uu___ = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, [])) in
        let uu___1 = FStar_Tests_Util.nm x in
        (uu___, FStar_Pervasives_Native.None, uu___1) in
      let sbranch =
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n) in
                  (uu___5, false) in
                [uu___4] in
              (snat_l, uu___3) in
            FStar_Syntax_Syntax.Pat_cons uu___2 in
          pat uu___1 in
        let uu___1 =
          let uu___2 = FStar_Tests_Util.nm minus1 in
          let uu___3 =
            let uu___4 =
              let uu___5 = FStar_Tests_Util.nm x in pred_nat uu___5 in
            let uu___5 =
              let uu___6 = FStar_Tests_Util.nm FStar_Tests_Util.n in [uu___6] in
            uu___4 :: uu___5 in
          FStar_Tests_Util.app uu___2 uu___3 in
        (uu___, FStar_Pervasives_Native.None, uu___1) in
      let lb =
        let uu___ = FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange in
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 = b x in
              let uu___5 = let uu___6 = b y in [uu___6] in uu___4 :: uu___5 in
            let uu___4 =
              let uu___5 = FStar_Tests_Util.nm y in
              mk_match uu___5 [zbranch; sbranch] in
            FStar_Syntax_Util.abs uu___3 uu___4 FStar_Pervasives_Native.None in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, Prims.int_zero)] uu___2 in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Pervasives.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu___;
          FStar_Syntax_Syntax.lbdef = uu___1;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange
        } in
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_Tests_Util.nm minus1 in
              FStar_Tests_Util.app uu___4 [t1; t2] in
            FStar_Syntax_Subst.subst
              [FStar_Syntax_Syntax.NM (minus1, Prims.int_zero)] uu___3 in
          ((true, [lb]), uu___2) in
        FStar_Syntax_Syntax.Tm_let uu___1 in
      FStar_Syntax_Syntax.mk uu___ FStar_Range.dummyRange
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n ->
    let rec aux out n1 =
      if n1 = Prims.int_zero
      then out
      else (let uu___1 = snat out in aux uu___1 (n1 - Prims.int_one)) in
    aux znat n
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
  (let uu___25 =
     let uu___26 =
       let uu___27 =
         let uu___28 =
           let uu___29 =
             let uu___30 = FStar_Tests_Util.nm FStar_Tests_Util.n in
             [uu___30] in
           id :: uu___29 in
         one :: uu___28 in
       FStar_Tests_Util.app apply uu___27 in
     let uu___27 = FStar_Tests_Util.nm FStar_Tests_Util.n in
     (Prims.int_zero, uu___26, uu___27) in
   let uu___26 =
     let uu___27 =
       let uu___28 =
         let uu___29 =
           let uu___30 = FStar_Tests_Util.nm FStar_Tests_Util.x in [uu___30] in
         FStar_Tests_Util.app id uu___29 in
       let uu___29 = FStar_Tests_Util.nm FStar_Tests_Util.x in
       (Prims.int_one, uu___28, uu___29) in
     let uu___28 =
       let uu___29 =
         let uu___30 =
           let uu___31 =
             let uu___32 =
               let uu___33 = FStar_Tests_Util.nm FStar_Tests_Util.n in
               let uu___34 =
                 let uu___35 = FStar_Tests_Util.nm FStar_Tests_Util.m in
                 [uu___35] in
               uu___33 :: uu___34 in
             tt :: uu___32 in
           FStar_Tests_Util.app apply uu___31 in
         let uu___31 = FStar_Tests_Util.nm FStar_Tests_Util.n in
         (Prims.int_one, uu___30, uu___31) in
       let uu___30 =
         let uu___31 =
           let uu___32 =
             let uu___33 =
               let uu___34 =
                 let uu___35 = FStar_Tests_Util.nm FStar_Tests_Util.n in
                 let uu___36 =
                   let uu___37 = FStar_Tests_Util.nm FStar_Tests_Util.m in
                   [uu___37] in
                 uu___35 :: uu___36 in
               ff :: uu___34 in
             FStar_Tests_Util.app apply uu___33 in
           let uu___33 = FStar_Tests_Util.nm FStar_Tests_Util.m in
           ((Prims.of_int (2)), uu___32, uu___33) in
         let uu___32 =
           let uu___33 =
             let uu___34 =
               let uu___35 =
                 let uu___36 =
                   let uu___37 =
                     let uu___38 =
                       let uu___39 =
                         let uu___40 =
                           let uu___41 =
                             let uu___42 =
                               FStar_Tests_Util.nm FStar_Tests_Util.n in
                             let uu___43 =
                               let uu___44 =
                                 FStar_Tests_Util.nm FStar_Tests_Util.m in
                               [uu___44] in
                             uu___42 :: uu___43 in
                           ff :: uu___41 in
                         apply :: uu___40 in
                       apply :: uu___39 in
                     apply :: uu___38 in
                   apply :: uu___37 in
                 apply :: uu___36 in
               FStar_Tests_Util.app apply uu___35 in
             let uu___35 = FStar_Tests_Util.nm FStar_Tests_Util.m in
             ((Prims.of_int (3)), uu___34, uu___35) in
           let uu___34 =
             let uu___35 =
               let uu___36 =
                 let uu___37 =
                   let uu___38 =
                     let uu___39 =
                       let uu___40 = FStar_Tests_Util.nm FStar_Tests_Util.n in
                       let uu___41 =
                         let uu___42 = FStar_Tests_Util.nm FStar_Tests_Util.m in
                         [uu___42] in
                       uu___40 :: uu___41 in
                     ff :: uu___39 in
                   apply :: uu___38 in
                 FStar_Tests_Util.app twice uu___37 in
               let uu___37 = FStar_Tests_Util.nm FStar_Tests_Util.m in
               ((Prims.of_int (4)), uu___36, uu___37) in
             let uu___36 =
               let uu___37 =
                 let uu___38 = minus one z in
                 ((Prims.of_int (5)), uu___38, one) in
               let uu___38 =
                 let uu___39 =
                   let uu___40 = FStar_Tests_Util.app pred [one] in
                   ((Prims.of_int (6)), uu___40, z) in
                 let uu___40 =
                   let uu___41 =
                     let uu___42 = minus one one in
                     ((Prims.of_int (7)), uu___42, z) in
                   let uu___42 =
                     let uu___43 =
                       let uu___44 = FStar_Tests_Util.app mul [one; one] in
                       ((Prims.of_int (8)), uu___44, one) in
                     let uu___44 =
                       let uu___45 =
                         let uu___46 = FStar_Tests_Util.app mul [two; one] in
                         ((Prims.of_int (9)), uu___46, two) in
                       let uu___46 =
                         let uu___47 =
                           let uu___48 =
                             let uu___49 =
                               let uu___50 = FStar_Tests_Util.app succ [one] in
                               [uu___50; one] in
                             FStar_Tests_Util.app mul uu___49 in
                           ((Prims.of_int (10)), uu___48, two) in
                         let uu___48 =
                           let uu___49 =
                             let uu___50 =
                               let uu___51 = encode (Prims.of_int (10)) in
                               let uu___52 = encode (Prims.of_int (10)) in
                               minus uu___51 uu___52 in
                             ((Prims.of_int (11)), uu___50, z) in
                           let uu___50 =
                             let uu___51 =
                               let uu___52 =
                                 let uu___53 = encode (Prims.of_int (100)) in
                                 let uu___54 = encode (Prims.of_int (100)) in
                                 minus uu___53 uu___54 in
                               ((Prims.of_int (12)), uu___52, z) in
                             let uu___52 =
                               let uu___53 =
                                 let uu___54 =
                                   let uu___55 = encode (Prims.of_int (100)) in
                                   let uu___56 =
                                     let uu___57 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x in
                                     let uu___58 =
                                       FStar_Tests_Util.nm FStar_Tests_Util.x in
                                     minus uu___57 uu___58 in
                                   let_ FStar_Tests_Util.x uu___55 uu___56 in
                                 ((Prims.of_int (13)), uu___54, z) in
                               let uu___54 =
                                 let uu___55 =
                                   let uu___56 =
                                     let uu___57 =
                                       FStar_Tests_Util.app succ [one] in
                                     let uu___58 =
                                       let uu___59 =
                                         let uu___60 =
                                           let uu___61 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.x in
                                           let uu___62 =
                                             let uu___63 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x in
                                             [uu___63] in
                                           uu___61 :: uu___62 in
                                         FStar_Tests_Util.app mul uu___60 in
                                       let uu___60 =
                                         let uu___61 =
                                           let uu___62 =
                                             let uu___63 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.y in
                                             let uu___64 =
                                               let uu___65 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y in
                                               [uu___65] in
                                             uu___63 :: uu___64 in
                                           FStar_Tests_Util.app mul uu___62 in
                                         let uu___62 =
                                           let uu___63 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h in
                                           let uu___64 =
                                             FStar_Tests_Util.nm
                                               FStar_Tests_Util.h in
                                           minus uu___63 uu___64 in
                                         let_ FStar_Tests_Util.h uu___61
                                           uu___62 in
                                       let_ FStar_Tests_Util.y uu___59
                                         uu___60 in
                                     let_ FStar_Tests_Util.x uu___57 uu___58 in
                                   ((Prims.of_int (15)), uu___56, z) in
                                 let uu___56 =
                                   let uu___57 =
                                     let uu___58 =
                                       let uu___59 =
                                         FStar_Tests_Util.app succ [one] in
                                       let uu___60 =
                                         let uu___61 =
                                           let uu___62 =
                                             let uu___63 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.x in
                                             let uu___64 =
                                               let uu___65 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x in
                                               [uu___65] in
                                             uu___63 :: uu___64 in
                                           FStar_Tests_Util.app mul uu___62 in
                                         let uu___62 =
                                           let uu___63 =
                                             let uu___64 =
                                               let uu___65 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.y in
                                               let uu___66 =
                                                 let uu___67 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y in
                                                 [uu___67] in
                                               uu___65 :: uu___66 in
                                             FStar_Tests_Util.app mul uu___64 in
                                           let uu___64 =
                                             let uu___65 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h in
                                             let uu___66 =
                                               FStar_Tests_Util.nm
                                                 FStar_Tests_Util.h in
                                             minus uu___65 uu___66 in
                                           mk_let FStar_Tests_Util.h uu___63
                                             uu___64 in
                                         mk_let FStar_Tests_Util.y uu___61
                                           uu___62 in
                                       mk_let FStar_Tests_Util.x uu___59
                                         uu___60 in
                                     ((Prims.of_int (16)), uu___58, z) in
                                   let uu___58 =
                                     let uu___59 =
                                       let uu___60 =
                                         let uu___61 =
                                           FStar_Tests_Util.app succ [one] in
                                         let uu___62 =
                                           let uu___63 =
                                             let uu___64 =
                                               let uu___65 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.x in
                                               let uu___66 =
                                                 let uu___67 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.x in
                                                 [uu___67] in
                                               uu___65 :: uu___66 in
                                             FStar_Tests_Util.app mul uu___64 in
                                           let uu___64 =
                                             let uu___65 =
                                               let uu___66 =
                                                 let uu___67 =
                                                   FStar_Tests_Util.nm
                                                     FStar_Tests_Util.y in
                                                 let uu___68 =
                                                   let uu___69 =
                                                     FStar_Tests_Util.nm
                                                       FStar_Tests_Util.y in
                                                   [uu___69] in
                                                 uu___67 :: uu___68 in
                                               FStar_Tests_Util.app mul
                                                 uu___66 in
                                             let uu___66 =
                                               let uu___67 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h in
                                               let uu___68 =
                                                 FStar_Tests_Util.nm
                                                   FStar_Tests_Util.h in
                                               minus uu___67 uu___68 in
                                             let_ FStar_Tests_Util.h uu___65
                                               uu___66 in
                                           let_ FStar_Tests_Util.y uu___63
                                             uu___64 in
                                         let_ FStar_Tests_Util.x uu___61
                                           uu___62 in
                                       ((Prims.of_int (17)), uu___60, z) in
                                     let uu___60 =
                                       let uu___61 =
                                         let uu___62 =
                                           let uu___63 =
                                             let uu___64 = snat znat in
                                             snat uu___64 in
                                           pred_nat uu___63 in
                                         let uu___63 = snat znat in
                                         ((Prims.of_int (18)), uu___62,
                                           uu___63) in
                                       let uu___62 =
                                         let uu___63 =
                                           let uu___64 =
                                             let uu___65 =
                                               let uu___66 =
                                                 let uu___67 = snat znat in
                                                 snat uu___67 in
                                               let uu___67 = snat znat in
                                               minus_nat uu___66 uu___67 in
                                             FStar_Tests_Pars.tc_nbe_term
                                               uu___65 in
                                           let uu___65 = snat znat in
                                           ((Prims.of_int (19)), uu___64,
                                             uu___65) in
                                         let uu___64 =
                                           let uu___65 =
                                             let uu___66 =
                                               let uu___67 =
                                                 let uu___68 =
                                                   encode_nat
                                                     (Prims.of_int (10)) in
                                                 let uu___69 =
                                                   encode_nat
                                                     (Prims.of_int (10)) in
                                                 minus_nat uu___68 uu___69 in
                                               FStar_Tests_Pars.tc_nbe_term
                                                 uu___67 in
                                             ((Prims.of_int (20)), uu___66,
                                               znat) in
                                           let uu___66 =
                                             let uu___67 =
                                               let uu___68 =
                                                 let uu___69 =
                                                   let uu___70 =
                                                     encode_nat
                                                       (Prims.of_int (100)) in
                                                   let uu___71 =
                                                     encode_nat
                                                       (Prims.of_int (100)) in
                                                   minus_nat uu___70 uu___71 in
                                                 FStar_Tests_Pars.tc_nbe_term
                                                   uu___69 in
                                               ((Prims.of_int (21)), uu___68,
                                                 znat) in
                                             let uu___68 =
                                               let uu___69 =
                                                 let uu___70 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "recons [0;1]" in
                                                 let uu___71 =
                                                   FStar_Tests_Pars.tc_nbe
                                                     "[0;1]" in
                                                 ((Prims.of_int (24)),
                                                   uu___70, uu___71) in
                                               let uu___70 =
                                                 let uu___71 =
                                                   let uu___72 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "recons [false;true;false]" in
                                                   let uu___73 =
                                                     FStar_Tests_Pars.tc_nbe
                                                       "[false;true;false]" in
                                                   ((Prims.of_int (241)),
                                                     uu___72, uu___73) in
                                                 let uu___72 =
                                                   let uu___73 =
                                                     let uu___74 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "copy [0;1]" in
                                                     let uu___75 =
                                                       FStar_Tests_Pars.tc_nbe
                                                         "[0;1]" in
                                                     ((Prims.of_int (25)),
                                                       uu___74, uu___75) in
                                                   let uu___74 =
                                                     let uu___75 =
                                                       let uu___76 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "rev [0;1;2;3;4;5;6;7;8;9;10]" in
                                                       let uu___77 =
                                                         FStar_Tests_Pars.tc_nbe
                                                           "[10;9;8;7;6;5;4;3;2;1;0]" in
                                                       ((Prims.of_int (26)),
                                                         uu___76, uu___77) in
                                                     let uu___76 =
                                                       let uu___77 =
                                                         let uu___78 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "(fun x y z q -> z) T T F T" in
                                                         let uu___79 =
                                                           FStar_Tests_Pars.tc_nbe
                                                             "F" in
                                                         ((Prims.of_int (28)),
                                                           uu___78, uu___79) in
                                                       let uu___78 =
                                                         let uu___79 =
                                                           let uu___80 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]" in
                                                           let uu___81 =
                                                             FStar_Tests_Pars.tc_nbe
                                                               "[T; F]" in
                                                           ((Prims.of_int (29)),
                                                             uu___80,
                                                             uu___81) in
                                                         let uu___80 =
                                                           let uu___81 =
                                                             let uu___82 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "id_tb T" in
                                                             let uu___83 =
                                                               FStar_Tests_Pars.tc_nbe
                                                                 "T" in
                                                             ((Prims.of_int (31)),
                                                               uu___82,
                                                               uu___83) in
                                                           let uu___82 =
                                                             let uu___83 =
                                                               let uu___84 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "(fun #a x -> x) #tb T" in
                                                               let uu___85 =
                                                                 FStar_Tests_Pars.tc_nbe
                                                                   "T" in
                                                               ((Prims.of_int (32)),
                                                                 uu___84,
                                                                 uu___85) in
                                                             let uu___84 =
                                                               let uu___85 =
                                                                 let uu___86
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "revtb T" in
                                                                 let uu___87
                                                                   =
                                                                   FStar_Tests_Pars.tc_nbe
                                                                    "F" in
                                                                 ((Prims.of_int (33)),
                                                                   uu___86,
                                                                   uu___87) in
                                                               let uu___86 =
                                                                 let uu___87
                                                                   =
                                                                   let uu___88
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun x y -> x) T F" in
                                                                   let uu___89
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T" in
                                                                   ((Prims.of_int (34)),
                                                                    uu___88,
                                                                    uu___89) in
                                                                 let uu___88
                                                                   =
                                                                   let uu___89
                                                                    =
                                                                    let uu___90
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "fst_a T F" in
                                                                    let uu___91
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T" in
                                                                    ((Prims.of_int (35)),
                                                                    uu___90,
                                                                    uu___91) in
                                                                   let uu___90
                                                                    =
                                                                    let uu___91
                                                                    =
                                                                    let uu___92
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T" in
                                                                    let uu___93
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T" in
                                                                    ((Prims.of_int (36)),
                                                                    uu___92,
                                                                    uu___93) in
                                                                    let uu___92
                                                                    =
                                                                    let uu___93
                                                                    =
                                                                    let uu___94
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list [T]" in
                                                                    let uu___95
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]" in
                                                                    ((Prims.of_int (301)),
                                                                    uu___94,
                                                                    uu___95) in
                                                                    let uu___94
                                                                    =
                                                                    let uu___95
                                                                    =
                                                                    let uu___96
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "id_list_m [T]" in
                                                                    let uu___97
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]" in
                                                                    ((Prims.of_int (3012)),
                                                                    uu___96,
                                                                    uu___97) in
                                                                    let uu___96
                                                                    =
                                                                    let uu___97
                                                                    =
                                                                    let uu___98
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons_m [T; F]" in
                                                                    let uu___99
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T; F]" in
                                                                    ((Prims.of_int (302)),
                                                                    uu___98,
                                                                    uu___99) in
                                                                    let uu___98
                                                                    =
                                                                    let uu___99
                                                                    =
                                                                    let uu___100
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T A1 A3" in
                                                                    let uu___101
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "A1" in
                                                                    ((Prims.of_int (303)),
                                                                    uu___100,
                                                                    uu___101) in
                                                                    let uu___100
                                                                    =
                                                                    let uu___101
                                                                    =
                                                                    let uu___102
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select T 3 4" in
                                                                    let uu___103
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3" in
                                                                    ((Prims.of_int (3031)),
                                                                    uu___102,
                                                                    uu___103) in
                                                                    let uu___102
                                                                    =
                                                                    let uu___103
                                                                    =
                                                                    let uu___104
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_bool false 3 4" in
                                                                    let uu___105
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "4" in
                                                                    ((Prims.of_int (3032)),
                                                                    uu___104,
                                                                    uu___105) in
                                                                    let uu___104
                                                                    =
                                                                    let uu___105
                                                                    =
                                                                    let uu___106
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_int3 1 7 8 9" in
                                                                    let uu___107
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "8" in
                                                                    ((Prims.of_int (3033)),
                                                                    uu___106,
                                                                    uu___107) in
                                                                    let uu___106
                                                                    =
                                                                    let uu___107
                                                                    =
                                                                    let uu___108
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]" in
                                                                    let uu___109
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[5]" in
                                                                    ((Prims.of_int (3034)),
                                                                    uu___108,
                                                                    uu___109) in
                                                                    let uu___108
                                                                    =
                                                                    let uu___109
                                                                    =
                                                                    let uu___110
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]" in
                                                                    let uu___111
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[\"abcd\"]" in
                                                                    ((Prims.of_int (3035)),
                                                                    uu___110,
                                                                    uu___111) in
                                                                    let uu___110
                                                                    =
                                                                    let uu___111
                                                                    =
                                                                    let uu___112
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "select_string3 \"def\" 5 6 7" in
                                                                    let uu___113
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6" in
                                                                    ((Prims.of_int (3036)),
                                                                    uu___112,
                                                                    uu___113) in
                                                                    let uu___112
                                                                    =
                                                                    let uu___113
                                                                    =
                                                                    let uu___114
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "idd T" in
                                                                    let uu___115
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "T" in
                                                                    ((Prims.of_int (305)),
                                                                    uu___114,
                                                                    uu___115) in
                                                                    let uu___114
                                                                    =
                                                                    let uu___115
                                                                    =
                                                                    let uu___116
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "recons [T]" in
                                                                    let uu___117
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T]" in
                                                                    ((Prims.of_int (306)),
                                                                    uu___116,
                                                                    uu___117) in
                                                                    let uu___116
                                                                    =
                                                                    let uu___117
                                                                    =
                                                                    let uu___118
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_tb_list_2 [T;F;T;F;T;F;F]" in
                                                                    let uu___119
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]" in
                                                                    ((Prims.of_int (307)),
                                                                    uu___118,
                                                                    uu___119) in
                                                                    let uu___118
                                                                    =
                                                                    let uu___119
                                                                    =
                                                                    let uu___120
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "copy_list_2    [T;F;T;F;T;F;F]" in
                                                                    let uu___121
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[T;F;T;F;T;F;F]" in
                                                                    ((Prims.of_int (308)),
                                                                    uu___120,
                                                                    uu___121) in
                                                                    let uu___120
                                                                    =
                                                                    let uu___121
                                                                    =
                                                                    let uu___122
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [T; F; F]" in
                                                                    let uu___123
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[F; F; T]" in
                                                                    ((Prims.of_int (304)),
                                                                    uu___122,
                                                                    uu___123) in
                                                                    let uu___122
                                                                    =
                                                                    let uu___123
                                                                    =
                                                                    let uu___124
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "rev [[T]; [F; T]]" in
                                                                    let uu___125
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "[[F; T]; [T]]" in
                                                                    ((Prims.of_int (305)),
                                                                    uu___124,
                                                                    uu___125) in
                                                                    let uu___124
                                                                    =
                                                                    let uu___125
                                                                    =
                                                                    let uu___126
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x1" in
                                                                    let uu___127
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "6" in
                                                                    ((Prims.of_int (309)),
                                                                    uu___126,
                                                                    uu___127) in
                                                                    let uu___126
                                                                    =
                                                                    let uu___127
                                                                    =
                                                                    let uu___128
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "x2" in
                                                                    let uu___129
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "2" in
                                                                    ((Prims.of_int (310)),
                                                                    uu___128,
                                                                    uu___129) in
                                                                    let uu___128
                                                                    =
                                                                    let uu___129
                                                                    =
                                                                    let uu___130
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "7 + 3" in
                                                                    let uu___131
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "10" in
                                                                    ((Prims.of_int (401)),
                                                                    uu___130,
                                                                    uu___131) in
                                                                    let uu___130
                                                                    =
                                                                    let uu___131
                                                                    =
                                                                    let uu___132
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "true && false" in
                                                                    let uu___133
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false" in
                                                                    ((Prims.of_int (402)),
                                                                    uu___132,
                                                                    uu___133) in
                                                                    let uu___132
                                                                    =
                                                                    let uu___133
                                                                    =
                                                                    let uu___134
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "3 = 5" in
                                                                    let uu___135
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "false" in
                                                                    ((Prims.of_int (403)),
                                                                    uu___134,
                                                                    uu___135) in
                                                                    let uu___134
                                                                    =
                                                                    let uu___135
                                                                    =
                                                                    let uu___136
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abc\" ^ \"def\"" in
                                                                    let uu___137
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "\"abcdef\"" in
                                                                    ((Prims.of_int (404)),
                                                                    uu___136,
                                                                    uu___137) in
                                                                    let uu___136
                                                                    =
                                                                    let uu___137
                                                                    =
                                                                    let uu___138
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "(fun (x:list int) -> match x with | [] -> 0 | hd::tl -> 1) []" in
                                                                    let uu___139
                                                                    =
                                                                    FStar_Tests_Pars.tc_nbe
                                                                    "0" in
                                                                    ((Prims.of_int (405)),
                                                                    uu___138,
                                                                    uu___139) in
                                                                    [uu___137] in
                                                                    uu___135
                                                                    ::
                                                                    uu___136 in
                                                                    uu___133
                                                                    ::
                                                                    uu___134 in
                                                                    uu___131
                                                                    ::
                                                                    uu___132 in
                                                                    uu___129
                                                                    ::
                                                                    uu___130 in
                                                                    uu___127
                                                                    ::
                                                                    uu___128 in
                                                                    uu___125
                                                                    ::
                                                                    uu___126 in
                                                                    uu___123
                                                                    ::
                                                                    uu___124 in
                                                                    uu___121
                                                                    ::
                                                                    uu___122 in
                                                                    uu___119
                                                                    ::
                                                                    uu___120 in
                                                                    uu___117
                                                                    ::
                                                                    uu___118 in
                                                                    uu___115
                                                                    ::
                                                                    uu___116 in
                                                                    uu___113
                                                                    ::
                                                                    uu___114 in
                                                                    uu___111
                                                                    ::
                                                                    uu___112 in
                                                                    uu___109
                                                                    ::
                                                                    uu___110 in
                                                                    uu___107
                                                                    ::
                                                                    uu___108 in
                                                                    uu___105
                                                                    ::
                                                                    uu___106 in
                                                                    uu___103
                                                                    ::
                                                                    uu___104 in
                                                                    uu___101
                                                                    ::
                                                                    uu___102 in
                                                                    uu___99
                                                                    ::
                                                                    uu___100 in
                                                                    uu___97
                                                                    ::
                                                                    uu___98 in
                                                                    uu___95
                                                                    ::
                                                                    uu___96 in
                                                                    uu___93
                                                                    ::
                                                                    uu___94 in
                                                                    uu___91
                                                                    ::
                                                                    uu___92 in
                                                                   uu___89 ::
                                                                    uu___90 in
                                                                 uu___87 ::
                                                                   uu___88 in
                                                               uu___85 ::
                                                                 uu___86 in
                                                             uu___83 ::
                                                               uu___84 in
                                                           uu___81 :: uu___82 in
                                                         uu___79 :: uu___80 in
                                                       uu___77 :: uu___78 in
                                                     uu___75 :: uu___76 in
                                                   uu___73 :: uu___74 in
                                                 uu___71 :: uu___72 in
                                               uu___69 :: uu___70 in
                                             uu___67 :: uu___68 in
                                           uu___65 :: uu___66 in
                                         uu___63 :: uu___64 in
                                       uu___61 :: uu___62 in
                                     uu___59 :: uu___60 in
                                   uu___57 :: uu___58 in
                                 uu___55 :: uu___56 in
                               uu___53 :: uu___54 in
                             uu___51 :: uu___52 in
                           uu___49 :: uu___50 in
                         uu___47 :: uu___48 in
                       uu___45 :: uu___46 in
                     uu___43 :: uu___44 in
                   uu___41 :: uu___42 in
                 uu___39 :: uu___40 in
               uu___37 :: uu___38 in
             uu___35 :: uu___36 in
           uu___33 :: uu___34 in
         uu___31 :: uu___32 in
       uu___29 :: uu___30 in
     uu___27 :: uu___28 in
   uu___25 :: uu___26)
let run_either :
  'uuuuu .
    Prims.int ->
      'uuuuu ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_TypeChecker_Env.env -> 'uuuuu -> FStar_Syntax_Syntax.term)
            -> unit
  =
  fun i ->
    fun r ->
      fun expected ->
        fun normalizer ->
          (let uu___1 = FStar_Util.string_of_int i in
           FStar_Util.print1 "%s: ... \n\n" uu___1);
          (let tcenv = FStar_Tests_Pars.init () in
           (let uu___2 = FStar_Main.process_args () in
            FStar_All.pipe_right uu___2 (fun uu___3 -> ()));
           (let x = normalizer tcenv r in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu___5 =
               let uu___6 = FStar_Syntax_Util.unascribe x in
               FStar_Tests_Util.term_eq uu___6 expected in
             FStar_Tests_Util.always i uu___5)))
let (run_interpreter :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun i ->
    fun r ->
      fun expected ->
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
  fun i ->
    fun r ->
      fun expected ->
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
  fun i ->
    fun r ->
      fun expected ->
        let interp uu___ = run_interpreter i r expected in
        let uu___ =
          let uu___1 = FStar_Util.return_execution_time interp in
          FStar_Pervasives_Native.snd uu___1 in
        (i, uu___)
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (Prims.int * FStar_BaseTypes.float))
  =
  fun i ->
    fun r ->
      fun expected ->
        let nbe uu___ = run_nbe i r expected in
        let uu___ =
          let uu___1 = FStar_Util.return_execution_time nbe in
          FStar_Pervasives_Native.snd uu___1 in
        (i, uu___)
let run_tests :
  'uuuuu .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'uuuuu)
      -> 'uuuuu Prims.list
  =
  fun run ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___1 ->
            match uu___1 with | (no, test, res) -> run no test res) tests in
     FStar_Options.__clear_unit_tests (); l)
let (run_all_nbe : unit -> unit) =
  fun uu___ ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu___2 = run_tests run_nbe in FStar_Util.print_string "NBE ok\n")
let (run_all_interpreter : unit -> unit) =
  fun uu___ ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu___2 = run_tests run_interpreter in
     FStar_Util.print_string "Normalizer ok\n")
let (run_all_nbe_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu___ ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time in
     FStar_Util.print_string "NBE ok\n"; l)
let (run_all_interpreter_with_time :
  unit -> (Prims.int * FStar_BaseTypes.float) Prims.list) =
  fun uu___ ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let l = run_tests run_interpreter_with_time in
     FStar_Util.print_string "Normalizer ok\n"; l)
let (run_both_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun i ->
    fun r ->
      fun expected ->
        let nbe uu___ = run_nbe i r expected in
        let norm uu___ = run_interpreter i r expected in
        FStar_Util.measure_execution_time "nbe" nbe;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm;
        FStar_Util.print_string "\n"
let (compare : unit -> unit) =
  fun uu___ ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu___2 =
       let uu___3 = encode (Prims.of_int (1000)) in
       let uu___4 =
         let uu___5 = FStar_Tests_Util.nm FStar_Tests_Util.x in
         let uu___6 = FStar_Tests_Util.nm FStar_Tests_Util.x in
         minus uu___5 uu___6 in
       let_ FStar_Tests_Util.x uu___3 uu___4 in
     run_both_with_time (Prims.of_int (14)) uu___2 z)
let (compare_times :
  (Prims.int * FStar_BaseTypes.float) Prims.list ->
    (Prims.int * FStar_BaseTypes.float) Prims.list -> unit)
  =
  fun l_int ->
    fun l_nbe ->
      FStar_Util.print_string "Comparing times for normalization and nbe\n";
      FStar_List.iter2
        (fun res1 ->
           fun res2 ->
             let uu___1 = res1 in
             match uu___1 with
             | (t1, time_int) ->
                 let uu___2 = res2 in
                 (match uu___2 with
                  | (t2, time_nbe) ->
                      if t1 = t2
                      then
                        let uu___3 = FStar_Util.string_of_int t1 in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu___3 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
let (run_all : unit -> unit) =
  fun uu___ ->
    (let uu___2 = FStar_Syntax_Print.term_to_string znat in
     FStar_Util.print1 "%s" uu___2);
    (let l_int = run_all_interpreter_with_time () in
     let l_nbe = run_all_nbe_with_time () in compare_times l_int l_nbe)