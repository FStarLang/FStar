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
      (let uu____7 =
         let uu____10 = encode (n1 - (Prims.parse_int "1"))  in [uu____10]
          in
       FStar_Tests_Util.app succ uu____7)
  
let (minus :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun m1  -> fun n1  -> FStar_Tests_Util.app n1 [pred; m1] 
let (let_ :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun x1  ->
    fun e  ->
      fun e'  ->
        let uu____32 =
          let uu____35 = let uu____36 = b x1  in [uu____36]  in
          FStar_Syntax_Util.abs uu____35 e' FStar_Pervasives_Native.None  in
        FStar_Tests_Util.app uu____32 [e]
  
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
                   FStar_Syntax_Syntax.lbattrs = []
                 }]), e'1)) FStar_Pervasives_Native.None
          FStar_Range.dummyRange
  
let (lid : Prims.string -> FStar_Ident.lident) =
  fun x1  -> FStar_Ident.lid_of_path [x1] FStar_Range.dummyRange 
let (znat_l : FStar_Syntax_Syntax.fv) =
  let uu____64 = lid "Z"  in
  FStar_Syntax_Syntax.lid_as_fv uu____64 FStar_Syntax_Syntax.Delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (snat_l : FStar_Syntax_Syntax.fv) =
  let uu____65 = lid "S"  in
  FStar_Syntax_Syntax.lid_as_fv uu____65 FStar_Syntax_Syntax.Delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (tm_fv :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun fv  ->
    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
      FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (znat : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  tm_fv znat_l 
let (snat :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    let uu____78 =
      let uu____81 =
        let uu____82 =
          let uu____97 = tm_fv snat_l  in
          let uu____100 =
            let uu____103 = FStar_Syntax_Syntax.as_arg s  in [uu____103]  in
          (uu____97, uu____100)  in
        FStar_Syntax_Syntax.Tm_app uu____82  in
      FStar_Syntax_Syntax.mk uu____81  in
    uu____78 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let pat :
  'Auu____113 . 'Auu____113 -> 'Auu____113 FStar_Syntax_Syntax.withinfo_t =
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
      let uu____171 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
      (uu____171, FStar_Pervasives_Native.None, znat)  in
    let sbranch =
      let uu____213 =
        let uu____216 =
          let uu____217 =
            let uu____230 =
              let uu____239 =
                let uu____246 =
                  pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.x)  in
                (uu____246, false)  in
              [uu____239]  in
            (snat_l, uu____230)  in
          FStar_Syntax_Syntax.Pat_cons uu____217  in
        pat uu____216  in
      let uu____271 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_bvar
             (let uu___77_276 = FStar_Tests_Util.x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___77_276.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                FStar_Syntax_Syntax.sort =
                  (uu___77_276.FStar_Syntax_Syntax.sort)
              })) FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      (uu____213, FStar_Pervasives_Native.None, uu____271)  in
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
        let uu____351 = pat (FStar_Syntax_Syntax.Pat_cons (znat_l, []))  in
        let uu____368 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
        (uu____351, FStar_Pervasives_Native.None, uu____368)  in
      let sbranch =
        let uu____392 =
          let uu____395 =
            let uu____396 =
              let uu____409 =
                let uu____418 =
                  let uu____425 =
                    pat (FStar_Syntax_Syntax.Pat_var FStar_Tests_Util.n)  in
                  (uu____425, false)  in
                [uu____418]  in
              (snat_l, uu____409)  in
            FStar_Syntax_Syntax.Pat_cons uu____396  in
          pat uu____395  in
        let uu____450 =
          let uu____453 = FStar_Tests_Util.nm minus1  in
          let uu____456 =
            let uu____459 =
              let uu____462 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
              pred_nat uu____462  in
            let uu____465 =
              let uu____470 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
              [uu____470]  in
            uu____459 :: uu____465  in
          FStar_Tests_Util.app uu____453 uu____456  in
        (uu____392, FStar_Pervasives_Native.None, uu____450)  in
      let lb =
        let uu____484 =
          FStar_Ident.lid_of_path ["Pure"] FStar_Range.dummyRange  in
        let uu____485 =
          let uu____488 =
            let uu____489 =
              let uu____490 = b FStar_Tests_Util.x  in
              let uu____491 =
                let uu____494 = b FStar_Tests_Util.y  in [uu____494]  in
              uu____490 :: uu____491  in
            let uu____495 =
              let uu____496 = FStar_Tests_Util.nm FStar_Tests_Util.y  in
              mk_match uu____496 [zbranch; sbranch]  in
            FStar_Syntax_Util.abs uu____489 uu____495
              FStar_Pervasives_Native.None
             in
          FStar_Syntax_Subst.subst
            [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
            uu____488
           in
        {
          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl minus1);
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
          FStar_Syntax_Syntax.lbeff = uu____484;
          FStar_Syntax_Syntax.lbdef = uu____485;
          FStar_Syntax_Syntax.lbattrs = []
        }  in
      let uu____541 =
        let uu____544 =
          let uu____545 =
            let uu____558 =
              let uu____559 =
                let uu____560 = FStar_Tests_Util.nm minus1  in
                FStar_Tests_Util.app uu____560 [t1; t2]  in
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.NM (minus1, (Prims.parse_int "0"))]
                uu____559
               in
            ((true, [lb]), uu____558)  in
          FStar_Syntax_Syntax.Tm_let uu____545  in
        FStar_Syntax_Syntax.mk uu____544  in
      uu____541 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (encode_nat : Prims.int -> FStar_Syntax_Syntax.term) =
  fun n1  ->
    let rec aux out n2 =
      if n2 = (Prims.parse_int "0")
      then out
      else
        (let uu____585 = snat out  in
         aux uu____585 (n2 - (Prims.parse_int "1")))
       in
    aux znat n1
  
let (tests :
  (Prims.int,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term)
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
  (let uu____620 =
     let uu____629 =
       let uu____632 =
         let uu____635 =
           let uu____638 =
             let uu____641 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
             [uu____641]  in
           id :: uu____638  in
         one :: uu____635  in
       FStar_Tests_Util.app apply uu____632  in
     let uu____642 = FStar_Tests_Util.nm FStar_Tests_Util.n  in
     ((Prims.parse_int "0"), uu____629, uu____642)  in
   let uu____645 =
     let uu____656 =
       let uu____663 = FStar_Tests_Pars.tc_nbe "x1"  in
       let uu____664 = FStar_Tests_Pars.tc_nbe "6"  in
       ((Prims.parse_int "309"), uu____663, uu____664)  in
     let uu____665 =
       let uu____674 =
         let uu____681 = FStar_Tests_Pars.tc_nbe "x2"  in
         let uu____682 = FStar_Tests_Pars.tc_nbe "2"  in
         ((Prims.parse_int "310"), uu____681, uu____682)  in
       [uu____674]  in
     uu____656 :: uu____665  in
   uu____620 :: uu____645)
  
let run_either :
  'Auu____714 .
    Prims.int ->
      'Auu____714 ->
        FStar_Syntax_Syntax.term ->
          (FStar_TypeChecker_Env.env ->
             'Auu____714 -> FStar_Syntax_Syntax.term)
            -> Prims.unit
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        fun normalizer  ->
          (let uu____742 = FStar_Util.string_of_int i  in
           FStar_Util.print1 "%s: ... \n\n" uu____742);
          (let tcenv = FStar_Tests_Pars.init ()  in
           (let uu____745 = FStar_Main.process_args ()  in
            FStar_All.pipe_right uu____745 FStar_Pervasives.ignore);
           (let x1 = normalizer tcenv r  in
            FStar_Options.init ();
            FStar_Options.set_option "print_universes"
              (FStar_Options.Bool true);
            FStar_Options.set_option "print_implicits"
              (FStar_Options.Bool true);
            (let uu____768 =
               let uu____769 = FStar_Syntax_Util.unascribe x1  in
               FStar_Tests_Util.term_eq uu____769 expected  in
             FStar_Tests_Util.always i uu____768)))
  
let (run_interpreter :
  Prims.int ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        run_either i r expected
          (FStar_TypeChecker_Normalize.normalize
             [FStar_TypeChecker_Normalize.Beta;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.Primops])
  
let (run_nbe :
  Prims.int ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        run_either i r expected FStar_TypeChecker_NBE.normalize
  
let (run_interpreter_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let interp uu____804 = run_interpreter i r expected  in
        let uu____805 =
          let uu____806 = FStar_Util.return_execution_time interp  in
          FStar_Pervasives_Native.snd uu____806  in
        (i, uu____805)
  
let (run_nbe_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe uu____827 = run_nbe i r expected  in
        let uu____828 =
          let uu____829 = FStar_Util.return_execution_time nbe  in
          FStar_Pervasives_Native.snd uu____829  in
        (i, uu____828)
  
let run_tests :
  'Auu____836 .
    (Prims.int ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term -> 'Auu____836)
      -> 'Auu____836 Prims.list
  =
  fun run1  ->
    FStar_Options.__set_unit_tests ();
    (let l =
       FStar_List.map
         (fun uu___76_878  ->
            match uu___76_878 with | (no,test,res) -> run1 no test res) tests
        in
     FStar_Options.__clear_unit_tests (); l)
  
let (run_all_nbe : Prims.unit -> Prims.unit) =
  fun uu____897  ->
    FStar_Util.print_string "Testing NBE\n";
    (let uu____899 = run_tests run_nbe  in FStar_Util.print_string "NBE ok\n")
  
let (run_all_interpreter : Prims.unit -> Prims.unit) =
  fun uu____904  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let uu____906 = run_tests run_interpreter  in
     FStar_Util.print_string "Normalizer ok\n")
  
let (run_all_nbe_with_time :
  Prims.unit ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____917  ->
    FStar_Util.print_string "Testing NBE\n";
    (let l = run_tests run_nbe_with_time  in
     FStar_Util.print_string "NBE ok\n"; l)
  
let (run_all_interpreter_with_time :
  Prims.unit ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____939  ->
    FStar_Util.print_string "Testing the normalizer\n";
    (let l = run_tests run_interpreter_with_time  in
     FStar_Util.print_string "Normalizer ok\n"; l)
  
let (run_both_with_time :
  Prims.int ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun i  ->
    fun r  ->
      fun expected  ->
        let nbe uu____965 = run_nbe i r expected  in
        let norm1 uu____969 = run_interpreter i r expected  in
        FStar_Util.measure_execution_time "nbe" nbe;
        FStar_Util.print_string "\n";
        FStar_Util.measure_execution_time "normalizer" norm1;
        FStar_Util.print_string "\n"
  
let (compare : Prims.unit -> Prims.unit) =
  fun uu____975  ->
    FStar_Util.print_string "Comparing times for normalization and nbe\n";
    (let uu____977 =
       let uu____978 = encode (Prims.parse_int "1000")  in
       let uu____979 =
         let uu____980 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         let uu____981 = FStar_Tests_Util.nm FStar_Tests_Util.x  in
         minus uu____980 uu____981  in
       let_ FStar_Tests_Util.x uu____978 uu____979  in
     run_both_with_time (Prims.parse_int "14") uu____977 z)
  
let (compare_times :
  (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2 Prims.list
    ->
    (Prims.int,FStar_BaseTypes.float) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.unit)
  =
  fun l_int  ->
    fun l_nbe  ->
      FStar_Util.print_string "Comparing times for normalization and nbe\n";
      FStar_List.iter2
        (fun res1  ->
           fun res2  ->
             let uu____1042 = res1  in
             match uu____1042 with
             | (t1,time_int) ->
                 let uu____1049 = res2  in
                 (match uu____1049 with
                  | (t2,time_nbe) ->
                      if t1 = t2
                      then
                        let uu____1056 = FStar_Util.string_of_int t1  in
                        FStar_Util.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                          uu____1056 (FStar_Util.string_of_float time_nbe)
                          (FStar_Util.string_of_float time_int)
                      else
                        FStar_Util.print_string
                          "Test numbers do not match...\n")) l_int l_nbe
  
let (run_all : Prims.unit -> Prims.unit) =
  fun uu____1060  ->
    let l_int = run_all_interpreter_with_time ()  in
    let l_nbe = run_all_nbe_with_time ()  in compare_times l_int l_nbe
  