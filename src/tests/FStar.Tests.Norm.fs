#light "off"
module FStar.Tests.Norm
//Normalization tests

open FStar
open FStar.Syntax.Syntax
open FStar.Tests.Pars
module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module SS = FStar.Syntax.Subst
module I = FStar.Ident
module P  = FStar.Syntax.Print
module Const = FStar.Parser.Const
module BU = FStar.Util
module N = FStar.TypeChecker.Normalize
module Env = FStar.TypeChecker.Env
open FStar.Ident
open FStar.Range
open FStar.Tests.Util


let b = mk_binder
let id     = pars "fun x -> x"
let apply  = pars "fun f x -> f x"
let twice  = pars "fun f x -> f (f x)"
let tt     = pars "fun x y -> x"
let ff     = pars "fun x y -> y"
let z      = pars "fun f x -> x"
let one    = pars "fun f x -> f x"
let two    = pars "fun f x -> f (f x)"
let succ   = pars "fun n f x -> f (n f x)"
let pred   = pars "fun n f x -> n (fun g h -> h (g f)) (fun y -> x) (fun y -> y)"
let mul    = pars "fun m n f -> m (n f)"


let rec encode n =
    if n = 0 then z
    else app succ [encode (n - 1)]
let minus m n = app n [pred; m]
let let_ x e e' : term = app (U.abs [b x] e' None) [e]
let mk_let x e e' : term =
    let e' = FStar.Syntax.Subst.subst [NM(x, 0)] e' in
    mk (Tm_let((false, [{lbname=BU.Inl x; lbunivs=[]; lbtyp=tun; lbdef=e; lbeff=Const.effect_Tot_lid; lbattrs=[];lbpos=dummyRange}]), e'))
                           None dummyRange

let lid x = lid_of_path ["Norm"; x] dummyRange
let znat_l = S.lid_as_fv (lid "Z") delta_constant (Some Data_ctor)
let snat_l = S.lid_as_fv (lid "S") delta_constant (Some Data_ctor)
let tm_fv fv = mk (Tm_fvar fv) None dummyRange
let znat : term = tm_fv znat_l
let snat s      = mk (Tm_app(tm_fv snat_l, [as_arg s])) None dummyRange
let pat p = withinfo p dummyRange
open FStar.Syntax.Subst
module SS=FStar.Syntax.Subst
let mk_match h branches =
    let branches = branches |> List.map U.branch in
    mk (Tm_match(h, branches)) None dummyRange
let pred_nat s  =
    let zbranch = pat (Pat_cons(znat_l, [])),
                  None,
                  znat in
    let sbranch = pat (Pat_cons(snat_l, [pat (Pat_var x), false])),
                  None,
                  mk (Tm_bvar({x with index=0})) None dummyRange in
    mk_match s [zbranch;sbranch]
let minus_nat t1 t2 =
    let minus = m in
    let zbranch = pat (Pat_cons(znat_l, [])),
                  None,
                  nm x in
    let sbranch = pat (Pat_cons(snat_l, [pat (Pat_var n), false])),
                  None,
                  app (nm minus) [pred_nat (nm x); nm n] in
    let lb = {lbname=BU.Inl minus; lbeff=lid_of_path ["Pure"] dummyRange; lbunivs=[]; lbtyp=tun;
              lbdef=subst [NM(minus, 0)] (U.abs [b x; b y] (mk_match (nm y) [zbranch; sbranch]) None);
              lbattrs=[]; lbpos=dummyRange} in
    mk (Tm_let((true, [lb]), subst [NM(minus, 0)] (app (nm minus) [t1; t2]))) None dummyRange
let encode_nat n =
    let rec aux out n =
        if n=0 then out
        else aux (snat out) (n - 1) in
    aux znat n

let tests =
  let _ = Pars.pars_and_tc_fragment "let rec copy (x:list int) : Tot (list int) = \
                                         match x with \
                                          | [] -> []  \
                                          | hd::tl -> hd::copy tl" in
  let _ = Pars.pars_and_tc_fragment "let recons (x:list 'a) : Tot (list 'a) = \
                                         match x with \
                                          | [] -> []  \
                                          | hd::tl -> hd::tl" in
  let _ = Pars.pars_and_tc_fragment "let rev (x:list 'a) : Tot (list 'a) = \
                                         let rec aux (x:list 'a) (out:list 'a) : Tot (list 'a) = \
                                             match x with \
                                               | [] -> out \
                                               | hd::tl -> aux tl (hd::out) in \
                                          aux x []" in
  let _ = Pars.pars_and_tc_fragment "type t = \
                                      | A : int -> int -> t \
                                      | B : int -> int -> t \
                                     let f = function \
                                       | A x y \
                                       | B y x -> y - x" in
  let _ = Pars.pars_and_tc_fragment "type tb = | T | F" in
  let _ = Pars.pars_and_tc_fragment "type rb = | A1 | A2 | A3" in
  let _ = Pars.pars_and_tc_fragment "type hb = | H : tb -> hb" in
  let _ = Pars.pars_and_tc_fragment "let select (i:tb) (x:'a) (y:'a) : Tot 'a = \
                                         match i with \
                                          | T -> x \
                                          | F -> y" in
  let _ = Pars.pars_and_tc_fragment "let select_int3 (i:int) (x:'a) (y:'a) (z:'a) : Tot 'a = \
                                         match i with \
                                          | 0 -> x \
                                          | 1 -> y \
                                          | _ -> z" in
  let _ = Pars.pars_and_tc_fragment "let select_bool (b:bool) (x:'a) (y:'a) : Tot 'a = \
                                         if b then x else y" in
  let _ = Pars.pars_and_tc_fragment "let select_string3 (s:string) (x:'a) (y:'a) (z:'a) : Tot 'a = \
                                         match s with \
                                         | \"abc\" -> x \
                                         | \"def\" -> y \
                                         | _ -> z" in
  let _ = Pars.pars_and_tc_fragment "let recons_m (x:list tb) = \
                                         match x with \
                                          | [] -> []  \
                                          | hd::tl -> hd::tl" in
  let _ = Pars.pars_and_tc_fragment "let rec copy_tb_list_2 (x:list tb) : Tot (list tb) = \
                                         match x with \
                                          | [] -> []  \
                                          | [hd] -> [hd]
                                          | hd1::hd2::tl -> hd1::hd2::copy_tb_list_2 tl" in
  let _ = Pars.pars_and_tc_fragment "let rec copy_list_2 (x:list 'a) : Tot (list 'a) = \
                                         match x with \
                                          | [] -> []  \
                                          | [hd] -> [hd]
                                          | hd1::hd2::tl -> hd1::hd2::copy_list_2 tl" in
  let _ = Pars.pars_and_tc_fragment "let (x1:int{x1>3}) = 6" in
  let _ = Pars.pars_and_tc_fragment "let (x2:int{x2+1>3 /\ not (x2-5>0)}) = 2" in
  let _ = Pars.pars_and_tc_fragment "let my_plus (x:int) (y:int) = x + y" in
  let _ = Pars.pars_and_tc_fragment "let (x3:int{forall (a:nat). a > x2}) = 7" in

  let _ = Pars.pars_and_tc_fragment "let idd (x: 'a) = x" in
  let _ = Pars.pars_and_tc_fragment "let revtb (x: tb) = match x with | T -> F | F -> T" in
  let _ = Pars.pars_and_tc_fragment "let id_tb (x: tb) = x" in
  let _ = Pars.pars_and_tc_fragment "let fst_a (x: 'a) (y: 'a) = x" in
  let _ = Pars.pars_and_tc_fragment "let id_list (x: list 'a) = x" in
  let _ = Pars.pars_and_tc_fragment "let id_list_m (x: list tb) = x" in //same as recons_m, but no pattern matching
  [ (0, (app apply [one; id; nm n]), (nm n))
  ; (1, (app id [nm x]), (nm x))
  ; (1, (app apply [tt; nm n; nm m]), (nm n))
  ; (2, (app apply [ff; nm n; nm m]), (nm m))
  ; (3, (app apply [apply; apply; apply; apply; apply; ff; nm n; nm m]), (nm m))
  ; (4, (app twice [apply; ff; nm n; nm m]), (nm m))
  ; (5, (minus one z), one)
  ; (6, (app pred [one]), z)
  ; (7, (minus one one), z)
  ; (8, (app mul [one; one]), one)
  ; (9, (app mul [two; one]), two)
  ; (10, (app mul [app succ [one]; one]), two)
  ; (11, (minus (encode 10) (encode 10)), z)
  ; (12, (minus (encode 100) (encode 100)), z)
  ; (13, (let_ x (encode 100) (minus (nm x) (nm x))), z)

  // ; (14, (let_ x (encode 1000) (minus (nm x) (nm x))), z) //takes ~10s; wasteful for CI
  ; (15, (let_ x (app succ [one])
            (let_ y (app mul [nm x; nm x])
               (let_ h (app mul [nm y; nm y])
                       (minus (nm h) (nm h))))), z)
  ; (16, (mk_let x (app succ [one])
            (mk_let y (app mul [nm x; nm x])
                    (mk_let h (app mul [nm y; nm y])
                            (minus (nm h) (nm h))))), z)
  ; (17, (let_ x (app succ [one])
            (let_ y (app mul [nm x; nm x])
               (let_ h (app mul [nm y; nm y])
                       (minus (nm h) (nm h))))), z)
  ; (18, (pred_nat (snat (snat znat))), (snat znat))
  ; (19, (minus_nat (snat (snat znat)) (snat znat)), (snat znat))
  ; (20, (minus_nat (encode_nat 10) (encode_nat 10)), znat)
  ; (21, (minus_nat (encode_nat 100) (encode_nat 100)), znat)
  // ; (22, (minus_nat (encode_nat 10000) (encode_nat 10000)), znat) // Stack overflow in Normalizer when run with mono
  // ; (23, (minus_nat (encode_nat 1000000) (encode_nat 1000000)), znat) //this one takes about 30 sec and ~3.5GB of memory. Stack overflow in NBE when run with mono
  ; (24, (tc_nbe "recons [0;1]"), (tc_nbe "[0;1]"))
  ; (241, (tc_nbe "recons [false;true;false]"), (tc_nbe "[false;true;false]"))
  ; (25, (tc_nbe "copy [0;1]"), (tc_nbe "[0;1]"))
  ; (26, (tc_nbe "rev [0;1;2;3;4;5;6;7;8;9;10]"), (tc_nbe "[10;9;8;7;6;5;4;3;2;1;0]"))
  // Type defs not yet implemented for NBE
  // ; (271, (tc_nbe "(FStar.String.substring \"abcdef\" 1 2)"), (tc_nbe "\"bc\"")) //VD: Not sure why, but this test fails on the normalizer
  // ; (27, (tc_nbe "(rev (FStar.String.list_of_string \"abcd\"))"), (tc_nbe "['d'; 'c'; 'b'; 'a']"))// -- CH: works up to an unfolding too much (char -> char')
  ; (28, (tc_nbe "(fun x y z q -> z) T T F T"), (tc_nbe "F"))
  ; (29, (tc_nbe "[T; F]"), (tc_nbe "[T; F]"))
  ; (31, (tc_nbe "id_tb T"), (tc_nbe "T"))
  ; (32, (tc_nbe "(fun #a x -> x) #tb T"), (tc_nbe "T"))
  ; (33, (tc_nbe "revtb T"), (tc_nbe "F"))
  ; (34, (tc_nbe "(fun x y -> x) T F"), (tc_nbe "T"))
  ; (35, (tc_nbe "fst_a T F"), (tc_nbe "T"))
  ; (36, (tc_nbe "idd T"), (tc_nbe "T"))
  ; (301, (tc_nbe "id_list [T]"), (tc_nbe "[T]"))
  ; (3012, (tc_nbe "id_list_m [T]"), (tc_nbe "[T]"))
  ; (302, (tc_nbe "recons_m [T; F]"), (tc_nbe "[T; F]"))
  ; (303, (tc_nbe "select T A1 A3"), (tc_nbe "A1"))
  ; (3031, (tc_nbe "select T 3 4"), (tc_nbe "3"))
  ; (3032, (tc_nbe "select_bool false 3 4"), (tc_nbe "4"))
  ; (3033, (tc_nbe "select_int3 1 7 8 9"), (tc_nbe "8"))
  ; (3034, (tc_nbe "[5]"), (tc_nbe "[5]"))
  ; (3035, (tc_nbe "[\"abcd\"]"), (tc_nbe "[\"abcd\"]"))
  ; (3036, (tc_nbe "select_string3 \"def\" 5 6 7"), (tc_nbe "6"))
  //; (3037, (tc_nbe "['c']"), (tc_nbe "['c']")) //VD: Fails unless FStar.Char is imported (see FStar.Tests.Pars)
  ; (305, (tc_nbe "idd T"), (tc_nbe "T"))
  ; (306, (tc_nbe "recons [T]"), (tc_nbe "[T]"))
  ; (307, (tc_nbe "copy_tb_list_2 [T;F;T;F;T;F;F]"), (tc_nbe "[T;F;T;F;T;F;F]"))
  ; (308, (tc_nbe "copy_list_2    [T;F;T;F;T;F;F]"), (tc_nbe "[T;F;T;F;T;F;F]"))

  ; (304, (tc_nbe "rev [T; F; F]"), (tc_nbe "[F; F; T]"))
  ; (305, (tc_nbe "rev [[T]; [F; T]]"), (tc_nbe "[[F; T]; [T]]"))

  ; (309, (tc_nbe "x1"), (tc_nbe "6"))
  ; (310, (tc_nbe "x2"), (tc_nbe "2"))
  //; (311, (tc_nbe "x3"), (tc_nbe "7")) // Throws parsing exceptiomn

  // Tests for primops
  ; (401, (tc_nbe "7 + 3"), (tc_nbe "10"))
  ; (402, (tc_nbe "true && false"), (tc_nbe "false"))
  ; (403, (tc_nbe "3 = 5"), (tc_nbe "false"))
  ; (404, (tc_nbe "\"abc\" ^ \"def\""), (tc_nbe "\"abcdef\"")) 

  // Test for refinements 
  //; (501, (tc_nbe "fun (x1:int{x1>(3+1)}) -> x1 + (1 + 0)"), (tc_nbe "fun (x1:int{x1>4}) -> x1 + 1")) // ZP : Fails because the two functions are not syntactically equal
  //; (502, (tc_nbe "x1:int{x1>(3+1)}"), (tc_nbe "x1:int{x1>4}"))
  ]


let run_either i r expected normalizer =
//    force_term r;
    BU.print1 "%s: ... \n\n" (BU.string_of_int i);
    let tcenv = Pars.init() in
    FStar.Main.process_args() |> ignore; //set the command line args for debugging
    let x = normalizer tcenv r in
    Options.init(); //reset them
    Options.set_option "print_universes" (Options.Bool true);
    Options.set_option "print_implicits" (Options.Bool true);
    // ignore (Options.set_options Options.Set "--debug Test --debug_level univ_norm --debug_level NBE");
    always i (term_eq (U.unascribe x) expected)

let run_interpreter i r expected = run_either i r expected (N.normalize [Env.Beta; Env.UnfoldUntil delta_constant; Env.Primops])
let run_nbe i r expected = run_either i r expected (FStar.TypeChecker.NBE.normalize_for_unit_test [FStar.TypeChecker.Env.UnfoldUntil delta_constant])
let run_interpreter_with_time i r expected =
  let interp () = run_interpreter i r expected in
  (i, snd (FStar.Util.return_execution_time interp))

let run_nbe_with_time i r expected =
  let nbe () = run_nbe i r expected in
  (i, snd (FStar.Util.return_execution_time nbe))

let run_tests run =
  Options.__set_unit_tests();
  let l = List.map (function (no, test, res) -> run no test res) tests in
  Options.__clear_unit_tests();
  l

let run_all_nbe () =
    BU.print_string "Testing NBE\n";
    let _ = run_tests run_nbe in
    BU.print_string "NBE ok\n"

let run_all_interpreter () =
    BU.print_string "Testing the normalizer\n";
    let _ = run_tests run_interpreter in
    BU.print_string "Normalizer ok\n"

let run_all_nbe_with_time () =
  BU.print_string "Testing NBE\n";
  let l = run_tests run_nbe_with_time in
  BU.print_string "NBE ok\n";
  l

let run_all_interpreter_with_time () =
  BU.print_string "Testing the normalizer\n";
  let l = run_tests run_interpreter_with_time in
  BU.print_string "Normalizer ok\n";
  l


// old compare
let run_both_with_time i r expected =
  let nbe () = run_nbe i r expected in
  let norm () = run_interpreter i r expected in
  FStar.Util.measure_execution_time "nbe" nbe;
  BU.print_string "\n";
  FStar.Util.measure_execution_time "normalizer" norm;
  BU.print_string "\n"

let compare () =
  BU.print_string "Comparing times for normalization and nbe\n";
  run_both_with_time 14 (let_ x (encode 1000) (minus (nm x) (nm x))) z

let compare_times l_int l_nbe =
  BU.print_string "Comparing times for normalization and nbe\n";
  List.iter2 (fun res1 res2 ->
                let (t1, time_int) = res1 in
                let (t2, time_nbe) = res2 in
                if (t1 = t2) // sanity check
                then
                  BU.print3 "Test %s\nNBE %s\nInterpreter %s\n"
                  // Figure out if there is division compatible with both F* and F#
                  //BU.print4 "%s: NBE %s    Interpreter %s    Ratio %s\n"
                    (BU.string_of_int t1)
                    (BU.string_of_float time_nbe)
                    (BU.string_of_float time_int)
                    //IN F*: (BU.string_of_float (time_nbe /. time_int))
                    //(BU.string_of_float (time_nbe / time_int)) //JUST FSHARP
                else
                  BU.print_string "Test numbers do not match...\n"
              ) l_int l_nbe

let run_all () =
    BU.print1 "%s" (P.term_to_string znat);
    let l_int = run_all_interpreter_with_time () in
    let l_nbe = run_all_nbe_with_time () in
    compare_times l_int l_nbe
