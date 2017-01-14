#light "off"
module FStar.Tests.Norm
//Normalization tests

open FStar
open FStar.Util
open FStar.Syntax.Syntax
open FStar.Tests.Pars
module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module SS = FStar.Syntax.Subst
module I = FStar.Ident
module P  = FStar.Syntax.Print
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
    mk (Tm_let((false, [{lbname=Inl x; lbunivs=[]; lbtyp=tun; lbdef=e; lbeff=FStar.Syntax.Const.effect_Tot_lid}]), e')) 
                           None dummyRange

let lid x = lid_of_path [x] dummyRange                           
let znat_l = S.lid_as_fv (lid "Z") Delta_constant (Some Data_ctor)
let snat_l = S.lid_as_fv (lid "S") Delta_constant (Some Data_ctor)
let tm_fv fv = mk (Tm_fvar fv) None dummyRange
let znat : term = tm_fv znat_l
let snat s      = mk (Tm_app(tm_fv snat_l, [as_arg s])) None dummyRange
let pat p = withinfo p tun.n dummyRange
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
    let lb = {lbname=Inl minus; lbeff=lid_of_path ["Pure"] dummyRange; lbunivs=[]; lbtyp=tun; 
              lbdef=subst [NM(minus, 0)] (U.abs [b x; b y] (mk_match (nm y) [zbranch; sbranch]) None)} in
    mk (Tm_let((true, [lb]), subst [NM(minus, 0)] (app (nm minus) [t1; t2]))) None dummyRange
let encode_nat n = 
    let rec aux out n = 
        if n=0 then out
        else aux (snat out) (n - 1) in 
    aux znat n

module N = TypeChecker.Normalize

let run i r expected = 
//    force_term r;
    Printf.printf "%d: ... \n" i;
    let _, tcenv = Pars.init() in
    FStar.process_args() |> ignore; //set the command line args for debugging
    let x = N.normalize [N.Beta; N.UnfoldUntil Delta_constant; N.Primops] tcenv r in
    Options.init(); //reset them
    Options.set_option "print_universes" (Options.Bool true);
    Options.set_option "print_implicits" (Options.Bool true);
//    Printf.printf "result = %s\n" (P.term_to_string x);
//    Printf.printf "expected = %s\n\n" (P.term_to_string expected);
    Util.always i (Util.term_eq (U.unascribe x) expected)
    
let run_all () = 
    Printf.printf "Testing the normalizer\n";
    let _ = Pars.pars_and_tc_fragment "let rec copy (x:list int) : Tot (list int) = \
                                           match x with \
                                            | [] -> []  \
                                            | hd::tl -> hd::copy tl" in
    let _ = Pars.pars_and_tc_fragment "let recons (x:list int) : Tot (list int) = \
                                           match x with \
                                            | [] -> []  \
                                            | hd::tl -> hd::tl" in
    let _ = Pars.pars_and_tc_fragment "let rev (x:list 'a) : Tot (list 'a) = \
                                            let rec aux (x:list 'a) (out:list 'a) : Tot (list 'a) = \
                                                match x with \
                                                | [] -> out \
                                                | hd::tl -> aux tl (hd::out) in \
                                            aux x []" in
    Options.__set_unit_tests();
    run 0 (app apply [one; id; nm n]) (nm n);
    run 1 (app apply [tt; nm n; nm m]) (nm n);
    run 2 (app apply [ff; nm n; nm m]) (nm m);
    run 3 (app apply [apply; apply; apply; apply; apply; ff; nm n; nm m]) (nm m);
    run 4 (app twice [apply; ff; nm n; nm m]) (nm m);
    run 5 (minus one z) one;
    run 6 (app pred [one]) z;
    run 7 (minus one one) z;
    run 8 (app mul [one; one]) one;
    run 9 (app mul [two; one]) two;
    run 10 (app mul [app succ [one]; one]) two;
    run 11 (minus (encode 10) (encode 10)) z;
    run 12 (minus (encode 100) (encode 100)) z;
    run 13 (let_ x (encode 100) (minus (nm x) (nm x))) z; 
//    run 13 (let_ x (encode 1000) (minus (nm x) (nm x))) z; //takes ~10s; wasteful for CI
    run 14 (let_ x (app succ [one])
            (let_ y (app mul [nm x; nm x])
                (let_ h (app mul [nm y; nm y]) 
                        (minus (nm h) (nm h))))) z;
    run 15 (mk_let x (app succ [one])
            (mk_let y (app mul [nm x; nm x])
                (mk_let h (app mul [nm y; nm y]) 
                          (minus (nm h) (nm h))))) z;
    run 16 (pred_nat (snat (snat znat))) (snat znat);
    run 17 (minus_nat (snat (snat znat)) (snat znat)) (snat znat);
    run 18 (minus_nat (encode_nat 100) (encode_nat 100)) znat;
    run 19 (minus_nat (encode_nat 10000) (encode_nat 10000)) znat;
    run 20 (minus_nat (encode_nat 10) (encode_nat 10)) znat;
//    run 21 (minus_nat (encode_nat 1000000) (encode_nat 1000000)) znat; //this one takes about 30 sec and ~3.5GB of memory
    Options.__clear_unit_tests();
    run 21 (tc "recons [0;1]") (tc "[0;1]");
    run 22 (tc "copy [0;1]") (tc "[0;1]");
    run 23 (tc "rev [0;1;2;3;4;5;6;7;8;9;10]") (tc "[10;9;8;7;6;5;4;3;2;1;0]");
//  run 24 (tc "(rev (FStar.String.list_of_string \"abcd\"))") (tc "['d'; 'c'; 'b'; 'a']"); -- CH: works up to an unfolding too much (char -> char')
    Printf.printf "Normalizer ok\n"
 
    
