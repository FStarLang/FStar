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
let let_ x e e' : term = app (U.abs [b x] e') [e]
let mk_let x e e' : term = 
    let e' = FStar.Syntax.Subst.subst [NM(x, 0)] e' in
    mk (Tm_let((false, [{lbname=Inl x; lbunivs=[]; lbtyp=tun; lbdef=e; lbeff=lid_of_path ["Pure"] dummyRange}]), e')) 
                           None dummyRange

let lid x = lid_of_path [x] dummyRange                           
let znat_l = S.fv (lid "Z") None
let snat_l = S.fv (lid "S") None
let tm_fv fv = mk (Tm_fvar fv) None dummyRange
let znat : term = tm_fv znat_l
let snat s      = mk (Tm_app(tm_fv snat_l, [arg s])) None dummyRange
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
              lbdef=subst [NM(minus, 0)] (U.abs [b x; b y] (mk_match (nm y) [zbranch; sbranch]))} in
    mk (Tm_let((true, [lb]), subst [NM(minus, 0)] (app (nm minus) [t1; t2]))) None dummyRange
let encode_nat n = 
    let rec aux out n = 
        if n=0 then out
        else aux (snat out) (n - 1) in 
    aux znat n


let run r expected = 
//    force_term r;
//    Printf.printf "redex = %s\n" (P.term_to_string r);
    let x = FStar.TypeChecker.Normalize.normalize [] TypeChecker.Env.dummy r in
    Printf.printf "result = %s\n" (P.term_to_string x);
    Printf.printf "expected = %s\n\n" (P.term_to_string expected);
    assert (Util.term_eq x expected)
    
let run_all debug = 
    if debug then TypeChecker.Normalize.debug();
    run (app apply [one; id; nm n]) (nm n);
    run (app apply [tt; nm n; nm m]) (nm n);
    run (app apply [ff; nm n; nm m]) (nm m);
    run (app apply [apply; apply; apply; apply; apply; ff; nm n; nm m]) (nm m);
    run (app twice [apply; ff; nm n; nm m]) (nm m);
    run (minus one z) one;
    run (app pred [one]) z;
    run (minus one one) z;
    run (app mul [one; one]) one;
    run (app mul [two; one]) two;
    run (app mul [app succ [one]; one]) two;
    run (minus (encode 10) (encode 10)) z;
    run (minus (encode 100) (encode 100)) z;
    run (let_ x (encode 1000) (minus (nm x) (nm x))) z;
    run (let_ x (app succ [one])
        (let_ y (app mul [nm x; nm x])
            (let_ h (app mul [nm y; nm y]) 
                    (minus (nm h) (nm h))))) z;
    run (mk_let x (app succ [one])
        (mk_let y (app mul [nm x; nm x])
            (mk_let h (app mul [nm y; nm y]) 
                      (minus (nm h) (nm h))))) z;
    run (pred_nat (snat (snat znat))) (snat znat);
    run (minus_nat (snat (snat znat)) (snat znat)) (snat znat);
    run (minus_nat (encode_nat 100) (encode_nat 100)) znat;
    run (minus_nat (encode_nat 10000) (encode_nat 10000)) znat;
    run (minus_nat (encode_nat 10) (encode_nat 10)) znat
//    run (minus_nat (encode_nat 1000000) (encode_nat 1000000)) znat
    
