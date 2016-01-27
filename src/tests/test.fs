#light "off"
module FStar.Tests.Test
open FStar.Syntax
open FStar
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module U = FStar.Syntax.Util
let r = Range.dummyRange
[<EntryPoint>] 
let main argv =
    let debug = argv.Length >= 1 && argv.[0] = "debug" in
//    Norm.run_all debug; 
//    Unif.run_all debug;
    FStar.Options.print_implicits := true;
    FStar.Options.print_real_names := true;
    FStar.Options.print_bound_var_types := true;
    let uvar = Unionfind.fresh S.Uvar in
    let uv = S.mk (S.Tm_uvar(uvar, S.tun)) None r in
    let list_uv = S.mk_Tm_app (S.fvar None (Ident.lid_of_path ["Prims"; "list"] r) r) [uv, None] None r in
    let x = S.new_bv None list_uv in
    let abs = U.abs [x, None] S.tun in
    Printf.printf "Abstraction is %s\n" (Print.term_to_string abs);
    let y = S.new_bv None S.tun in
    Unionfind.change uvar (S.Fixed(S.bv_to_name y, true));
    let abs' = U.abs [y, None] abs in
    Printf.printf "Closed abstraction is %s\n" (Print.term_to_string abs');
    0
     