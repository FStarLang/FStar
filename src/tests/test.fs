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
    let uvar1 = Unionfind.fresh S.Uvar in
    let uvar2 = Unionfind.fresh S.Uvar in
    let uv1 = S.mk (S.Tm_uvar(uvar1, S.tun)) None r in
    let uv2 = S.mk (S.Tm_uvar(uvar2, S.tun)) None r in
    let list_uv1 = S.mk_Tm_app (S.fvar (Ident.lid_of_path ["Prims"; "list"] r) S.Delta_constant None) [uv1, None] None r in
    let x = S.new_bv None uv2 in
    let abs = U.abs [x, None] S.tun None in
    Printf.printf "Abstraction is %s\n" (Print.term_to_string abs);
    let y = S.new_bv None S.tun in
    Unionfind.change uvar2 (S.Fixed (list_uv1));
    Unionfind.change uvar1 (S.Fixed(S.bv_to_name y));
    let abs' = U.abs [y, None] abs None in
    Printf.printf "Closed abstraction is %s\n" (Print.term_to_string abs');
    0
     