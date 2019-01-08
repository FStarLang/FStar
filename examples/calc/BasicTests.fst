module BasicTests

open FStar.Preorder
open FStar.Calc

(* Ouch, (>=) doesn't typecheck as a preorder *)
let (<=) : relation int = (fun x y -> x <= y <: Type)
let (>=) : relation int = (fun x y -> x >= y <: Type)
let (>) : relation int = (fun x y -> x > y <: Type)
let (<) : relation int = (fun x y -> x < y <: Type)

let test1 () = assert_norm (calc_chain_compatible [(<); (<=)] (<))
let test2 () = assert_norm (calc_chain_compatible [(<=); (<)] (<))
let test3 () = assert_norm (calc_chain_compatible [(<); (<)] (<))
let test4 () = assert_norm (calc_chain_compatible [(<)] (<))
let test5 () = assert_norm (calc_chain_compatible [(<); (==); (<=)] (<))

[@expect_failure] let test6 () = assert_norm (not (calc_chain_compatible [(<)] (==)))
[@expect_failure] let test7 () = assert_norm (calc_chain_compatible [(<=)] (<))
