module BasicTests

open FStar.Preorder
open FStar.Calc

(* Ouch, (>=) doesn't typecheck as a preorder *)
let (<=) : relation int = (fun x y -> x <= y <: Type)
let (>=) : relation int = (fun x y -> x >= y <: Type)
let (>) : relation int = (fun x y -> x > y <: Type)
let (<) : relation int = (fun x y -> x < y <: Type)

let test1 () = assert (calc_chain_compatible [(<); (<=)] (<))
let test2 () = assert (calc_chain_compatible [(<=); (<)] (<))
let test3 () = assert (calc_chain_compatible [(<); (<)] (<))
let test4 () = assert (calc_chain_compatible [(<)] (<))
let test5 () = assert (calc_chain_compatible [(<); (==); (<=)] (<))

[@expect_failure] let test6 () = assert (not (calc_chain_compatible [(<)] (==)))
[@expect_failure] let test7 () = assert (calc_chain_compatible [(<=)] (<))
