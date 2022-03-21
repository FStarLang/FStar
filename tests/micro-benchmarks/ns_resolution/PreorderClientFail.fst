module PreorderClientFail

open FStar

(*
 * By explicitly opening the FStar namespace,
 *   Preorder below resolves to FStar.Preorder, and hence the code fails
 *)

[@@ expect_failure [72]]
let y : int = Preorder.preorder_x
