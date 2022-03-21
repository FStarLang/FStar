module PreorderClient

(*
 * Preorder is resolved to FStar.Preorder, and hence the failure
 *   F* emits a warning about the shadowing
 *)

[@@ expect_failure [72]]
let y : int = Preorder.preorder_x
