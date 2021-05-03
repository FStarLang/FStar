module My.PreorderClientFail

(*
 * In the absence of explicit opens,
 *   Preorder resolves to Preorder.fst, and hence the code below fails
 *)

[@@ expect_failure [72]]
let y : int = Preorder.my_preorder_x
