module PreorderClient

(*
 * In the absence of explicit opens,
 *   Preorder.fst takes precedence over FStar.Preorder
 *)

let y : int = Preorder.preorder_x
