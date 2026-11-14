module CherryUnboxCycle
module U32 = FStar.UInt32
open FStar.All

(* Both [term & bool] and [lam] are on a cycle through [term], which is boxed
   and breaks it, so neither needs a cell of its own: the pair is two words,
   stored inline in its list cell, and [lam] is no function's parameter or
   result, stored inline in the [Lam] cell. *)
noeq type term =
  | Var : int -> term
  | App : term -> list (term & bool) -> term
  | Lam : lam -> term
and lam = { body: term; arg: term; name: string }

let rec size (t: term) : ML int =
  match t with
  | Var _ -> 1
  | App h args -> List.fold_left (fun n (a, _) -> n + size a) (size h) args
  | Lam l -> size l.body + size l.arg + 1

let main () : ML U32.t =
  let t = App (Var 0) [(Var 1, true); (Lam { body = Var 2; arg = Var 3; name = "x" }, false)] in
  if size t = 5 then 0ul else 1ul
