module LetRecRefinedResultCall

(* The SMT solver must get the type of the recursive call, a list of
   elements of a refinement over the binders [a] and [p], from the typing
   axiom of the function: the binders must be encoded in the same way in
   the body as in the axiom. *)
open FStar.List.Tot

let rec list_refb (#a:eqtype) (#p:a -> Tot bool) (l:list a{for_all p l})
  : Tot (l':list (x:a{ p x }){ length l == length l' })
  = match l with
    | hd :: tl -> hd :: list_refb #a #p tl
    | [] -> []
