module NormForExtraction

(* Section 31.  EverParse's CDDL tool puts

     [@@normalize_for_extraction (nbe :: T.steps)]

   on every definition it generates, and that attribute is the whole reason
   the krml pipeline never meets the AST interpreter: F* reduces the
   definiens against the concrete AST *before* the extractor sees it.  Custard
   has its own front end and so has to honour it itself.

   [validate] below is that shape in miniature: a recursive interpreter over
   an AST, whose argument is a closed constant.  Unfolded against that
   constant it is three comparisons; left as written it is a [list] and a
   datatype the C backend has no representation for.

   The steps are the interesting part -- a hand-curated whitelist, exactly as
   [CDDL.Pulse.AST.Tactics.steps] is.  [prog] and [validate] unfold; nothing
   else does, and in particular [step] does not, so what comes out must still
   contain a call to it. *)

open FStar.Pervasives
module U32 = FStar.UInt32

type ast =
  | Lit  : U32.t -> ast
  | Add  : ast -> ast -> ast
  | Many : list ast -> ast

(* Deliberately *not* in the whitelist: it must survive as a call, which is
   what says the reduction stopped where it was told to. *)
let step (x: U32.t) : U32.t = U32.add_mod x 1ul

let rec eval (a: ast) : Tot U32.t (decreases a) =
  match a with
  | Lit n -> step n
  | Add x y -> U32.add_mod (eval x) (eval y)
  | Many l -> eval_list l

and eval_list (l: list ast) : Tot U32.t (decreases l) =
  match l with
  | [] -> 0ul
  | a :: tl -> U32.add_mod (eval a) (eval_list tl)

let prog : ast = Many [Lit 1ul; Add (Lit 2ul) (Lit 3ul); Lit 4ul]

let steps = [delta_only [`%eval; `%eval_list; `%prog]; zeta; iota; primops]

[@@normalize_for_extraction steps]
let validate () : U32.t = eval prog

let main () : FStar.All.ML unit =
  FStar.IO.print_string (U32.to_string (validate ()));
  FStar.IO.print_string "\n"
