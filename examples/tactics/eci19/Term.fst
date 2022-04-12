module Term

open FStar.Tactics

(*
When using tactics and metaprogramming, it is crucial to both be able
to inspect terms and goals, and to construct them efficiently. Meta-F*
exposes the syntax of F* (terms, binders, types, etc) as abstract types
with some primitives to inspect and construct them.

For instance, a value in the `term` type represents an F* term, we have
already seen values of type `term` before: quotations. A quotation
such as (`0) is a value of type `term` and *represents* the term 0 (of
type int). But it is distinct from 0! A quotation is just the *syntax*
of a term: while `1 + 1` is equal to `2`, the quotation (`(1 + 1)) is
distinct from (`2).

The `term` type is abstract. The only way to use it is via primitives
such as `inspect` and `pack`, which allow to map from the `term` type
into the following view

  noeq
  type term_view =
    | Tv_Var    : v:bv -> term_view
    | Tv_BVar   : v:bv -> term_view
    | Tv_FVar   : v:fv -> term_view
    | Tv_App    : hd:term -> a:argv -> term_view
    | Tv_Abs    : bv:binder -> body:term -> term_view
    | Tv_Arrow  : bv:binder -> c:comp -> term_view
    | Tv_Type   : unit -> term_view
    | Tv_Refine : bv:bv -> ref:term -> term_view
    | Tv_Const  : vconst -> term_view
    | Tv_Uvar   : int -> ctx_uvar_and_subst -> term_view
    | Tv_Let    : recf:bool -> bv:bv -> def:term -> body:term -> term_view
    | Tv_Match  : scrutinee:term -> brs:(list branch) -> term_view
    | Tv_AscribedT : e:term -> t:term -> tac:option term -> term_view
    | Tv_AscribedC : e:term -> c:comp -> tac:option term -> term_view
    | Tv_Unknown  : term_view // Baked in "None"

  val inspect : term -> Tac term_view
  val pack : term_view -> Tac view

Calling `inspect` on a term reveals *one level* of its syntax tree,
while `pack` goes the other way around and allows to build terms from
the view. Here are some examples of using them to inspect quotations.
*)

let _ =
  run_tactic (fun () -> match inspect (`2) with
                     | Tv_Const _ -> print "It's a constant"
                     | _ -> fail "Uh-oh!")

let _ =
  run_tactic (fun () -> match inspect (`(1 + 1)) with
                     | Tv_App _ _ -> print "It's an application"
                     | _ -> fail "Uh-oh!")

(*
`pack` goes the other way around, and constructs terms from the view.
Let us build some terms and display them with `term_to_string`.
*)

let _ =
  run_tactic (fun () -> let t = pack (Tv_Const (C_Int 99)) in
                     print ("t1 = " ^ term_to_string t))

let _ =
  run_tactic (fun () -> let t = pack (Tv_App (`(+)) ((`42), Q_Explicit)) in
                     print ("t2 = " ^ term_to_string t))

(*
We can use either quotations or `pack` to build syntax, as well as combine them
if that's more convenient:
*)

let oneplusone1 : int = _ by (exact (`(1 + 1)))
let oneplusone2 : int = _ by (exact (pack (Tv_App (`((+) 1)) ((`1), Q_Explicit))))


let one_t () : Tac term = pack (Tv_Const (C_Int 1))

let oneplusone3 : int = _ by (exact (pack (Tv_App (pack (Tv_App (`(+)) (one_t (), Q_Explicit))) (one_t (), Q_Explicit))))

(* Exercise: print the definitions of the `oneplusone` variants above. *)

(* Using the view explicitly can be very verbose (as `oneplusone3` shows). Hence,
we usually prefer static quotations such as the one we used in `oneplusone1`, which
can be thought of as simply an abbreviation for a sequence of `pack` calls.

However, sometimes we want to take an existing `term` representation
and modify it, say by applying it to a function. We can use
*antiquotations*, marked by `# within a quotation, in order to do
that. An antiquotation withing a static quotation marks a piece of the
represented syntax that is to be filled with some other `term`.

For instance, if we have a term `x`, we can add 1 to it like this:
*)

let add_one (t:term) : Tac term = `(`#t + 1)
let add_terms (t1 t2 : term) : Tac term = `(`#t1 + `#t2)

let zeroplusone : int = _ by (exact (add_one (`0)))

let twoplusthree : int = _ by (exact (add_terms (`2) (`3)))
