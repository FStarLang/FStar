(*
   Documentation comments: sugar for the `doc` attribute, and nothing
   else.

   This file is also the regression test for the property that matters
   most about the marker. Every other comment form still lexes exactly as
   it always did -- two-star, three-star and empty comments all appear
   below, and none of them is documentation. The doc opener occurs
   nowhere in the tree today, so no existing lexeme changes meaning.

   Note that no comment here can quote a comment delimiter: F*, OCaml and
   menhir all nest them, so a delimiter written inside a comment either
   opens a comment or closes one early. That is worth knowing when
   documenting documentation.
*)
module DocsSugar

(*| Doubles 'x'. *)
let double (x:int) : int = x + x

(*| Triples 'x'.

    Continuation lines are dedented by their common indentation, so this
    paragraph sits flush with the first line rather than keeping the
    four spaces it is written with.

    A leading `*` would be part of the text rather than stripped: the
    payload is opaque, and deciding what a `*` means would be
    interpreting it. *)
let triple (x:int) : int = 3 * x

(** An ordinary comment, not documentation. `quadruple` must not appear
    in the exported index at all. *)
let quadruple (x:int) : int = 4 * x

(*************** A banner. Also an ordinary comment. ***************)

(*| Documented and attributed at once. The doc comment desugars to its
    own attribute set, so before `add_decorations` learned to
    concatenate them this was rejected as "more than one attribute set".
    Around a hundred declarations in `ulib` are written this way. *)
[@@ "opaque_to_smt"]
let attributed (x:int) : int = x

(*| A nested (* comment *) is part of the documentation text, not the
    end of it. *)
let nested (x:int) : int = x

(*| The empty-comment idiom still lexes as `(*` followed by `*)`, so it
    is a comment in expression position and not a marker. *)
let empty_comment_still_works (x:int) : int =
  (**) x + 1

(*| A tiny type. As for a hand-written attribute, this documents
    `flag` and neither `On` nor `Off`. *)
type flag =
  | On
  | Off

private
(*| A doc comment may sit anywhere among a declaration's decorations,
    including after a qualifier. This one is private, so it is absent
    from the exported index. *)
let hidden (x:int) : int = x
