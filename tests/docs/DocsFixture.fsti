(*
   Fixture for the F* documentation tracer bullet.

   Documentation is authored *explicitly*, as an ordinary attribute on
   an ordinary top-level declaration. There is no comment syntax
   involved: [@@doc [...]] is just an attribute, and its payload is a
   list of opaque strings -- one per line -- that F* stores and hands
   back unchanged, without parsing, joining or rendering them.

   This interface is the authoritative description of what the module
   exports, so it is what --export_docs documents and what an IDE
   lookup from another module reports.
*)
module DocsFixture

(* Several lines. F* stores them as written: it does not join them, does
   not strip them, and attaches no meaning to their contents. *)
[@@doc ["Increments 'x'.";
        "";
        "This text is written in the interface, which is what clients of";
        "this module see. Opaque text is escaped by the HTML renderer:";
        "<unsafe> & \"quoted\"."]]
val incr (x:int) : int

(* No [doc] attribute. This declaration is exported with a null doc, and
   an IDE lookup asking for documentation must answer null rather than
   fail; the implementation's documentation must not fill the gap. *)
val decr (x:int) : int

[@@doc ["A tiny colour.";
        "The typechecker copies the attributes of a type definition onto each";
        "of its data constructors, so this text must be reported for 'colour'";
        "and for neither 'Red' nor 'Blue'."]]
type colour =
  | Red
  | Blue

(* A computation that has a contract, which the exported type reports as
   the effect stores it: 'pre' is the requires, and 'post' is abstracted
   over the result, so the ensures is the body of a one-binder 'abs'. The
   binder's own type restates the requires -- that is how a Lemma's post
   is built -- which a consumer reading the contract should expect.

   'incr' and 'decr' above are 'Tot', and report a null 'pre' and 'post'.
   Without this declaration nothing in the suite exercises an effect that
   has a contract at all. *)
[@@doc ["Adding a positive number gives a larger one."]]
val incr_grows (x:int) (k:int) : Lemma
  (requires k > 0)
  (ensures  x + k > x)

(* A total function whose result is refined: the specification is in the
   result type rather than in a contract, so 'post' stays null and the
   refinement travels inside 'res'. *)
[@@doc ["Doubles a natural number, which cannot shrink it."]]
val double_nat (n:nat) : m:nat{m >= n}
