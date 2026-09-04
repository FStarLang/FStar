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

(* No [doc] attribute. This declaration must not appear in the exported
   documentation at all, and an IDE lookup asking for documentation must
   answer null rather than fail. *)
val decr (x:int) : int

[@@doc ["A tiny colour.";
        "The typechecker copies the attributes of a type definition onto each";
        "of its data constructors, so this text must be reported for 'colour'";
        "and for neither 'Red' nor 'Blue'."]]
type colour =
  | Red
  | Blue
