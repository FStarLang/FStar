module BoxedFields
open FStar.All
open FStar.Attributes

(* Section 5.7.  [@@custard_boxed_fields] withdraws the inlining of tuple
   fields that [InlineFields] relies on, so [Bar] holds one field of pair type
   -- what the ML extraction emits, and what a consumer that marshals the type
   from its own OCaml declaration reads back. *)
[@@custard_boxed_fields]
type abi =
  | Bar of bool & string
  | Qux of int
  | Sub of nested

(* The attribute is written once on a mutually recursive group -- the shape
   [FStarC.Extraction.KrmlAst] is declared in -- and holds for every type in
   it. *)
and nested =
  | Nested of bool & string
  | Leaf

noeq type pair = { pa: bool; pb: string }

(* The withdrawal is of what Custard does uninvited.  A field that asks is
   still inlined. *)
[@@custard_boxed_fields]
noeq type asked =
  | W : [@@@custard_inline_field] p:pair -> asked
  | V

(* The control: no attribute, so the pair is inlined as usual. *)
type ordinary =
  | Baz of bool & string
  | Quux of int

let show (f:abi) : string =
  match f with
  | Bar (b, s) -> if b then s else "no"
  | Sub (Nested (b, s)) -> if b then s else "no"
  | Sub Leaf -> "l"
  | Qux _ -> "q"

let showo (f:ordinary) : string =
  match f with
  | Baz (b, s) -> if b then s else "no"
  | Quux _ -> "q"

let showw (w:asked) : string =
  match w with
  | W p -> if p.pa then p.pb else "no"
  | V -> "v"

let mk (b:bool) (s:string) : abi = Bar (b, s)
let mko (b:bool) (s:string) : ordinary = Baz (b, s)
let mkw (b:bool) (s:string) : asked = W ({ pa = b; pb = s })

let main () : ML unit =
  FStar.IO.print_string (show (mk true "a"));
  FStar.IO.print_string (showo (mko true "b"));
  FStar.IO.print_string (showw (mkw true "c"))
