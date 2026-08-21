module InlineFields
open FStar.All
open FStar.Attributes

(* [| Bar of a & b] is a one-argument constructor pointing at a pair.  Custard
   inlines the pair, so [Bar] carries the two fields directly. *)
type foo =
  | Bar of bool & string
  | Qux of int

noeq type pair = { pa: bool; pb: string }

(* Anything that is not a tuple has to ask. *)
noeq type wrap =
  | W : [@@@custard_inline_field] p:pair -> wrap
  | V

(* Not asked for: [keep] still holds a [pair] behind a pointer. *)
noeq type keep = | K : p:pair -> n:int -> keep

let show (f:foo) : string =
  match f with
  | Bar (b, s) -> if b then s else "no"
  | Qux _ -> "q"

(* A whole-field binder: the pair has to be put back together, and the
   projection out of it taken apart again. *)
let showw (w:wrap) : string =
  match w with
  | W p -> if p.pa then p.pb else "no"
  | V -> "v"

(* Two reads of the same reconstructed pair. *)
let bothw (w:wrap) : string =
  match w with
  | W p -> (if p.pa then p.pb else p.pb)
  | V -> "v"

let mk (b:bool) (s:string) : foo = Bar (b, s)
let mkw (b:bool) (s:string) : wrap = W ({ pa = b; pb = s })
let mkk (b:bool) (s:string) : keep = K ({ pa = b; pb = s }) 3
let unk (k:keep) : string = match k with K p _ -> p.pb

(* A field read out of a value whose shape is not known here. *)
let fst_of (f:foo) : bool = match f with Bar (b, _) -> b | Qux _ -> false

let main () : ML unit =
  FStar.IO.print_string (show (mk true "a"));
  FStar.IO.print_string (showw (mkw true "b"));
  FStar.IO.print_string (bothw (mkw true "c"));
  FStar.IO.print_string (unk (mkk true "d"));
  FStar.IO.print_string (if fst_of (mk true "e") then "y" else "n")
