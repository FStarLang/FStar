module CherryBoxedAttr
open FStar.All

(* [@@cherry_boxed] makes a non-recursive type a counted heap cell under
   Cherry, as a recursive one is: on a mutual bundle every type in it, and a
   variant as well as a record.  Passing one is passing a pointer, so a tail
   call taking one is a guaranteed tail call. *)

[@@FStar.Attributes.cherry_boxed]
noeq type inner = { a: int; name: string }
and outer = { i: inner; n: int; f: int -> int; w0: int; w1: int; w2: int; w3: int }

[@@FStar.Attributes.cherry_boxed]
type shape =
  | Circle of int
  | Rect of int & int

let area (s:shape) : int =
  match s with
  | Circle r -> 3 * r * r
  | Rect (w, h) -> w * h

let rec walk (o:outer) (k:int) : ML int =
  if k = 0 then o.n + o.i.a else step { o with n = o.f o.n } (k - 1) "x"
and step (o:outer) (k:int) (s:string) : ML int =
  walk { o with i = { o.i with name = s; a = o.i.a + 1 } } k

let main () : ML unit =
  let o = { i = { a = 1; name = "" }; n = 0; f = (fun x -> x + 2);
            w0 = 0; w1 = 1; w2 = 2; w3 = 3 } in
  FStar.IO.print_string (string_of_int (walk o 1000000) ^ "\n");
  FStar.IO.print_string (string_of_int (area (Circle 2) + area (Rect (3, 4))) ^ "\n");
  FStar.IO.print_string (if Rect (1, 2) = Rect (1, 2) && Circle 1 <> Circle 2 then "eq\n" else "neq\n")
