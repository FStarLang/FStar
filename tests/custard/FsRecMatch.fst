(* FStarLang/FStar#4622, section 122.2.  A field's value begins after its
   label, not at the column the label does, so a [match] that is the value of
   a field has its bars under the [match] -- and not under the label, where
   they are offside of it (FS0058).  Registered on the F# leg, whose build is
   the check: the defect is a program that does not compile. *)
module FsRecMatch

open FStar.All

type r = { a : option string; b : int }

let mk (xs : list string) (n : int) : r =
  { a = (match xs with
         | [] -> None
         | x :: _ -> Some x);
    b = n }

(* Every field multi-line, and one nested record: a later field's label is
   at the record's column plus two, and its value after that. *)
type s = { first : int; inner : r; last : bool }

let mk2 (xs : list string) (k : int) : s =
  { first = (match xs with
             | [] -> k
             | _ -> k + 1);
    inner = { a = (match xs with
                   | [] -> None
                   | x :: _ -> Some x);
              b = (match xs with
                   | [] -> 0
                   | _ -> 1) };
    last = (match xs with
            | [] -> true
            | _ -> false) }

let main () : ML Int32.t =
  let v = mk ["x"] 3 in
  let w = mk2 [] 5 in
  let u = mk2 ["y"] 5 in
  if v.a = Some "x" && v.b = 3
     && w.first = 5 && w.inner.a = None && w.inner.b = 0 && w.last
     && u.first = 6 && u.inner.a = Some "y" && u.inner.b = 1 && not u.last
  then 0l else 1l
