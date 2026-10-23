(* Model implementation of FStar.Parse: verified, but never extracted (the real
   implementation is native, FStar.Parse-ocaml.fst).  It accepts an optional
   sign followed by decimal digits, a subset of what OCaml's int_of_string_opt
   accepts. *)
module FStar.Parse

let bool_of_string s =
  if s = "true" then Some true
  else if s = "false" then Some false
  else None

let digit (c:FStar.Char.char) : option nat =
  let n = FStar.UInt32.v (FStar.Char.u32_of_char c) in
  if 48 <= n && n <= 57 then Some (n - 48) else None

let rec digits (acc:nat) (cs:list FStar.Char.char) : Tot (option nat) (decreases cs) =
  match cs with
  | [] -> Some acc
  | c :: cs ->
    match digit c with
    | Some d -> digits (10 * acc + d) cs
    | None -> None

let int_of_string s =
  match FStar.String.list_of_string s with
  | [] -> None
  | c :: cs ->
    let n = FStar.UInt32.v (FStar.Char.u32_of_char c) in
    if (n = 45 || n = 43) && Cons? cs then
      (match digits 0 cs with
       | Some d -> Some (if n = 45 then - d else d)
       | None -> None)
    else
      (match digits 0 (c :: cs) with
       | Some d -> Some d
       | None -> None)
