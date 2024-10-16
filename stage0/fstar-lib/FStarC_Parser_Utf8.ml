(*
   Originally part of the ulex package with the following license:

   Copyright 2005 by Alain Frisch.

   Permission is hereby granted, free of charge, to any person obtaining
   a copy of this software and associated documentation files (the
   "Software"), to deal in the Software without restriction, including
   without limitation the rights to use, copy, modify, merge, publish,
   distribute, sublicense, and/or sell copies of the Software, and to
   permit persons to whom the Software is furnished to do so, subject to
   the following conditions:

   The above copyright notice and this permission notice shall be
   included in all copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
   EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
   MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
   NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
   LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
   OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
   WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*)


exception MalFormed

(* cf http://www.faqs.org/rfcs/rfc3629.html *)

let width = Array.make 256 (-1)
let () =
  for i = 0 to 127 do width.(i) <- 1 done;
  for i = 192 to 223 do width.(i) <- 2 done;
  for i = 224 to 239 do width.(i) <- 3 done;
  for i = 240 to 247 do width.(i) <- 4 done

let next s i =
  match s.[i] with
    | '\000'..'\127' as c ->
        Char.code c
    | '\192'..'\223' as c ->
	let n1 = Char.code c in
	let n2 = Char.code s.[i+1] in
        if (n2 lsr 6 != 0b10) then raise MalFormed;
        ((n1 land 0x1f) lsl 6) lor (n2 land 0x3f)
    | '\224'..'\239' as c ->
	let n1 = Char.code c in
	let n2 = Char.code s.[i+1] in
	let n3 = Char.code s.[i+2] in
        if (n2 lsr 6 != 0b10) || (n3 lsr 6 != 0b10) then raise MalFormed;
	let p =
          ((n1 land 0x0f) lsl 12) lor ((n2 land 0x3f) lsl 6) lor (n3 land 0x3f)
	in
	if (p >= 0xd800) && (p <= 0xdf00) then raise MalFormed;
	p
    | '\240'..'\247' as c ->
	let n1 = Char.code c in
	let n2 = Char.code s.[i+1] in
	let n3 = Char.code s.[i+2] in
	let n4 = Char.code s.[i+3] in
        if (n2 lsr 6 != 0b10) || (n3 lsr 6 != 0b10) || (n4 lsr 6 != 0b10)
	then raise MalFormed;
        ((n1 land 0x07) lsl 18) lor ((n2 land 0x3f) lsl 12) lor
        ((n3 land 0x3f) lsl 6) lor (n4 land 0x3f)
    | _ -> raise MalFormed


(* With this implementation, a truncated code point will result
   in Stream.Failure, not in MalFormed. *)

let from_stream s =
  match Stream.next s with
    | '\000'..'\127' as c ->
        Char.code c
    | '\192'..'\223' as c ->
	let n1 = Char.code c in
	let n2 = Char.code (Stream.next s) in
        if (n2 lsr 6 != 0b10) then raise MalFormed;
        ((n1 land 0x1f) lsl 6) lor (n2 land 0x3f)
    | '\224'..'\239' as c ->
	let n1 = Char.code c in
	let n2 = Char.code (Stream.next s) in
	let n3 = Char.code (Stream.next s) in
        if (n2 lsr 6 != 0b10) || (n3 lsr 6 != 0b10) then raise MalFormed;
        ((n1 land 0x0f) lsl 12) lor ((n2 land 0x3f) lsl 6) lor (n3 land 0x3f)
    | '\240'..'\247' as c ->
	let n1 = Char.code c in
	let n2 = Char.code (Stream.next s) in
	let n3 = Char.code (Stream.next s) in
	let n4 = Char.code (Stream.next s) in
        if (n2 lsr 6 != 0b10) || (n3 lsr 6 != 0b10) || (n4 lsr 6 != 0b10)
	then raise MalFormed;
        ((n1 land 0x07) lsl 18) lor ((n2 land 0x3f) lsl 12) lor
        ((n3 land 0x3f) lsl 6) lor (n4 land 0x3f)
    | _ -> raise MalFormed



let compute_len s pos bytes =
  let rec aux n i =
    if i >= pos + bytes then if i = pos + bytes then n else raise MalFormed
    else
      let w = width.(Char.code s.[i]) in
      if w > 0 then aux (succ n) (i + w)
      else raise MalFormed
  in
  aux 0 pos

let rec blit_to_int s spos a apos n =
  if n > 0 then begin
    a.(apos) <- next s spos;
    blit_to_int s (spos + width.(Char.code s.[spos])) a (succ apos) (pred n)
  end

let to_int_array s pos bytes =
  let n = compute_len s pos bytes in
  let a = Array.make n 0 in
  blit_to_int s pos a 0 n;
  a

(**************************)

let width_code_point p =
  if p <= 0x7f then 1
  else if p <= 0x7ff then 2
  else if p <= 0xffff then 3
  else if p <= 0x10ffff then 4
  else raise MalFormed

let store b p =
  if p <= 0x7f then
    Buffer.add_char b (Char.chr p)
  else if p <= 0x7ff then (
    Buffer.add_char b (Char.chr (0xc0 lor (p lsr 6)));
    Buffer.add_char b (Char.chr (0x80 lor (p land 0x3f)))
  )
  else if p <= 0xffff then (
    if (p >= 0xd800 && p < 0xe000) then raise MalFormed;
    Buffer.add_char b (Char.chr (0xe0 lor (p lsr 12)));
    Buffer.add_char b (Char.chr (0x80 lor ((p lsr 6) land 0x3f)));
    Buffer.add_char b (Char.chr (0x80 lor (p land 0x3f)))
  )
  else if p <= 0x10ffff then (
    Buffer.add_char b (Char.chr (0xf0 lor (p lsr 18)));
    Buffer.add_char b (Char.chr (0x80 lor ((p lsr 12) land 0x3f)));
    Buffer.add_char b (Char.chr (0x80 lor ((p lsr 6)  land 0x3f)));
    Buffer.add_char b (Char.chr (0x80 lor (p land 0x3f)))
  )
  else raise MalFormed


let from_int_array a apos len =
  let b = Buffer.create (len * 4) in
  let rec aux apos len =
    if len > 0 then (store b a.(apos); aux (succ apos) (pred len))
    else Buffer.contents b in
  aux apos len

let stream_from_char_stream s =
  Stream.from
    (fun _ ->
       try Some (from_stream s)
       with Stream.Failure -> None)
