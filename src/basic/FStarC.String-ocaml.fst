(*
   Copyright 2008-2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.String

open FStarC.Effect
open FStar.Char
module I = FStarC.SmallInt

(* OCaml implementation.  [char] is an OCaml [int] holding a code point and
   [string] is UTF-8: [length], [get] and friends count code points, through
   Batteries' BatUTF8. *)

[@@custard_extern "String.length"]
let byte_length _ = admit ()

[@@custard_extern "(fun s i -> if i >= 0 && i < String.length s then Char.code (String.unsafe_get s i) else -1)"]
let byte_at _ _ = admit ()

[@@custard_extern "(fun s i -> try BatUChar.code (BatUTF8.look s i) with _ -> 0xFFFD)"]
private assume val code_point_at_slow : string -> I.t -> I.t

let code_point_at s i =
  let b = byte_at s i in
  if I.(b < of_int 0x80) then b else code_point_at_slow s i

let next_code_point s i =
  let b = byte_at s i in
  let w =
    if I.(b < of_int 0x80) then I.one
    else if I.(b < of_int 0xE0) then I.of_int 2
    else if I.(b < of_int 0xF0) then I.of_int 3
    else I.of_int 4 in
  let j = I.(i + w) in
  let n = byte_length s in
  if I.(j < n) then j else n

[@@custard_extern "(fun s i j -> let n = String.length s in let i = if i > 0 then i else 0 and j = if j < n then j else n in if j <= i then \"\" else String.sub s i (j - i))"]
let byte_substring _ _ _ = admit ()

(* Whether [t] occurs in [s] at offset [i]: compares [t]'s bytes from [k] on.
   The fuel bounds the recursion; it is never what stops it. *)
private
let rec occurs_at (s t:string) (i k tlen:I.t) (fuel:nat) : Tot bool (decreases fuel) =
  if fuel = 0 || I.(k >= tlen) then true
  else if byte_at s I.(i + k) = byte_at t k then occurs_at s t i I.(k + one) tlen (fuel - 1)
  else false

(* The pieces of [s] from [start] on, the earlier ones in [acc] in reverse.
   [i] is where to look for [t] next. *)
private
let rec split_from (s t:string) (slen tlen start i:I.t) (fuel:nat) (acc:list string)
  : Tot (list string) (decreases fuel)
  = if fuel = 0 || I.(i + tlen > slen) then
      List.Tot.rev (byte_substring s start slen :: acc)
    else if occurs_at s t i I.zero tlen (I.to_int tlen) then
      let j = I.(i + tlen) in
      split_from s t slen tlen j j (fuel - 1) (byte_substring s start i :: acc)
    else
      split_from s t slen tlen start I.(i + one) (fuel - 1) acc

let split_on_string s sep =
  let slen = byte_length s in
  let tlen = byte_length sep in
  if slen = I.zero then []
  else if tlen = I.zero then [s]
  else split_from s sep slen tlen I.zero I.zero (I.to_int slen + 1) []

[@@custard_extern "(fun i c -> BatUTF8.init (Z.to_int i) (fun _ -> BatUChar.chr c))"]
let make _ _ = admit ()

[@@custard_extern "(fun c -> BatUTF8.init 1 (fun _ -> BatUChar.chr c))"]
private assume val string_of_code_point : char -> string

(* Splits on each separator in turn.  As [split_on_string] has nothing for
   an empty piece, a separator drops the empty pieces left by those before
   it. *)
let split seps s =
  let rec go (acc:list string) (seps:list char) : Tot (list string) (decreases seps) =
    match seps with
    | [] -> acc
    | sep :: seps ->
      let usep = string_of_code_point sep in
      go (List.Tot.concatMap (fun x -> split_on_string x usep) acc) seps
  in
  go [s] seps

[@@custard_extern "(^)"]
let strcat _ _ = admit ()

[@@custard_extern "BatString.concat"]
let concat _ _ = admit ()

[@@custard_extern "(fun x y -> Z.of_int (BatString.compare x y))"]
let compare _ _ = admit ()

[@@custard_extern "(fun s -> Z.of_int (BatUTF8.length s))"]
let strlen _ = admit ()

[@@custard_extern "(fun s -> Z.of_int (BatUTF8.length s))"]
let length _ = admit ()

[@@custard_extern "BatString.lowercase_ascii"]
let lowercase _ = admit ()

[@@custard_extern "BatString.uppercase_ascii"]
let uppercase _ = admit ()

[@@custard_extern "BatString.escaped"]
let escaped _ = admit ()

[@@custard_extern "(fun c -> BatString.of_char (Char.chr c))"]
let string_of_char _ = admit ()

[@@custard_extern "(fun s i j -> BatUTF8.init (Z.to_int j) (fun k -> BatUTF8.get s (k + Z.to_int i)))"]
let substring _ _ _ = admit ()

[@@custard_extern "(fun s i -> BatUChar.code (BatUTF8.get s (Z.to_int i)))"]
let get _ _ = admit ()

[@@custard_extern "(fun f s -> let b = Buffer.create 16 in BatUTF8.iter (fun c -> Buffer.add_string b (f (BatUChar.code c))) s; Buffer.contents b)"]
let collect _ _ = admit ()

[@@custard_extern "(fun s c -> let c = BatUChar.chr c in let r = Stdlib.ref (-1) in (try BatUTF8.iteri (fun c' i -> if c = c' then (Stdlib.(:=) r i; Stdlib.raise_notrace Stdlib.Exit)) s with Stdlib.Exit -> ()); Z.of_int (Stdlib.(!) r))"]
let index_of _ _ = admit ()

let index s i = get s i

(* [BatUTF8.get s i] walks from the start of [s], so indexing in a loop is
   quadratic in the length of the string.  Both of these fold instead.
   Custard prints mangled names through [list_of_string], and a
   specialization name can be long; see doc/ref/custard.md section 30.15. *)
[@@custard_extern "(fun s -> List.rev (BatUTF8.fold (fun acc c -> BatUChar.code c :: acc) [] s))"]
let list_of_string _ = admit ()

[@@custard_extern "(fun l -> let b = BatUTF8.Buf.create 16 in List.iter (fun c -> BatUTF8.Buf.add_char b (BatUChar.chr c)) l; BatUTF8.Buf.contents b)"]
let string_of_list _ = admit ()

[@@custard_extern "(^)"]
let ( ^ ) _ _ = admit ()
