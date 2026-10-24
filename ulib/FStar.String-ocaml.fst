(*
   Copyright 2008-2019 Microsoft Research

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
module FStar.String

(* The OCaml implementation, over UTF-8 encoded OCaml strings.  The
   definitions marked [custard_extern] are not compiled, their uses refer to
   the OCaml symbol directly. *)

open FStar.List.Tot

[@@custard_extern "(fun s -> BatList.init (BatUTF8.length s) (fun i -> BatUChar.code (BatUTF8.get s i)))"]
let list_of_string _ = admit ()

[@@custard_extern "(fun l -> BatUTF8.init (BatList.length l) (fun i -> BatUChar.chr (BatList.at l i)))"]
let string_of_list _ = admit ()

let string_of_list_of_string _ = admit ()

let list_of_string_of_list _ = admit ()

[@@custard_extern "(fun s -> Z.of_int (BatUTF8.length s))"]
let length _ = admit ()

[@@custard_extern "(fun i c -> BatUTF8.init (Z.to_int i) (fun _ -> BatUChar.chr c))"]
let make _ _ = admit ()

(* Splits on each separator in turn.  Like the pre-2.11 [BatString.nsplit],
   an empty piece splits into no pieces at all. *)
[@@custard_extern "(fun seps s -> BatList.fold_left (fun acc sep -> let usep = BatUTF8.init 1 (fun _ -> BatUChar.chr sep) in BatList.concat_map (fun x -> if x = \"\" then [] else BatString.split_on_string usep x) acc) [s] seps)"]
let split _ _ = admit ()

[@@custard_extern "BatString.concat"]
let concat _ _ = admit ()

[@@custard_extern "(fun x y -> Z.of_int (BatString.compare x y))"]
let compare _ _ = admit ()

[@@custard_extern "BatString.lowercase_ascii"]
let lowercase _ = admit ()

[@@custard_extern "BatString.uppercase_ascii"]
let uppercase _ = admit ()

[@@custard_extern "(fun s i -> BatUChar.code (BatUTF8.get s (Z.to_int i)))"]
let index _ _ = admit ()

[@@custard_extern "(fun s c -> let c = BatUChar.chr c in let r = Stdlib.ref (-1) in (try BatUTF8.iteri (fun c' i -> if BatUChar.eq c c' then (Stdlib.(:=) r i; Stdlib.raise Stdlib.Exit)) s with Stdlib.Exit -> ()); Z.of_int (Stdlib.(!) r))"]
let index_of _ _ = admit ()

[@@custard_extern "(fun s i j -> BatUTF8.init (Z.to_int j) (fun k -> BatUTF8.get s (k + Z.to_int i)))"]
let sub _ _ _ = admit ()

[@@custard_extern "(fun f s -> let b = Buffer.create (String.length s) in BatUTF8.iter (fun c -> Buffer.add_string b (f (BatUChar.code c))) s; Buffer.contents b)"]
let collect _ _ = admit ()

[@@custard_extern "(fun s i j -> BatUTF8.init (Z.to_int j) (fun k -> BatUTF8.get s (k + Z.to_int i)))"]
let substring _ _ _ = admit ()

[@@custard_extern "(fun s i -> BatUChar.code (BatUTF8.get s (Z.to_int i)))"]
let get _ _ = admit ()

let concat_length _ _ = admit ()

let list_of_concat _ _ = admit ()

let index_string_of_list _ _ = admit ()
