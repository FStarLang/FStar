let make i c = BatUTF8.init (Z.to_int i) (fun _ -> BatUChar.chr c)
let strcat s t = s ^ t
let op_Hat s t =  strcat s t

(* restore pre-2.11 BatString.nsplit behavior,
   see https://github.com/ocaml-batteries-team/batteries-included/issues/845 *)
let batstring_nsplit s t =
  if s = "" then [] else BatString.split_on_string t s

let split seps s =
  let rec repeat_split acc = function
    | [] -> acc
    | sep::seps ->
       let usep = BatUTF8.init 1 (fun _ -> BatUChar.chr sep) in
       let l = BatList.flatten (BatList.map (fun x -> batstring_nsplit x usep) acc) in
       repeat_split l seps in
  repeat_split [s] seps
let compare x y = Z.of_int (BatString.compare x y)
type char = FStar_Char.char
let concat = BatString.concat
let length s = Z.of_int (BatUTF8.length s)
let strlen s = length s

let substring s i j =
  BatUTF8.init (Z.to_int j) (fun k -> BatUTF8.get s (k + Z.to_int i))
let sub = substring

let get s i = BatUChar.code (BatUTF8.get s (Z.to_int i))
let collect f s =
  let r = ref "" in
  BatUTF8.iter (fun c -> r := !r ^ f (BatUChar.code c)) s; !r
let lowercase = BatString.lowercase
let uppercase = BatString.uppercase
let escaped = BatString.escaped
let index = get
exception Found of int
let index_of s c =
    let c = BatUChar.chr c in
    try let _ = BatUTF8.iteri (fun c' i -> if c = c' then raise (Found i) else ()) s in Z.of_int (-1)
    with Found i -> Z.of_int i
let list_of_string s = BatList.init (BatUTF8.length s) (fun i -> BatUChar.code (BatUTF8.get s i))
let string_of_list l = BatUTF8.init (BatList.length l) (fun i -> BatUChar.chr (BatList.at l i))
let string_of_char (c:char) = BatString.of_char (Char.chr c)
