let make i c = BatUTF8.init (Z.to_int i) (fun _ -> BatUChar.chr c)
let strcat s t = s ^ t
let op_Hat s t =  strcat s t

(* Stack-safe replacement for BatString.split_on_string.
   BatString.find_from is not tail-recursive and overflows on long strings. *)
let batstring_nsplit s t =
  if s = "" then []
  else if t = "" then invalid_arg "batstring_nsplit: empty separator"
  else
    let slen = String.length s in
    let tlen = String.length t in
    let find_sep start =
      let result = ref (-1) in
      let i = ref start in
      while !i + tlen <= slen && !result = -1 do
        if String.sub s !i tlen = t then result := !i
        else i := !i + 1
      done;
      !result
    in
    let rec collect acc start =
      if start > slen then List.rev acc
      else if start = slen then List.rev ("" :: acc)
      else
        let p = find_sep start in
        if p = -1 then List.rev (String.sub s start (slen - start) :: acc)
        else
          let tok = String.sub s start (p - start) in
          collect (tok :: acc) (p + tlen)
    in
    collect [] 0

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
let lowercase = BatString.lowercase_ascii
let uppercase = BatString.uppercase_ascii
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
