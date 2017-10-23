let make i ci = String.make (Z.to_int i) (Char.chr ci)
let strcat s t = s ^ t
let split seps s =
  let rec repeat_split acc = function
    | [] -> acc
    | sep::seps ->
       let usep = BatUTF8.init 1 (fun _ -> BatUChar.chr sep) in
       let l = BatList.flatten (BatList.map (fun x -> BatString.nsplit x usep) acc) in
       repeat_split l seps in
  repeat_split [s] seps
let compare x y = Z.of_int (BatString.compare x y)
let concat = BatString.concat
let length s = Z.of_int (BatUTF8.length s)
let strlen s = length s

let substring s i j =
  BatUTF8.init (Z.to_int j) (fun k -> BatUTF8.get s (k + Z.to_int i))
let sub s i j =
   substring s i (Z.of_int (BatUTF8.length s - (Z.to_int j) + 1))

let get s i = BatUChar.code (BatUTF8.get s (Z.to_int i))
let collect f s =
  let r = ref "" in
  BatUTF8.iter (fun c -> r := !r ^ f (BatUChar.code c)) s; !r
let lowercase = BatString.lowercase
let uppercase = BatString.uppercase
let index = get
let sub = substring
let list_of_string s = BatList.init (BatUTF8.length s) (fun i -> BatUChar.code (BatUTF8.get s i))
let string_of_list l = BatUTF8.init (BatList.length l) (fun i -> BatUChar.chr (BatList.at l i))
