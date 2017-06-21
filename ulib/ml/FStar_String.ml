let make i = String.make (Z.to_int i)
let strcat s t = s^t
let split seps s =
  let rec repeat_split acc = function
    | [] -> acc
    | sep::seps ->
       let l = BatList.flatten (BatList.map (fun x -> BatString.nsplit x (BatString.make 1 sep)) acc) in
       repeat_split l seps in
  repeat_split [s] seps
let compare x y = Z.of_int (BatString.compare x y)
let concat = BatString.concat
let length s = Z.of_int (BatString.length s)
let sub s i j = BatString.slice ~first:(Z.to_int i) ~last:(Z.to_int j) s
let get s i = FStar_List.nth (BatString.to_list s) i
let collect = BatString.replace_chars
let lowercase = String.lowercase
let index = get
let substring s i j= String.sub s (Z.to_int i) (Z.to_int j)
let sub = substring
let list_of_string = BatString.explode
let string_of_list = BatString.implode
