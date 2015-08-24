module S = String
let make len v : Prims.string = BatString.init len (fun x -> char_of_int v)
let strcat s t = s^t
let split seps s =
  let rec repeat_split acc = function
    | [] -> acc
    | sep::seps ->
       let l = BatList.flatten (BatList.map (fun x -> BatString.nsplit x (BatString.make 1 sep)) acc) in
       repeat_split l seps in
  repeat_split [s] seps
let compare x y = BatString.compare x y
let concat = BatString.concat
let length = BatString.length
let sub = S.sub
let get = S.get
let collect = BatString.replace_chars
