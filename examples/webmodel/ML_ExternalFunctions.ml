open Prims

let trim : Prims.string -> Prims.string = fun s  -> String.trim s 
let int_of_string : Prims.string -> Prims.int =
  fun s  -> Prims.parse_int s 
let substringImpl : Prims.string -> Prims.nat -> Prims.nat -> Prims.string =
  fun s  -> fun i  -> fun l  -> String.sub s (Z.to_int i) (Z.to_int l) 
let randomVal : Prims.nat -> Prims.string =
  fun length ->
    let gen() = match Random.int(Z.to_int ((Z.of_int 26)+(Z.of_int 26)+(Z.of_int 10))) with
        n when (Z.of_int n < Z.of_int 26) -> Z.of_int (int_of_char 'a') + (Z.of_int n)
      | n when (Z.of_int n < (Z.of_int 26 + Z.of_int 26)) -> Z.of_int (int_of_char 'A') + (Z.of_int n) - (Z.of_int 26)
      | n -> Z.of_int (int_of_char '0') + (Z.of_int n) - (Z.of_int 26) - (Z.of_int 26) in
    let gen _ = String.make 1 (char_of_int(Z.to_int (gen()))) in
    String.concat "" (Array.to_list (Array.init (Z.to_int length) gen));;
