type 'a t = 'a array

let of_list (l:'a list) = Array.of_list l

let length (a: 'a t) = Z.of_int (Array.length a)

let index (a: 'a t) (i:Z.t) = Array.get a (Z.to_int i)
