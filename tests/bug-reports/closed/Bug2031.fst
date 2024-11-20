module Bug2031

let rec add_n_t (n:nat) : Type =
    if n = 0 then int
    else int -> add_n_t (n-1)

let f11 (ff : add_n_t 1) = ff 1

let f21 (ff : add_n_t 2) = ff 1
let f22 (ff : add_n_t 2) = ff 1 2

let f31 (ff : add_n_t 3) = ff 1
let f32 (ff : add_n_t 3) = ff 1 2
let f33 (ff : add_n_t 3) = ff 1 2 3

let f41 (ff : add_n_t 4) = ff 1
let f42 (ff : add_n_t 4) = ff 1 2
let f43 (ff : add_n_t 4) = ff 1 2 3
let f44 (ff : add_n_t 4) = ff 1 2 3 4

val comp : #a:_ -> #b:_ -> #c:_ -> (b -> c) -> (a -> b) -> (a -> c)
let comp f g = fun x -> f (g x)

let rec mk_add_n (n:nat) : add_n_t n =
    if n = 0 then 0
    else if n = 1 then (fun (x:int) -> x)
    else
     fun (x:int) ->
       let f1 y = x + y in
       comp #int #int #(add_n_t (n-2)) (mk_add_n (n-1)) f1

let _ = assert_norm (mk_add_n 10 1 2 3 4 5 6 7 8 9 10 == 55)
