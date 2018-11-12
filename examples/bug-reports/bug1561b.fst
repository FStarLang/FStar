module Bug1561b

class a = {x : bool}

let t [| a |] : Tot Type = if x then ℤ else unit

type u = | A | B

let f_t [| _ : a |]  :  Tot Type = u → t → Tot t

instance ii : a = { x = true }

let f0 : f_t = fun l y → y

(* used to explode with an assertion failure *)
val test : unit -> unit
let test () : unit =
    let f : f_t = fun l y → y
    in ()

val f1 : f_t
let f1 = fun l y → y
