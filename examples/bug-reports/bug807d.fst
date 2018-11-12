module Bug807d

let t x = #y:int -> unit -> Lemma (x + y == y + x)
assume val f : x:int -> #y:int -> unit -> Lemma (x + y == y + x)

(* Works *)
val h : unit -> #y:int -> unit -> Lemma (5 + y == y + 5)
let h () = f 5

(* Used to fail *)
val g : unit -> t 5
let g () = f 5

let k (f : t 5) : #y:int -> unit -> Lemma (5 + y == y + 5) = f

let j (f : (#y:int -> unit -> Lemma (5 + y == y + 5))) : t 5 = f
