module ExtractMe

open FStar.All

/// Pure code
let add (x y: int) : Tot int = x + y

let safe_div (x:int) (y:int) : Pure int (requires (y =!= 0)) (ensures (fun r -> True)) =
  x / y

/// Divergent code
let rec loop (x:int) : Dv int =
  if x = 0 then 0 else loop (x - 1)

let rec collatz (n:int) : Dv int =
  if n <= 1 then 0
  else if n % 2 = 0 then 1 + collatz (n / 2)
  else 1 + collatz (3 * n + 1)

/// ML code: may diverge and raise
let checked_div (x:int) (y:int) : ML int =
  if y = 0 then failwith "div by zero" else x / y

let rec ml_loop (x:int) : ML int =
  if x = 0 then failwith "done" else ml_loop (x - 1)

/// Pure inside ML, and Div inside ML (lattice: PURE ~> DIV ~> ALL)
let mixed (x:int) : ML int =
  let a = add x 1 in
  let b = loop a in
  checked_div a (b + 1)

/// A list function extracted to OCaml
let rec length (#a:Type) (l : list a) : Tot int =
  match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl

let main () : ML unit =
  let _ = mixed 3 in ()

let _ : unit = main ()
