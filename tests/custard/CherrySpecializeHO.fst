module CherrySpecializeHO
module U32 = FStar.UInt32
open FStar.All

(* [@@@custard_specialize] on a function parameter (custard.md, 3.2d): a call
   that passes a lambda gets its own copy of the function, with the lambda's
   body in place of the parameter's calls and its captures passed as
   arguments, so no closure is built.  A call that passes a variable shares
   one copy that takes the function at run time. *)
let rec map_acc ([@@@FStar.Attributes.custard_specialize] f: int -> ML int)
                (l: list int) (acc: list int) : ML (list int) =
  match l with
  | [] -> List.rev acc
  | x :: t -> let y = f x in map_acc f t (y :: acc)

let map ([@@@FStar.Attributes.custard_specialize] f: int -> ML int) (l: list int)
  : ML (list int) = map_acc f l []

let rec fold ([@@@FStar.Attributes.custard_specialize] f: (list int & int) -> int -> ML (list int & int))
             (a: list int & int) (l: list int) : ML (list int & int) =
  match l with
  | [] -> a
  | x :: t -> fold f (f a x) t

let rec sum (l: list int) : Tot int = match l with [] -> 0 | x :: t -> x + sum t

(* A lambda: specialized, no closure. *)
let add_all (k: int) (l: list int) : ML (list int) = map (fun x -> x + k) l

(* A variable: passed at run time. *)
let apply_all (g: int -> ML int) (l: list int) : ML (list int) = map g l

(* A local function, passed by name. *)
let scale_all (k: int) (l: list int) : ML (list int) =
  let sc (x: int) : ML int = x * k in
  map sc l

let add (x y: int) : int = x + y

(* A partial application of a top-level function is keyed as written: [add]
   is not unfolded into the key. *)
let shift_all (k: int) (l: list int) : ML (list int) = map (add k) l

(* A local recursive function that specializes on a lambda calling itself
   with a growing argument.  Unfolding [go] into the key would make every
   specialization ask for a larger one. *)
let deep (l: list int) : ML (list int) =
  let rec go (ix: int) (n: int) : ML (list int) =
    if n = 0 then [ix]
    else map (fun x -> sum (go (ix + x) (n - 1)) + ix) l in
  go 0 2

(* The lambda rebinds a name its enclosing function binds. *)
let rebinds (env: int) (l: list int) : ML (list int & int) =
  fold (fun (acc, env) x -> (x + env) :: acc, env + 1) ([], env) l

let main () : ML U32.t =
  if add_all 1 [1; 2] = [2; 3]
  && apply_all (fun x -> x * 2) [1; 2] = [2; 4]
  && scale_all 3 [1; 2] = [3; 6]
  && shift_all 2 [1; 2] = [3; 4]
  && deep [1; 2] = [7; 11]
  && rebinds 10 [1; 2] = ([13; 11], 12)
  then 0ul else 1ul
