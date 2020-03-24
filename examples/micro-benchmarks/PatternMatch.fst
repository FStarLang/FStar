module PatternMatch

(* Error 19: assertion failed (from incomplete pattern matching in this case
 * Error 114: Type of pattern __ does not match type of scrutinee __
 * Error 178: Type ascriptions within patterns are only allowed on variables [2 times]
 *)

let _ = (=)

let pair_on_arg ((x,y) : int & int) : int = x + y

type ab = | A | B

%Fail [178]
let oops2 = match A with | (A : _) -> ()

%Fail [178]
let blah = match None with | (None : option int) -> ()

%Fail [19]
let None = Some 42

%Fail [19]
let Some () = None

let true = true

%Fail [19]
let true = false

%Fail [114]
let false = 1

%Fail [114]
let A = 2

%Fail [19]
let A = B

%Fail [178]
let None : option unit = Some 42

let x1, y1 = 42, true
let ((x2 : int), (y2 : bool)) = (42, true)

let _ = assert (x1 == 42)
let _ = assert (y1 == true)
let _ = assert (x2 == 42)
let _ = assert (y2 == true)


type r = { x : int }

%Fail [114]
let true = 2

%Fail [114]
let { x = true } = { x = 2 }

%Fail [19]
let (x, true) = (2, false)

%Fail [19]
let (false, false, x) = (true, true, 9)

let (x, true)  = (2, true)

%Fail [114]
let (true, true) = (2, false)

let (z, 0) = (42, 0)

let () = ()
