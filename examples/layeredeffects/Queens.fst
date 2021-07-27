module Queens

open FStar.List.Tot
open Alg

(* A hacky way to extend the operations from Alg externally. *)
let flipOp = Other 3
assume FlipArity : op_inp flipOp == unit /\ op_out flipOp == bool
let flip = geneff flipOp

let quitOp = Other 4
assume QuitArity : op_inp quitOp == unit /\ op_out quitOp == empty
let quit = geneff quitOp

(* But... we should be careful since if we make a typo above we could become
inconsistent, so we add a sanity check. *)
[@@expect_failure] let _ = assert False

type board = list int

let rec no_clash_plus (n:int) (qs:board) : Tot bool (decreases qs) =
  match qs with
  | [] -> true
  | q::qs -> n+1 <> q && no_clash_plus (n+1) qs

let rec no_clash_minus (n:int) (qs:board) : Tot bool (decreases qs) =
  match qs with
  | [] -> true
  | q::qs -> n-1 <> q && no_clash_minus (n-1) qs

let ok1 (n:int) (qs:board) : bool =
     List.Tot.for_all (fun i -> i <> n) qs
  && no_clash_plus n qs
  && no_clash_minus n qs

val valid : board -> prop
let rec valid b =
  match b with
  | [] -> True
  | q::qs -> ok1 q qs /\ valid qs

type valid_board = b:board{valid b}

let rec pickn (p : pos) : Alg nat [flipOp] =
  if p = 1
  then 0
  else if flip ()
       then p-1
       else pickn (p-1)

let rec _queens (n : pos)
                (k : nat{k <= n})
                (b : valid_board{List.Tot.length b == k})
: Alg valid_board [flipOp; quitOp]
      (decreases (n - k))
=
  if k = n then b
  else begin
    let q = pickn n in
    if ok1 q b
    then _queens n (k+1) (q::b)
    else quit ()
  end

let queens (n:pos) : list valid_board =
  run (fun () ->
    handle_with (fun () -> _queens n 0 [])
                (fun b -> [b])
                (function Other 3 -> fun _ k -> k true @ k false
                        | Other 4 -> fun _ _ -> []))

let qs8 = queens 8

(* With a patch to reify layered effects:

Reducing ‘qs8’…
qs8 ↓βδιζr
[
  [4; 6; 1; 5; 2; 0; 3; 7]; [3; 6; 4; 1; 5; 0; 2; 7]; [5; 3; 6; 0; 2; 4; 1; 7];
  [5; 2; 4; 6; 0; 3; 1; 7]; [3; 1; 7; 5; 0; 2; 4; 6]; [4; 2; 0; 5; 7; 1; 3; 6];
  [5; 2; 0; 7; 4; 1; 3; 6]; [3; 5; 0; 4; 1; 7; 2; 6]; [3; 1; 4; 7; 5; 0; 2; 6];
  [4; 7; 3; 0; 2; 5; 1; 6]; [5; 2; 4; 7; 0; 3; 1; 6]; [4; 1; 3; 5; 7; 2; 0; 6];
  [2; 4; 6; 0; 3; 1; 7; 5]; [2; 4; 1; 7; 0; 6; 3; 5]; [7; 1; 4; 2; 0; 6; 3; 5];
  [2; 0; 6; 4; 7; 1; 3; 5]; [2; 6; 1; 7; 4; 0; 3; 5]; [4; 1; 7; 0; 3; 6; 2; 5];
  [3; 0; 4; 7; 1; 6; 2; 5]; [4; 0; 7; 3; 1; 6; 2; 5]; [6; 1; 3; 0; 7; 4; 2; 5];
  [7; 1; 3; 0; 6; 4; 2; 5]; [6; 3; 1; 4; 7; 0; 2; 5]; [4; 6; 1; 3; 7; 0; 2; 5];
  [3; 1; 7; 4; 6; 0; 2; 5]; [2; 4; 7; 3; 0; 6; 1; 5]; [3; 7; 4; 2; 0; 6; 1; 5];
  [3; 6; 2; 7; 1; 4; 0; 5]; [2; 5; 1; 6; 0; 3; 7; 4]; [6; 1; 5; 2; 0; 3; 7; 4];
  [1; 5; 7; 2; 0; 3; 6; 4]; [3; 7; 0; 2; 5; 1; 6; 4]; [7; 3; 0; 2; 5; 1; 6; 4];
  [5; 2; 0; 7; 3; 1; 6; 4]; [2; 5; 7; 1; 3; 0; 6; 4]; [1; 3; 5; 7; 2; 0; 6; 4];
  [1; 5; 0; 6; 3; 7; 2; 4]; [3; 5; 7; 1; 6; 0; 2; 4]; [6; 3; 1; 7; 5; 0; 2; 4];
  [5; 2; 6; 3; 0; 7; 1; 4]; [2; 7; 3; 6; 0; 5; 1; 4]; [0; 5; 7; 2; 6; 3; 1; 4];
  [6; 0; 2; 7; 5; 3; 1; 4]; [3; 1; 6; 2; 5; 7; 0; 4]; [5; 2; 6; 1; 3; 7; 0; 4];
  [2; 6; 1; 7; 5; 3; 0; 4]; [5; 1; 6; 0; 2; 4; 7; 3]; [2; 5; 1; 6; 4; 0; 7; 3];
  [4; 6; 1; 5; 2; 0; 7; 3]; [1; 7; 5; 0; 2; 4; 6; 3]; [7; 2; 0; 5; 1; 4; 6; 3];
  [5; 0; 4; 1; 7; 2; 6; 3]; [2; 5; 1; 4; 7; 0; 6; 3]; [1; 4; 6; 0; 2; 7; 5; 3];
  [4; 2; 0; 6; 1; 7; 5; 3]; [6; 2; 7; 1; 4; 0; 5; 3]; [6; 4; 2; 0; 5; 7; 1; 3];
  [5; 2; 0; 6; 4; 7; 1; 3]; [2; 5; 7; 0; 4; 6; 1; 3]; [0; 4; 7; 5; 2; 6; 1; 3];
  [4; 0; 7; 5; 2; 6; 1; 3]; [6; 2; 0; 5; 7; 4; 1; 3]; [1; 6; 2; 5; 7; 4; 0; 3];
  [5; 2; 6; 1; 7; 4; 0; 3]; [4; 1; 5; 0; 6; 3; 7; 2]; [4; 0; 3; 5; 7; 1; 6; 2];
  [5; 3; 0; 4; 7; 1; 6; 2]; [4; 6; 0; 3; 1; 7; 5; 2]; [3; 1; 6; 4; 0; 7; 5; 2];
  [1; 4; 6; 3; 0; 7; 5; 2]; [0; 6; 4; 7; 1; 3; 5; 2]; [1; 6; 4; 7; 0; 3; 5; 2];
  [3; 7; 0; 4; 6; 1; 5; 2]; [4; 7; 3; 0; 6; 1; 5; 2]; [3; 6; 0; 7; 4; 1; 5; 2];
  [5; 1; 6; 0; 3; 7; 4; 2]; [5; 7; 1; 3; 0; 6; 4; 2]; [0; 6; 3; 5; 7; 1; 4; 2];
  [5; 3; 6; 0; 7; 1; 4; 2]; [5; 3; 1; 7; 4; 6; 0; 2]; [3; 6; 4; 2; 0; 5; 7; 1];
  [2; 5; 3; 0; 7; 4; 6; 1]; [3; 0; 4; 7; 5; 2; 6; 1]; [4; 6; 3; 0; 2; 7; 5; 1];
  [4; 2; 7; 3; 6; 0; 5; 1]; [2; 5; 7; 0; 3; 6; 4; 1]; [3; 5; 7; 2; 0; 6; 4; 1];
  [4; 6; 0; 2; 7; 5; 3; 1]; [2; 5; 3; 1; 7; 4; 6; 0]; [2; 4; 1; 7; 5; 3; 6; 0];
  [4; 1; 3; 6; 2; 7; 5; 0]; [3; 1; 6; 2; 5; 7; 4; 0]
]
<:
Prims.Tot
(list (b:
      list int
        { (match b with
            | [] -> l_True
            | q :: qs -> ok1 q qs /\ valid qs)
          <:
          a: Type0{forall (x: a). has_type x unit} }))
*)
