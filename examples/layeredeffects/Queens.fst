module Queens

(* The original version used the Alg layered effect to combine nondeterministic
   flip and quit operations.  Layered effects are gone, so this is the same
   example expressed directly in the underlying list nondeterminism monad. *)

open FStar.List.Tot

type repr (a:Type0) = list a

let return (#a:Type0) (x:a) : repr a = [x]

let bind (#a #b:Type0) (m:repr a) (f:a -> repr b) : repr b =
  concatMap f m

let (let!) (#a #b:Type0) (m:repr a) (f:a -> repr b) : repr b = bind m f

let flip () : repr bool = [true; false]
let quit #a () : repr a = []
let run #a (f:unit -> repr a) : list a = f ()

type board = list int

let rec no_clash_plus (n:int) (qs:board) : Tot bool (decreases qs) =
  match qs with
  | [] -> true
  | q::qs -> n + 1 <> q && no_clash_plus (n + 1) qs

let rec no_clash_minus (n:int) (qs:board) : Tot bool (decreases qs) =
  match qs with
  | [] -> true
  | q::qs -> n - 1 <> q && no_clash_minus (n - 1) qs

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

let rec pickn (p:pos) : repr nat =
  if p = 1
  then return 0
  else let! b = flip () in
       if b then return (p - 1) else pickn (p - 1)

let rec _queens (n:pos)
                (k:nat{k <= n})
                (b:valid_board{List.Tot.length b == k})
  : Tot (repr valid_board) (decreases (n - k))
  = if k = n then return b
    else
      let! q = pickn n in
      if ok1 q b
      then _queens n (k + 1) (q::b)
      else quit ()

let queens (n:pos) : list valid_board =
  run (fun () -> _queens n 0 [])

let qs8 = queens 8
