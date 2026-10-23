module CoreFailedChain

(* Phase-2 Core relates [t e24] and [t (ext e22 2)] by first trying, without
   a guard, to relate [e24] and [ext e22 2], unfolding one side and then the
   other at each step of the chain, and retrying each failure. Without
   remembering the failures this is exponential in the length of the chain,
   as with EverCDDL's environments in EverParse's COSE.Format. *)

noeq type env = { a: nat; b: nat -> Type0 }

let ext (e:env) (n:nat) : env = { a = e.a + n; b = (fun x -> e.b x) }

let e0 : env = { a = 0; b = (fun _ -> unit) }
let e1 : env = ext e0 1
let e2 : env = ext e1 1
let e3 : env = ext e2 1
let e4 : env = ext e3 1
let e5 : env = ext e4 1
let e6 : env = ext e5 1
let e7 : env = ext e6 1
let e8 : env = ext e7 1
let e9 : env = ext e8 1
let e10 : env = ext e9 1
let e11 : env = ext e10 1
let e12 : env = ext e11 1
let e13 : env = ext e12 1
let e14 : env = ext e13 1
let e15 : env = ext e14 1
let e16 : env = ext e15 1
let e17 : env = ext e16 1
let e18 : env = ext e17 1
let e19 : env = ext e18 1
let e20 : env = ext e19 1
let e21 : env = ext e20 1
let e22 : env = ext e21 1
let e23 : env = ext e22 1
let e24 : env = ext e23 1

let t (e:env) = x:nat{x < e.a}

let f (x:t e24) : t (ext e22 2) = x
