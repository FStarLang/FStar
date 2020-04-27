(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Bug1414

open FStar.Tactics

let constant (t:term) : Tac unit = exact (norm_term [primops; delta; iota; zeta] t)

let f (x:option int) : int = if Some? x then Some?.v x else 0
let c1 : int = (synth (fun()-> constant (`( f (Some 42) ))))
// c1 = 42
let _ = assert (c1 == 42) by trefl ()

let f' (x:list int) : int = if Cons? x then Cons?.hd x else 0
let c1' : int = (synth (fun()-> constant (`( f' (Cons 42 Nil) ))))
// c1' = if Cons? [42] then Cons?.hd [42] else 0 -- old result
let _ = assert (c1' == 42) by trefl () // this used to fail

type list (a:Type) =
  | Nil  : list a
  | Cons : hd:a -> tl:list a -> list a

let f'' (x:list int) : int = if Cons? x then Cons?.hd x else 0
let c1'' : int = (synth (fun()-> constant (`( f'' (Cons 42 Nil) ))))
// c1'' = 42
let _ = assert (c1'' == 42) by trefl ()
