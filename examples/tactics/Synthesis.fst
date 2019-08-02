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
module Synthesis

open FStar.Tactics

let a : unit = synth (fun () -> exact (`()))

let _ = assert (a == ())

let rec fib (n : int) : Tac unit =
    if n < 2
    then
        exact (`1)
    else (
        apply (`op_Addition);
        iseq [ (fun () -> fib (n - 1)) ;
               (fun () -> fib (n - 2)) ]
    )

let f8 : int = synth (fun () -> fib 8)
let _ = assert (f8 == 34) // equal after normalization

let rec fib_norm (n : int) : Tac unit =
    if n < 2
    then
        exact (`1)
    else (
        dup ();
        apply (`op_Addition);
        iseq [ (fun () -> fib_norm (n - 1)) ;
               (fun () -> fib_norm (n - 2)) ];
        norm [primops];
        trefl ()
    )

let fn8 : int = synth (fun () -> fib_norm 8)
let _ = assert (fn8 == 34) // syntactically equal

let iszero (x : int) : int =
    synth (fun () ->
        set_guard_policy SMT;
        let x = quote x in
        let t_int = quote int in
        let _f = fresh_bv t_int in
        let t = Tv_Match x
                    [(Pat_Constant (C_Int 0), pack (Tv_Const (C_Int 1)));
                     (Pat_Wild _f, pack (Tv_Const (C_Int 0)))] in
        exact (pack t))

let _ = assert (iszero 0 = 1)
let _ = assert (iszero 1 = 0)
let _ = assert (iszero 2 = 0)

let mk_let () : Tac unit =
   match (inspect (quote ( let f x = if x<=1 then 1 else x - 1 in f 5 ))) with
   | Tv_Let r b t1 t2 ->
     let t = pack (Tv_Let r b t1 t2) in
     exact_guard t
   | _ -> dump "uh oh"; exact (`0)

let f2 : int = synth mk_let
let _ = assert (f2 == 4)

let mk_let_rec () : Tac unit =
   match (inspect (quote ( let rec fr (x:nat) = if x <= 1 then 1 else fr (x-1) in fr 5 ))) with
   | Tv_Let r b t1 t2 ->
     let t = pack (Tv_Let r b t1 t2) in
     exact_guard t
   | _ -> dump "uh oh"; exact (`0)

let f3 : int = synth mk_let_rec
let _ = assert_norm (f3 == 1)
let ascribe : int = synth (fun () -> exact (pack (Tv_AscribedT (`0) (`int) None)))

