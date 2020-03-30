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
module DoNotation

(* Making sure do notation works *)

let st t = int -> t * int

let return (x : 'a) : st 'a =
    fun s -> (x, s)

let bind (m : st 'a) (f : 'a -> st 'b) : st 'b =
    fun s -> let (x, s') = m s in f x s'

let get () : st int =
    fun s -> (s, s)

let put (s : int) : st unit =
    fun _ -> ((), s)

let incr () : st unit =
    n <-- get ();
    let n' = n + 1 in
    put n'

let rec add (n:nat) : st unit =
    if n = 0
    then return ()
    else begin
        incr ();;
        add (n-1)
    end

let _ = assert_norm (add 8 5 = ((), 13))
