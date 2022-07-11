(*
   Copyright 2021 Microsoft Research

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
module OPLSS2021.Basic
open FStar.Mul

/// A refinement type
let nat = x:int{ x >= 0 }

/// A simple recursive function
let rec factorial (n:nat)
  : nat
  = if n = 0 then 1 else n * factorial (n - 1)

/// A proof by induction about factorial
let rec factorial_increasing (n:nat)
  : _:unit{factorial n >= n}
  = if n <= 2 then ()
    else factorial_increasing (n - 1)

/// Lemma is syntactic sugar
let rec factorial_increasing_lemma (n:nat)
  : Lemma (factorial n >= n)
  = if n <= 2 then ()
    else factorial_increasing_lemma (n - 1)

/// More sugar for lemma
#push-options "--z3rlimit 20"
let rec factorial_increasing_lemma' (n:int)
  : Lemma 
    (requires n >= 0)
    (ensures factorial n >= n)
  = if n <= 2 then ()
    else factorial_increasing_lemma' (n - 1)
#pop-options

////////////////////////////////////////////////////////////////////////////////

/// Polymorphic functions
///   - #a is notation for an implicit argument
///     a Type argument, in this case
let id (#a:Type) (x:a) : a = x

/// Higher order functions
let rec map #a #b (f: a -> b) (l:list a) 
  : list b 
  = match l with
    | [] -> []
    | hd :: tl -> f hd :: map f tl

/// `assert` is statically checked, by the SMT solver
let test0 = assert (map (fun x -> x + 1) [1;2;3] == [2;3;4])

/// The SMT solver isn't great at doing proofs by computation
/// Limited unrolling
[@@expect_failure]
let test1 = assert (map (fun x -> x + 1) [1;2;3;4;5;6;7;8;9;10] == [2;3;4;5;6;7;8;9;10;11])

/// But, F* offers many other ways of doing proofs,
/// which we'll learn about as we go.
///
/// Here, we ask F* to prove the assertion by just normalizing it on
/// its abstract machine
let test1 = assert_norm (map (fun x -> x + 1) [1;2;3;4;5;6;7;8;9;10] == [2;3;4;5;6;7;8;9;10;11])

/// Here, we do script the proof with a tactic
let test2 = assert (map (fun x -> x + 1) [1;2;3;4;5;6;7;8;9;10] == [2;3;4;5;6;7;8;9;10;11])
                by FStar.Tactics.(norm [delta; zeta; iota; primops]; //reduce both sides
                                  trefl(); //prove them equal
                                  qed())   //check that we're done with all goals

////////////////////////////////////////////////////////////////////////////////
// Types can be computed from any pure term
////////////////////////////////////////////////////////////////////////////////
let string_or_int (x:bool)
  : (if x then string else int)
  =  if x then "hello" else 0

let msg : string = FStar.Printf.sprintf "Hello %s %d!" "OPLSS" 2021
let msg' : string = FStar.Printf.sprintf "Hello %s %d%d%d%d!" "OPLSS" 2 0 2 1

////////////////////////////////////////////////////////////////////////////////
// Indexed types: Vectors
////////////////////////////////////////////////////////////////////////////////
type vector (a:Type) : nat -> Type =
  | VNil : vector a 0
  | VCons : hd:a
          -> #n:nat //implicit argument again, doesn't always have to by a Type
          -> tl:vector a n
          -> vector a (n + 1)

/// Using a refinement to state a precondition
let head' #a #n (v:vector a n { (match v with VCons _ _ -> true | _ -> false) }) 
  : a
  = match v with
    | VCons x xs -> x

/// VCons? v is syntactic sugar for saying that v is in the VCons case
let head'' #a #n (v:vector a n { VCons? v }) 
  : a
  = match v with
    | VCons x xs -> x

/// Or, just constrain the length index
let head #a (#n:nat{n > 0}) (v:vector a n)
  : a
  = match v with
    | VCons x xs -> x

/// Extracting the n'th element from a vector
///   needs to have at least n elements
let rec nth #a (n:nat) (#m:nat{m > n}) (v:vector a m) : a =
  let VCons x xs = v in // F* can prove that since m > n, m > 0, and so v <> VNil
  if n = 0
  then x
  else nth (n-1) xs

/// Appending two vectors, notice that the index of the result
/// is the sum on the indices of the arguments
let rec append #a #n1 #n2 (v1:vector a n1) (v2:vector a n2)
  : vector a (n1 + n2)
  = match v1 with
    | VNil -> v2
    | VCons hd tl -> VCons hd (append tl v2)

/// Reversing a vector
let rec reverse #a #n (v:vector a n)
  : vector a n
  = match v with
    | VNil -> VNil
    | VCons hd tl -> append (reverse tl) (VCons hd VNil)

/// map_vec, just like map, but now with vectors
let rec map_vec #a #b (f:a -> b) #n (v:vector a n)
  : vector b n
  = match v with
    | VNil -> VNil
    | VCons hd tl -> VCons (f hd) (map_vec f tl)

/// fold_right
let rec fold_right #a #b (f: a -> b -> b) #n (v:vector a n) (acc: b)
  : b
  = match v with
    | VNil -> acc
    | VCons hd tl -> f hd (fold_right f tl acc)

/// Exercise: redefine all the vector functions above
/// but for the `llist` type below

let rec length #a (l:list a) 
  : nat
  = match l with
    | [] -> 0
    | _ :: tl -> 1 + length tl
    
let llist a (n:nat) = l:list a { length l = n}
