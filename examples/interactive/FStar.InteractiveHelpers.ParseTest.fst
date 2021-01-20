module FStar.InteractiveHelpers.ParseTest

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

open FStar.List
open FStar.Tactics
open FStar.Mul

open FStar.FStar.InteractiveHelpers
open FStar.InteractiveHelpers.Tutorial.Definitions

/// This file contains some functions "interesting to parse", to test the parser
/// for the F* extended mode. It is for development/debugging purpose only.

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(*** Tests *)
let a'_ = 3
let f = FStar.InteractiveHelpers.ParseTest.a'_

let x1 = Some?.v (Some 3)
let x2 = 3
let x3 = x1-x2

let simpl_ex1 (x : nat) =
  let y = 4 in
  let 'x = 7 in
  let 'a = 4 in
  let 'd = "hello world!" in
  let '_u''x = 5 in
  let z = 3 in
  let w : w:nat{w >= 10} =
    if x > 3 then
      begin
      assert(y + x > 7);
      let x' = x + 1 in
      assert(y + x' > 8);
      let x'' = 2 * (y + x') in
      assert(x'' > 16);
      assert(x'' >= 10);
      2 * x'
      end
    else 12
  in
  assert(
    x >= 0 /\
    y >= 0);
  let w' = 2 * w + z in
  w'

let test1 b (l : list int) =
  if b then
    match l with
    | [] -> true
    | _ -> false
  else
    match l with
    | [x] -> true
    | _ -> false

let test2 #a b (l : list a) =
  if b then ()
  else assert(not b);
  let x = 3 in
  let y =
    4 +
    begin
    if b then
    let x = 4 in 2 * x
    else 8
    end
  in
  x + y

let test3 'a = FStar.InteractiveHelpers.ParseTest.test2 'a

let test4 b l =
  assert(FStar.InteractiveHelpers.ParseTest.test2 b l == test2 b l)

let f1 (#a : Type0) : Type = list a

let test5 a =
  f1 #(list a)
