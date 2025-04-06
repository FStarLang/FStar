(*
   Copyright 2023 Microsoft Research

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

module PulseTutorial.UserDefinedPredicates
#lang-pulse
open Pulse.Lib.Pervasives
open FStar.Mul
//pts_to_diag$
let pts_to_diag 
        #a 
        (r:ref (a & a))
        (v:a)
: slprop
= pts_to r (v, v)
//end pts_to_diag$

//double$
fn double (r:ref (int & int))
requires pts_to_diag r 'v
ensures pts_to_diag r (2 * 'v)
{
  unfold (pts_to_diag r 'v);
  let v = !r;
  let v2 = fst v + snd v;
  r := (v2, v2);
  fold (pts_to_diag r v2);
}
//end double$

//double_alt$
fn double_alt (r:ref (int & int))
requires pts_to_diag r 'v
ensures pts_to_diag r (2 * 'v)
{
  unfold pts_to_diag;
  let v = !r;
  let v2 = fst v + snd v;
  r := (v2, v2);
  fold pts_to_diag;
}
//end double_alt$

//point$
noeq
type point = {
    x:ref int;
    y:ref int;
}

let is_point (p:point) (xy: int & int) =
    pts_to p.x (fst xy) **
    pts_to p.y (snd xy)
//end point$

//move$
fn move (p:point) (dx:int) (dy:int)
requires is_point p 'xy
ensures is_point p (fst 'xy + dx, snd 'xy + dy)
{
  unfold is_point;
  let x = !p.x;
  let y = !p.y;
  p.x := x + dx;
  p.y := y + dy;
  fold (is_point p (x + dx, y + dy));
}
//end move$

//fold_is_point$
ghost
fn fold_is_point (p:point)
requires pts_to p.x 'x ** pts_to p.y 'y
ensures is_point p (reveal 'x, reveal 'y)
{
  fold (is_point p (reveal 'x, reveal 'y))
}
//end fold_is_point$


//move_alt$
fn move_alt (p:point) (dx:int) (dy:int)
requires is_point p 'xy
ensures is_point p (fst 'xy + dx, snd 'xy + dy)
{
  unfold is_point;
  let x = !p.x;
  let y = !p.y;
  p.x := x + dx;
  p.y := y + dy;
  fold_is_point p;
}
//end move_alt$


//create_and_move$
fn create_and_move ()
requires emp
ensures emp
{
    let mut x = 0;
    let mut y = 0;
    let p = { x; y };
    //pts_to x 0 ** pts_to y 0
    with _v. rewrite pts_to x _v as pts_to p.x _v;
    with _v. rewrite pts_to y _v as pts_to p.y _v;
    //pts_to p.x 0 ** pts_to p.y 0
    fold_is_point p;
    move p 1 1;
    assert (is_point p (1, 1));
    unfold is_point;
    //pts_to p.x (fst (1, 1)) ** pts_to p.y (snd (1, 1))
    with _v. rewrite pts_to p.x _v as pts_to x _v;
    with _v. rewrite pts_to p.y _v as pts_to y _v;
    //pts_to x (fst (1, 1)) ** pts_to y (snd (1, 1))
}
//end create_and_move$


//create_and_move_alt$
fn create_and_move_alt ()
requires emp
ensures emp
{
    let mut x = 0;
    let mut y = 0;
    let p = { x; y };
    rewrite each x as p.x, y as p.y;
    fold_is_point p;
    move p 1 1;
    assert (is_point p (1, 1));
    unfold is_point;
    rewrite each p.x as x, p.y as y;
}
//end create_and_move_alt$


// FIXME, need to explain
let is_point_curry ([@@@mkey] p:point) (x y : int) =
    pts_to p.x x **
    pts_to p.y y

fn move_curry (p:point) (dx:int) (dy:int)
requires is_point_curry p 'x 'y
ensures is_point_curry p ('x + dx) ('y + dy)
{
  unfold is_point_curry;
  let x = !p.x;
  let y = !p.y;
  p.x := x + dx;
  p.y := y + dy;
  fold is_point_curry; 
}

