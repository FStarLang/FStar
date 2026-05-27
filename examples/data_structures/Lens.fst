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
/// A small experiment with lenses, including stateful lenses toward
/// the end.
///
/// Part of what I'm experimenting with is how to shoehorn this into
/// the existing notational support in F*.
module Lens

let ignore (x:'a) : unit = ()

/// A `lens a b` focuses on the `b` component of `a`
/// It provides a `get` to access the component
/// And a `set` to update and `a` by updating its `b` component
noeq
type lens (a:Type) (b:Type) = {
  get: a -> b;
  put: b -> a -> a
}

/// `x |. l` : projects using the lens `l` from `x`
let ( |. ) (x:'a) (l:lens 'a 'b) : 'b = l.get x

/// `(x |:= l) v` : updates the `l`-focused component of `x` with `v`
///    – The additional parentheses on the left are necesssary here
let ( |:= ) (x:'a) (l:lens 'a 'b) : 'b -> 'a = fun b -> l.put b x

/// `l |.. m`: composes lenses, building an "access path" that extends
/// the focus of `l` with `m`
let ( |.. ) (m:lens 'a 'b) (l:lens 'b 'c) : lens 'a 'c = {
  get = (fun x -> l.get (m.get x));
  put = (fun (x:'c) (y:'a) -> m.put (l.put x (m.get y)) y)
}

(* Using these operators provides slightly better notation *)
/// `x.[l] <- v`: updates the l-focused component of x with v
let op_String_Assignment (x:'a) (l:lens 'a 'b) (v:'b) : 'a = (x |:= l) v

/// `x.[l]`: accesses the l-focused component
let op_String_Access (x:'a) (l:lens 'a 'b) : 'b = x |. l

(** Now for some pure examples **)

/// A simple 3d point defined as a record
type point = {
  x:int;
  y:int;
  z:int
}
/// Followed by bit of boilerplate (which would be nice to metaprogram)
/// to define lenses for each of its components
let x : lens point int = {
  get = (fun p -> p.x);
  put = (fun x' p -> {p with x=x'})
}

let y : lens point int = {
  get = (fun p -> p.y);
  put = (fun y' p -> {p with y=y'})
}

let z : lens point int = {
  get = (fun p -> p.z);
  put = (fun z' p -> {p with z=z'})
}

/// A circle is a point and a radius
type circle = {
  center: point;
  radius: nat
}

/// Again, a bit of boiler plate for lenses on its fields
let center : lens circle point = {
  get = (fun c -> c.center);
  put = (fun n c -> {c with center = n})
}
let radius : lens circle nat= {
  get = (fun c -> c.radius);
  put = (fun n c -> {c with radius = n})
}

(** Now some clients that use the lenses **)
let getY  (c:circle) = c |. center |. y

/// Or, using the accessor notation
let getY' (c:circle) = c.[center |.. y]

/// Or, of course, using the built-in notation
/// ...
/// So,this doesn't look like much progress so far : )
let getY'' (c:circle) = c.center.y

/// But, updating a nested record is somewhat easier now
let setY (c:circle) (new_y: int) =
    c.[center |.. y] <- new_y
/// As opposed to:
let tedious_setY (c:circle) (new_y: int) =
    {c with center = {c.center with y = new_y}}

/// You can mix accessors and mutators
let moveUp (c:circle) (offset_y: int) =
    c.[center |.. y] <- c.[center |.. y] + offset_y

(** Now lets add more layers of objects **)

/// Here's an RGB color
type rgb = {
  red:nat;
  green:nat;
  blue:nat;
}
/// Boilerplate
let red : lens rgb nat = {
  get = (fun p -> p.red);
  put = (fun z p -> {p with red=z})
}
let green : lens rgb nat = {
  get = (fun p -> p.green);
  put = (fun z p -> {p with green=z})
}
let blue : lens rgb nat = {
  get = (fun p -> p.blue);
  put = (fun z p -> {p with blue=z})
}

/// And a `colored a` is a `color` and an `a`
type colored (a:Type) = {
  color:rgb;
  payload:a
}
/// Boilerplate
let color (#a:Type) : lens (colored a) rgb = {
  get = (fun p -> p.color);
  put = (fun z p -> {p with color=z})
}
let payload (#a:Type) : lens (colored a) a = {
  get = (fun p -> p.payload);
  put = (fun z p -> {p with payload=z})
}

/// And you can build longer lenses to reach into an object quite easily
let moveUp' (c:colored circle) (offset_y: int) =
    c.[payload |.. center |.. y] <- c.[payload |.. center |.. y] + offset_y

/// You can also build other kinds of lens combinator
/// For example, focusing on two different parts of an object at once
let ( || ) (l1:lens 'a 'b) (l2:lens 'a 'c) : lens 'a ('b & 'c) = {
  get = (fun a -> l1.get a, l2.get a);
  put = (fun (b, c) a -> l2.put c (l1.put b a))
}

/// And now you can use these to update multiple components at once
let makeGreen (c:colored circle) =
    c.[color |.. (red || green || blue )] <- (0, 1), 0

