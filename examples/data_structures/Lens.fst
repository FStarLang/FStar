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
let ( || ) (l1:lens 'a 'b) (l2:lens 'a 'c) : lens 'a ('b * 'c) = {
  get = (fun a -> l1.get a, l2.get a);
  put = (fun (b, c) a -> l2.put c (l1.put b a))
}

/// And now you can use these to update multiple components at once
let makeGreen (c:colored circle) =
    c.[color |.. (red || green || blue )] <- (0, 1), 0

////////////////////////////////////////////////////////////////////////////////
/// Now for some stateful stuff
///   – This is not quite as nice an compositional as before
///     Would be curious to have your thoughts on how it could be generalized
/// (My first naive attempt: See StatefulLens for how to do it better)
////////////////////////////////////////////////////////////////////////////////

open FStar.Heap
open FStar.Ref

/// An `stlens #a #b l` goes via a `ref a` to access the `b`component
/// that is focused by `l`
noeq
type stlens (#a:Type) (#b:Type) (l:lens a b) = {
     // Getting a `b` from an `r:ref a` requires dereferencing it
     // and then reaching into the result with `l`
     st_get: r:ref a
           -> ST b
             (requires (fun h -> True))
             (ensures (fun h0 b h1 -> h0==h1 /\ b == ((sel h1 r)|. l)));
     // Setting a `b` component inside a `r:ref a` modifies only `r`
     // and updates the contents of `r` using `l`
     st_put: y:b
           -> r:ref a
           -> ST (ref a)
             (requires (fun h -> True))
             (ensures (fun h0 s h1 ->
                         r == s /\
                         modifies (Set.singleton (addr_of r)) h0 h1 /\
                         (sel h1 r == ((sel h0 r).[l] <- y))))
}

/// You can turn a regular lens into a stateful lens
let st #a #b (l:lens a b) : stlens l = {
  st_get = (fun (r:ref a) -> (!r).[l]);
  st_put = (fun (x:b) (r:ref a) -> r := (!r.[l] <- x); r)
}

/// And we can compose a stateful lens with a pure lens on the right
let ( |:.. ) #a #b #c (#l:lens a b) (sl:stlens l) (m:lens b c) : stlens (l |.. m) = {
     st_get = (fun (r:ref a) -> (sl.st_get r).[m]);
     st_put = (fun (x:c) (r:ref a) -> sl.st_put ((sl.st_get r).[m] <- x) r)
}

/// Limitations:
/// But, you can't compose an stlens with another stlens
///  – Because the spec of st_get and st_put is inherently rigged to
///    work with a single reference
/// Nor can you compose a pure lens with an stlens on the left
///  - Because stlens's always start with a ref


/// We can define access and mutation operators for stlenses
let ( |:. ) #a #b (#l:lens a b) (x:ref a) (s:stlens l) = s.st_get x
let ( |::= ) #a #b (#l:lens a b) (x:ref a) (s:stlens l) (y:b) = s.st_put y x
/// Although, as before the access/assignment operators probably work better


/// x.(m) <- v: promotes m to a stateful lens and then updates x's m
/// component with v
///   -- Making them return unit since that works better with sequencing `;`
let op_Array_Assignment #a #b (x:ref a) (m:lens a b) (y:b)
   = let _ = (x |::= (st m)) y in ()

/// x.(m): promotes m to a stateful lens and access x's m component
let op_Array_Access #a #b (x:ref a) (m:lens a b)
   = x |:. (st m)

/// You can write stuff like this to go past a ref and then update
let mutate (c:ref (colored circle)) =
    c.(color |.. (red || green || blue)) <- (0, 1), 2

/// But, as you nest refs further, you're forces to break up the updates
/// piecewise, since stlenses don't compose
let mutate2 (c:ref (colored (ref circle))) =
    c.(color |.. (red || green || blue)) <- (0, 1), 2;
    (c.(payload)).(center |.. x) <- 17
    //i.e., you can't write c.(payload |.. center |.. x) <- 17
    //Also, sadly, you seem to need parantheses on the first access
    //i.e., c.(payload).(center |.. x) <- 17 parses as
    //      c.(payload.(center |.. x)) <- 17

/// You can keep doing this ...
let mutate3 (c:ref (colored (ref (colored (ref circle))))) =
    ((c.(payload)).(payload)).(center |.. x) <- 17
