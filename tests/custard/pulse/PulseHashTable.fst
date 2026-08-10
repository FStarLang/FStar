(* A larger Pulse program: the linear-probing hash table of
   pulse/test/Example.Hashtable.fst, driven from a [main].  It exercises
   polymorphic Pulse definitions loaded from another module's .fst through its
   interface, arrays, [while] loops, and Pulse's [unreachable]. *)
module PulseHashTable
open Pulse
open Pulse.Lib.HashTable
#lang-pulse

let hash (x: SizeT.t) : SizeT.t = x

type data = { left: bool; right: bool }

(* [main] reports whether the key it inserted was found again, so that the
   compiled C is run rather than only compiled: the whole point of this module
   is the array, the struct-valued cell and the function pointer, none of
   which a grep over the source can tell is right. *)
fn main ()
  returns r:SizeT.t
{
  let h = alloc #SizeT.t #data hash 100sz;
  let h, _ = insert h 1sz { left = true; right = false };
  let h, found = lookup h 1sz;
  match found {
    Some i -> {
      let h, _ = replace h i 1sz { left = false; right = true } (magic ());
      dealloc h;
      0sz
    }
    None -> {
      dealloc h;
      1sz
    }
  }
}
