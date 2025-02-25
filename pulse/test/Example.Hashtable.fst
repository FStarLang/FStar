module Example.Hashtable
open Pulse
open Pulse.Lib.HashTable
#lang-pulse

let hash (x: SizeT.t) : SizeT.t = x

type data = { left: bool; right: bool }

fn insert_lookup_and_replace ()
  requires emp
  ensures emp
{
  let h = alloc #SizeT.t #data hash 100sz;
  let h, _ = insert h 1sz { left = true; right = false };
  let h, found = lookup h 1sz;
  match found {
    Some i -> {
      let h, _ = replace h i 1sz { left = false; right = true } (magic ());
      dealloc h
    }
    None -> {
      dealloc h
    }
  }
}
