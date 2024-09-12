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
  let r = insert h 1sz { left = true; right = false }; let h = r._1;
  let r = lookup h 1sz; let h = r._1;
  match r._2 {
    Some i -> {
      let r = replace h i 1sz { left = false; right = true } (magic ());
      let h = r._1;
      dealloc h
    }
    None -> {
      dealloc h
    }
  }
}
