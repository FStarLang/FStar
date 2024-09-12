module Example.Hashtable
open Pulse
open Pulse.Lib.HashTable
#lang-pulse

let hash (x: SizeT.t) : SizeT.t = x

fn insert_lookup_and_replace ()
  requires emp
  ensures emp
{
  let h = alloc #SizeT.t #bool hash 100sz;
  let r = insert h 1sz true; let h = r._1;
  let r = lookup h 1sz; let h = r._1;
  match r._2 {
    Some i -> {
      let r = replace h i 1sz false (magic ());
      let h = r._1;
      dealloc h
    }
    None -> {
      dealloc h
    }
  }
}
