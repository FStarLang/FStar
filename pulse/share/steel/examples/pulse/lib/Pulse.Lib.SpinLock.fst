module Pulse.Lib.SpinLock
open Pulse.Lib.Core
module S = Steel.ST.Util
module L = Steel.ST.SpinLock
friend Pulse.Lib.Core

let lock = L.lock

let new_lock p = fun _ -> let l = L.new_lock p in l

let acquire #p l = fun _ -> let _ = L.acquire #p l in ()

let release #p l = fun _ -> let _ = L.release #p l in ()