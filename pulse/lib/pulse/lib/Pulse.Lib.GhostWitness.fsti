module Pulse.Lib.GhostWitness

open Pulse.Lib.Pervasives

val ghost_witness (a:Type u#0) (_:squash a) :
  stt_ghost a emp (fun _ -> emp)

val ghost_witness2 (a:Type u#3) (_:squash a) :
  stt_ghost a emp (fun _ -> emp)

val ghost_witness_exists (a:Type u#0) :
  stt_ghost a (pure (exists (x:a). True)) (fun _ -> emp)

val ghost_witness_exists2 (a:Type u#3) :
  stt_ghost a (pure (exists (x:a). True)) (fun _ -> emp)
