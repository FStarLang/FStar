module Pulse.Lib.Sort.Base
open Pulse.Lib.Pervasives

module I16 = FStar.Int16

inline_for_extraction
let impl_compare_t
  (#tl #th: Type)
  (vmatch: tl -> th -> slprop)
  (compare: th -> th -> int)
= (x1: tl) ->
  (x2: tl) ->
  (#y1: Ghost.erased th) ->
  (#y2: Ghost.erased th) ->
  stt I16.t
    (vmatch x1 y1 ** vmatch x2 y2)
    (fun res -> vmatch x1 y1 ** vmatch x2 y2 ** pure (
      let v = compare y1 y2 in
      (v < 0 <==> I16.v res < 0) /\
      (v > 0 <==> I16.v res > 0)
    ))
