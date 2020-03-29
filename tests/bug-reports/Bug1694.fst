module Bug1694
type t_min = #a:Type -> a -> Tot a
let f_min : t_min = fun #a x -> x
let h_min : t_min = f_min

module B = LowStar.Monotonic.Buffer
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST

inline_for_extraction
type t =
  (#rrel : B.srel U32.t) ->
  (#rel: B.srel U32.t) ->
  (b: B.mbuffer U32.t rrel rel) ->
  HST.ST unit (fun _ -> True) (fun _ _ _ -> True)

let f : t = fun #rrel #rel b -> ()

let h : t = f
