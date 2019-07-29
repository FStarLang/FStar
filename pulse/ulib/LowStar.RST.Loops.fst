module LowStar.RST.Loops


module R = LowStar.Resource
module RST = LowStar.RST
module A = LowStar.Array
module AR = LowStar.RST.Array
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module P = LowStar.Permissions
module U32 = FStar.UInt32

open FStar.Mul

let rec while res inv guard test body =
  if test () then begin
    body ();
    while res inv guard test body
  end


inline_for_extraction val for:
  start:U32.t ->
  finish:U32.t{U32.v finish >= U32.v start} ->
  context: resource ->
  loop_inv:(h:imem (inv (context)) -> nat -> Type0) ->
  f:(i:U32.t{U32.(v start <= v i /\ v i < v finish)} -> RST unit
    (context)
    (fun _ -> context)
    (requires (fun h -> loop_inv h (U32.v i)))
    (ensures (fun h_1 _ h_2 -> U32.(loop_inv h_1 (v i) /\ loop_inv h_2 (v i + 1))))
  ) ->
  RST unit
    (context)
    (fun _ -> context)
    (requires (fun h -> loop_inv h (U32.v start)))
    (ensures (fun _ _ h_2 -> loop_inv h_2 (U32.v finish)))

inline_for_extraction let rec for start finish context loop_inv f =
  if start = finish then
    ()
  else begin
    f start;
    for (U32.(start +^ 1ul)) finish context loop_inv f
  end

val iteri:
  #a: Type0 ->
  b: A.array a ->
  context: resource ->
  loop_inv:(h:imem (inv (context)) -> nat -> Type) ->
  f: (i:U32.t{U32.v i < A.vlength b} -> x:a -> RST unit
    (context)
    (fun _ -> context)
    (fun h0 -> loop_inv h0 (U32.v i))
    (fun h0 _ h1 -> loop_inv h0 (U32.v i) /\ loop_inv h1 (U32.v i + 1))
  ) ->
  RST unit
    (R.(AR.array_resource b <*> context))
    (fun _ -> R.(AR.array_resource b <*> context))
    (fun h0 -> loop_inv h0 0)
    (fun h0 _ h1 -> loop_inv h1 (A.vlength b) /\
      R.sel (R.view_of (AR.array_resource b)) h0 ==
      R.sel (R.view_of (AR.array_resource b)) h1
    )

let iteri #a b context loop_inv f =
  (**) let hinit = HST.get () in
  (**) let correct_inv = fun h i -> loop_inv h i /\
  (**)  R.sel (R.view_of (AR.array_resource b)) hinit ==
  (**)  R.sel (R.view_of (AR.array_resource b)) h
  (**) in
  let correct_f (i:U32.t{U32.(0 <= v i /\ v i < A.vlength b)})
    : RST unit
      (R.(AR.array_resource b) <*> context)
      (fun _ -> R.(AR.array_resource b <*> context))
      (requires (fun h0 ->
        correct_inv h0 (U32.v i)
      ))
      (ensures (fun h0 _ h1 ->
        U32.(correct_inv h0 (v i) /\ correct_inv h1 (v i + 1))
      ))
  =
    let x = RST.rst_frame
      (R.(AR.array_resource b <*> context))
      (fun _ -> R.(AR.array_resource b <*> context))
      (fun _ -> AR.index b i)
    in
    let f' () : RST unit // TODO: figure out why we cannot remove this superfluous let-binding
      (context)
      (fun _ -> context)
      (fun h0 ->  loop_inv h0 (U32.v i))
      (fun h0 _ h1 -> loop_inv h0 (U32.v i) /\ loop_inv h1 (U32.v i + 1))
      =
      f i x
    in
     RST.rst_frame
       (AR.array_resource b <*> context)
       #(context)
       #unit
       (fun _ -> R.(AR.array_resource b <*> context))
       #(fun _ -> context)
       #(AR.array_resource b)
       #(fun h0 ->  loop_inv h0 (U32.v i))
       #(fun h0 _ h1 -> loop_inv h0 (U32.v i) /\ loop_inv h1 (U32.v i + 1))
       f'
  in
  for
    0ul
    (A.length b)
    R.(AR.array_resource b <*> context)
    correct_inv
    correct_f
