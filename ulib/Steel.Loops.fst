module Steel.Loops

open Steel.RST
module A = Steel.Array
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module P = LowStar.Permissions
module U32 = FStar.UInt32

open FStar.Mul

inline_for_extraction let rec while res inv guard test body =
  if test () then begin
    body ();
    while res inv guard test body
  end

inline_for_extraction let rec for start finish context loop_inv f =
  if start = finish then
    ()
  else begin
    f start;
    for (U32.(start +^ 1ul)) finish context loop_inv f
  end
