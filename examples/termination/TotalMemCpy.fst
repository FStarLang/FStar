module TotalMemCpy
open TotalST
open LowStar.Buffer
open TotalLowStar.Lib
module HS = FStar.HyperStack
open FStar.Integers
module B = LowStar.Buffer

let prefix_equal (#l:uint_32) (#a:Type) (h:HS.mem)
                 (b1 b2: lbuffer a (v l))
                 (i:uint_32{i <= l}) =
  forall (j:uint_32). j < i ==>
                 get h b1 (v j) == B.get h b2 (v j)

(* This one is correctly extracted by Kremlin and the
   additional unit arg in the thunk is also removed *)
let copy1 (len:uint_32)
          (cur:uint_32{v cur < v len})
          (src dest:lbuffer uint_8 (v len))
  : TotST unit
       (requires fun h ->
         live h src  /\
         live h dest /\
         disjoint src dest)
       (ensures fun h0 _ h1 ->
         modifies (loc_buffer dest) h0 h1)
  = dest.(cur) <- src.(cur)

(* This one fails to extract via Kremlin ...
   some confusion about additional unit args *)
let rec copy
        (len:uint_32)
        (cur:uint_32{v cur <= v len})
        (src dest:lbuffer uint_8 (v len))
  : TotST unit
       (requires fun h ->
         live h src  /\
         live h dest /\
         disjoint src dest /\
         prefix_equal h src dest cur)
       (ensures fun h0 _ h1 ->
         modifies (loc_buffer dest) h0 h1 /\
         prefix_equal h1 src dest len)
       (decreases (v len - v cur))
  = if cur < len
    then begin
      dest.(cur) <- src.(cur);
      copy len (cur + 1ul) src dest
    end
