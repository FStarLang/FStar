module LArith

open FStar.BaseTypes

abstract
let logxor (#n : pos) (x:int) (y:int) : res:nat{res < pow2 n} =
  if FStar.UInt.fits x n
  && FStar.UInt.fits y n
  then FStar.UInt.logxor #n x y
  else 0

let logxor_uint  (#n:pos) (x:int) (y:int)
  : Lemma (ensures (FStar.UInt.fits x n /\
                    FStar.UInt.fits y n) ==>
                    logxor #n x y = FStar.UInt.logxor #n x y)
           [SMTPat (logxor #n x y)]
  = ()          

abstract
let logand (#n:pos) (x:int) (y:int) : res:nat{res < pow2 n} =
  if FStar.UInt.fits x n
  && FStar.UInt.fits y n
  then FStar.UInt.logand #n x y
  else 0

let logand_uint (#n:pos) (x:int) (y:int)
  : Lemma (ensures (FStar.UInt.fits x n /\
                    FStar.UInt.fits y n) ==>
                    logand #n x y = FStar.UInt.logand #n x y)
          [SMTPat (logand #n x y)]
  = ()          

abstract
let shift_right (#n:pos) (x:int) (y:int) : res:nat{res < pow2 n} =
  if FStar.UInt.fits x n
  && y >= 0
  then FStar.UInt.shift_right #n x y
  else 0

let shift_right_uint (#n:pos) (x:int) (y:int)
  : Lemma (ensures (FStar.UInt.fits x n /\
                    0 <= y /\
                    y < n ==>
                    shift_right #n x y = FStar.UInt.shift_right #n x y))
          [SMTPat (shift_right #n x y)]
  = ()          

abstract
let shift_left (#n:pos) (x:int) (y:int) : res:nat{res < pow2 n} =
  if FStar.UInt.fits x n
  && y >= 0
  then FStar.UInt.shift_left #n x y
  else 0

let shift_left_uint (#n:pos) (x:int) (y:int)
  : Lemma (ensures (FStar.UInt.fits x n /\
                    0 <= y /\
                    y < n ==>
                    shift_left #n x y = FStar.UInt.shift_left #n x y))
          [SMTPat (shift_left #n x y)]
  = ()
