module Stlc
open Prims.PURE

type ty =
  | TBool  : ty

type exp =
  | ETrue  : exp
  | EFalse : exp

val typing : exp -> Tot (option ty)
let rec typing e = 
  match e with
  | ETrue -> Some TBool
  | _ -> None

val inconsistent : e:exp -> t:ty -> Pure unit
      (requires (typing e = Some t))
      (ensures (fun r -> False))
let inconsistent e t = ()
