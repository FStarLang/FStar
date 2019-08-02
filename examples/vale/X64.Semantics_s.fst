(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module X64.Semantics_s

open FStar.BaseTypes
open X64.Machine_s

module F = FStar.FunctionalExtensionality

type uint64 = UInt64.t

let map (key:eqtype) (value:Type) = Map.t key value

// syntax for map accesses, m.[key] and m.[key] <- value
unfold
let op_String_Access (#a:eqtype) (#b:Type) (x:Map.t a b) (y:a) : Tot b = Map.sel x y

unfold
let op_String_Assignment = Map.upd

type ins =
  | Mov64      : dst:dst_op -> src:operand -> ins
  | Add64      : dst:dst_op -> src:operand -> ins
  | AddLea64   : dst:dst_op -> src1:operand -> src2:operand -> ins
  | AddCarry64 : dst:dst_op -> src:operand -> ins
  | Sub64      : dst:dst_op -> src:operand -> ins
  | Mul64      : src:operand -> ins
  | IMul64     : dst:dst_op -> src:operand -> ins
  | Xor64      : dst:dst_op -> src:operand -> ins
  | And64      : dst:dst_op -> src:operand -> ins
  | Shr64      : dst:dst_op -> amt:operand -> ins
  | Shl64      : dst:dst_op -> amt:operand -> ins

type ocmp =
  | OEq: o1:operand -> o2:operand -> ocmp
  | ONe: o1:operand -> o2:operand -> ocmp
  | OLe: o1:operand -> o2:operand -> ocmp
  | OGe: o1:operand -> o2:operand -> ocmp
  | OLt: o1:operand -> o2:operand -> ocmp
  | OGt: o1:operand -> o2:operand -> ocmp

type code = precode ins ocmp
type codes = list code

(* TODO: Eventually this should be a map to bytes.  Simplifying for now *)
type mem = map int uint64
assume val mem_make (#v:Type0) (mappings:int -> v) (domain:Set.set int) : m:(map int v){
  Set.equal (Map.domain m) domain /\
  (forall (i:int).{:pattern (Map.sel m i)} Map.sel m i == mappings i)}

noeq type state = {
  ok: bool;
  regs: F.restricted_t reg (fun _ -> uint64);
  flags: uint64;
  mem: mem;
}

let u (i:int{FStar.UInt.fits i 64}) : uint64 = FStar.UInt64.uint_to_t i
assume val havoc : state -> ins -> uint64

unfold let eval_reg (r:reg) (s:state) : uint64 = s.regs r
unfold let eval_mem (ptr:int) (s:state) : uint64 = s.mem.[ptr]

let eval_maddr (m:maddr) (s:state) : int =
  let open FStar.UInt64 in
  let open FStar.Mul in
    match m with
    | MConst n -> n
    | MReg reg offset -> v (eval_reg reg s) + offset
    | MIndex base scale index offset -> v (eval_reg base s) + scale * v (eval_reg index s) + offset

let eval_operand (o:operand) (s:state) : uint64 =
  match o with
  | OConst n -> u (int_to_nat64 n)
  | OReg r -> eval_reg r s
  | OMem m -> eval_mem (eval_maddr m s) s

let update_reg' (r:reg) (v:uint64) (s:state) : state =
  { s with regs = F.on_dom reg (fun r' -> if r' = r then v else s.regs r') }

let update_mem (ptr:int) (v:uint64) (s:state) : state = { s with mem = s.mem.[ptr] <- v }

let valid_maddr (m:maddr) (s:state) : bool =
  s.mem `Map.contains` (eval_maddr m s)

let valid_operand (o:operand) (s:state) : bool =
  match o with
  | OConst n -> true
  | OReg r -> true
  | OMem m -> valid_maddr m s

let update_operand_preserve_flags' (o:dst_op) (v:uint64) (s:state) : state =
  match o with
  | OReg r -> update_reg' r v s
  | OMem m -> update_mem (eval_maddr m s) v s

let update_operand' (o:dst_op) (ins:ins) (v:uint64) (s:state) : state =
  { (update_operand_preserve_flags' o v s) with flags = havoc s ins }

open FStar.UInt64

(* REVIEW: Will we regret exposing a mod here?  Should flags be something with more structure? *)
let cf (flags:uint64) : bool =
  v flags % 2 = 1

let update_cf (flags:uint64) (new_cf:bool) : (new_flags:uint64{cf new_flags == new_cf}) =
  if new_cf then
    if not (cf flags) then
      flags +^ 1uL
    else
      flags
  else
    if (cf flags) then
      flags -^ 1uL
    else
      flags



let st (a:Type) = state -> a * state

unfold
let return (#a:Type) (x:a) :st a =
  fun s -> x, s

unfold
let bind (#a:Type) (#b:Type) (m:st a) (f:a -> st b) :st b =
fun s0 ->
  let x, s1 = m s0 in
  let y, s2 = f x s1 in
  y, {s2 with ok=s0.ok && s1.ok && s2.ok}

unfold
let get :st state =
  fun s -> s, s

unfold
let set (s:state) :st unit =
  fun _ -> (), s

unfold
let fail :st unit =
  fun s -> (), {s with ok=false}

unfold
let check (valid: state -> bool) : st unit =
  s <-- get;
  if valid s then
    return ()
  else
    fail

unfold
let run (f:st unit) (s:state) : state = snd (f s)

(*
let check_eval_operand (valid: operand -> state -> bool) (o:operand) : uint64 * st =
 check (valid o);;
 s <-- get();
 (2, return s)

 (eval_operand o s, return s)
*)

unfold
let update_operand_preserve_flags (dst:dst_op) (v:uint64) :st unit =
  check (valid_operand dst);;
  s <-- get;
  set (update_operand_preserve_flags' dst v s)

(* Default version havocs flags *)
unfold
let update_operand (dst:dst_op) (ins:ins) (v:uint64) :st unit =
  check (valid_operand dst);;
  s <-- get;
  set (update_operand' dst ins v s)

let update_reg (r:reg) (v:uint64) :st unit =
  s <-- get;
  set (update_reg' r v s)

let update_flags (new_flags:uint64) :st unit =
  s <-- get;
  set ( { s with flags = new_flags } )

abstract
let example (dst:dst_op) (src:operand) :st unit =
  check (valid_operand dst);;
  check (valid_operand src);;
  update_operand_preserve_flags dst 2uL

//abstract
//let test (dst:dst_op) (src:operand) (s:state) :state =
//  run (example dst src) s

abstract
let logxor (x:int) (y:int) : nat64 =
  if FStar.UInt.fits x 64
  && FStar.UInt.fits y 64
  then FStar.UInt.logxor #64 x y
  else 0

let logxor_uint64 (x:int) (y:int)
  : Lemma (ensures (FStar.UInt.fits x 64 /\
                    FStar.UInt.fits y 64) ==>
                    logxor x y = FStar.UInt.logxor #64 x y)
          [SMTPat (logxor x y)]
  = ()          

abstract
let logand (x:int) (y:int) : nat64 =
  if FStar.UInt.fits x 64
  && FStar.UInt.fits y 64
  then FStar.UInt.logand #64 x y
  else 0

let logand_uint64 (x:int) (y:int)
  : Lemma (ensures (FStar.UInt.fits x 64 /\
                    FStar.UInt.fits y 64) ==>
                    logand x y = FStar.UInt.logand #64 x y)
          [SMTPat (logand x y)]
  = ()          

abstract
let shift_right (x:int) (y:int) : nat64 =
  if FStar.UInt.fits x 64
  && y >= 0
  then FStar.UInt.shift_right #64 x y
  else 0

let shift_right_uint64 (x:int) (y:int)
  : Lemma (ensures (FStar.UInt.fits x 64 /\
                    0 <= y /\
                    y < 64 ==>
                    shift_right x y = FStar.UInt.shift_right #64 x y))
          [SMTPat (shift_right x y)]
  = ()          

abstract
let shift_left (x:int) (y:int) : nat64 =
  if FStar.UInt.fits x 64
  && y >= 0
  then FStar.UInt.shift_left #64 x y
  else 0

let shift_left_uint64 (x:int) (y:int)
  : Lemma (ensures (FStar.UInt.fits x 64 /\
                    0 <= y /\
                    y < 64 ==>
                    shift_left x y = FStar.UInt.shift_left #64 x y))
          [SMTPat (shift_left x y)]
  = ()          

let eval_ocmp (s:state) (c:ocmp) :bool =
  match c with
  | OEq o1 o2 -> eval_operand o1 s = eval_operand o2 s
  | ONe o1 o2 -> eval_operand o1 s <> eval_operand o2 s
  | OLe o1 o2 -> eval_operand o1 s <=^ eval_operand o2 s
  | OGe o1 o2 -> eval_operand o1 s >=^ eval_operand o2 s
  | OLt o1 o2 -> eval_operand o1 s <^ eval_operand o2 s
  | OGt o1 o2 -> eval_operand o1 s >^ eval_operand o2 s

(* These wrappers of the operators from FStar.UInt are only present
   because we discovered that using specs of the form (v a + v b) % pow2 64
   causes Z3 to require some amount of non-linear arithmetic, 
   which we prefer to avoid *)
val add_mod64: a:uint64 -> b:uint64 -> Pure uint64
  (requires True)
  (ensures (fun c -> (v a + v b) % nat64_max = v c))
let add_mod64 a b = a +%^ b

val sub_mod64: a:uint64 -> b:uint64 -> Pure uint64
  (requires True)
  (ensures (fun c -> (v a - v b) % nat64_max = v c))
let sub_mod64 a b = a -%^ b

val mul_mod64: a:uint64 -> b:uint64 -> Pure uint64
  (requires True)
  (ensures (fun c -> (v a `op_Multiply` v b) % nat64_max = v c))
let mul_mod64 a b = a *%^ b

val mul_div64: a:uint64 -> b:uint64 -> Pure uint64
  (requires True)
  (ensures (fun c -> v a `op_Multiply` v b >= 0 /\ (v a `op_Multiply` v b) / nat64_max = v c))
let mul_div64 a b = a */^ b

let eval_ins (ins:ins) : st unit =
  let open FStar.Mul in
  s <-- get;
  match ins with
  | Mov64 dst src ->
    check (valid_operand src);;
    update_operand_preserve_flags dst (eval_operand src s)

  | Add64 dst src ->
    let sum = v (eval_operand dst s) + v (eval_operand src s) in
    let new_carry = sum >= nat64_max in
    check (valid_operand src);;
    update_operand dst ins (eval_operand dst s `add_mod64` eval_operand src s);;
    update_flags (update_cf s.flags new_carry)

  | AddLea64 dst src1 src2 ->
    check (valid_operand src1);;
    check (valid_operand src2);;
    update_operand_preserve_flags dst (eval_operand src1 s `add_mod64` eval_operand src2 s)

  | AddCarry64 dst src ->
    let old_carry = if cf(s.flags) then 1 else 0 in
    let sum = v (eval_operand dst s) + v (eval_operand src s) + old_carry in
    let new_carry = sum >= nat64_max in
    check (valid_operand src);;
    update_operand dst ins (uint_to_t (sum % nat64_max));;
    update_flags (update_cf s.flags new_carry)

  | Sub64 dst src ->
    check (valid_operand src);;
    update_operand dst ins (eval_operand dst s `sub_mod64` eval_operand src s)

  | Mul64 src ->
    let hi = eval_reg Rax s `mul_div64` eval_operand src s in
    let lo = eval_reg Rax s `mul_mod64` eval_operand src s in
    check (valid_operand src);;
    update_reg Rax lo;;
    update_reg Rdx hi;;
    update_flags (havoc s ins)

  | IMul64 dst src ->
    check (valid_operand src);;
    update_operand dst ins (eval_operand dst s `mul_mod64` eval_operand src s)

  | Xor64 dst src ->
    check (valid_operand src);;
    update_operand dst ins (u (v (eval_operand dst s) `logxor` v (eval_operand src s)))

  | And64 dst src ->
    check (valid_operand src);;
    update_operand dst ins (u (v (eval_operand dst s) `logand` v (eval_operand src s)))

  | Shr64 dst amt ->
    update_operand dst ins (u (v (eval_operand dst s) `shift_right` v (eval_operand amt s)))

  | Shl64 dst amt ->
    update_operand dst ins (u (v (eval_operand dst s) `shift_left` v (eval_operand amt s)))

  | _ -> fail

(*
 * these functions return an option state
 * None case arises when the while loop runs out of fuel
 *)

// TODO: IfElse and While should havoc the flags

val eval_code:  c:code           -> fuel:nat -> s:state -> Tot (option state) (decreases %[fuel; c])
val eval_codes: l:codes          -> fuel:nat -> s:state -> Tot (option state) (decreases %[fuel; l])
val eval_while: b:ocmp -> c:code -> fuel:nat -> s:state -> Tot (option state) (decreases %[fuel; c])

let rec eval_code c fuel s =
  match c with
  | Ins ins                       -> Some (run (eval_ins ins) s)
  | Block l                       -> eval_codes l fuel s
  | IfElse ifCond ifTrue ifFalse  -> if eval_ocmp s ifCond then eval_code ifTrue fuel s else eval_code ifFalse fuel s
  | While b c                     -> eval_while b c fuel s

and eval_codes l fuel s =
  match l with
  | []   -> Some s
  | c::tl ->
    let s_opt = eval_code c fuel s in
    if None? s_opt then None else eval_codes tl fuel (Some?.v s_opt)

and eval_while b c fuel s0 =
  if fuel = 0 then None else
  if not (eval_ocmp s0 b) then Some s0
  else
    match eval_code c (fuel - 1) s0 with
    | None -> None
    | Some s1 ->
      if s1.ok then eval_while b c (fuel - 1) s1  // success: continue to next iteration
      else Some s1  // failure: propagate failure immediately
