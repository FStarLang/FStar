module Interop
open FStar.FunctionalExtensionality
open FStar.Integers
open FStar.HyperStack.ST
module L = LowStar.Buffer
module M = FStar.Map

(* Some fixed register type *)
type reg =
  | R1
  | R2
  | R3
  | R4

(* A register file is a map from registers to words *)
type registers = FStar.Map.t reg uint_64

(* A machine state includes a register file and a memory *)
noeq
type state = {
  registers: registers;
  memory: FStar.HyperStack.mem
}

(* It's convenient to use integers for registers in several places below
   ireg is an integer interpretable as a register (via as_reg) *)
let ireg = n:pos{ n <= 4 }
let as_reg (n:ireg) =
  match n with
  | 1 -> R1
  | 2 -> R2
  | 3 -> R3
  | 4 -> R4

(* We support arities up to the number of registers *)
let max_arity = 4
let arity = n:nat { n <= max_arity }

(* `n_arrow n r` is `x1:uint_64 -> ... -> xn:uint_64 -> r` *)
let rec n_arrow (n:arity) (result:Type) =
  if n = 0 then result
  else uint_64 -> n_arrow (n - 1) result

(* `elim` is a coercon to force a bit of normalization *)
let elim #n #result (f:n_arrow n result)
  : normalize_term (n_arrow n result)
  = f

(* `elim_1` peels of one arrow in an n_arrow *)
let elim_1 (#n:arity{n > 0}) #r (f:n_arrow n r)
  : (uint_64 -> n_arrow (n - 1) r)
  = f

(* `elim_m m f` is a function that receives its first
`  `n - m` arguments from the corresponding registers in a file
    leaving an m-ary function *)
let rec elim_m (#n:arity) #r (m:arity{m <= n}) (f:n_arrow n r)
  : (registers -> n_arrow m r)
  = fun regs ->
      match (n - m) with
      | 0 -> f
      | _ ->
        elim_m #(n - 1) #r m (elim_1 f (Map.sel regs (as_reg (1 + max_arity - n)))) regs

module HS = FStar.HyperStack

(* Vale preconditions are are n-ary functions returning heap predicates *)
let vale_pre (n:arity) = n_arrow n (HS.mem -> prop)
(* Vale postconditions are are n-ary functions returning binary heap relations *)
let vale_post (n:arity) = n_arrow n (HS.mem -> HS.mem -> prop)

(* as_vale_pre: turns a vale_pre into a predicate on a machine state *)
unfold
let as_vale_pre
       (#n:arity)
       (pre:vale_pre n)
    : state -> prop =
    fun state ->
      elim_m 0 pre state.registers state.memory

(* as_vale_post: turns a vale_post into a relation machine states *)
unfold
let as_vale_post
       (#n:arity)
       (post:n_arrow n (HS.mem -> HS.mem -> prop))
    : state -> state -> prop =
    fun s0 s1 ->
      elim_m 0 post s0.registers s0.memory s1.memory

(* vale_sig n pre post:
   The expected signature of a Vale function (i.e., a machine state transformer) *)
let vale_sig
    (n:arity)
    (pre:vale_pre n)
    (post:vale_post n)
    = s0:state
    -> Ghost state
        (requires (as_vale_pre pre s0))
        (ensures (fun s1 -> as_vale_post post s0 s1))

(* as_lowstar_sig n pre post: 
     Interprets a Vale signature as a Low* signature
     i.e., a stateful function with n arguments, 
     whose pre and post are the corresponding Vale pre/post
 *)
let rec as_lowstar_sig (n:arity{n > 0}) (pre:vale_pre n) (post:vale_post n) : Type0 =
  match n with
  | 1 -> x:uint_64 -> ST unit (requires (fun h0 -> elim #1 pre x h0))
                            (ensures (fun h0 _ h1 -> elim #1 post x h0 h1))
  | _ -> x:uint_64 -> as_lowstar_sig (n - 1) (elim_1 pre x) (elim_1 post x)

(* A primitives to update the state monolithically with the result of a ghost function *)
assume val gput: f:(unit -> GTot HS.mem) -> ST unit (requires (fun _ -> True)) (ensures (fun _ _ h1 -> h1 == f()))

//Avoid some inductive proofs by just letting Z3 unfold the recursive functions above
#reset-options "--z3rlimit_factor 2 --max_fuel 5 --initial_fuel 5 --max_ifuel 1 --initial_ifuel 1"
(* wrap v: Turns `v`, a Vale function, into an equivalent a Low* function *) 
let rec wrap
        (#n:arity{n > 0})
        (#pre:vale_pre n)
        (#post:vale_post n)
        (v:vale_sig n pre post)
  : as_lowstar_sig n pre post
  =
  let rec aux (m:arity{0 < m /\ m <= n}) //number of arguments still to be received
              (regs:registers)         //arguments already received in registers
    : Tot (as_lowstar_sig m (elim_m m pre regs) (elim_m m post regs))
    = let pre0 = pre in
      let post0 = post in
      let pre = elim_m m pre0 regs in
      let post = elim_m m post regs in
      match m with
      | 1 -> //last argument
        let f : x:uint_64
              -> ST unit
                (requires (fun h -> elim #1 pre x h))
                (ensures (fun h0 _ h1 -> elim #1 post x h0 h1)) =
            fun (x:uint_64) ->
              //Get the initial Low* state
              let h0 = get () in
              //Add the last argument into the registers
              let state = {
                registers = Map.upd regs (as_reg (1 + max_arity - m)) x;
                memory = h0;
              } in
              //Apply the vale function
              //and replace the Low* state
              gput (fun () -> (v state).memory)
       in
       (f <: as_lowstar_sig 1 pre post)

    | _ ->
      let f : x:uint_64
              -> as_lowstar_sig
                   (m - 1)
                   (elim_1 pre x)
                   (elim_1 post x) =
          fun (x:uint_64) -> 
            let i = (1 + max_arity - m) in //`x` is the `i`th argument
            let regs1 = (Map.upd regs (as_reg i) x) in //add it to the registers
            aux (m - 1) regs1 //recurse
      in
      f
    in
    aux n (Map.const 0uL)
