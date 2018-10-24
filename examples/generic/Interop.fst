module Interop
open FStar.FunctionalExtensionality
open FStar.Integers
module L = LowStar.Buffer
module M = FStar.Map

type reg =
  | R1
  | R2
  | R3
  | R4

type registers = FStar.Map.t reg uint_64

noeq
type state = {
  registers: registers;
  memory: FStar.HyperStack.mem
}

let ireg = n:pos{ n <= 4 }
let as_reg (n:ireg) =
  match n with
  | 1 -> R1
  | 2 -> R2
  | 3 -> R3
  | 4 -> R4

let rec arrow (args: list Type) (result:Type) =
  match args with
  | [] -> result
  | a :: rest -> (a ^-> arrow rest result)

let vale_args = n:list (a:Type0{a == uint_64}){List.Tot.length n <= 4}

let max_arity = 4
let arity = n:nat { n <= max_arity }

let rec n_arrow (n:arity) (result:Type) =
  if n = 0 then result
  else uint_64 -> n_arrow (n - 1) result

let elim #n #result (f:n_arrow n result)
  : normalize_term (n_arrow n result)
  = f
  
module F = FStar.FunctionalExtensionality
let elim_1 (#n:arity{n > 0}) #r (f:n_arrow n r)
  : (uint_64 -> n_arrow (n - 1) r)
  = f

let rec elim_m (#n:arity) #r (m:arity{m <= n}) (f:n_arrow n r)
  : (registers -> n_arrow m r)
  = fun regs ->
      match (n - m) with
      | 0 -> f
      | _ ->
        elim_m #(n - 1) #r m (elim_1 f (Map.sel regs (as_reg (1 + max_arity - n)))) regs

module HS = FStar.HyperStack
let vale_pre (n:arity) = n_arrow n (HS.mem -> prop)
let vale_post (n:arity) = n_arrow n (HS.mem -> HS.mem -> prop)

unfold
let as_vale_pre
       (#n:arity)
       (pre:vale_pre n)
    : state -> prop =
    fun state ->
      elim_m 0 pre state.registers state.memory

unfold
let as_vale_post
       (#n:arity)
       (post:n_arrow n (HS.mem -> HS.mem -> prop))
    : state -> state -> prop =
    fun s0 s1 ->
      elim_m 0 post s0.registers s0.memory s1.memory

let vale_sig
    (n:arity)
    (pre:vale_pre n)
    (post:vale_post n)
    = s0:state
    -> Pure state
        (requires (as_vale_pre pre s0))
        (ensures (fun s1 -> as_vale_post post s0 s1))
open FStar.HyperStack.ST

let rec as_lowstar_sig (n:arity{n > 0}) (pre:vale_pre n) (post:vale_post n) : Type0 =
  match n with
  | 1 -> x:uint_64 -> ST unit (requires (fun h0 -> elim #1 pre x h0))
                            (ensures (fun h0 _ h1 -> elim #1 post x h0 h1))
  | _ -> x:uint_64 -> as_lowstar_sig (n - 1) (elim_1 pre x) (elim_1 post x)

assume val gput: f:(unit -> GTot HS.mem) -> ST unit (requires (fun _ -> True)) (ensures (fun _ _ h1 -> h1 == f()))
assume val put: h:HS.mem -> ST unit (requires (fun _ -> True)) (ensures (fun _ _ h1 -> h1 == h))

// module List = FStar.List.Tot
#reset-options "--z3rlimit_factor 10 --max_fuel 6 --initial_fuel 6 --max_ifuel 6 --initial_ifuel 6"

let idem_elim_m (#n:arity) (m1:arity{m1 <= n}) (m2:arity{m2 <= m1}) (f:vale_pre n) regs h
   : Lemma (elim_m 0 (elim_m m2 (elim_m m1 f regs) regs) regs h <==> (elim_m 0 (elim_m m2 f regs) regs h))
   = ()

// let widen_elim_m (#n:arity) (m1:arity{m1 <= n}) (m2:arity{m2 <= m1}) (f:vale_pre n) regs h
//    : Lemma (elim_m 0 (widen (elim_m 0 f regs) max_arity) regs h <==> elim_m 0 f regs h)
//    = ()

let rec elim_1_m_aux (#n:arity{n > 0}) (m:arity{m = 1 /\ m <= n}) (pre0:vale_pre n) (regs:registers) (x:uint_64) h
  : Lemma (ensures (let regs1 = Map.upd regs (as_reg 1) x in
                    elim_m 0 pre0 regs1 h <==>
                    elim_m 0 (elim_m m pre0 regs1) regs1 h))
  = ()                    

let rec elim_1_m (#n:arity{n > 0}) (m:arity{m = 1 /\ m <= n}) (pre0:vale_pre n) (regs:registers) (x:uint_64) h
  : Lemma (ensures (let regs1 = Map.upd regs (as_reg 1) x in
                    elim_m 0 pre0 regs1 h <==>
                    elim_m 0 (elim_m m pre0 regs) regs1 h))
  = admit()                    

let rec elim_1_m_ (#n:arity{n > 0}) (m:arity{m = 1 /\ m <= n}) (pre0:vale_pre n) (regs:registers) (x:uint_64) h
  : Lemma (ensures (let regs1 = Map.upd regs (as_reg 4) x in
                    elim_m 0 pre0 regs1 h <==>
                    elim #1 (elim_m m pre0 regs) x h))
  = ()
           
let rec wrap
        (#n:arity{n > 0})
        (#pre:vale_pre n)
        (#post:vale_post n)
        (v:vale_sig n pre post)
  : as_lowstar_sig n pre post
  =
  let rec aux (m:arity{0 < m /\ m <= n}) (regs:registers)
    : Tot (as_lowstar_sig m (elim_m m pre regs) (elim_m m post regs))
    = let pre0 = pre in
      let post0 = post in
      let pre = elim_m m pre0 regs in
      let post = elim_m m post regs in
      match m with
      | 1 ->
        let f : x:uint_64
              -> ST unit
                (requires (fun h -> elim #1 pre x h))
                (ensures (fun h0 _ h1 -> elim #1 post x h0 h1)) =
            fun (x:uint_64) ->
              let h0 = get () in
              let state = {
                registers = Map.upd regs (as_reg (1 + max_arity - m)) x;
                memory = h0;
              } in
              // assert (elim #1 pre x h0);
              // elim_1_m m pre0 regs x h0;
              // assert (elim_m 0 pre0 state.registers h0);
              let state1 = v state in
              // assert (as_vale_post post0 state (v state));
              //assume (as_vale_post post state (v state));
              //assume (elim #1 post x h0 (v state).memory);
              put (v state).memory
       in
       (f <: as_lowstar_sig 1 pre post)

    | _ ->
      let f : x:uint_64
              -> as_lowstar_sig
                   (m - 1)
                   (elim_1 pre x)
                   (elim_1 post x) =
          fun (x:uint_64) ->
            let regs1 = (Map.upd regs (as_reg (1 + max_arity - m)) x) in
            let f : as_lowstar_sig (m - 1) (elim_m (m - 1) pre0 regs1) (elim_m (m - 1) post0 regs1) = aux (m - 1) regs1 in
            // assume (elim_m (m - 1) pre0 regs1 == elim_1 pre x);
            // assume (elim_m (m - 1) post0 regs1 == elim_1 post x);
            f
      in
      f
    in
    aux n (Map.const 0uL)
