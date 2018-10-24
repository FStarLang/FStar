module Interop
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
  | a :: rest -> (a -> arrow rest result)

let vale_args = n:list (a:Type0{a == uint_64}){List.Tot.length n <= 4}

let max_arity = 4
let arity = n:nat { n <= max_arity }

let rec n_arrow (n:arity) (result:Type) =
  if n = 0 then result
  else uint_64 -> n_arrow (n - 1) result


let elim #n #result (f:n_arrow n result)
  : normalize_term (n_arrow n result)
  = f

let elim_1 (#n:arity{n > 0}) #r (f:n_arrow n r)
  : uint_64 -> n_arrow (n - 1) r
  = f

let rec widen_2 (#n:arity) (#r:Type) (f:n_arrow n r) (m:arity{n <= m})
  : Tot (n_arrow m r) (decreases m) =
  if m = n then f
  else (fun (x:uint_64) -> widen_2 f (m - 1))

let rec widen (#n:arity) (#r:Type) (f:n_arrow n r) (m:arity{n <= m})
  : Tot (n_arrow m r) (decreases m) =
  if m = n then f
  else if n = 0 then (fun (x:uint_64) -> widen f (m - 1))
  else fun (x:uint_64) -> widen #(n - 1) #r (elim_1 f x) (m - 1)

let rec elim_m (#n:arity) #r (m:arity{m <= n}) (f:n_arrow n r)
  : registers -> n_arrow m r
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

module List = FStar.List.Tot

// let rec elim_l (#n:arity{n > 0}) #r (m:arity{0 < m /\ m <= n}) (f:n_arrow n r)
//   : List.llist uint_64 (n - m) -> n_arrow m r
//   = fun nl ->
//       match (n - m) with
//       | 0 -> f
//       | _ -> elim_l #(n - 1) #r m (elim_1 f (List.hd nl)) (List.tl nl)


// let rec list_as_registers (m:arity) (l:List.llist uint_64 m) : registers =
//   match l with
//   | [] -> Map.const 0uL
//   | hd::tl ->
//     let tl = list_as_registers (m - 1) tl in
//     let reg = as_reg (1 + max_arity - m) in
//     Map.upd tl reg hd


let idem_elim_m (#n:arity) (m1:arity{m1 <= n}) (m2:arity{m2 <= m1}) (f:vale_pre n) regs h
   : Lemma (elim_m 0 (elim_m m2 (elim_m m1 f regs) regs) regs h <==> (elim_m 0 (elim_m m2 f regs) regs h))
   = ()

let widen_elim_m (#n:arity) (m1:arity{m1 <= n}) (m2:arity{m2 <= m1}) (f:vale_pre n) regs h
   : Lemma (elim_m 0 (widen (elim_m 0 f regs) max_arity) regs h <==> elim_m 0 f regs h)
   = ()

module F = FStar.FunctionalExtensionality

// let elim_m_elim (#n:arity{n > 0}) (#pre:vale_pre n) (#post:vale_post n)
//                 (v:vale_sig n pre post)
//     : Lemma (elim_m n pre (Map.const 0uL) == elim (elim_m n
//             (ensures (elim

// let elim_m_pre (#n:arity) (#r:Type)
//                (f:n_arrow n r)
//                (m:arity{0 < m /\ m <= n})
//                (regs:registers)
//   : Lemma (elim_m
// val elim_m_pre (#n:arity) (m:arity{0 < m /\ m <= n /\ m = 1}) (pre:vale_pre n) (regs:registers) (x:uint_64) (h:HS.mem)
//   : Lemma (requires (elim #1 (elim_m m pre regs) x h))
//           (ensures  (elim_m 0 pre (Map.upd regs R1 x) h))
//   = admit()
//   = match n - m with
//     | 0 ->
//       assert (elim_m m pre regs
//     | _ -> admit()
#reset-options "--z3rlimit_factor 10 --max_fuel 6 --initial_fuel 6 --max_ifuel 6 --initial_ifuel 6"

// let rec elim_m_elim_vale_pre
//                  (n:arity)
//                  (pre0:vale_pre n)
//                  (h:HS.mem)
//                  (regs:registers{elim_m 0 pre0 regs h})
//     : Lemma (as_vale_pre (widen_2 pre0 4) ({registers=regs; memory=h}))
//     = match m - n with
//       | 0 -> ()
//       | _ -> let pre1 = elim_1 pre0 (Map.sel regs (as_reg (1 + max_arity - n))) in
//             assert (elim_m 0 pre1 regs h);
//             elim_m_elim_vale_pre (n - 1) pre1 h regs;
//             assert (as_vale_pre (widen2 pre1 4) ({registers=regs; memory=h}))

// let elim_m_widen_post (n:arity{0 < n})
//                       (m:arity{m = 1})
//                       (post0:vale_post n)
//                       (regs:registers)
//                       (h:HS.mem)
//                       (state1:state)
//     : Lemma (let post : n_arrow 1 (HS.mem -> HS.mem -> prop) = elim_m m post0 regs in
//              let state = { registers = regs; memory = h } in
//              as_vale_post (widen post 4) state state1 <==>
//              as_vale_post (widen post0 4) state state1)
//     = admit()

let rec wrap
        (#n:arity{n > 0})
        (#pre:vale_pre n)
        (#post:vale_post n)
        (v:vale_sig n pre post)
  : as_lowstar_sig n pre post
  =
  let rec aux (m:arity{0 < m /\ m <= n}) (regs:registers{
          let pre0 = pre in
          let pre : vale_pre m = elim_m m pre0 regs in
          (forall h.
             elim_m 0 pre0 regs h <==>
             elim_m 0 pre regs h)
      })
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
                registers = Map.upd regs (as_reg m) x;
                memory = h0;
              } in
              assert (elim #1 pre x h0);
              // elim_m_elim_vale_pre n 1 pre0 x h0 regs;
              // assert (as_vale_pre (widen pre 4) state);
              // elim_m_widen_pre n m pre0 state.registers h0;
              assert (as_vale_pre (widen pre0 4) state);
              let state1 = v state in
              assert (as_vale_post (widen post0 4) state (v state));
              admit();
              // elim_m_widen_post n m post0 state.registers h0 (v state);
              assert (as_vale_post (widen post 4) state (v state));
              put (v state).memory
       in
       (f <: as_lowstar_sig 1 pre post)

    | _ ->
      admit()
    in
    admit()

      let f : x:uint_64
              -> as_lowstar_sig
                   (m - 1)
                   (elim_m (m - 1) (elim_1 pre x) regs)
                   (elim_m (m - 1) (elim_1 post x) regs) =
          fun (x:uint_64) ->
            aux (m - 1) (Map.upd regs (as_reg m) x)
      in
      f
    in
    aux n (Map.const 0uL)
