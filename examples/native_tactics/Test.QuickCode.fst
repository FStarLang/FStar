module Test.QuickCode
module R = Registers.List

irreducible let qattr = ()

noeq type state = {
  ok: bool;
  regs: R.regmap int;
  xmms: R.regmap int;
  flags: int;
  mem: int;
}

[@qattr]
let up_reg (r:int) (v:int) (s:state) : state =
  { s with regs = R.upd s.regs r v }

[@qattr]
let up_xmm (x:int) (v:int) (s:state) : state =
  { s with xmms = R.upd s.xmms x v }

[@qattr]
let update_reg (r:int) (sM:state) (sK:state) : state = up_reg r (R.sel sM.regs r) sK

[@qattr]
let update_xmm (x:int) (sM:state) (sK:state) : state = up_xmm x (R.sel sM.xmms x) sK

[@qattr]
let upd_flags (flags:int) (s:state) : state = { s with flags = flags }

[@qattr]
let upd_mem (mem:int) (s:state) : state = { s with mem = mem }

unfold
let normal_steps : list string =
  [
    `%Mkstate?.ok;
    `%Mkstate?.regs;
    `%Mkstate?.xmms;
    `%Mkstate?.flags;
    `%Mkstate?.mem;
    `%R.sel;
    `%R.upd;
    `%R.create;
    `%R.eta_map;
  ]

unfold
let normal (x:Type0) : Type0 = norm [iota; zeta; simplify; primops; delta_attr qattr; delta_only normal_steps//; nbe
  ] x

[@qattr]
let eta_state (s0:state) =
  {
    ok    = s0.ok;
    regs  = R.eta_map 20 s0.regs;
    xmms  = R.eta_map 20 s0.xmms;
    flags = s0.flags;
    mem   = s0.mem
  }

[@ "opaque_to_smt" qattr]
let wp_compute_ghash_incremental (x:int) (s0:state) (k:(state -> Type0)) : Type0 =
  let sM = eta_state s0 in
  let sM = up_xmm 1 x (up_xmm 2 x (up_reg 9 x (up_reg 4 x sM))) in
  let sM = up_xmm 3 x (up_xmm 2 x (up_xmm 1 x (upd_flags x sM))) in
  let sM = up_xmm 6 x (up_xmm 5 x (up_xmm 4 x sM)) in
  (k sM)

let my_assert (p:Type) : Lemma (requires (normal p))
                               (ensures True) = ()

let lemma_gcm_core (s0:state) (x:int) =
  let s0 = eta_state s0 in
  let k s =
    let sM = s in
    let sM = up_reg 1 x sM in
    let sM = up_reg 1 x sM in
    let sM = upd_flags x (up_xmm 2 x sM) in
    let sM = upd_flags x (up_xmm 2 x sM) in
    let sM = upd_flags x (up_xmm 2 x sM) in
    let sM = up_xmm 6 x (up_xmm 5 x (up_xmm 4 x (up_xmm 3 x (up_xmm 2 x (upd_flags x (up_xmm 1 x sM)))))) in
    let sM = upd_flags x (up_xmm 7 x sM) in
    let sM = upd_flags x (up_xmm 2 x (up_xmm 1 x (up_xmm 0 x sM))) in
    let sU = s0 in
    let sU = update_reg 1 sM s0 in
    let sU = update_reg 10 sM (update_reg 9 sM (update_reg 4 sM (update_reg 3 sM sU))) in
    let sU = update_xmm 3 sM (update_xmm 2 sM (update_xmm 1 sM (update_xmm 0 sM sU))) in
    let sU = update_xmm 6 sM (update_xmm 7 sM (update_xmm 5 sM (update_xmm 4 sM sU))) in
    let sU = update_xmm 7 sM sU in
    R.sel sM.xmms 7 == R.sel sU.xmms 7
    in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  my_assert (k s0)
