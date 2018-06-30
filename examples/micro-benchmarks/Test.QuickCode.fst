module Test.QuickCode

////////////////////////////////////////////////////////////////////////////////
// A simpler first example
////////////////////////////////////////////////////////////////////////////////

irreducible
let qattr = ()

unfold let norm_simple #a (x:a) : a =
  norm [iota; zeta; simplify; primops; delta_attr qattr; nbe] x

type reg_file = int -> int


[@qattr]
let sel (r:reg_file) (x:int) = r x

[@qattr]
let upd (r:reg_file) (x:int) (v:int) = fun y -> if x=y then v else sel r y

#set-options "--debug_level NBE"

//#set-options "--debug_level print_normalized_terms --debug_level NBE"

let test = 
  assert (norm_simple (if 0 = 0 then true else false) == true)
  
//let test (r:reg_file) =
//  assert (norm_simple (sel (upd r 0 0) 0) == 0)
//  assert (norm_simple (sel (upd (upd (upd r 0 0) 1 1) 2 2) 0) == 0)


////////////////////////////////////////////////////////////////////////////////
// Something a bit more involved, but more representative of Vale's quick code
////////////////////////////////////////////////////////////////////////////////
#reset-options "--z3rlimit 10 --lax"

noeq type state = {
  ok: bool;
  regs: int -> int;
  xmms: int -> int;
  flags: int;
  mem: int;
}

[@qattr]
let up_reg (r:int) (v:int) (s:state) : state =
  { s with regs = fun r' -> if r = r' then v else s.regs r' }

[@qattr]
let up_xmm (x:int) (v:int) (s:state) : state =
  { s with xmms = fun x' -> if x = x' then v else s.xmms x' }

[@qattr] let update_reg (r:int) (sM:state) (sK:state) : state = up_reg r (sM.regs r) sK [@qattr] let update_xmm (x:int) (sM:state) (sK:state) : state = up_xmm x (sM.xmms x) sK [@qattr] let upd_flags (flags:int) (s:state) : state = { s with flags = flags } [@qattr] let upd_mem (mem:int) (s:state) : state = { s with mem = mem }



unfold let normal_steps : list string =
  [
    %`Mkstate?.ok;
    %`Mkstate?.regs;
    %`Mkstate?.xmms;
    %`Mkstate?.flags;
    %`Mkstate?.mem
  ]

unfold let normal (x:Type0) : Type0 =
  norm [iota; zeta; simplify; primops; delta_attr qattr; delta_only normal_steps] x


[@ "opaque_to_smt" qattr]
let wp_compute_ghash_incremental (x:int) (s0:state) (k:(state -> Type0)) : Type0 =
  let sM = s0 in
// COMMENT OUT 1-3 OF THE FOLLOWING LINES TO SPEED UP:
  let sM = up_xmm 1 x (up_xmm 2 x (up_reg 9 x (up_reg 4 x sM))) in
  let sM = up_xmm 3 x (up_xmm 2 x (up_xmm 1 x (upd_flags x sM))) in
  let sM = up_xmm 6 x (up_xmm 5 x (up_xmm 4 x sM)) in
  (k sM)

#reset-options "--z3rlimit 10 --admit_smt_queries true"

let lemma_gcm_core (s0:state) (x:int) : Lemma False =
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
    sM.xmms 0 == sU.xmms 0
    in
  let k s = wp_compute_ghash_incremental x s k in
  let k s = wp_compute_ghash_incremental x s k in
  assert (normal (k s0))
