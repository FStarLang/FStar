module QuickTestNBE

open FStar.Range

irreducible let va_qattr = ()

noeq type vale_state = {vs_ok:bool;}

let quickProc_wp (a:Type0) : Type u#1 = (s0:vale_state) -> (wp_continue:vale_state -> a -> Type0) -> Type0

let t_ensure (#a:Type0) (wp:quickProc_wp a) (s0:vale_state) (k:(vale_state -> a -> Type0)) =
  fun (sM, g) -> k sM g

let t_proof (#a:Type0) (wp:quickProc_wp a) : Type =
  s0:vale_state -> k:(vale_state -> a -> Type0) -> Ghost (vale_state & a)
    (requires wp s0 k)
    (ensures t_ensure wp s0 k)

// Code that returns a ghost value of type a
[@va_qattr]
noeq type quickCode (a:Type0) : Type =
| QProc:
    wp:quickProc_wp a ->
    proof:t_proof wp ->
    quickCode a

[@va_qattr "opaque_to_smt"]
let labeled_wrap (r:range) (msg:string) (p:Type0) : GTot Type0 = labeled r msg p

[@va_qattr "opaque_to_smt"]
let label (r:range) (msg:string) (p:Type0) : Ghost Type (requires True) (ensures fun q -> q <==> p) =
  assert_norm (labeled_wrap r msg p <==> p);
  labeled_wrap r msg p

noeq type quickCodes (a:Type0) : Type =
| QEmpty: a -> quickCodes a
| QPURE: r:range -> msg:string -> pre:pure_wp unit ->
    (unit -> PURE unit pre) -> quickCodes a -> quickCodes a

[@va_qattr]
let qPURE
    (#pre:pure_wp unit) (#a:Type0) (r:range) (msg:string)
    ($l:unit -> PURE unit pre) (qcs:quickCodes a)
  : quickCodes a =
  QPURE r msg pre l qcs

[@va_qattr]
let range1 = mk_range "QuickTestNBE" 1 2 3 4

[@va_qattr]
let rec wp (#a:Type0) (qcs:quickCodes a) (k:vale_state -> a -> Type0) (s0:vale_state) :
  Tot Type0 (decreases %[0; qcs])
  =
  match qcs with
  | QEmpty g -> k s0 g
  | QPURE r msg pre l qcs ->
      (forall (p:unit -> GTot Type0).//{:pattern (pre p)}
        (forall (u:unit).{:pattern (guard_free (p u))} wp qcs k s0 ==> p ())
        ==>
        label r msg (pre p))

[@va_qattr]
let wp_block (#a:Type) (qcs:vale_state -> GTot (quickCodes a)) (s0:vale_state) (k:vale_state -> a -> Type0) : Type0 =
  wp (qcs s0) k s0

assume val qblock_proof (#a:Type) (qcs:vale_state -> GTot (quickCodes a)) (s0:vale_state) (k:vale_state -> a -> Type0)
  : Ghost (vale_state & a)
  (requires wp_block qcs s0 k)
  (ensures fun (sM, g) -> k sM g)

[@"opaque_to_smt" va_qattr]
let qblock (#a:Type) (qcs:vale_state -> GTot (quickCodes a)) : quickCode a =
  QProc (wp_block qcs) (qblock_proof qcs)

[@va_qattr]
unfold let wp_sound_code_pre (#a:Type0) (qc:quickCode a) (s0:vale_state) (k:(s0':vale_state{s0 == s0'}) -> vale_state -> a -> Type0) : Type0 =
  forall (ok:bool). QProc?.wp qc s0 (k s0)

unfold let wp_sound_code_post (#a:Type0) (qc:quickCode a) (s0:vale_state) (k:(s0':vale_state{s0 == s0'}) -> vale_state -> a -> Type0) ((sN:vale_state), (gN:a)) : Type0 =
  k s0 sN gN

unfold let normal_steps : list string = [`%QProc?.wp;]
unfold let normal (x:Type0) : Type0 = norm [nbe; iota; zeta; simplify; primops; delta_attr [`%va_qattr]; delta_only normal_steps] x

assume val wp_sound_code_norm (#a:Type0) (qc:quickCode a) (s0:vale_state) (k:(s0':vale_state{s0 == s0'}) -> vale_state -> a -> Type0) : Lemma 
  (requires normal (wp_sound_code_pre qc s0 k))
  (ensures True)

assume val f (x:int) : int
assume val lem (x:int) : Lemma
  (requires f x - f x == 0)
  (ensures (forall (i:int).{:pattern f i} f i > 0))

open FStar.Monotonic.Pure

[@"opaque_to_smt" va_qattr]
let va_qcode_Test : (quickCode unit) =
  reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic;
  (qblock
    (fun (va_s:vale_state) ->
      qPURE range1 "" (fun (_:unit) -> lem 4) (
      qPURE range1 "" (fun (_:unit) -> lem 5) (
      qPURE range1 "" (fun (_:unit) -> lem 6) (
      QEmpty ()
    ))))
  )

let va_lemma_Test (va_s0:vale_state) =
  wp_sound_code_norm
    va_qcode_Test
    va_s0
    (fun va_s0 va_sM va_g -> True)

assume val lem2 (x:int) : Lemma
  (requires f x - f x == 0 /\
            f x == 0)
  (ensures (forall (i:int).{:pattern f i} f i > 0))

[@"opaque_to_smt" va_qattr]
let va_qcode_Test2 : (quickCode unit) =
  reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic;
  (qblock
    (fun (va_s:vale_state) ->
      qPURE range1 "" (fun (_:unit) -> lem2 4) (
      QEmpty ()
    ))
  )

#push-options "--print_expected_failures"
//#push-options "--debug QuickTestNBE --debug_level SMTQuery --ugly --print_implicits"
[@@expect_failure [19]]
let va_lemma_Test2 (va_s0:vale_state) =
  wp_sound_code_norm
    va_qcode_Test2
    va_s0
    (fun va_s0 va_sM va_g -> True)

