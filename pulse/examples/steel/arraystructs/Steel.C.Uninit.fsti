module Steel.C.Uninit

open FStar.PCM
open Steel.C.PCM
open Steel.C.Ref
open Steel.C.Connection
open Steel.Effect

/// Uninitialized

noeq
type uninit_t (a: Type)
= | Uninitialized
  | InitOrUnit: a -> uninit_t a

let uninit_composable
  (#a: Type)
  (p: pcm a)
: Tot (symrel (uninit_t a))
= fun u1 u2 ->
  match u1, u2 with
  | Uninitialized, InitOrUnit x
  | InitOrUnit x, Uninitialized
    -> x == one p
  | InitOrUnit x1, InitOrUnit x2
    -> composable p x1 x2
  | _ -> False

let uninit_compose
  (#a: Type)
  (p: pcm a)
  (u1: uninit_t a)
  (u2: uninit_t a { uninit_composable p u1 u2 })
: Tot (uninit_t a)
= match u1, u2 with
  | Uninitialized, _
  | _, Uninitialized
    -> Uninitialized
  | InitOrUnit x1, InitOrUnit x2
    -> InitOrUnit (op p x1 x2)

let uninit_refine
  (#a: Type)
  (p: pcm a)
  (x: uninit_t a)
: Tot prop
= match x with
  | Uninitialized -> True
  | InitOrUnit y -> p.refine y

let pcm_uninit #a (p: pcm a) : pcm (uninit_t a) = {
  FStar.PCM.p = {
         composable = uninit_composable p;
         op = uninit_compose p;
         one = InitOrUnit (one p);
      };
  comm = (fun _ _ ->
    Classical.forall_intro_2 p.comm
  );
  assoc = (fun x1 x2 x3 ->
    Classical.forall_intro_3 p.assoc;
    Classical.forall_intro (is_unit p)
  );
  assoc_r = (fun _ _ _ -> 
    Classical.forall_intro_3 p.assoc_r;
    Classical.forall_intro (is_unit p)
  );
  is_unit = (fun _ -> Classical.forall_intro (is_unit p));
  refine = uninit_refine p;
}

let value_to_uninit
  (#a: Type)
  (p: pcm a)
: Tot (morphism p (pcm_uninit p))
= mkmorphism
    (fun x -> InitOrUnit x)
    ()
    (fun _ _ -> ())

let uninit_to_value
  (#a: Type)
  (p: pcm a)
: Tot (morphism (pcm_uninit p) p)
= mkmorphism
    (fun x -> match x with InitOrUnit y -> y | _ -> one p)
    ()
    (fun _ _ -> Classical.forall_intro (is_unit p))

let uninit_conn_fpu'
  (#a: Type)
  (p: pcm a)
  (x: Ghost.erased a { ~ (Ghost.reveal x == one p) })
  (y: Ghost.erased a)
  (f: frame_preserving_upd p x y)
  (v: uninit_t a {
    (pcm_uninit p).refine v /\
    compatible (pcm_uninit p) ((value_to_uninit p).morph x) v
  })
: Tot (uninit_t a)
=
  let InitOrUnit x' = v in
  InitOrUnit (f x')

let uninit_conn_fpu_prop
  (#a: Type)
  (p: pcm a)
  (x: Ghost.erased a { ~ (Ghost.reveal x == one p) })
  (y: Ghost.erased a)
  (f: frame_preserving_upd p x y)
  (v: uninit_t a {
    (pcm_uninit p).refine v /\
    compatible (pcm_uninit p) ((value_to_uninit p).morph x) v
  })
: Lemma
  (let v_new = uninit_conn_fpu' p x y f v in
    (pcm_uninit p).refine v_new /\
    compatible (pcm_uninit p) ((value_to_uninit p).morph y) v_new /\
    (forall (frame:_{composable (pcm_uninit p) ((value_to_uninit p).morph x) frame}).
       composable (pcm_uninit p) ((value_to_uninit p).morph y) frame /\
       (op (pcm_uninit p) ((value_to_uninit p).morph x) frame == v ==> op (pcm_uninit p) ((value_to_uninit p).morph y) frame == v_new))
  )
= Classical.forall_intro (is_unit p);
  let y' = (value_to_uninit p).morph y in
  let InitOrUnit x' = v in
  let v_new = uninit_conn_fpu' p x y f v in
  let frame : a = compatible_elim p y (f x') in
  let frame' : uninit_t a = InitOrUnit frame in
  assert (composable (pcm_uninit p) y' frame');
  assert (op (pcm_uninit p) frame' y' == v_new);
  compatible_intro (pcm_uninit p) y' v_new frame';
  assert (forall (frame:_{composable (pcm_uninit p) ((value_to_uninit p).morph x) frame}).
       composable (pcm_uninit p) ((value_to_uninit p).morph y) frame /\
       (op (pcm_uninit p) ((value_to_uninit p).morph x) frame == v ==> op (pcm_uninit p) ((value_to_uninit p).morph y) frame == v_new));
  ()

let uninit_conn_fpu
  (#a: Type)
  (p: pcm a)
  (x: Ghost.erased a { ~ (Ghost.reveal x == one p) })
  (y: Ghost.erased a)
  (f: frame_preserving_upd p x y)
: Tot (frame_preserving_upd (pcm_uninit p) ((value_to_uninit p).morph x) ((value_to_uninit p).morph y))
=
  fun v ->
    uninit_conn_fpu_prop p x y f v;
    uninit_conn_fpu' p x y f v

let uninit_conn
  (#a: Type)
  (p: pcm a)
: Tot (connection (pcm_uninit p) p)
= mkconnection
    (value_to_uninit p)
    (uninit_to_value p)
    ()
    (uninit_conn_fpu p)

let exclusive_uninit
  (#a: Type)
  (p: pcm a)
  (x: uninit_t a)
: Lemma
  (exclusive (pcm_uninit p) x <==> begin match x with
  | Uninitialized -> True
  | InitOrUnit z -> exclusive p z /\ (~ (z == one p))
  end)
= match x with
  | Uninitialized -> ()
  | InitOrUnit z ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (z == one p)
    then begin
      assert (composable (pcm_uninit p) x Uninitialized)
    end else
      let phi2
        frame
      : Lemma
        (requires (exclusive (pcm_uninit p) x /\ composable p z frame))
        (ensures (frame == one p))
        [SMTPat (composable p z frame)]
      = assert (composable (pcm_uninit p) x (InitOrUnit frame))
      in
      ()


let uninit_view
  (#a: Type)
  (#p: pcm a)
  (#b: Type)
  (w: sel_view p b)
: Tot (sel_view #(uninit_t a) (pcm_uninit p) (uninit_t b))
= {
  to_view_prop = (fun x -> match x with
  | Uninitialized -> True
  | InitOrUnit x' -> w.to_view_prop x'
  );
  to_view = (fun x -> match x with
  | Uninitialized -> Uninitialized
  | InitOrUnit x' -> InitOrUnit (w.to_view x')
  );
  to_carrier = (fun v -> match v with
  | Uninitialized -> Uninitialized
  | InitOrUnit v' -> w.to_carrier_not_one v'; InitOrUnit (w.to_carrier v')
  );
  to_carrier_not_one = (fun v -> match v with
  | Uninitialized -> ()
  | InitOrUnit v' -> w.to_carrier_not_one v'
  );
  to_view_frame = (fun v frame -> match v with
  | Uninitialized -> ()
  | InitOrUnit v' -> w.to_carrier_not_one v'; let InitOrUnit frame' = frame in w.to_view_frame v' frame'
  );
}

let uninit_view_initialized
  (#a: Type)
  (#p: pcm a)
  (#b: Type)
  (w: sel_view p b)
: Tot (sel_view #(uninit_t a) (pcm_uninit p) b)
= {
  to_view_prop = (fun x -> match x with
  | Uninitialized -> False
  | InitOrUnit x' -> w.to_view_prop x'
  );
  to_view = (fun x -> match x with
  | InitOrUnit x' -> w.to_view x'
  );
  to_carrier = (fun v' -> w.to_carrier_not_one v'; InitOrUnit (w.to_carrier v'));
  to_carrier_not_one = (fun v -> w.to_carrier_not_one v);
  to_view_frame = (fun v frame ->
    w.to_carrier_not_one v; let InitOrUnit frame' = frame in w.to_view_frame v frame'
  );
}
