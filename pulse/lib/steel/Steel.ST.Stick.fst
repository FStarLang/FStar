module Steel.ST.Stick

let stick_elim_t
  (hyp concl: vprop)
  (v: vprop)
: Tot Type
= (opened: inames) -> STGhostT unit opened (v `star` hyp) (fun _ -> concl)

let is_stick
  (hyp concl: vprop)
  (v: vprop)
: GTot prop
= squash (stick_elim_t hyp concl v)

let stick
  (hyp concl: vprop)
: Tot vprop
= exists_ (fun (v: vprop) ->
    v `star` pure (is_stick hyp concl v)
  )

#set-options "--ide_id_info_off"

let stick_unfold
  (#opened: _)
  (hyp concl: vprop)
: STGhost vprop opened
    (hyp `stick` concl)
    (fun v -> v)
    True
    (fun v -> is_stick hyp concl v)
= let v = elim_exists () in
  let _ = elim_pure _ in
  v

let stick_apply
  (#opened: _)
  (v hyp concl: vprop)
: STGhost unit opened
    (v `star` hyp)
    (fun _ -> concl)
    (is_stick hyp concl v)
    (fun _ -> True)
= let sq : squash (is_stick hyp concl v) = () in
  let _ : squash (stick_elim_t hyp concl v) = FStar.Squash.join_squash sq in
  let f : Ghost.erased (stick_elim_t hyp concl v) = FStar.IndefiniteDescription.elim_squash #(stick_elim_t hyp concl v) () in
  Ghost.reveal f _

let stick_elim
  (#opened: _)
  (hyp concl: vprop)
: STGhostT unit opened
    ((hyp `stick` concl) `star` hyp)
    (fun _ -> concl)
= let v = stick_unfold hyp concl in
  stick_apply v hyp concl

let stick_fold
  (#opened: _)
  (hyp concl: vprop)
  (v: vprop)
  (f_elim: stick_elim_t hyp concl v)
: STGhostT unit opened
    v
    (fun _ -> hyp `stick` concl)
= intro_pure (squash (stick_elim_t hyp concl v));
  intro_exists v (fun v -> v `star` pure (squash (stick_elim_t hyp concl v)))

let stick_intro = stick_fold
