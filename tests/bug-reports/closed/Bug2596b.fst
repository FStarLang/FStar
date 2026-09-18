module Bug2596b

open FStar.Tactics.V2

assume val p: int -> int -> prop

/// Generates a lemma with signature `val lem (x y:int) : Lemma (p x y) [SMTPat (p x y)]`
let gen_lemma () : Tac decls =
  let lemma_name = List.Tot.snoc (moduleof (top_env ()), "lemGGGGGGGGGG") in
  let x_binder = fresh_binder_named "x" (`int) in
  let x_term = binder_to_term x_binder in
  let y_binder = fresh_binder_named "y" (`int) in
  let y_term = binder_to_term y_binder in

  let all_binders = [x_binder; y_binder] in

  let lemma_smtpat = (`[smt_pat (p (`#x_term) (`#y_term))]) in
  (* A [Lemma] is an abbreviation of [Tot unit]; its postcondition is a
     refinement of the result type -- here a [squash], since the result is
     [unit] and the postcondition does not mention it.

     [source_effect_name] is presentation only, so this deliberately leaves it
     at [Tot] rather than [FStar.Pervasives.Lemma]: what makes the SMT encoding
     turn this [val] into an axiom is the [SMTPAT] flag, not the abbreviation
     the user would have written.  See [Syntax.Util.is_smt_lemma]. *)
  let lemma_post = (`(squash (p (`#x_term) (`#y_term)))) in
  let lemma_comp = (pack_comp ({ effect_name = tot_effect_name
                               ; result_typ = lemma_post
                               ; flags = [SMTPAT lemma_smtpat]
                               ; source_effect_name = tot_effect_name })) in
  let lemma_type = mk_arr all_binders lemma_comp in

  let lemma_val = mk_abs all_binders (`(admit())) in

  let lemma_letbinding = ({
    lb_fv = pack_fv lemma_name;
    lb_us = [];
    lb_typ = lemma_type;
    lb_def = lemma_val;
  }) in
  [pack_sigelt (Sg_Let {isrec=false; lbs=[lemma_letbinding]})]

%splice [] (gen_lemma ())

let f (x y:int) : Lemma (p x y) = ()
