open Prims
let (match_syntactic :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      (unit Pulse_Checker_Prover_Base.prover_state, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  Pulse_Checker_Prover_Match_Comb.match_with "SYNTACTIC"
    Pulse_Checker_Prover_Match_Matchers.match_syntactic_11
let (match_fastunif :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      (unit Pulse_Checker_Prover_Base.prover_state, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  Pulse_Checker_Prover_Match_Comb.match_with "FASTUNIF"
    Pulse_Checker_Prover_Match_Matchers.match_fastunif_11
let (match_fastunif_i :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      (unit Pulse_Checker_Prover_Base.prover_state, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  Pulse_Checker_Prover_Match_Comb.match_with "FASTUNIF_INST"
    Pulse_Checker_Prover_Match_Matchers.match_fastunif_inst_11
let (match_full :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      (unit Pulse_Checker_Prover_Base.prover_state, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  Pulse_Checker_Prover_Match_Comb.match_with "FULL"
    Pulse_Checker_Prover_Match_Matchers.match_full_11