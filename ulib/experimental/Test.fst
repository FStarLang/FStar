module Test

// Repro for failure due to layered effects.
// If the two open directives are swapped, the file typechecks

// Old one
open Steel.EffectX
// Framing Tactic
open Steel.Effect
