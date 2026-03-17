module PulseCore.Tags

type tag =
  | GHOST
  | CONCRETE

type mutability =
  | ONLY_GHOST
  | IMMUTABLE
  | MUTABLE