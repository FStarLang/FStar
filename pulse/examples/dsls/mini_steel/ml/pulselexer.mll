{
open Pulseparser
}

rule token =
  parse
  | "true"    { TRUE }
