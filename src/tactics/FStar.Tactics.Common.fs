module FStar.Tactics.Common

open FStar.Syntax.Syntax

exception TacticFailure of string
exception EExn of term
