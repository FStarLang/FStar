module PatternMatching.Types

open FStar.Tactics

type varname = string
type qn = list string

type pattern =
| PAny: pattern
| PVar: name: varname -> pattern
| PQn: qn: qn -> pattern
| PType: pattern
| PApp: hd: pattern -> arg: pattern -> pattern
