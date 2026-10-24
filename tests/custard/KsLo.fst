module KsLo

module U32 = FStar.UInt32

type point = { px : U32.t; py : U32.t }

let flip (p : point) : point = { px = p.py; py = p.px }
