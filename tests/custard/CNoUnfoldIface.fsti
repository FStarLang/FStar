module CNoUnfoldIface

[@@FStar.Attributes.custard_no_unfold]
type word = FStar.UInt32.t

val identity : word -> Tot word
