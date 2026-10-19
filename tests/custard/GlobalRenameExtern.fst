module GlobalRenameExtern

[@@FStar.Attributes.rename_let "requested"; FStar.Attributes.custard_extern "foreign"]
assume val step : FStar.UInt32.t -> Tot FStar.UInt32.t

let main () = step 0ul
