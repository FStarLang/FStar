module Steel.SLDump

let sldump' #opened p q text sq () =
  change_equal_slprop p (guard_vprop q)

let sldump #opened #p #q text #sq () =
  sldump' #opened p q text sq ()
