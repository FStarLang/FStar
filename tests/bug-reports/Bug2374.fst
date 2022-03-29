module Bug2374

type r1 = { a: bool }
type r2 = { a: bool }
let r1_refined = x:r1{x.a == true}

let test_refine_1 (): r1_refined =
  ({a = true})

let test_refine_1_fix (): r1_refined =
  ({a = true} <: r1)

let test_refine_2 (x:r1_refined): bool =
  x.a

let test_refine_2_fix (x:r1_refined): bool =
  (x <: r1).a

//nested refinement
let r1_refined' = x:r1_refined{x.a == true}

let test_refine_1' (): r1_refined' =
  ({a = true})

let test_refine_2' (x:r1_refined'): bool =
  x.a

//nested refinement after reduction
let test_refine_1'' (): ((fun x -> x) r1_refined') =
  ({a = true})

let test_refine_2'' (x:((fun x -> x) r1_refined')): bool =
  x.a
