module BugRecordPoly

type record_ab 'a 'b = { a: 'a; b: 'b }
type record_ac 'a 'b = { a: 'a; b: 'b }

type record_r1 'rab = { r1_ab: 'rab }
type record_r2 'rab = { r2_ab: 'rab }

assume val rec1: record_r1 (record_ab string int)

let rec2: record_r2 (record_ab string int) = {
    r2_ab =
      { rec1.r1_ab  with a = "AA" }
}
