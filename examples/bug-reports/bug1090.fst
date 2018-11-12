module Bug1090

type idx (n:nat) =
  | Idx0 : idx 0
  | Inc : m:nat -> idx m -> idx (m+1)
