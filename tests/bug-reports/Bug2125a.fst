module Bug2125a

assume
val intro (#a:_) (#p:_) (l : list (list a))
  : Pure (list (m:list a{p}))
         (requires p)
         (ensures (fun _ -> True))

assume
val outro (#a:_) (#p:_) (l : list (m:list a{p}))
  : list (list a)

[@@expect_failure [66]]
let test () =
  outro (intro [[]])
