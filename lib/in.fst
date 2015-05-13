#push
module Test
let x = 0
end
#pop

#push
module Test
let x = 1
let y = assert (0=1)
end
#pop

#push
module Test
let x = 1
let y = assert (0=0)
end
#pop

#finish
