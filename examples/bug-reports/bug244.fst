module Bug244

let strcat s1 s2 = s1 ^ s2
let strcat3 s1 s2 s3 = strcat s1 (strcat s2 s3)
