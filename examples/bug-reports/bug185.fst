module Bug185
assume val data : Type0
let vk = data
let vkey (u:unit) = x:vk{x==x}
val validate: data -> vkey ()
#set-options "--debug Bug185 --debug_level Extreme,Rel --ugly"
let validate chain = chain
