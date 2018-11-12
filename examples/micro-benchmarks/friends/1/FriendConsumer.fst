module FriendConsumer
friend FriendProvider
let test = assert (FriendProvider.x == 0)
