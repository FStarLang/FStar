module FriendConsumer
friend FriendProvider
let test = assert (FriendProvider.x + Other.y == 1)
