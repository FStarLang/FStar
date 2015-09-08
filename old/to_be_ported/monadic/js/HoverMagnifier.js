var oldElt = undefined;
var oldSize = undefined;

function magnify(evt) {
    var elt = evt.target;
    
    if (oldElt) {
        oldElt.style.fontSize = oldSize;
    }
    
    oldElt = elt;
    oldSize = elt.style.fontSize;
    elt.style.fontSize = "30px";
}


var body = document.body; 
if (body)
{ 
    body.onmousemove = function (evt) { magnify(evt); };
    body.onmousemove(dummyEvent)
}

