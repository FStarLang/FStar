function cons(a, rest) {
    return {hd:a, tl:rest}
}

function getPath(cur, path) {
    while(path !== undefined && 
          cur !== undefined) 
    {
        cur = cur.getChild(path.hd); 
        path = path.tl;
    }
    return cur;
}

function findName() { 
    var elts = document.getElementsByTagName('title');
    var elt = elts.Next();
    if (elt) {
        return elt.text;
    }
}

function getWebsite(node1) {
    if (node1)
    {
        var node = node1.getChild(0);  
        if (node) 
        {
            if ((node.nodeType === 3 &&   
                 node.nodeValue === "Website")) 
            { 
                var node11 = node;
                var node2 = node11.getParent();
                var path = cons(1, cons(0, cons(0, cons(0, undefined))));
                var node3 = getPath(node2, path);
                if (node3) {
                    return node3.getAttribute('href');
                }
            }
        }
    }
}

function findWebsiteHelp(elts) {
    var elt = elts.Next();
    var result = undefined;
    while(elt !== undefined && result === undefined) {
        result = getWebsite(elt);
        elt = elts.Next();
    }
    return result;
}
    
function findWebsite() { 
    return findWebsiteHelp(document.getElementsByClassName("label"));
}

function saveWebsite(friend, href) {
    consoleLog('saving website...');
    // request = new XMLHttpRequest();
    // request.open("GET", "https://api.del.icio.us/v1/posts/add?url=" + href + "&description=" + friend);
    // request.send();
}

function start() {
    var friendName, href;
    
    if (document.domain === 'facebook.com') { 
	friendName = findName();
	href = findWebsite();
	if (href) {
	    consoleLog("Website on " + href);
	    consoleLog("Name is " + friendName);
	    saveWebsite(friendName, href);
	} 
        else {
	    console.log(friendName + " does not have a website");
	}
    }
}

start();
