function magnify(elt) {
	/* If the element is *not* a text node... */
	if (elt.nodeType !== 3) {
		elt.style.fontSize = "30px";
	}
}

function iter_elts(elt) {
	var i;

	for (i = 0; i < elt.children.length; i++) {
		magnify(elt.children[i]);
		iter_elts(elt.children[i]);
	}
}

iter_elts(document.body);
