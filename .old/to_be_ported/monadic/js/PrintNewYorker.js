function toPrintUrl(elt) {
	var url = elt.getAttribute('href');
	var start, end;
	var host;

	if (url) {
	    if (url.indexOf('/') == 0 ||
		url.indexOf('http://www.newyorker.com') == 0 ||
		url.indexOf('http://newyorker.com') == 0) {
	        url = url + '?printable=true';
	        elt.setAttribute('href', url);
	    }	
	}

	
}

function printUrls(anchors) {
	for (anchor in anchors) {
		toPrintUrl(anchors[anchor]);
	}
}

if (document.domain === 'newyorker.com') {
	printUrls(document.getElementsByTagName('a'));
}
