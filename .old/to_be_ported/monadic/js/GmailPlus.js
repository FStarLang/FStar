function redirMailTo(anchors) {
	var i, elt, mailto_index, replaced;
	for (i = 0; i < anchors.length; i++) {
		elt = anchors[i];
		if (elt.getAttribute('href')) {
			mailto_index = elt.getAttribute('href').search('mailto:');
			if (mailto_index != -1) {
				replaced = elt.getAttribute('href').replace('mailto:',
					'https://mail.google.com/mail/?view=cm&fs=1&tf=1&to=');
				elt.setAttribute('href', replaced);
				elt.setAttribute('target', '_blank');
			}
		}
	}
};

chrome.extension.sendRequest({command: "getURL"}, function(response) {
	redirMailTo(document.getElementsByTagName('a'));
});
