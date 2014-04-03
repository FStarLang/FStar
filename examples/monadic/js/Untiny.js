chrome.addListener(function(request, sender, callback) {
	var selection;
	if (request.action === 'getSelectedUrl') {
		//selection = window.getSelection().toString();
	    console.log('selection: ' + window.getSelection().toString());
	    callback({ url: window.getSelection().toString() });
	}
});

