chrome.addListener(
	function (request, sender, sendResponse) {
	    if (sender.tab != null) {
	        if (request.id == "pageDetails") {
	            console.log('making note: ' + window.getSelection().toString());
	            sendResponse({
	                notes: window.getSelection().toString()
	            });
	        }
	    }
	}
);

