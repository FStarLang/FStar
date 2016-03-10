var saved_elt={value:undefined};

function captureText(elt, callback) {
    if (elt.tagName === 'INPUT') {
	saved_elt = elt;
	callback({ text: elt.value });
    } else {
	console.log('Wrong kind of text, man');
    }
}

function pasteText(text) {
    if (saved_elt) {
	saved_elt.value = text;
    } else {
        console.log('nowhere to paste');
    }
}


chrome.addListener(function(request, sender, callback) {
    if (request.command === 'captureText') {
	captureText(document.activeElement, callback);
    } else if (request.command === 'pasteText') {
	pasteText(request.text);
    }
});

