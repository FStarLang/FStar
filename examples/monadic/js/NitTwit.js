var currentDiv = undefined;
var currentPosition = undefined;

function searchResult(response) {
	var results, div, txt, i;

	results = JSON.parse(response)['results'];

	if (results.length > 0) {
		div = document.createElement('div');
		txt = document.createTextNode(results[0].text);
		div.appendChild(txt);
		document.body.appendChild(div);

		div.style.left = currentPosition.x + "px";
		div.style.top = currentPosition.y + "px";
		div.style.position = "absolute";
		div.style.backgroundColor = "white";
		div.style.borderStyle = "solid";
		div.style.borderWidth = "3px";
		div.style.borderColor = "red";
		currentDiv = div;
	}
}

function silence() {
	if (currentDiv) {
		document.body.removeChild(currentDiv);
		currentDiv = undefined;
	}
}

function selectText(e) {
	var selection = document.getSelection();
	var query;

	if (selection == "" || selection == undefined) {
		silence();
	} else {
		query = "http://search.twitter.com/search.json?q=" + selection;
		chrome.extension.sendRequest(query, function(response) {
			silence();
			currentPosition = {x: e.clientX, y: e.clientY};
			searchResult(response);
		});
	}
}

function start() {
		document.body.onclick = selectText;
}

start();
