var myPapers = "http://research.microsoft.com/en-us/um/people/nswamy/papers/index.html"

function logEntry(entry) {
	console.log('entry:');
	console.log('title: ' + entry._title);
	console.log('authors: ' + entry._authors);
	console.log('venue: ' + entry._venue);
	console.log('url: ' + entry._url);
}

function loadEntries() {
	chrome.extension.sendRequest({method: 'loadEntries'}, function(entries) {
		var i;
		console.log('loading entries...');
		for (i = 0; i < entries.length; i++) {
			logEntry(entries[i]);
		}
	});
}

function storeEntry(entry) {
	chrome.extension.sendRequest(
		{method: 'storeEntry', entry: entry}
	);
}

function clearEntries() {
	console.log('clearing entries');
	chrome.extension.sendRequest(
		{method: 'clearEntries'}
	);
}

function evalAttrs(elt, attrs, result) {
	var attr;
	for (attr in attrs) {
		if (attrs[attr].indexOf('_') == 0) {
			result[attrs[attr]] = elt.getAttribute(attr);
		} else if (elt.getAttribute(attr) != attrs[attr]) {
			return false;
		}
	}

	return true;
}

function evalValue(elt, value, result) {
	if (!elt.textContent) return false;

	if (value.value.indexOf('_') == 0) {
		result[value.value] = elt.textContent;
	} else if (elt.textContent != value.value) {
		return false;
	}

	return true;
}

function evalNode(elt, node, result) {
	var i, tmp;

	if (elt.tagName && elt.tagName.toLowerCase() == node.node.toLowerCase()) {
		if (node.attrs) {
			tmp = {};
			if (!evalAttrs(elt, node.attrs, tmp)) {
				return false;
			}
			mixin(result, tmp);
		}

		if (node.children) {
			if (!evalChildren(elt, node.children, result)) {
				return false;
			}
		}
	} else {
		return false;
	}

	return true;
}

function mixin(obj, add) {
	var p;
	for (p in add) {
		obj[p] = add[p];
	}
}

function evalChildren(elt, pat, result) {
	var i, j, wild = false, tmp, res;

	for (i = 0, j = 0; i < pat.length; i++, j++) {
		if (j >= elt.childNodes.length) {
			return false;
		}

		if (pat[i].node) {
			do {
				tmp = {};
				res = evalNode(elt.childNodes[j], pat[i], tmp);
				j++;
			} while (j < elt.childNodes.length && !res && wild);

			j--;
			if (!res) return false;
			mixin(result, tmp);
			wild = false;
		} else if (pat[i].value) {
			do {
				tmp = {};
				res = evalValue(elt.childNodes[j], pat[i], tmp);
				j++;
			} while (j < elt.childNodes.length && !res && wild);

			j--;
			if (!res) return false;
			mixin(result, tmp);
			wild = false;
		} else if (pat[i].wild && (pat.length - 1 == i)) {
			break;
		} else if (pat[i].wild) {
			--j
			wild = true;
		} else {
			console.log('Unexpected non-node and non-value');
			return false;
		}
	}

	return true;
}

function evalPattern(elt, pat) {
	var result = {};
	if (evalNode(elt, pat, result)) {
		return result;
	} else {
		return undefined;
	}
}

function processOneEntry(elt) {
	var tr = elt;
	var td, node, i, a;
	var j;
	var entry;

	var pat = {
		node: 'tr',
		children: [
			{ wild: true },
			{
			node: 'td',
			children: [
				{ wild: true },
				{ node: 'b', children: [ { value: '_title' } ] },
				{ wild: true },
				{ value: '_authors' },
				{ wild: true },
				{ node: 'i', children: [ { value: '_venue' } ] },
				{ wild: true },
				{ node: 'a', attrs: { 'href': '_url' }, children: [ { value: '.pdf' } ] },
				{ wild: true }
			]}
		]
	};

	entry = evalPattern(tr, pat)
	return entry;
}

function processPage() {
	var tbodies = document.getElementsByTagName('tbody');
	var entries = [];
	var tbody, entry, i;

	if (tbodies.length === 1) {
		clearEntries();

		tbody = tbodies[0];
		for (i = 0; i < tbody.children.length; i++) {
			entry = processOneEntry(tbody.children[i]);
			if (entry !== undefined) {
				entries.push(entry);
			}
		}

		for (i = 0; i < entries.length; i++) {
			storeEntry(entries[i]);
		}
	} else {
		console.log("unexpected more than one body");
	}
}

function start() {
	if (myPapers == document.location) {
		processPage();
		loadEntries();
	} else {
		console.log("NiksBib ignoring doc at " + document.location);
	}
}

start();
