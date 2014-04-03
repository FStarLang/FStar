function recoverPassword(password) {
	var p;

	p = document.getElementById('password');
	if (p) {
		p.value = password;
	}
}

function start() {
	var p, pwrd;

	p = document.getElementById('password');
	if (p) {
		p.Onblur = function () {
			pwrd = p.value
			chrome.sendRequest1({method: "setPassword", domain: document.domain, password: pwrd});
		};
	}
}


chrome.sendRequest2({ method: 'getPassword', domain: document.domain }, function (response) {
	if (response.password) {
		recoverPassword(response.password);
	}
	start();
});

