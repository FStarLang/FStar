window.onload = function(e) {
    require(["ace/ace", "ace/ext/static_highlight"], function(ace) {
        var highlight = ace.require("ace/ext/static_highlight");
        document.querySelectorAll("code").forEach(function (codeEl) {
            highlight(codeEl, {
                mode: "ace/mode/fstar",
                trim: true
            }, function (highlighted) {});
        });
    });
};
