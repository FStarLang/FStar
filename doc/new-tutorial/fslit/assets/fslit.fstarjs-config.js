/* global $ FSLit FStar __FSTAR_JS_CURRENT_FST_FILE_NAME__ */
$(function() {
    FStar.CLI.WORKER_DIRECTORY = "_static/fstar.js/";
    FStar.IDE.WORKER_DIRECTORY = "_static/fstar.js/";

    if (typeof WebAssembly === "object") {
        // Only switch to the local CLI if we can actually run it
        FSLit.StandaloneClient = FStar.CLI.Client;
    }

    // Always switch to the local IDE (we don't have a remote alternative)
    FStar.IDE.LiterateClient.run(__FSTAR_JS_CURRENT_FST_FILE_NAME__);
});
