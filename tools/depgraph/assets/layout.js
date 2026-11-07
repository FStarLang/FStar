/* Layered (Sugiyama-style) graph layout used by the F* dependence viewer.
   Self-contained, no dependencies. */
(function (global) {
  'use strict';

  function buildAdj(n, edges) {
    var out = [], inn = [];
    for (var i = 0; i < n; i++) { out.push([]); inn.push([]); }
    for (var e = 0; e < edges.length; e++) {
      var a = edges[e][0], b = edges[e][1];
      if (a === b) continue;
      if (a < 0 || b < 0 || a >= n || b >= n) continue;
      out[a].push(b); inn[b].push(a);
    }
    return { out: out, inn: inn };
  }

  /* Greedy DFS cycle breaking: returns the set of back edges, keyed "a>b". */
  function breakCycles(n, edges) {
    var adj = buildAdj(n, edges).out;
    var color = new Int8Array(n);      // 0 white, 1 grey, 2 black
    var reversed = Object.create(null);
    for (var s = 0; s < n; s++) {
      if (color[s] !== 0) continue;
      var stack = [[s, 0]];
      color[s] = 1;
      while (stack.length) {
        var top = stack[stack.length - 1];
        var v = top[0];
        if (top[1] < adj[v].length) {
          var w = adj[v][top[1]++];
          if (color[w] === 1) reversed[v + '>' + w] = true;
          else if (color[w] === 0) { color[w] = 1; stack.push([w, 0]); }
        } else { color[v] = 2; stack.pop(); }
      }
    }
    return reversed;
  }

  function longestPathLayering(n, out, inn) {
    var indeg = new Int32Array(n);
    for (var i = 0; i < n; i++) indeg[i] = inn[i].length;
    var layer = new Int32Array(n);
    var queue = [], head = 0;
    for (i = 0; i < n; i++) if (indeg[i] === 0) queue.push(i);
    while (head < queue.length) {
      var v = queue[head++];
      for (var k = 0; k < out[v].length; k++) {
        var w = out[v][k];
        if (layer[w] < layer[v] + 1) layer[w] = layer[v] + 1;
        if (--indeg[w] === 0) queue.push(w);
      }
    }
    return layer;
  }

  function median(vals) {
    if (vals.length === 0) return -1;
    vals.sort(function (a, b) { return a - b; });
    var m = vals.length >> 1;
    if (vals.length % 2) return vals[m];
    return (vals[m - 1] + vals[m]) / 2;
  }

  /* nodes: [{w,h}], edges: [[from,to]] */
  function layout(nodes, edges, opts) {
    opts = opts || {};
    var layerGap = opts.layerGap || 84;
    var nodeGap = opts.nodeGap || 16;
    var n = nodes.length;
    if (n === 0) return { nodes: [], edges: [], width: 10, height: 10, layers: 0 };

    var reversed = breakCycles(n, edges);
    var acyc = [], isRev = [];
    for (var e = 0; e < edges.length; e++) {
      var a = edges[e][0], b = edges[e][1];
      if (a === b || a < 0 || b < 0 || a >= n || b >= n) { acyc.push(null); isRev.push(false); continue; }
      if (reversed[a + '>' + b]) { acyc.push([b, a]); isRev.push(true); }
      else { acyc.push([a, b]); isRev.push(false); }
    }
    var clean = [];
    for (e = 0; e < acyc.length; e++) if (acyc[e]) clean.push(acyc[e]);
    var adj = buildAdj(n, clean);
    var layer = longestPathLayering(n, adj.out, adj.inn);

    var nLayers = 1;
    for (var i = 0; i < n; i++) nLayers = Math.max(nLayers, layer[i] + 1);

    /* virtual nodes so that long edges route between layers */
    var vLayers = [];
    var chains = [];
    var totalV = 0;
    var maxVirtual = opts.maxVirtual === undefined ? 60000 : opts.maxVirtual;
    for (e = 0; e < acyc.length; e++) {
      if (acyc[e] === null) { chains.push(null); continue; }
      var s = acyc[e][0], t = acyc[e][1];
      var ls = layer[s], lt = layer[t];
      var chain = [s];
      if (lt - ls > 1 && totalV < maxVirtual) {
        for (var L = ls + 1; L < lt; L++) {
          vLayers.push(L);
          chain.push(n + vLayers.length - 1);
          totalV++;
        }
      }
      chain.push(t);
      chains.push(chain);
    }

    var N = n + vLayers.length;
    var lay = new Int32Array(N);
    for (i = 0; i < n; i++) lay[i] = layer[i];
    for (i = 0; i < vLayers.length; i++) lay[n + i] = vLayers[i];

    var sout = [], sinn = [];
    for (i = 0; i < N; i++) { sout.push([]); sinn.push([]); }
    for (e = 0; e < chains.length; e++) {
      var ch = chains[e];
      if (!ch) continue;
      for (var c = 0; c + 1 < ch.length; c++) {
        sout[ch[c]].push(ch[c + 1]);
        sinn[ch[c + 1]].push(ch[c]);
      }
    }

    var layersArr = [];
    for (i = 0; i < nLayers; i++) layersArr.push([]);
    for (i = 0; i < N; i++) layersArr[lay[i]].push(i);
    var pos = new Float64Array(N);
    for (var L2 = 0; L2 < nLayers; L2++)
      for (var j = 0; j < layersArr[L2].length; j++) pos[layersArr[L2][j]] = j;

    var sweeps = N > 6000 ? 2 : (N > 1200 ? 4 : 8);
    var key = new Float64Array(N);
    for (var it = 0; it < sweeps; it++) {
      var down = (it % 2 === 0);
      var step = down ? 1 : -1;
      var start = down ? 1 : nLayers - 2;
      for (var L3 = start; down ? L3 < nLayers : L3 >= 0; L3 += step) {
        var lst = layersArr[L3];
        for (j = 0; j < lst.length; j++) {
          var v = lst[j];
          var nb = down ? sinn[v] : sout[v];
          var vals = [];
          for (var q = 0; q < nb.length; q++) vals.push(pos[nb[q]]);
          var md = median(vals);
          key[v] = md < 0 ? pos[v] : md;
        }
        lst.sort(function (a, b) { return key[a] - key[b] || pos[a] - pos[b]; });
        for (j = 0; j < lst.length; j++) pos[lst[j]] = j;
      }
    }

    var w = new Float64Array(N), h = new Float64Array(N);
    for (i = 0; i < n; i++) { w[i] = nodes[i].w || 90; h[i] = nodes[i].h || 26; }
    for (i = n; i < N; i++) { w[i] = 1; h[i] = 12; }

    var x = new Float64Array(N);
    for (L2 = 0; L2 < nLayers; L2++) {
      var cur = 0, lst2 = layersArr[L2];
      lst2.sort(function (a, b) { return pos[a] - pos[b]; });
      for (j = 0; j < lst2.length; j++) {
        var v2 = lst2[j];
        x[v2] = cur + w[v2] / 2;
        cur += w[v2] + nodeGap;
      }
    }

    for (it = 0; it < 6; it++) {
      var dn = (it % 2 === 0);
      for (L3 = 0; L3 < nLayers; L3++) {
        var lidx = dn ? L3 : nLayers - 1 - L3;
        var lst3 = layersArr[lidx];
        for (j = 0; j < lst3.length; j++) {
          var vv = lst3[j];
          var nbs = dn ? sinn[vv] : sout[vv];
          if (nbs.length === 0) continue;
          var xs = [];
          for (q = 0; q < nbs.length; q++) xs.push(x[nbs[q]]);
          var mx = median(xs);
          if (mx >= 0) x[vv] = (x[vv] + mx) / 2;
        }
        for (j = 1; j < lst3.length; j++) {
          var p = lst3[j - 1], cu = lst3[j];
          var minx = x[p] + w[p] / 2 + nodeGap + w[cu] / 2;
          if (x[cu] < minx) x[cu] = minx;
        }
        for (j = lst3.length - 2; j >= 0; j--) {
          var nx = lst3[j + 1], cu2 = lst3[j];
          var maxx = x[nx] - w[nx] / 2 - nodeGap - w[cu2] / 2;
          if (x[cu2] > maxx) x[cu2] = maxx;
        }
      }
    }

    var layerH = new Float64Array(nLayers);
    for (i = 0; i < N; i++) layerH[lay[i]] = Math.max(layerH[lay[i]], h[i]);
    var y = new Float64Array(N);
    var yy = 20, layerY = new Float64Array(nLayers);
    for (L2 = 0; L2 < nLayers; L2++) { layerY[L2] = yy + layerH[L2] / 2; yy += layerH[L2] + layerGap; }
    for (i = 0; i < N; i++) y[i] = layerY[lay[i]];

    var minX = Infinity, maxX = -Infinity;
    for (i = 0; i < N; i++) { minX = Math.min(minX, x[i] - w[i] / 2); maxX = Math.max(maxX, x[i] + w[i] / 2); }
    if (!isFinite(minX)) { minX = 0; maxX = 1; }
    for (i = 0; i < N; i++) x[i] -= minX - 20;

    var resNodes = [];
    for (i = 0; i < n; i++) resNodes.push({ x: x[i], y: y[i], w: w[i], h: h[i], layer: lay[i] });

    var resEdges = [];
    for (e = 0; e < chains.length; e++) {
      var ch2 = chains[e];
      if (!ch2) { resEdges.push(null); continue; }
      var pts = [];
      for (c = 0; c < ch2.length; c++) pts.push([x[ch2[c]], y[ch2[c]]]);
      resEdges.push({ points: pts, reversed: isRev[e] });
    }

    return {
      nodes: resNodes,
      edges: resEdges,
      width: maxX - minX + 40,
      height: yy + 20,
      layers: nLayers
    };
  }

  global.Layout = { layout: layout };
})(typeof window !== 'undefined' ? window : this);
