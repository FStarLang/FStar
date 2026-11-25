/* F* dependence viewer.
   Data is delivered by generated <script> files calling DG.setXxx, which keeps
   the whole package usable straight from the file:// scheme. */
var DG = (function () {
  'use strict';

  var IDX = null;
  var MOD = {};                 // modId -> module payload
  var SRC = {};                 // srcId -> source text
  var SEARCH = null;
  var UNUSED = null;
  var waiters = {};             // url -> [cb]
  var loaded = {};

  /* ------------------------------------------------------------------ */
  /* data loading                                                        */
  /* ------------------------------------------------------------------ */

  function loadScript(url, cb) {
    if (loaded[url]) { cb(); return; }
    if (waiters[url]) { waiters[url].push(cb); return; }
    waiters[url] = [cb];
    var s = document.createElement('script');
    s.src = url;
    s.onload = function () {
      loaded[url] = true;
      var ws = waiters[url]; waiters[url] = null;
      ws.forEach(function (f) { f(); });
    };
    s.onerror = function () {
      loaded[url] = true;
      var ws = waiters[url]; waiters[url] = null;
      console.warn('failed to load', url);
      ws.forEach(function (f) { f(); });
    };
    document.head.appendChild(s);
  }

  function needModule(id, cb) {
    if (MOD[id]) { cb(MOD[id]); return; }
    loadScript('data/m/' + id + '.js', function () { cb(MOD[id] || { defs: [], e: [], o: [], in: [] }); });
  }
  function needModules(ids, cb) {
    var left = ids.length;
    if (!left) return cb();
    ids.forEach(function (i) { needModule(i, function () { if (--left === 0) cb(); }); });
  }
  function needSource(id, cb) {
    if (id < 0) { cb(null); return; }
    if (SRC[id] !== undefined) { cb(SRC[id]); return; }
    loadScript('data/s/' + id + '.js', function () { cb(SRC[id] === undefined ? null : SRC[id]); });
  }
  function needSearch(cb) { if (SEARCH) return cb(SEARCH); loadScript('data/search.js', function () { cb(SEARCH || []); }); }
  function needUnused(cb) { if (UNUSED) return cb(UNUSED); loadScript('data/unused.js', function () { cb(UNUSED || { dead: [], implicit: [] }); }); }

  /* ------------------------------------------------------------------ */
  /* namespace tree over module names                                    */
  /* ------------------------------------------------------------------ */

  var NS = null;   // prefix -> {subs:{name->prefix}, mods:[modId], count}

  function buildNS() {
    NS = {};
    function node(p) { if (!NS[p]) NS[p] = { subs: {}, mods: [], count: 0 }; return NS[p]; }
    node('');
    IDX.mods.forEach(function (m, i) {
      var parts = m.n.split('.');
      var pref = '';
      for (var k = 0; k < parts.length; k++) {
        var parent = pref;
        pref = pref === '' ? parts[k] : pref + '.' + parts[k];
        node(parent).subs[parts[k]] = pref;
        node(pref);
        node(parent).count++;
      }
      node(pref).mods.push(i);
      node(pref).isModule = true;
    });
    // recompute counts as number of modules in the subtree
    Object.keys(NS).forEach(function (p) { NS[p].count = 0; });
    IDX.mods.forEach(function (m) {
      var parts = m.n.split('.'), pref = '';
      NS[''].count++;
      for (var k = 0; k < parts.length; k++) {
        pref = pref === '' ? parts[k] : pref + '.' + parts[k];
        if (NS[pref]) NS[pref].count++;
      }
    });
  }

  function nsOf(modName, prefix) {
    // the child of `prefix` that contains modName, or null
    if (prefix !== '' && modName.indexOf(prefix + '.') !== 0 && modName !== prefix) return null;
    var rest = prefix === '' ? modName : modName.slice(prefix.length + 1);
    if (rest === '') return prefix;
    var head = rest.split('.')[0];
    return prefix === '' ? head : prefix + '.' + head;
  }

  /* ------------------------------------------------------------------ */
  /* view state                                                          */
  /* ------------------------------------------------------------------ */

  var state = { kind: 'ns', ns: '', mod: -1, def: -1, depth: 1 };
  var opts = { hideUnused: false, hideGenerated: true };
  var view = null;      // current rendered graph {nodes, edges, meta}
  var cam = { x: 0, y: 0, k: 1 };

  var $ = function (id) { return document.getElementById(id); };
  function el(tag, attrs, kids) {
    var e = document.createElementNS('http://www.w3.org/2000/svg', tag);
    if (attrs) for (var k in attrs) e.setAttribute(k, attrs[k]);
    if (kids) kids.forEach(function (c) { e.appendChild(c); });
    return e;
  }
  function h(tag, attrs, kids) {
    var e = document.createElement(tag);
    if (attrs) for (var k in attrs) {
      if (k === 'text') e.textContent = attrs[k];
      else if (k === 'html') e.innerHTML = attrs[k];
      else if (k === 'cls') e.className = attrs[k];
      else if (k.slice(0, 2) === 'on') e[k] = attrs[k];
      else e.setAttribute(k, attrs[k]);
    }
    if (kids) kids.forEach(function (c) { if (c) e.appendChild(c); });
    return e;
  }
  function esc(s) { return String(s).replace(/[&<>"]/g, function (c) { return ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' })[c]; }); }

  /* ------------------------------------------------------------------ */
  /* graph construction per view                                         */
  /* ------------------------------------------------------------------ */

  function textWidth(s, size) { return Math.max(40, s.length * size * 0.58 + 18); }

  /* Namespace / module overview. */
  function buildNsView(prefix) {
    var groups = {};        // childPrefix -> {name, mods:[], isMod}
    IDX.mods.forEach(function (m, i) {
      var c = nsOf(m.n, prefix);
      if (c === null) return;
      if (!groups[c]) groups[c] = { pref: c, mods: [] };
      groups[c].mods.push(i);
    });
    var keys = Object.keys(groups).sort();
    var idxOf = {}, nodes = [];
    keys.forEach(function (k, i) {
      var g = groups[k];
      var isMod = g.mods.length === 1 && IDX.mods[g.mods[0]].n === k;
      var label = prefix === '' ? k : k.slice(prefix.length + 1);
      var dead = 0, defs = 0, isRoot = false;
      g.mods.forEach(function (mi) { dead += IDX.mods[mi].nu; defs += IDX.mods[mi].nd; if (IDX.mods[mi].r) isRoot = true; });
      idxOf[k] = i;
      nodes.push({
        key: k, label: label, isMod: isMod, mods: g.mods,
        sub: isMod ? (defs + ' defs' + (dead ? ', ' + dead + ' unused' : ''))
                   : (g.mods.length + ' modules, ' + defs + ' defs' + (dead ? ', ' + dead + ' unused' : '')),
        root: isRoot, dead: dead, defs: defs,
        w: textWidth(label, 12), h: 34
      });
    });
    var emap = {};
    IDX.medges.forEach(function (e) {
      var a = nsOf(IDX.mods[e[0]].n, prefix), b = nsOf(IDX.mods[e[1]].n, prefix);
      if (a === null || b === null || a === b) return;
      var k = idxOf[a] + ',' + idxOf[b];
      emap[k] = (emap[k] || 0) + e[2];
    });
    var edges = [];
    Object.keys(emap).forEach(function (k) {
      var p = k.split(',');
      edges.push([+p[0], +p[1], emap[k]]);
    });
    return { kind: 'ns', prefix: prefix, nodes: nodes, edges: edges };
  }

  function defVisible(d) {
    if (opts.hideGenerated && d.g) return false;
    if (opts.hideUnused && d.u === 0) return false;
    return true;
  }

  /* Definitions inside one module. */
  function buildModView(mid, md) {
    var keep = [], map = {};
    md.defs.forEach(function (d, i) {
      if (opts.hideGenerated && d.g) return;
      if (opts.hideUnused && d.u === 0) return;
      map[i] = keep.length;
      keep.push(i);
    });
    var nodes = keep.map(function (i) {
      var d = md.defs[i];
      return {
        key: 'd:' + mid + ':' + i, defIdx: i, mid: mid,
        label: d.n, sub: d.k, kindClass: d.u === 1 ? 'dead' : (d.u === 2 ? 'implicit' : ''),
        w: textWidth(d.n, 12), h: 32, def: d
      };
    });
    var edges = [];
    md.e.forEach(function (e) {
      if (map[e[0]] === undefined || map[e[1]] === undefined) return;
      edges.push([map[e[0]], map[e[1]], 1]);
    });
    // aggregate cross-module edges into boundary nodes
    var outMods = {}, inMods = {};
    md.o.forEach(function (t) { if (map[t[0]] !== undefined) (outMods[t[1]] = outMods[t[1]] || []).push(map[t[0]]); });
    md.in.forEach(function (t) { if (map[t[2]] !== undefined) (inMods[t[0]] = inMods[t[0]] || []).push(map[t[2]]); });
    Object.keys(inMods).forEach(function (om) {
      var mi = +om;
      var name = IDX.mods[mi].n;
      var id = nodes.length;
      nodes.push({ key: 'ext-in:' + mi, ext: true, extMod: mi, label: name, sub: 'caller module',
                   w: textWidth(name, 11), h: 28 });
      var seen = {};
      inMods[om].forEach(function (j) { if (!seen[j]) { seen[j] = 1; edges.push([id, j, 1]); } });
    });
    Object.keys(outMods).forEach(function (om) {
      var mi = +om;
      var name = IDX.mods[mi].n;
      var id = nodes.length;
      nodes.push({ key: 'ext-out:' + mi, ext: true, extMod: mi, label: name, sub: 'callee module',
                   w: textWidth(name, 11), h: 28 });
      var seen = {};
      outMods[om].forEach(function (j) { if (!seen[j]) { seen[j] = 1; edges.push([j, id, 1]); } });
    });
    return { kind: 'mod', mid: mid, nodes: nodes, edges: edges, map: map };
  }

  /* Ego network around one definition, across module boundaries. */
  var DEF_VIEW_BUDGET = 250;

  function buildDefView(mid, didx, depth, cb) {
    var want = {};                       // "mid:didx" -> true
    var frontier = [[mid, didx]];
    var levels = {};
    levels[mid + ':' + didx] = 0;
    var count = 1, truncated = 0;

    function keyOf(m, d) { return m + ':' + d; }

    function expand(round, done) {
      if (round > depth || !frontier.length) return done();
      var pend = frontier;
      frontier = [];
      var mids = {};
      pend.forEach(function (p) { mids[p[0]] = true; });
      needModules(Object.keys(mids).map(Number), function () {
        pend.forEach(function (p) {
          var m = p[0], d = p[1], md = MOD[m];
          if (!md) return;
          want[keyOf(m, d)] = true;
          md.e.forEach(function (e) {
            if (e[0] === d) push(m, e[1], round);
            if (e[1] === d) push(m, e[0], round);
          });
          md.o.forEach(function (t) { if (t[0] === d) push(t[1], t[2], round); });
          md.in.forEach(function (t) { if (t[2] === d) push(t[0], t[1], round); });
        });
        expand(round + 1, done);
      });
      function push(m, d, round) {
        var k = keyOf(m, d);
        if (levels[k] !== undefined) return;
        if (count >= DEF_VIEW_BUDGET) { truncated++; return; }
        count++;
        levels[k] = round;
        frontier.push([m, d]);
      }
    }

    expand(1, function () {
      Object.keys(levels).forEach(function (k) { want[k] = true; });
      var mids = {};
      Object.keys(want).forEach(function (k) { mids[+k.split(':')[0]] = true; });
      needModules(Object.keys(mids).map(Number), function () {
        var idxOf = {}, nodes = [];
        Object.keys(want).forEach(function (k) {
          var p = k.split(':'), m = +p[0], d = +p[1];
          var md = MOD[m]; if (!md || !md.defs[d]) return;
          var def = md.defs[d];
          idxOf[k] = nodes.length;
          var lbl = (m === mid) ? def.n : IDX.mods[m].n.split('.').pop() + '.' + def.n;
          nodes.push({ key: 'd:' + m + ':' + d, defIdx: d, mid: m, label: lbl, def: def,
                       sub: (m === mid ? def.k : IDX.mods[m].n),
                       kindClass: def.u === 1 ? 'dead' : (def.u === 2 ? 'implicit' : ''),
                       focus: (m === mid && d === didx),
                       w: textWidth(lbl, 12), h: 32 });
        });
        var edges = [], seen = {};
        function addEdge(am, ad, bm, bd) {
          var a = idxOf[keyOf(am, ad)], b = idxOf[keyOf(bm, bd)];
          if (a === undefined || b === undefined || a === b) return;
          var k = a + ',' + b; if (seen[k]) return; seen[k] = 1;
          edges.push([a, b, 1]);
        }
        Object.keys(mids).map(Number).forEach(function (m) {
          var md = MOD[m]; if (!md) return;
          md.e.forEach(function (e) { addEdge(m, e[0], m, e[1]); });
          md.o.forEach(function (t) { addEdge(m, t[0], t[1], t[2]); });
        });
        cb({ kind: 'def', mid: mid, didx: didx, nodes: nodes, edges: edges, idxOf: idxOf,
             truncated: truncated });
      });
    });
  }

  /* ------------------------------------------------------------------ */
  /* rendering                                                           */
  /* ------------------------------------------------------------------ */

  var selected = null;

  function render(v) {
    view = v;
    var gN = $('nodes'), gE = $('edges');
    gN.textContent = ''; gE.textContent = '';
    $('empty').classList.toggle('hidden', v.nodes.length > 0);
    $('graphinfo').textContent = v.nodes.length + ' nodes, ' + v.edges.length + ' edges' +
      (v.truncated ? ' \u2014 truncated at ' + v.nodes.length + ' nodes; lower the depth or use the module view' : '');

    var lay = Layout.layout(v.nodes, v.edges, { layerGap: v.kind === 'ns' ? 90 : 74, nodeGap: 18 });
    v.layout = lay;

    var frag = document.createDocumentFragment();
    lay.edges.forEach(function (e, i) {
      if (!e) return;
      var p = e.points, d = '';
      for (var k = 0; k + 1 < p.length; k++) {
        var a = p[k], b = p[k + 1];
        var ay = k === 0 ? a[1] + v.nodes[v.edges[i][0]].h / 2 : a[1];
        var by = (k + 2 === p.length) ? b[1] - v.nodes[v.edges[i][1]].h / 2 : b[1];
        if (k === 0) d += 'M ' + a[0].toFixed(1) + ' ' + ay.toFixed(1);
        var my = (ay + by) / 2;
        d += ' C ' + a[0].toFixed(1) + ' ' + my.toFixed(1) + ', ' + b[0].toFixed(1) + ' ' + my.toFixed(1) +
             ', ' + b[0].toFixed(1) + ' ' + by.toFixed(1);
      }
      var path = el('path', { d: d });
      path.__e = i;
      frag.appendChild(path);
    });
    gE.appendChild(frag);

    frag = document.createDocumentFragment();
    v.nodes.forEach(function (nd, i) {
      var p = lay.nodes[i];
      var cls = 'node';
      if (nd.ext) cls += ' kind-external';
      if (nd.root) cls += ' kind-root';
      if (!nd.isMod && v.kind === 'ns' && !nd.ext) cls += ' kind-cluster';
      if (nd.kindClass) cls += ' ' + nd.kindClass;
      if (nd.focus) cls += ' sel';
      var g = el('g', { class: cls, transform: 'translate(' + (p.x - p.w / 2).toFixed(1) + ',' + (p.y - p.h / 2).toFixed(1) + ')' });
      g.appendChild(el('rect', { width: p.w, height: p.h }));
      var t = el('text', { x: 9, y: nd.sub ? p.h / 2 - 5 : p.h / 2 });
      t.textContent = nd.label;
      g.appendChild(t);
      if (nd.sub) {
        var t2 = el('text', { x: 9, y: p.h / 2 + 8, class: 'sub' });
        t2.textContent = nd.sub;
        g.appendChild(t2);
      }
      g.__i = i;
      frag.appendChild(g);
    });
    gN.appendChild(frag);

    fit();
    if (selected !== null && selected < v.nodes.length) highlight(selected);
  }

  function applyCam() {
    $('viewport').setAttribute('transform',
      'translate(' + cam.x.toFixed(2) + ',' + cam.y.toFixed(2) + ') scale(' + cam.k.toFixed(4) + ')');
    var lod = cam.k < 0.34;
    $('nodes').style.opacity = 1;
    $('graph').classList.toggle('lod', lod);
  }

  function fit() {
    if (!view || !view.layout) return;
    var svg = $('graph'), r = svg.getBoundingClientRect();
    var w = view.layout.width, hgt = view.layout.height;
    var k = Math.min(r.width / (w + 60), r.height / (hgt + 60));
    k = Math.min(k, 1.4);
    if (!isFinite(k) || k <= 0) k = 1;
    cam.k = k;
    cam.x = (r.width - w * k) / 2;
    cam.y = (r.height - hgt * k) / 2;
    applyCam();
  }

  function highlight(i) {
    selected = i;
    var ns = $('nodes').childNodes, es = $('edges').childNodes;
    var inSet = {}, outSet = {};
    view.edges.forEach(function (e, k) {
      if (e[0] === i) outSet[e[1]] = 1;
      if (e[1] === i) inSet[e[0]] = 1;
    });
    for (var k = 0; k < ns.length; k++) {
      var nd = ns[k];
      nd.classList.toggle('sel', k === i);
      nd.classList.toggle('faded', !(k === i || inSet[k] || outSet[k]));
    }
    for (k = 0; k < es.length; k++) {
      var e = view.edges[es[k].__e];
      es[k].classList.remove('hi-in', 'hi-out', 'faded');
      if (!e) continue;
      if (e[0] === i) es[k].classList.add('hi-out');
      else if (e[1] === i) es[k].classList.add('hi-in');
      else es[k].classList.add('faded');
    }
  }

  function clearHighlight() {
    selected = null;
    var ns = $('nodes').childNodes, es = $('edges').childNodes;
    for (var k = 0; k < ns.length; k++) ns[k].classList.remove('sel', 'faded');
    for (k = 0; k < es.length; k++) es[k].classList.remove('hi-in', 'hi-out', 'faded');
  }

  function centerOn(i) {
    if (!view || !view.layout || !view.layout.nodes[i]) return;
    var p = view.layout.nodes[i];
    var r = $('graph').getBoundingClientRect();
    cam.k = Math.max(cam.k, 0.75);
    cam.x = r.width / 2 - p.x * cam.k;
    cam.y = r.height / 2 - p.y * cam.k;
    applyCam();
  }

  /* ------------------------------------------------------------------ */
  /* navigation                                                          */
  /* ------------------------------------------------------------------ */

  function crumbs(items) {
    var c = $('crumbs'); c.textContent = '';
    items.forEach(function (it, i) {
      if (i) c.appendChild(h('span', { cls: 'sep', text: '/' }));
      c.appendChild(h('span', { cls: 'crumb' + (i === items.length - 1 ? ' cur' : ''), text: it[0],
                                onclick: i === items.length - 1 ? null : it[1] }));
    });
  }

  function goNS(prefix, push) {
    state = { kind: 'ns', ns: prefix, mod: -1, def: -1, depth: state.depth };
    if (push !== false) setHash(prefix === '' ? '' : 'ns/' + prefix);
    var items = [['All modules', function () { goNS(''); }]];
    if (prefix !== '') {
      var parts = prefix.split('.'), acc = '';
      parts.forEach(function (p) {
        acc = acc === '' ? p : acc + '.' + p;
        (function (a) { items.push([p, function () { goNS(a); }]); })(acc);
      });
    }
    crumbs(items);
    $('depth-wrap').classList.add('hidden');
    render(buildNsView(prefix));
    showNSDetails(prefix);
  }

  function goModule(mid, push) {
    state = { kind: 'mod', ns: '', mod: mid, def: -1, depth: state.depth };
    if (push !== false) setHash('m/' + IDX.mods[mid].n);
    needModule(mid, function (md) {
      var name = IDX.mods[mid].n;
      var items = [['All modules', function () { goNS(''); }]];
      var parts = name.split('.'), acc = '';
      for (var i = 0; i < parts.length - 1; i++) {
        acc = acc === '' ? parts[i] : acc + '.' + parts[i];
        (function (a, p) { items.push([p, function () { goNS(a); }]); })(acc, parts[i]);
      }
      items.push([parts[parts.length - 1], null]);
      crumbs(items);
      $('depth-wrap').classList.add('hidden');
      render(buildModView(mid, md));
      showModuleDetails(mid, md);
    });
  }

  function goDef(mid, didx, push) {
    state = { kind: 'def', ns: '', mod: mid, def: didx, depth: state.depth };
    needModule(mid, function (md) {
      var def = md.defs[didx];
      if (!def) return goModule(mid);
      if (push !== false) setHash('d/' + def.f);
      var name = IDX.mods[mid].n;
      var items = [['All modules', function () { goNS(''); }]];
      var parts = name.split('.'), acc = '';
      for (var i = 0; i < parts.length - 1; i++) {
        acc = acc === '' ? parts[i] : acc + '.' + parts[i];
        (function (a, p) { items.push([p, function () { goNS(a); }]); })(acc, parts[i]);
      }
      (function (m) { items.push([parts[parts.length - 1], function () { goModule(m); }]); })(mid);
      items.push([def.n, null]);
      crumbs(items);
      $('depth-wrap').classList.remove('hidden');
      buildDefView(mid, didx, state.depth, function (v) {
        render(v);
        var fi = v.nodes.findIndex(function (n) { return n.focus; });
        if (fi >= 0) { highlight(fi); centerOn(fi); }
        showDefDetails(mid, didx);
      });
    });
  }

  /* ------------------------------------------------------------------ */
  /* side pane                                                           */
  /* ------------------------------------------------------------------ */

  function section(title, open, build) {
    var body = h('div');
    var head = h('h4', { text: title, onclick: function () { body.classList.toggle('hidden'); } });
    if (!open) body.classList.add('hidden');
    var s = h('div', { cls: 'sect' }, [head, body]);
    build(body);
    return s;
  }

  function setSide(title, sub, nodes) {
    $('sidetitle').textContent = title;
    $('sidesub').textContent = sub || '';
    var b = $('sidebody'); b.textContent = '';
    nodes.forEach(function (n) { if (n) b.appendChild(n); });
  }

  function showNSDetails(prefix) {
    var mods = IDX.mods.map(function (m, i) { return [m, i]; })
      .filter(function (p) { return prefix === '' || p[0].n === prefix || p[0].n.indexOf(prefix + '.') === 0; });
    var defs = 0, dead = 0;
    mods.forEach(function (p) { defs += p[0].nd; dead += p[0].nu; });
    setSide(prefix === '' ? 'All modules' : prefix,
      mods.length + ' modules · ' + defs + ' definitions · ' + dead + ' unused', [
      section('Modules', true, function (b) {
        var ul = h('ul');
        mods.sort(function (a, b2) { return a[0].n < b2[0].n ? -1 : 1; }).forEach(function (p) {
          ul.appendChild(h('li', {
            onclick: (function (i) { return function () { goModule(i); }; })(p[1]),
            html: '<span class="k">' + p[0].nd + '</span>' + esc(p[0].n) +
                  (p[0].nu ? ' <span class="tag dead">' + p[0].nu + ' unused</span>' : '') +
                  (p[0].r ? ' <span class="tag root">root</span>' : '')
          }));
        });
        b.appendChild(ul);
      })
    ]);
  }

  function locLink(fileId, line, label) {
    if (fileId === undefined || fileId < 0 || !line) return null;
    return h('li', { text: label, onclick: function () { openSource(fileId, line, line); } });
  }

  function showModuleDetails(mid, md) {
    var m = IDX.mods[mid];
    var deps = [], rdeps = [];
    IDX.medges.forEach(function (e) {
      if (e[0] === mid) deps.push([e[1], e[2]]);
      if (e[1] === mid) rdeps.push([e[0], e[2]]);
    });
    var unusedDeps = IDX.unusedDeps.filter(function (e) { return e[0] === mid; }).map(function (e) { return e[1]; });
    setSide(m.n, m.nd + ' definitions · ' + m.nu + ' unused · ' + deps.length + ' deps · ' + rdeps.length + ' clients', [
      section('Source', true, function (b) {
        var ul = h('ul');
        var a = locLink(m.i, 1, 'interface (.fsti)'); if (a) ul.appendChild(a);
        var c = locLink(m.s, 1, 'implementation (.fst)'); if (c) ul.appendChild(c);
        if (!ul.childNodes.length) ul.appendChild(h('li', { cls: 'note', text: 'source not bundled' }));
        b.appendChild(ul);
      }),
      section('Definitions (' + md.defs.length + ')', true, function (b) {
        var ul = h('ul');
        md.defs.forEach(function (d, i) {
          if (opts.hideGenerated && d.g) return;
          ul.appendChild(h('li', {
            onclick: function () { goDef(mid, i); },
            html: '<span class="k">' + esc(d.k) + '</span>' + esc(d.n) +
                  (d.u === 1 ? ' <span class="tag dead">unused</span>' :
                   d.u === 2 ? ' <span class="tag implicit">no direct use</span>' : '')
          }));
        });
        b.appendChild(ul);
      }),
      section('Depends on (' + deps.length + ')', false, function (b) {
        var ul = h('ul');
        deps.sort(function (a, c) { return c[1] - a[1]; }).forEach(function (p) {
          ul.appendChild(h('li', { onclick: function () { goModule(p[0]); },
            html: '<span class="k">' + p[1] + '</span>' + esc(IDX.mods[p[0]].n) }));
        });
        b.appendChild(ul);
      }),
      section('Used by (' + rdeps.length + ')', false, function (b) {
        var ul = h('ul');
        rdeps.sort(function (a, c) { return c[1] - a[1]; }).forEach(function (p) {
          ul.appendChild(h('li', { onclick: function () { goModule(p[0]); },
            html: '<span class="k">' + p[1] + '</span>' + esc(IDX.mods[p[0]].n) }));
        });
        b.appendChild(ul);
      }),
      unusedDeps.length ? section('Declared but unused deps (' + unusedDeps.length + ')', false, function (b) {
        var ul = h('ul');
        unusedDeps.forEach(function (i) {
          ul.appendChild(h('li', { text: IDX.mods[i].n, onclick: function () { goModule(i); } }));
        });
        b.appendChild(ul);
        b.appendChild(h('div', { cls: 'note', text: 'These modules are dependencies of the checked file but no definition here refers to any of their definitions.' }));
      }) : null
    ]);
  }

  function showDefDetails(mid, didx) {
    var md = MOD[mid], d = md.defs[didx], m = IDX.mods[mid];
    var uses = [], usedBy = [];
    md.e.forEach(function (e) {
      if (e[0] === didx) uses.push([mid, e[1]]);
      if (e[1] === didx) usedBy.push([mid, e[0]]);
    });
    md.o.forEach(function (t) { if (t[0] === didx) uses.push([t[1], t[2]]); });
    md.in.forEach(function (t) { if (t[2] === didx) usedBy.push([t[0], t[1]]); });

    function refList(list) {
      var ul = h('ul');
      var mids = {}; list.forEach(function (p) { mids[p[0]] = true; });
      needModules(Object.keys(mids).map(Number), function () {
        list.sort(function (a, b) {
          var an = IDX.mods[a[0]].n, bn = IDX.mods[b[0]].n;
          return an < bn ? -1 : an > bn ? 1 : a[1] - b[1];
        }).forEach(function (p) {
          var om = MOD[p[0]]; if (!om || !om.defs[p[1]]) return;
          var od = om.defs[p[1]];
          ul.appendChild(h('li', {
            onclick: function () { goDef(p[0], p[1]); },
            html: '<span class="k">' + esc(od.k) + '</span>' +
                  (p[0] === mid ? '' : '<span style="color:var(--dim)">' + esc(IDX.mods[p[0]].n) + '.</span>') +
                  esc(od.n)
          }));
        });
      });
      return ul;
    }

    var tags = (d.h || []).map(function (t) { return '<span class="tag">' + esc(t) + '</span>'; }).join('') +
      (d.q || []).map(function (t) { return '<span class="tag">' + esc(t) + '</span>'; }).join('') +
      (d.u === 1 ? '<span class="tag dead">unreachable</span>' : '') +
      (d.u === 2 ? '<span class="tag implicit">no direct use</span>' : '');

    setSide(d.n, d.k + ' in ' + m.n, [
      h('div', { cls: 'sect' }, [h('div', { cls: 'note', html: tags || '&nbsp;' })]),
      section('Source', true, function (b) {
        var ul = h('ul');
        var a = locLink(m.i, d.il, 'declaration — ' + (m.i >= 0 ? IDX.files[m.i].n : '') + ':' + d.il);
        if (a) ul.appendChild(a);
        var c = locLink(m.s, d.l, 'definition — ' + (m.s >= 0 ? IDX.files[m.s].n : '') + ':' + d.l);
        if (c) ul.appendChild(c);
        if (!ul.childNodes.length) ul.appendChild(h('li', { cls: 'note', text: 'no source location' }));
        b.appendChild(ul);
      }),
      section('Uses (' + uses.length + ')', true, function (b) { b.appendChild(refList(uses)); }),
      section('Used by (' + usedBy.length + ')', true, function (b) { b.appendChild(refList(usedBy)); })
    ]);
    // auto-open the source at the definition
    var fid = (d.l && m.s >= 0) ? m.s : (d.il && m.i >= 0 ? m.i : -1);
    var line = (d.l && m.s >= 0) ? d.l : d.il;
    if (fid >= 0 && line) openSource(fid, line, d.e || line, true);
  }

  /* ------------------------------------------------------------------ */
  /* source viewer                                                       */
  /* ------------------------------------------------------------------ */

  var KW = {};
  ('let rec and in val type match with if then else fun function module open include ' +
   'assume new private noeq unopteq irreducible inline_for_extraction noextract abstract ' +
   'effect sub_effect total logic instance class exception try begin end of when as friend ' +
   'by calc returns ensures requires decreases forall exists').split(' ')
    .forEach(function (k) { KW[k] = 1; });

  function isIdStart(c) { return (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c === 95; }
  function isIdChar(c) { return isIdStart(c) || (c >= 48 && c <= 57) || c === 39; }

  /* Tokenize the whole file into [start, end, class] spans.  Done over the
     full text rather than line by line so that block comments and strings
     spanning several lines are handled, and emitted by slicing the original
     text -- never by rewriting already-generated markup. */
  function tokenize(text) {
    var toks = [], n = text.length, i = 0;
    function push(s, e, c) { if (e > s) toks.push([s, e, c]); }
    while (i < n) {
      var c0 = text.charCodeAt(i), j;
      if (c0 === 40 /* ( */ && text.charCodeAt(i + 1) === 42 /* * */) {
        var depth = 1; j = i + 2;
        while (j < n && depth > 0) {
          if (text.charCodeAt(j) === 40 && text.charCodeAt(j + 1) === 42) { depth++; j += 2; }
          else if (text.charCodeAt(j) === 42 && text.charCodeAt(j + 1) === 41) { depth--; j += 2; }
          else j++;
        }
        push(i, j, 'cm'); i = j;
      } else if (c0 === 47 /* / */ && text.charCodeAt(i + 1) === 47) {
        j = text.indexOf('\n', i); if (j < 0) j = n;
        push(i, j, 'cm'); i = j;
      } else if (c0 === 34 /* " */) {
        j = i + 1;
        while (j < n) {
          var cj = text.charCodeAt(j);
          if (cj === 92 /* \ */) { j += 2; continue; }
          j++;
          if (cj === 34) break;
        }
        push(i, j, 'st'); i = j;
      } else if (isIdStart(c0)) {
        j = i + 1;
        while (j < n && isIdChar(text.charCodeAt(j))) j++;
        push(i, j, KW[text.slice(i, j)] ? 'kw' : '');
        i = j;
      } else {
        j = i + 1;
        while (j < n) {
          var cn = text.charCodeAt(j);
          if (isIdStart(cn) || cn === 34 || cn === 40 || cn === 47) break;
          j++;
        }
        push(i, j, ''); i = j;
      }
    }
    return toks;
  }

  function renderSource(text, from, to) {
    var toks = tokenize(text);
    var lines = [], cur = '';
    for (var t = 0; t < toks.length; t++) {
      var seg = text.slice(toks[t][0], toks[t][1]), cls = toks[t][2];
      var parts = seg.split('\n');
      for (var p = 0; p < parts.length; p++) {
        if (p > 0) { lines.push(cur); cur = ''; }
        if (parts[p] === '') continue;
        var e = esc(parts[p]);
        cur += cls ? '<span class="' + cls + '">' + e + '</span>' : e;
      }
    }
    lines.push(cur);
    var out = [];
    for (var i = 0; i < lines.length; i++) {
      var hl = (i + 1 >= from && i + 1 <= to) ? ' hl' : '';
      out.push('<div class="ln' + hl + '" id="L' + (i + 1) + '"><span class="n">' + (i + 1) +
               '</span><span class="c">' + lines[i] + '</span></div>');
    }
    return out.join('');
  }

  var srcState = { file: -1 };

  function openSource(fileId, from, to, keepSide) {
    needSource(fileId, function (text) {
      var host = keepSide ? ensureSourceSection() : ensureSourceSection();
      if (text === null) { host.innerHTML = '<div class="note">source file not bundled</div>'; return; }
      if (srcState.file !== fileId) {
        host.innerHTML = '<div class="filehdr"><b>' + esc(IDX.files[fileId].n) + '</b></div><pre id="srccode"></pre>';
        document.getElementById('srccode').innerHTML = renderSource(text, from, to);
        srcState.file = fileId;
      } else {
        var code = document.getElementById('srccode');
        if (!code) {
          host.innerHTML = '<div class="filehdr"><b>' + esc(IDX.files[fileId].n) + '</b></div><pre id="srccode"></pre>';
          code = document.getElementById('srccode');
        }
        code.innerHTML = renderSource(text, from, to);
      }
      var t = document.getElementById('L' + from);
      if (t && t.scrollIntoView) t.scrollIntoView({ block: 'center' });
    });
  }

  function ensureSourceSection() {
    var s = document.getElementById('srcwrap');
    if (!s) {
      s = h('div', { id: 'srcwrap' });
      var sect = h('div', { cls: 'sect' }, [h('h4', { text: 'Source' }), s]);
      $('sidebody').appendChild(sect);
      srcState.file = -1;
    }
    return s;
  }

  /* ------------------------------------------------------------------ */
  /* search                                                              */
  /* ------------------------------------------------------------------ */

  function doSearch(q) {
    var box = $('results');
    q = q.trim();
    if (q.length < 2) { box.classList.add('hidden'); return; }
    var ql = q.toLowerCase();
    var res = [];
    IDX.mods.forEach(function (m, i) {
      var p = m.n.toLowerCase().indexOf(ql);
      if (p >= 0) res.push({ score: (p === 0 ? 0 : 1) + m.n.length / 1000, k: 'module', n: m.n, go: function () { goModule(i); } });
    });
    needSearch(function (S) {
      S.forEach(function (e) {
        var lid = e[0];
        var short = lid.slice(lid.lastIndexOf('.') + 1);
        var p = short.toLowerCase().indexOf(ql);
        var p2 = p >= 0 ? p : lid.toLowerCase().indexOf(ql);
        if (p2 < 0) return;
        res.push({ score: 2 + (p === 0 ? 0 : 1) + short.length / 1000, k: e[3], n: lid,
                   m: IDX.mods[e[1]].n, go: function () { goDef(e[1], e[2]); } });
      });
      res.sort(function (a, b) { return a.score - b.score || a.n.length - b.n.length; });
      res = res.slice(0, 200);
      box.textContent = '';
      if (!res.length) { box.appendChild(h('div', { cls: 'r', text: 'no matches' })); }
      res.forEach(function (r) {
        box.appendChild(h('div', { cls: 'r', onclick: function () { box.classList.add('hidden'); r.go(); } }, [
          h('span', { cls: 'k', text: r.k }),
          h('span', { text: r.n }),
          r.m ? h('span', { cls: 'm', text: r.m }) : null
        ]));
      });
      box.classList.remove('hidden');
    });
  }

  /* ------------------------------------------------------------------ */
  /* unused report modal                                                 */
  /* ------------------------------------------------------------------ */

  function showUnused() {
    needUnused(function (U) {
      var b = $('modalbody');
      b.textContent = '';
      b.appendChild(h('h2', { text: 'Unused definitions' }));
      b.appendChild(h('p', { cls: 'note', html:
        'Reachability was computed from the root module(s) <b>' + esc(IDX.roots.join(', ')) + '</b>. ' +
        'Auto-generated projectors, discriminators and internal axioms are excluded.' }));
      function table(title, rows, withWhy) {
        b.appendChild(h('h3', { text: title + ' (' + rows.length + ')' }));
        if (!rows.length) { b.appendChild(h('div', { cls: 'note', text: 'none' })); return; }
        var tb = h('tbody');
        rows.slice(0, 4000).forEach(function (r) {
          tb.appendChild(h('tr', {}, [
            h('td', { cls: 'lnk', text: r[0], onclick: function () { $('modal').classList.add('hidden'); goDef(r[1], r[2]); } }),
            h('td', { text: r[3] }),
            h('td', { text: IDX.mods[r[1]].n + (r[4] ? ':' + r[4] : '') }),
            withWhy ? h('td', { text: (r[5] || []).join(', ') }) : null
          ]));
        });
        var thead = h('thead', {}, [h('tr', {}, [h('th', { text: 'definition' }), h('th', { text: 'kind' }),
          h('th', { text: 'location' }), withWhy ? h('th', { text: 'kept alive by' }) : null])]);
        b.appendChild(h('table', {}, [thead, tb]));
        if (rows.length > 4000) b.appendChild(h('div', { cls: 'note', text: '... ' + (rows.length - 4000) + ' more, see unused-report.txt' }));
      }
      table('Unreachable from the roots', U.dead, false);
      table('Reachable only implicitly (no syntactic use site)', U.implicit, true);
      $('modal').classList.remove('hidden');
    });
  }

  function showHelp() {
    var b = $('modalbody');
    b.innerHTML =
      '<h2>How to use this viewer</h2>' +
      '<p>The graph starts at the namespace level. <b>Click</b> a node to inspect it, ' +
      '<b>double-click</b> to descend into it: namespace &rarr; module &rarr; definition.</p>' +
      '<h3>Navigation</h3><ul>' +
      '<li>Scroll to zoom, drag to pan.</li>' +
      '<li><kbd>f</kbd> fit graph, <kbd>/</kbd> search, <kbd>Esc</kbd> go up one level, <kbd>u</kbd> unused report.</li>' +
      '<li>The breadcrumb at the top navigates back up.</li>' +
      '</ul>' +
      '<h3>Reading the graph</h3><ul>' +
      '<li>Edges point from a user to the thing it uses; layers run top to bottom.</li>' +
      '<li>Dashed boxes in a module view are neighbouring modules, not definitions.</li>' +
      '<li>A red border marks a definition unreachable from the roots; purple marks one that is ' +
      'only kept alive implicitly (SMT pattern, typeclass instance, plugin, top-level effect).</li>' +
      '</ul>' +
      '<h3>Source</h3><p>Selecting a definition opens its source file in the side pane at the ' +
      'right line. Module views link to both the interface and the implementation.</p>';
    $('modal').classList.remove('hidden');
  }

  /* ------------------------------------------------------------------ */
  /* hash routing                                                        */
  /* ------------------------------------------------------------------ */

  var settingHash = false;
  function setHash(s) { settingHash = true; location.hash = s; setTimeout(function () { settingHash = false; }, 0); }

  function applyHash() {
    var s = location.hash.replace(/^#/, '');
    if (!s) { goNS('', false); return; }
    var p = s.split('/');
    if (p[0] === 'ns') goNS(p.slice(1).join('/'), false);
    else if (p[0] === 'm') {
      var i = IDX.mods.findIndex(function (m) { return m.n === p[1]; });
      if (i >= 0) goModule(i, false); else goNS('', false);
    } else if (p[0] === 'd') {
      var lid = p.slice(1).join('/');
      needSearch(function (S) {
        var e = S.find(function (x) { return x[0] === lid; });
        if (e) goDef(e[1], e[2], false); else goNS('', false);
      });
    } else goNS('', false);
  }

  /* ------------------------------------------------------------------ */
  /* wiring                                                              */
  /* ------------------------------------------------------------------ */

  function wire() {
    var svg = $('graph');
    var dragging = false, sx = 0, sy = 0, moved = false;
    svg.addEventListener('mousedown', function (e) {
      dragging = true; moved = false; sx = e.clientX; sy = e.clientY; svg.classList.add('grabbing');
    });
    window.addEventListener('mousemove', function (e) {
      if (!dragging) return;
      var dx = e.clientX - sx, dy = e.clientY - sy;
      if (Math.abs(dx) + Math.abs(dy) > 3) moved = true;
      cam.x += dx; cam.y += dy; sx = e.clientX; sy = e.clientY; applyCam();
    });
    window.addEventListener('mouseup', function () { dragging = false; svg.classList.remove('grabbing'); });
    svg.addEventListener('wheel', function (e) {
      e.preventDefault();
      var r = svg.getBoundingClientRect();
      var mx = e.clientX - r.left, my = e.clientY - r.top;
      var f = Math.exp(-e.deltaY * 0.0015);
      var nk = Math.max(0.04, Math.min(6, cam.k * f));
      cam.x = mx - (mx - cam.x) * (nk / cam.k);
      cam.y = my - (my - cam.y) * (nk / cam.k);
      cam.k = nk;
      applyCam();
    }, { passive: false });

    function nodeAt(t) { while (t && t !== svg) { if (t.__i !== undefined) return t; t = t.parentNode; } return null; }
    svg.addEventListener('click', function (e) {
      var t = nodeAt(e.target);
      if (!t) { if (!moved) clearHighlight(); return; }
      if (moved) return;
      onNodeClick(view.nodes[t.__i], t.__i);
    });
    svg.addEventListener('dblclick', function (e) {
      var t = nodeAt(e.target);
      if (!t) return;
      onNodeDbl(view.nodes[t.__i]);
    });

    $('btn-fit').onclick = fit;
    $('btn-unused').onclick = showUnused;
    $('btn-help').onclick = showHelp;
    $('modalclose').onclick = function () { $('modal').classList.add('hidden'); };
    $('modal').onclick = function (e) { if (e.target === $('modal')) $('modal').classList.add('hidden'); };

    $('opt-hide-unused').onchange = function () { opts.hideUnused = this.checked; refresh(); };
    $('opt-hide-generated').onchange = function () { opts.hideGenerated = this.checked; refresh(); };
    $('opt-depth').onchange = function () {
      state.depth = Math.max(1, Math.min(4, +this.value || 1));
      if (state.kind === 'def') goDef(state.mod, state.def, false);
    };

    var si = $('search');
    si.addEventListener('input', function () { doSearch(this.value); });
    si.addEventListener('keydown', function (e) { if (e.key === 'Escape') { $('results').classList.add('hidden'); this.blur(); } });
    document.addEventListener('click', function (e) {
      if (e.target !== si && !$('results').contains(e.target)) $('results').classList.add('hidden');
    });

    document.addEventListener('keydown', function (e) {
      if (e.target.tagName === 'INPUT') return;
      if (e.key === '/') { e.preventDefault(); si.focus(); si.select(); }
      else if (e.key === 'f') fit();
      else if (e.key === 'u') showUnused();
      else if (e.key === '?') showHelp();
      else if (e.key === 'Escape') {
        if (!$('modal').classList.contains('hidden')) { $('modal').classList.add('hidden'); return; }
        up();
      }
    });

    // splitter
    var sp = $('splitter'), side = $('sidepane'), spDrag = false;
    sp.addEventListener('mousedown', function (e) { spDrag = true; e.preventDefault(); });
    window.addEventListener('mousemove', function (e) {
      if (!spDrag) return;
      var w = window.innerWidth - e.clientX;
      side.style.width = Math.max(220, Math.min(window.innerWidth - 260, w)) + 'px';
    });
    window.addEventListener('mouseup', function () { if (spDrag) { spDrag = false; fit(); } });
    window.addEventListener('resize', function () { fit(); });
    window.addEventListener('hashchange', function () { if (!settingHash) applyHash(); });
  }

  function up() {
    if (state.kind === 'def') goModule(state.mod);
    else if (state.kind === 'mod') {
      var n = IDX.mods[state.mod].n, i = n.lastIndexOf('.');
      goNS(i < 0 ? '' : n.slice(0, i));
    } else if (state.ns !== '') {
      var j = state.ns.lastIndexOf('.');
      goNS(j < 0 ? '' : state.ns.slice(0, j));
    }
  }

  function refresh() {
    if (state.kind === 'ns') goNS(state.ns, false);
    else if (state.kind === 'mod') goModule(state.mod, false);
    else goDef(state.mod, state.def, false);
  }

  function onNodeClick(nd, i) {
    highlight(i);
    if (view.kind === 'ns') {
      if (nd.isMod) goModule(nd.mods[0]);
      else showNSDetails(nd.key);
    } else if (nd.ext) {
      goModule(nd.extMod);
    } else {
      showDefDetails(nd.mid, nd.defIdx);
    }
  }

  function onNodeDbl(nd) {
    if (view.kind === 'ns') {
      if (nd.isMod) goModule(nd.mods[0]); else goNS(nd.key);
    } else if (nd.ext) goModule(nd.extMod);
    else goDef(nd.mid, nd.defIdx);
  }

  /* ------------------------------------------------------------------ */

  return {
    setIndex: function (d) { IDX = d; },
    setModule: function (id, d) { MOD[id] = d; },
    setSource: function (id, t) { SRC[id] = t; },
    setSearch: function (d) { SEARCH = d; },
    setUnused: function (d) { UNUSED = d; },
    goModule: goModule, goDef: goDef, goNS: goNS,
    start: function () {
      buildNS();
      wire();
      applyHash();
    }
  };
})();
