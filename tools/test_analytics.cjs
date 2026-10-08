/* Copyright 2026 Naoaki Tsuda. SPDX-License-Identifier: BSD-3-Clause */
const { test } = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');
const source = fs.readFileSync(new URL('../site/assets/analytics.js', `file://${__filename}`), 'utf8');
const key = 'research.analytics-consent.v1';
const legacyKey = 'lctr.analytics-consent.v1';
const id = 'G-4MHM8N068S';

function fixture({ choice = null, legacyChoice = null, hostname = 'tsuda-naoaki.github.io',
  pathname = '/lctr/', protocol = 'https:', storageFails = false, writeFails = false,
  lang = 'en', missing = [], cookies = 'research_ga=a; research_ga_4MHM8N068S=b; unrelated=c; lctr_ga_OTHER=d' } = {}) {
  const nodes = Object.fromEntries(['panel', 'settings', 'status', 'allow', 'deny', 'link', 'privacy'].map(name => [name, {
    hidden: true, events: {}, attrs: {}, focused: false,
    focus() { this.focused = true; }, setAttribute(k, v) { this.attrs[k] = v; },
    addEventListener(k, f) { this.events[k] = f; },
    querySelector(s) { return node(s === 'a' ? 'link' : s.includes('deny') ? 'deny' : 'allow'); }
  }]));
  function node(name) { return missing.includes(name) ? null : nodes[name]; }
  const scripts = [], cookieWrites = [], events = {}, stored = new Map();
  if (choice !== null) stored.set(key, choice);
  if (legacyChoice !== null) stored.set(legacyKey, legacyChoice);
  let reloads = 0;
  const document = {
    documentElement: { lang },
    querySelector(s) { return node(s.match(/analytics-(.+)\]/)[1]); },
    getElementById() { return node('privacy'); },
    createElement(tag) { assert.equal(tag, 'script'); return {}; },
    head: { appendChild(script) { scripts.push(script); } },
    get cookie() { return cookies; },
    set cookie(value) { cookieWrites.push(value); }
  };
  const window = { addEventListener(k, f) { events[k] = f; } };
  vm.runInNewContext(source, { window, document, location: { hostname, pathname, protocol, reload() { reloads++; } }, localStorage: {
    getItem(k) { if (storageFails) throw Error('blocked'); return stored.get(k) ?? null; },
    setItem(k, v) { if (storageFails || writeFails) throw Error('blocked'); stored.set(k, v); }
  } });
  return { nodes, scripts, cookieWrites, window, events, stored, reloads: () => reloads,
    click: name => nodes[name].events.click(), commands: () => (window.dataLayer || []).map(x => Array.from(x)) };
}

function assertExpired(writes, name, path) {
  for (const domain of ['', '; Domain=tsuda-naoaki.github.io']) {
    assert(writes.includes(`${name}=; Max-Age=0; Path=${path}${domain}; SameSite=Lax; Secure`), `${name} expired at ${path}${domain}`);
  }
}

test('unknown, rejected, and invalid consent never load Google', () => {
  for (const choice of [null, 'deny', 'corrupt']) {
    const f = fixture({ choice });
    assert.equal(f.scripts.length, 0); assert.equal(f.commands().length, 0);
    assert.equal(f.nodes.panel.hidden, choice === 'deny');
    assert.equal(f.window['ga-disable-' + id], true);
  }
});

test('allow loads one tag, disables advertising, and shares root cookies', () => {
  const f = fixture(); f.click('allow'); f.click('allow');
  assert.equal(f.scripts.length, 1);
  assert.equal(f.scripts[0].src, 'https://www.googletagmanager.com/gtag/js?id=' + id);
  assert.equal(f.scripts[0].async, true);
  assert.equal(f.stored.get(key), 'allow');
  const commands = f.commands();
  assert.equal(commands[0][0], 'consent'); assert.equal(commands[0][1], 'default');
  assert.equal(commands[0][2].analytics_storage, 'granted');
  for (const adKey of ['ad_storage', 'ad_user_data', 'ad_personalization']) assert.equal(commands[0][2][adKey], 'denied');
  const configs = commands.filter(x => x[0] === 'config'); assert.equal(configs.length, 1);
  assert.equal(configs[0][1], id);
  assert.equal(configs[0][2].allow_google_signals, false);
  assert.equal(configs[0][2].allow_ad_personalization_signals, false);
  assert.equal(configs[0][2].cookie_domain, 'tsuda-naoaki.github.io');
  assert.equal(configs[0][2].cookie_path, '/');
  assert.equal(configs[0][2].cookie_prefix, 'research');
  assert.equal(configs[0][2].cookie_flags, 'SameSite=Lax;Secure');
  assert.equal(commands.filter(x => x[0] === 'event').length, 0, 'No manual link or file events');
});

test('saved shared permission works on root, index, and the LCTR subtree', () => {
  for (const pathname of ['/', '/index.html', '/lctr/', '/lctr/en/papers/index.html']) {
    const f = fixture({ choice: 'allow', pathname });
    assert.equal(f.scripts.length, 1, pathname); assert.equal(f.nodes.panel.hidden, true);
    assert.equal(f.window['ga-disable-' + id], false);
  }
});

test('HTTP, preview hosts, private tests, and unrelated routes never send production analytics', () => {
  for (const params of [
    { protocol: 'http:' }, { protocol: 'file:' }, { hostname: '127.0.0.1' }, { hostname: 'localhost' },
    { hostname: 'preview.example.test' }, { hostname: 'tsuda-naoaki.github.io.example.test' },
    { pathname: '/private-test/' }, { pathname: '/lctr-private-test/' }, { pathname: '/other/' },
    { pathname: '/lctr' }, { pathname: '/lctr-other/' }, { pathname: '/index.html/other' }
  ]) {
    const f = fixture({ choice: 'allow', ...params }); f.click('allow');
    assert.equal(f.scripts.length, 0, JSON.stringify(params)); assert.equal(f.commands().length, 0);
  }
});

test('legacy LCTR allow prompts for the expanded scope; explicit new choice persists', () => {
  for (const pathname of ['/', '/lctr/']) {
    const f = fixture({ legacyChoice: 'allow', pathname });
    assert.equal(f.scripts.length, 0); assert.equal(f.nodes.panel.hidden, false);
    assert.equal(f.stored.has(key), false);
    f.click('allow'); assert.equal(f.scripts.length, 1); assert.equal(f.stored.get(key), 'allow');
  }
});

test('legacy denial is preserved, including when persisting migration fails', () => {
  for (const params of [{}, { choice: 'corrupt' }, { writeFails: true }]) {
    const f = fixture({ legacyChoice: 'deny', ...params });
    assert.equal(f.scripts.length, 0); assert.equal(f.nodes.panel.hidden, true);
    if (!params.writeFails) assert.equal(f.stored.get(key), 'deny');
  }
  const f = fixture({ legacyChoice: 'deny', choice: 'allow' });
  assert.equal(f.scripts.length, 1, 'A later explicit shared grant takes precedence');
});

test('initial setup and a new grant expire legacy cookies invisible from the root', () => {
  for (const choice of [null, 'allow', 'deny']) {
    const f = fixture({ choice, pathname: '/', cookies: 'unrelated=c' });
    for (const name of ['lctr_ga', 'lctr_ga_4MHM8N068S']) assertExpired(f.cookieWrites, name, '/lctr/');
    f.cookieWrites.length = 0; f.click('allow');
    for (const name of ['lctr_ga', 'lctr_ga_4MHM8N068S']) assertExpired(f.cookieWrites, name, '/lctr/');
    assert(f.cookieWrites.every(x => !x.startsWith('unrelated=')));
  }
});

test('denial disables GA, clears owned cookies at both paths, preserves others, and reloads', () => {
  const f = fixture({ choice: 'allow', cookies: 'research_ga=a; research_ga_4MHM8N068S=b; research_ga_EXTRA=c; unrelated=d; lctr_ga_OTHER=e; research_game=f' });
  f.cookieWrites.length = 0; f.click('deny');
  assert.equal(f.window['ga-disable-' + id], true); assert.equal(f.reloads(), 1);
  assert.equal(f.stored.get(key), 'deny');
  for (const name of ['research_ga', 'research_ga_4MHM8N068S', 'research_ga_EXTRA']) assertExpired(f.cookieWrites, name, '/');
  for (const name of ['lctr_ga', 'lctr_ga_4MHM8N068S']) assertExpired(f.cookieWrites, name, '/lctr/');
  assert(f.cookieWrites.every(x => !/^(?:unrelated|lctr_ga_OTHER|research_game)=/.test(x)));
});

test('saved denial also clears remaining shared identifiers on initial setup', () => {
  const f = fixture({ choice: 'deny' });
  for (const name of ['research_ga', 'research_ga_4MHM8N068S']) assertExpired(f.cookieWrites, name, '/');
  assert.equal(f.reloads(), 0);
});

test('denial, consent-key removal, corrupt values, and localStorage.clear immediately revoke other tabs', () => {
  for (const event of [
    { key, newValue: 'deny' }, { key, newValue: null }, { key, newValue: 'corrupt' }, { key: null, newValue: null }
  ]) {
    const f = fixture({ choice: 'allow' }); f.cookieWrites.length = 0;
    f.events.storage(event);
    assert.equal(f.window['ga-disable-' + id], true); assert.equal(f.reloads(), 1);
    assert.equal(f.nodes.panel.hidden, event.newValue === 'deny');
    assertExpired(f.cookieWrites, 'research_ga', '/');
    assertExpired(f.cookieWrites, 'lctr_ga', '/lctr/');
  }
});

test('other keys and a grant in another tab do not duplicate loading or revoke permission', () => {
  const f = fixture({ choice: 'allow' });
  f.events.storage({ key: 'unrelated', newValue: null });
  f.events.storage({ key, newValue: 'allow' });
  assert.equal(f.window['ga-disable-' + id], false); assert.equal(f.reloads(), 0); assert.equal(f.scripts.length, 1);
});

test('blocked storage stays usable and never implies permission', () => {
  const f = fixture({ storageFails: true }); assert.equal(f.scripts.length, 0);
  f.click('deny'); assert.equal(f.scripts.length, 0); f.click('allow'); assert.equal(f.scripts.length, 1);
});

test('settings reopen and explanation expands', () => {
  const f = fixture({ choice: 'deny' }); f.click('settings');
  assert.equal(f.nodes.panel.hidden, false); assert.equal(f.nodes.settings.attrs['aria-expanded'], 'true');
  assert.equal(f.nodes.allow.focused, true);
  f.click('link'); assert.equal(f.nodes.privacy.open, true); assert.equal(f.nodes.panel.hidden, true);
  assert.equal(f.nodes.settings.attrs['aria-expanded'], 'false');
});

test('Japanese and English status accurately reflect the choice', () => {
  for (const lang of ['ja', 'en']) {
    const f = fixture({ lang });
    assert.equal(f.nodes.status.textContent, lang === 'ja' ? 'GA4による計測は停止しています。' : 'GA4 measurement is off.');
    f.click('allow');
    assert.equal(f.nodes.status.textContent, lang === 'ja' ? 'GA4による計測を許可しています。' : 'GA4 measurement is allowed.');
    f.click('deny');
    assert.equal(f.nodes.status.textContent, lang === 'ja' ? 'GA4による計測は停止しています。' : 'GA4 measurement is off.');
  }
});

test('missing consent UI safely exits without loading GA or changing cookies', () => {
  for (const name of ['panel', 'settings', 'status', 'allow', 'deny', 'link', 'privacy']) {
    const f = fixture({ choice: 'allow', missing: [name] });
    assert.equal(f.scripts.length, 0, name); assert.equal(f.cookieWrites.length, 0, name);
  }
});
