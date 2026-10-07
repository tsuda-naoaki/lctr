/* Copyright 2026 Naoaki Tsuda. SPDX-License-Identifier: BSD-3-Clause */
const { test } = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');
const source = fs.readFileSync(new URL('../site/assets/analytics.js', `file://${__filename}`), 'utf8');
function fixture({ choice = null, hostname = 'tsuda-naoaki.github.io', pathname = '/lctr/', storageFails = false } = {}) {
  const nodes = Object.fromEntries(['panel', 'settings', 'status', 'allow', 'deny', 'link', 'privacy'].map(name => [name, {
    hidden: true, events: {}, attrs: {}, focus() {}, setAttribute(k, v) { this.attrs[k] = v; },
    addEventListener(k, f) { this.events[k] = f; }, querySelector(s) { return nodes[s === 'a' ? 'link' : s.includes('deny') ? 'deny' : 'allow']; }
  }]));
  const scripts = [], cookieWrites = [], events = {}, stored = new Map();
  if (choice !== null) stored.set('lctr.analytics-consent.v1', choice);
  let reloads = 0;
  const document = {
    documentElement: { lang: 'en' },
    querySelector(s) { return nodes[s.match(/analytics-(.+)\]/)[1]]; },
    getElementById() { return nodes.privacy; },
    createElement(tag) { assert.equal(tag, 'script'); return {}; },
    head: { appendChild(script) { scripts.push(script); } },
    get cookie() { return 'lctr_ga=a; lctr_ga_4MHM8N068S=b; unrelated=c'; },
    set cookie(value) { cookieWrites.push(value); }
  };
  const window = { addEventListener(k, f) { events[k] = f; } };
  vm.runInNewContext(source, { window, document, location: { hostname, pathname, reload() { reloads++; } }, localStorage: {
    getItem(k) { if (storageFails) throw Error('blocked'); return stored.get(k) ?? null; },
    setItem(k, v) { if (storageFails) throw Error('blocked'); stored.set(k, v); }
  } });
  return { nodes, scripts, cookieWrites, window, events, stored, reloads: () => reloads,
    click: name => nodes[name].events.click(), commands: () => (window.dataLayer || []).map(x => Array.from(x)) };
}
test('unknown, rejected, and invalid consent never load Google', () => {
  for (const choice of [null, 'deny', 'corrupt']) {
    const f = fixture({ choice });
    assert.equal(f.scripts.length, 0); assert.equal(f.commands().length, 0);
    assert.equal(f.nodes.panel.hidden, choice === 'deny');
  }
});
test('allow loads one tag, denies advertising, and uses isolated cookies', () => {
  const f = fixture(); f.click('allow'); f.click('allow');
  assert.equal(f.scripts.length, 1);
  assert.equal(f.scripts[0].src, 'https://www.googletagmanager.com/gtag/js?id=G-4MHM8N068S');
  const commands = f.commands();
  assert.equal(commands[0][0], 'consent'); assert.equal(commands[0][2].analytics_storage, 'granted');
  for (const key of ['ad_storage', 'ad_user_data', 'ad_personalization']) assert.equal(commands[0][2][key], 'denied');
  const configs = commands.filter(x => x[0] === 'config'); assert.equal(configs.length, 1);
  assert.equal(configs[0][2].allow_google_signals, false);
  assert.equal(configs[0][2].allow_ad_personalization_signals, false);
  assert.equal(configs[0][2].cookie_path, '/lctr/');
  assert.equal(configs[0][2].cookie_prefix, 'lctr');
  assert.equal(commands.filter(x => x[0] === 'event').length, 0, 'No duplicate manual file event');
});
test('saved permission loads on the next page without asking again', () => {
  const f = fixture({ choice: 'allow' }); assert.equal(f.scripts.length, 1); assert.equal(f.nodes.panel.hidden, true);
});
test('preview hosts and unrelated site paths never send production analytics', () => {
  for (const params of [{ hostname: '127.0.0.1' }, { hostname: 'localhost' }, { pathname: '/' }, { pathname: '/private-test/' }]) {
    const f = fixture(params); f.click('allow'); assert.equal(f.scripts.length, 0); assert.equal(f.commands().length, 0);
  }
});
test('denial persists; revocation disables GA, clears only its cookies, and reloads', () => {
  const f = fixture({ choice: 'allow' }); f.click('deny');
  assert.equal(f.window['ga-disable-G-4MHM8N068S'], true); assert.equal(f.reloads(), 1);
  assert.equal(f.stored.get('lctr.analytics-consent.v1'), 'deny');
  assert.equal(f.cookieWrites.length, 4); assert(f.cookieWrites.every(x => x.startsWith('lctr_ga')));
});
test('revocation propagates to another open tab', () => {
  const f = fixture({ choice: 'allow' });
  f.events.storage({ key: 'lctr.analytics-consent.v1', newValue: 'deny' });
  assert.equal(f.window['ga-disable-G-4MHM8N068S'], true); assert.equal(f.reloads(), 1);
});
test('blocked storage stays usable and never implies permission', () => {
  const f = fixture({ storageFails: true }); assert.equal(f.scripts.length, 0);
  f.click('deny'); assert.equal(f.scripts.length, 0); f.click('allow'); assert.equal(f.scripts.length, 1);
});
test('settings reopen and explanation expands', () => {
  const f = fixture({ choice: 'deny' }); f.click('settings');
  assert.equal(f.nodes.panel.hidden, false); assert.equal(f.nodes.settings.attrs['aria-expanded'], 'true');
  f.click('link'); assert.equal(f.nodes.privacy.open, true); assert.equal(f.nodes.panel.hidden, true);
});
