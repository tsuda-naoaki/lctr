/* Copyright 2026 Naoaki Tsuda. SPDX-License-Identifier: BSD-3-Clause */
(() => {
  'use strict';
  const id = 'G-4MHM8N068S';
  const key = 'lctr.analytics-consent.v1';
  const panel = document.querySelector('[data-analytics-panel]');
  const settings = document.querySelector('[data-analytics-settings]');
  const status = document.querySelector('[data-analytics-status]');
  if (!panel || !settings || !status) return;
  const ja = document.documentElement.lang === 'ja';
  let choice = null;
  let started = false;
  try { choice = localStorage.getItem(key); } catch (_) { /* No persistence. */ }
  if (choice !== 'allow' && choice !== 'deny') choice = null;

  function render() {
    status.textContent = choice === 'allow'
      ? (ja ? 'GA4による計測を許可しています。' : 'GA4 measurement is allowed.')
      : (ja ? 'GA4による計測は停止しています。' : 'GA4 measurement is off.');
    settings.hidden = false;
    panel.hidden = choice !== null;
    settings.setAttribute('aria-expanded', String(!panel.hidden));
  }

  function start() {
    // Preview and private-test hosts must never contribute production traffic.
    if (started || location.hostname !== 'tsuda-naoaki.github.io' ||
        !location.pathname.startsWith('/lctr/')) return;
    started = true;
    window['ga-disable-' + id] = false;
    window.dataLayer = window.dataLayer || [];
    window.gtag = function () { window.dataLayer.push(arguments); };
    window.gtag('consent', 'default', {
      ad_storage: 'denied', ad_user_data: 'denied',
      ad_personalization: 'denied', analytics_storage: 'granted'
    });
    window.gtag('js', new Date());
    window.gtag('config', id, {
      allow_google_signals: false,
      allow_ad_personalization_signals: false,
      cookie_domain: location.hostname,
      cookie_path: '/lctr/',
      cookie_prefix: 'lctr',
      cookie_flags: 'SameSite=Lax;Secure'
    });
    const script = document.createElement('script');
    script.async = true;
    script.src = 'https://www.googletagmanager.com/gtag/js?id=' + id;
    document.head.appendChild(script);
  }

  function stop() {
    window['ga-disable-' + id] = true;
    for (const cookie of document.cookie.split(';')) {
      const name = cookie.trim().split('=')[0];
      if (/^lctr_ga(?:_|$)/.test(name)) {
        for (const domain of ['', '; Domain=' + location.hostname]) {
          document.cookie = name + '=; Max-Age=0; Path=/lctr/' + domain + '; SameSite=Lax; Secure';
        }
      }
    }
  }

  function choose(value) {
    choice = value;
    try { localStorage.setItem(key, value); } catch (_) { /* Current page only. */ }
    render();
    if (value === 'allow') start();
    else {
      stop();
      if (started) location.reload();
    }
    settings.focus({ preventScroll: true });
  }
  settings.addEventListener('click', () => {
    panel.hidden = !panel.hidden;
    settings.setAttribute('aria-expanded', String(!panel.hidden));
    if (!panel.hidden) panel.querySelector('button').focus();
  });
  panel.querySelector('[data-analytics-allow]').addEventListener('click', () => choose('allow'));
  panel.querySelector('[data-analytics-deny]').addEventListener('click', () => choose('deny'));
  panel.querySelector('a').addEventListener('click', () => {
    document.getElementById('analytics-privacy').open = true;
    panel.hidden = true;
    settings.setAttribute('aria-expanded', 'false');
  });
  // Revoke immediately in other open LCTR tabs as well.
  window.addEventListener('storage', (event) => {
    if (event.key === key && event.newValue !== 'allow') {
      choice = event.newValue === 'deny' ? 'deny' : null;
      stop(); render();
      if (started) location.reload();
    }
  });
  render();
  if (choice === 'allow') start();
})();
