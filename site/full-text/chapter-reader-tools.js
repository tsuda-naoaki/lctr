(() => {
  const bar = document.querySelector(".reader-locator");
  if (bar) {
    const location = bar.querySelector(".locator-current");
    const chapter = bar.querySelector(".locator-chapter");
    const menu = bar.querySelector(".locator-outline");
    const links = new Map([...menu.querySelectorAll("a[data-heading-id]")]
      .map(link => [link.dataset.headingId, link]));
    const ordered = [...links.values()];
    const positions = new Map([...links.keys()].map((id, index) => [id, index]));
    const back = bar.querySelector(".locator-prev");
    const next = bar.querySelector(".locator-next");
    const updateStep = (control, adjacent, chapterStart = false) => {
      if (!control) return;
      const captions = control.dataset;
      const href = adjacent?.getAttribute("href") ?? (chapterStart ? captions.startHref : captions.edgeHref);
      const caption = adjacent ? captions.caption : chapterStart ? captions.startCaption : captions.edgeCaption;
      const destination = adjacent?.textContent.trim() ?? (chapterStart ? "" : captions.edgeName);
      const detail = caption + (destination && destination !== caption ? captions.joiner + destination : "");
      if (href) {
        control.setAttribute("href", href);
        control.removeAttribute("aria-disabled");
      } else {
        control.removeAttribute("href");
        control.setAttribute("aria-disabled", "true");
      }
      control.title = detail;
      control.setAttribute("aria-label", detail);
      control.querySelector(".locator-step-full").textContent = caption;
      control.querySelector(".locator-step-number").textContent =
        adjacent ? (destination.match(/^([0-9]+(?:\.[0-9]+)+)\s/)?.[1] ?? "") : "";
    };
    const headings = [...document.querySelectorAll(
      ".ltx_page_content :is(.ltx_title_subsection,.ltx_title_subsubsection,.ltx_title_paragraph,.ltx_title_subparagraph)"
    )].map(node => [node, node.closest("section[id]")?.id])
      .filter(([, id]) => links.has(id));
    let scheduled = false;
    let previous;
    const update = () => {
      scheduled = false;
      const cutoff = Math.max(bar.getBoundingClientRect().bottom, 0) + 58;
      let selected = location.dataset.initialAnchor;
      for (const [node, id] of headings) {
        if (node.getBoundingClientRect().top > cutoff) break;
        selected = id;
      }
      if (selected === previous) return;
      links.get(previous)?.removeAttribute("aria-current");
      const active = links.get(selected);
      active?.setAttribute("aria-current", "location");
      const label = active?.textContent ?? location.dataset.initialTitle;
      location.textContent = label;
      location.title = label;
      location.href = active?.getAttribute("href") ?? chapter.href;
      const ix = positions.get(selected) ?? -1;
      updateStep(back, ordered[ix - 1], ix === 0);
      updateStep(next, ordered[ix + 1]);
      const aside = document.querySelector(".pilot-aside");
      if (aside) {
        const a = [...aside.querySelectorAll("a")].find(item =>
          item.textContent.trim() === active?.textContent.trim());
        if (a) {
          aside.querySelector("[aria-current=location]")?.removeAttribute("aria-current");
          a.setAttribute("aria-current", "location");
        }
      }
      previous = selected;
    };
    const schedule = () => {
      if (!scheduled) {
        scheduled = true;
        requestAnimationFrame(update);
      }
    };
    const height = () => {
      const value = Math.ceil(bar.getBoundingClientRect().height);
      document.documentElement.style.setProperty("--reader-locator-height", `${value}px`);
      schedule();
    };
    new ResizeObserver(height).observe(bar);
    const article = document.querySelector(".ltx_page_content");
    if (article) new ResizeObserver(schedule).observe(article);
    function realignInitialLink() {
      if (userMoved || !locationHash) return;
      const target = document.getElementById(locationHash);
      if (!target || !article?.contains(target)) return;
      const top = target.getBoundingClientRect().top;
      const floor = bar.getBoundingClientRect().bottom;
      if (top < floor - 2 || top > floor + 55) {
        target.scrollIntoView({block:"start", inline:"nearest", behavior:"instant"});
        schedule();
      }
    }
    const locationHash = (() => {
      try { return decodeURIComponent(window.location.hash.slice(1)); }
      catch { return ""; }
    })();
    let userMoved = false;
    if (locationHash && performance.getEntriesByType("navigation")[0]?.type !== "back_forward") {
      const stopRealigning = () => {
        userMoved = true;
        for (const event of ["pointerdown","touchstart","wheel","keydown","hashchange"])
          removeEventListener(event, stopRealigning);
      };
      for (const event of ["pointerdown","touchstart","wheel","keydown","hashchange"])
        addEventListener(event, stopRealigning, {passive:true});
      requestAnimationFrame(() => requestAnimationFrame(realignInitialLink));
      const loaded = document.readyState === "complete" ? Promise.resolve()
        : new Promise(resolve => addEventListener("load",resolve,{once:true}));
      Promise.all([loaded, document.fonts.ready]).then(() => requestAnimationFrame(realignInitialLink));
    }
    addEventListener("scroll", schedule, {passive:true});
    addEventListener("hashchange", schedule);
    addEventListener("pageshow", schedule);
    menu.addEventListener("click", event => {
      if (event.target.closest("a")) menu.open = false;
    });
    document.addEventListener("pointerdown", event => {
      if (menu.open && !menu.contains(event.target)) menu.open = false;
    });
    menu.addEventListener("keydown", event => {
      if (event.key === "Escape" && menu.open) {
        menu.open = false;
        menu.querySelector("summary").focus();
      }
    });
    height();
    update();
  }

  const form = document.querySelector("[data-definition-filter]");
  if (form) {
    const input = form.querySelector("input");
    const result = form.querySelector("[data-result-label]");
    const groups = [...document.querySelectorAll("[data-definition-group]")].map(section =>
      [section, [...section.querySelectorAll("[data-definition-entry]")]]);
    const total = groups.reduce((n, [, rows]) => n + rows.length, 0);
    const empty = document.querySelector(".definition-empty");
    const normalized = value => value.normalize("NFKC").toLocaleLowerCase();
    const update = () => {
      const terms = normalized(input.value).split(/[\s、,]+/).filter(Boolean);
      let shown = 0;
      for (const [section, rows] of groups) {
        let matches = 0;
        for (const row of rows) {
          const text = normalized(row.dataset.search);
          const ok = terms.every(term =>
            /^\d+\.\d+$/.test(term)
              ? row.dataset.number === term
              : text.includes(term));
          row.hidden = !ok;
          if (ok) matches++;
        }
        section.hidden = !matches;
        shown += matches;
      }
      result.textContent = `${shown} / ${total} ${result.dataset.resultLabel}`;
      empty.hidden = shown !== 0;
    };
    input.addEventListener("input", update);
    form.hidden = false;
    update();
  }
})();
