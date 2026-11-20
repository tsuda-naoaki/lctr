(() => {
  const wrappers = [...document.querySelectorAll(".backmatter-table")];
  const controls = [];
  const resize = new ResizeObserver(entries => {
    for (const entry of entries) entry.target.closest(".backmatter-table")?.refreshTablePan?.();
  });
  for (const wrapper of wrappers) {
    const viewport = wrapper.querySelector(".backmatter-table-viewport");
    const bar = wrapper.querySelector(".backmatter-pan");
    const table = viewport.querySelector("table");
    if (wrapper.classList.contains("backmatter-summary-table")) {
      for (const row of table.tHead?.rows ?? [])
        if (!row.textContent.trim() && !row.querySelector("img,svg,math")) row.hidden = true;
    }
    if (!bar) {
      if (wrapper.classList.contains("table-reflow-stacked")) {
        table.setAttribute("role","table");
        for (const group of table.querySelectorAll("thead,tbody,tfoot")) group.setAttribute("role","rowgroup");
        for (const [i,row] of [...table.rows].entries()) {
          row.setAttribute("role","row");
          for(const cell of row.cells) cell.setAttribute("role",
            cell.tagName==="TH" || (i===0 && wrapper.classList.contains("table-reflow-first-header"))
              ? "columnheader" : "cell");
        }
      }
      continue;
    }
    const range = bar.querySelector("input");
    const update = () => {
      const max = Math.max(0, viewport.scrollWidth - viewport.clientWidth);
      bar.hidden = max < 2;
      viewport.tabIndex = max < 2 ? -1 : 0;
      range.max = max;
      range.value = Math.round(viewport.scrollLeft);
    };
    wrapper.refreshTablePan = update;
    viewport.addEventListener("scroll", () => { range.value = Math.round(viewport.scrollLeft); }, {passive:true});
    range.addEventListener("input", () => { viewport.scrollLeft = range.valueAsNumber; });
    resize.observe(viewport);
    resize.observe(table);
    controls.push(update);
  }
  const refreshAll = () => controls.forEach(update => update());
  addEventListener("pageshow",refreshAll);
  refreshAll();

  for (const index of document.querySelectorAll(".audit-directory")) {
    const filter = index.querySelector(".audit-directory-filter");
    const input = filter.querySelector("input");
    const count = filter.querySelector("output");
    const empty = index.querySelector(".audit-directory-empty");
    const cards = [...index.querySelectorAll("[data-audit-number]")];
    const normalize = text => text.normalize("NFKC").toLowerCase().replace(/[–—]/g,"-");
    const metadata = cards.map(card => [card, normalize(card.dataset.auditLabel)]);
    const update = () => {
      const terms = normalize(input.value).trim().split(/[\s、,]+/).filter(Boolean);
      let visible = 0;
      for(const [card,label] of metadata) {
        const hit = terms.every(word => {
          const number = /^(?:s\.2\.)?0*([0-9]{1,2})$/.exec(word);
          return number ? Number(number[1])===Number(card.dataset.auditNumber) : label.includes(word);
        });
        card.hidden = !hit;
        if (hit) visible++;
      }
      count.textContent = `${visible} / ${cards.length}`;
      empty.hidden = visible !== 0;
    };
    filter.hidden = false;
    input.addEventListener("input",update);
    update();
  }
})();
