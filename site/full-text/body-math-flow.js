/* Paint the original LuaLaTeX vector at its original size, one cut-safe slice per row. */
(() => {
  const formulas = [...document.querySelectorAll(".lctr-native-math[data-body-math-cuts]")];
  const reading = document.querySelector(".ltx_page_content");
  const tables = [...document.querySelectorAll(".reader-table-scroll:has(> table.ltx_eqn_table)")];
  const data = formulas.map(el => ({
    el,
    img: el.querySelector(":scope > img.lctr-math-vector"),
    view: el.querySelector(":scope > .body-math-lines"),
    cuts: JSON.parse(el.dataset.bodyMathCuts),
    table: el.closest(".reader-table-scroll"),
    signature: "",
  }));

  function linePlan(width, cuts, limit) {
    const breaks = [[0, 0], ...cuts, [width, 0]];
    const cost = Array(breaks.length).fill(Infinity);
    const next = Array(breaks.length).fill(-1);
    cost[breaks.length - 1] = 0;
    for (let i = breaks.length - 2; i >= 0; i--) {
      for (let j = i + 1; j < breaks.length; j++) {
        const span = breaks[j][0] - breaks[i][0];
        if (span > limit) break;
        // Prefer few lines and a meaningful TeX break over filling each line.
        const last = j === breaks.length - 1;
        const score = 100 + breaks[j][1] * .7 + (last ? 0 : 2 * (1 - span / limit)**2)
          + (span < Math.min(3, limit * .18) ? 7 : 0) + cost[j];
        if (score < cost[i]) {
          cost[i] = score;
          next[i] = j;
        }
      }
    }
    if (next[0] < 0) return [];
    const rows = [];
    for (let i = 0; i < breaks.length - 1; i = next[i]) {
      rows.push([breaks[i][0], breaks[next[i]][0]]);
    }
    return rows;
  }

  let queued = false, containerSignature = "";
  function refresh() {
    queued = false;
    if (!reading) return;
    const sizes = [reading.clientWidth, innerWidth, getComputedStyle(reading).fontSize].join("|");
    if (containerSignature === sizes) return;
    containerSignature = sizes;
    for (const table of tables) table.classList.remove("body-math-table-wrap");
    // Measure only stable containing widths before changing the contents of equation tables.
    const activeTables = new Set();
    for (const p of data) {
      const {el, img, view, cuts, table} = p;
      const prose = el.closest("p, .ltx_para, .ltx_title, .ltx_page_content");
      const font = parseFloat(getComputedStyle(el).fontSize);
      const width = parseFloat(img.style.width), height = parseFloat(img.style.height);
      const base = Math.min(reading.clientWidth, prose?.clientWidth || reading.clientWidth);
      const inline = el.closest(".reader-inline-scroll");
      const available = Math.max(0, base / font - (table ? .95 : inline ? 2.35 : 1.3));
      const signature = Math.round(available * 100) + "|" + font;
      if (signature !== p.signature) {
        p.signature = signature;
        const rows = width > available ? linePlan(width, cuts, available) : [];
        el.classList.toggle("body-math-reflowed", rows.length > 1);
        if (width > available && rows.length < 2) el.dataset.bodyMathState = "no-fitting-safe-cut";
        else el.dataset.bodyMathState = rows.length > 1 ? "wrapped" : "fits";
        const slices = rows.length > 1 ? rows.map(([start, end]) => {
          const line = document.createElement("span");
          line.className = "body-math-slice";
          line.style.inlineSize = (end - start).toFixed(6) + "em";
          line.style.blockSize = height + "em";
          // Cropping a background does not change any glyph, placement within a line, or scale.
          line.style.backgroundImage = 'url("' + img.getAttribute("src") + '")';
          line.style.backgroundSize = width + "em " + height + "em";
          line.style.backgroundPosition = "-" + start + "em 0";
          line.dataset.cutFrom = start;
          line.dataset.cutTo = end;
          return line;
        }) : [];
        view.replaceChildren(...slices);
      }
      if (table && el.classList.contains("body-math-reflowed")) activeTables.add(table);
    }
    // Centering spacers and multiple alignment columns can overflow even when
    // every original SVG fits by itself. Wrap whole cells in source order.
    const overflowing = innerWidth <= 650
      ? tables.filter(table => table.scrollWidth > table.clientWidth + 1) : [];
    for (const table of new Set([...activeTables, ...overflowing])) {
      table.classList.add("body-math-table-wrap");
    }
  }

  function schedule() {
    if (!queued) {
      queued = true;
      requestAnimationFrame(refresh);
    }
  }

  const observer = new ResizeObserver(schedule);
  if (reading) observer.observe(reading);
  addEventListener("resize", schedule, {passive: true});
  document.fonts.ready.then(schedule);
  refresh();
})();
