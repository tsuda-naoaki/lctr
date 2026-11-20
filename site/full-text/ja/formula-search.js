"use strict";
{
  const index = globalThis.lctrPrivateFormulaData;
  const field = document.querySelector("#formula-query");
  const count = document.querySelector("#formula-count");
  const list = document.querySelector("#formula-results");
  const normalize = source => source
    .replace(/%\r?\n[ \t]*/g, "")
    .replace(/\\mathchar\s+44\s*\\relax\s*\\allowbreak\b/g, ",")
    .replace(/(\\[A-Za-z]+)\s+(?=[A-Za-z])/g, "$1\u0000")
    .replace(/\s+/g, "")
    .replace(/([_^])\{([0-9A-Za-z])\}/g, "$1$2")
    .replace(/\u0000/g, " ");
  const element = (tag,text) => {
    const node = document.createElement(tag);
    if (text !== undefined) node.textContent = text;
    return node;
  };
  const render = () => {
    const query = normalize(field.value.trim());
    list.replaceChildren();
    if (!query) { count.textContent = ""; return; }
    const terms = index.rows.filter(row => row[3].includes(query) || row[4].includes(query));
    count.textContent = terms.length + " " + count.dataset.label + (terms.length > 50 ? " (50)" : "");
    for (const [href, svg, tex, , , page, id] of terms.slice(0,50)) {
      const row = element("li"), link = element("a",page+" #"+id), im = element("img");
      link.href = href; im.src = svg; im.alt = tex;
      row.append(link, im, element("code",tex));
      list.append(row);
    }
  };
  field.addEventListener("input",render);
}
