/* Finite order-representation example; no physical duration is assigned. */
"use strict";
(function (root) {
  const scenarios = {
    complete: [[0, 1], [1, 2]],
    incomplete: [[0, 1]],
    cycle: [[0, 1], [1, 2], [2, 0]]
  };
  function evaluate(name, spacing = "even") {
    if (!Object.hasOwn(scenarios, name)) throw new Error("Unknown comparison set");
    if (!["even", "uneven"].includes(spacing)) throw new Error("Unknown coordinates");
    const reach = Array.from({length: 3}, () => [false, false, false]);
    for (const [a, b] of scenarios[name]) reach[a][b] = true;
    for (let k = 0; k < 3; k++) for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) {
      reach[i][j] ||= reach[i][k] && reach[k][j];
    }
    const acyclic = reach.every((row, i) => !row[i]);
    const total = acyclic && reach.every((row, i) => row.every((_, j) => i === j || row[j] || reach[j][i]));
    return {reach, acyclic, total, coordinates: total ? (spacing === "even" ? [0, 1, 2] : [0, 1, 4]) : null};
  }
  if (typeof module !== "undefined" && module.exports) module.exports = {evaluate};
  if (!root.document) return;
  const demo = root.document.querySelector("[data-time-demo]");
  if (!demo) return;
  const ja = root.document.documentElement.lang === "ja";
  const copy = ja ? {
    complete: ["A ≺ B ≺ C", "比較可能な3類", "この例では、同じ類に同じ数を、前後関係に小さい数・大きい数を対応させられます。数の間隔を変えても、同一性と順序は変わりません。"],
    incomplete: ["A ≺ B　 A ? C　 B ? C", "非比較可能性が推移しない", "AとC、CとBは比較不能ですが、AとBには順序があります。比較不能な対を同じ数に対応させると、AとBまで同じ数になり、A ≺ Bを表せません。順序座標商を作る条件が満たされません。"],
    cycle: ["A ≺ B ≺ C ≺ A", "比較結果に循環", "この循環を推移的に閉じると、A ≺ A が生じます。厳密順序の条件を満たさず、この比較結果に対応する順序表現は得られません。"]
  } : {
    complete: ["A ≺ B ≺ C", "Three comparable classes", "The same class receives the same number, and the order is represented by smaller and larger numbers. Changing the gaps preserves both identity and order."],
    incomplete: ["A ≺ B　 A ? C　 B ? C", "Incomparability is not transitive", "A and C are incomparable, as are C and B, yet A precedes B. Giving incomparable pairs the same number would also identify A and B, contradicting A ≺ B. The condition for forming the order-coordinate quotient fails."],
    cycle: ["A ≺ B ≺ C ≺ A", "A cycle in the comparisons", "The transitive closure of this cycle includes A ≺ A. The comparisons fail the strict-order condition, so they do not support an order representation."]
  };
  function update() {
    const name = demo.querySelector('[name="comparison"]:checked').value;
    const spacing = demo.querySelector('[name="coordinates"]:checked').value;
    const result = evaluate(name, spacing);
    const [relation, title, description] = copy[name];
    demo.querySelector("[data-relation]").textContent = relation;
    demo.querySelector("[data-result-title]").textContent = title;
    demo.querySelector("[data-result-description]").textContent = description;
    demo.querySelector("[data-coordinate-controls]").disabled = !result.total;
    demo.querySelector("[data-coordinates]").textContent = result.coordinates
      ? "A ↦ " + result.coordinates[0] + "　B ↦ " + result.coordinates[1] + "　C ↦ " + result.coordinates[2]
      : (ja ? "実数値による順序表現：不成立" : "Real-valued order representation: not established");
    demo.querySelector("[data-result]").dataset.state = name;
  }
  demo.querySelector("[data-demo-controls]").hidden = false;
  demo.addEventListener("change", update);
  update();
})(typeof globalThis !== "undefined" ? globalThis : this);
