# Isabelle proofs supporting Questions 1–5

The two sessions build with Isabelle2025-2 and its bundled HOL, HOL-Analysis and HOL-Probability libraries.

From this directory:

```sh
isabelle build -b -D . -o quick_and_dirty=false Thermal_Logical_Core Thermal_Analytic_Core
```

[Verification record](verification.txt) lists the checked results and the source-file hashes. The theory files contain the mathematical definitions and proofs.

## Questions and formal results

| Question | Mathematical result | Source and principal result |
|---|---|---|
| Q1 | Positive normalized density, smoothness, inverse-coordinate solution, maximal domain and positive probability of undefined flow at every nonzero parameter | [Gaussian_Strip](analytic/Gaussian_Strip.thy), [Thermal_Smoothness](analytic/Thermal_Smoothness.thy), [Gaussian_Inverse_Flow](analytic/Gaussian_Inverse_Flow.thy), [Thermal_Measure](analytic/Thermal_Measure.thy): `original_undefined_positive_probability` |
| Q2 | Two probability-preserving measurable groups, local agreement, and a strictly positive correlation gap | [Periodic_Group](analytic/Periodic_Group.thy), [Reflection_Group](analytic/Reflection_Group.thy), [Concrete_Correlation](analytic/Concrete_Correlation.thy): `concrete_correlations_distinct` |
| Q3 | Almost-everywhere reading correspondence, restricted selections, Gibbs calibration, affine-clock obstruction, record and sampling error bounds, apparatus-dependent admissible scales | [Observable_Correspondence](analytic/Observable_Correspondence.thy), [Flow_Calibration](analytic/Flow_Calibration.thy), [Stationary_Clock](analytic/Stationary_Clock.thy), [Observation_Bounds](logical/Observation_Bounds.thy), [Sampling_Ambiguity](logical/Sampling_Ambiguity.thy) |
| Q4 | Quantum–classical correlation error and the additional measurement-error bound | [Measurement_Integral_Bounds](analytic/Measurement_Integral_Bounds.thy): `finite_measure.quantum_measurement_error` |
| Q5 | Positive undefined probability after nonzero rescaling; premise substitution, finite derivability and alternative inference routes | [Thermal_Measure](analytic/Thermal_Measure.thy): `rescaled_original_undefined`; [Dependency_Grounding](logical/Dependency_Grounding.thy): `grounded_iff_reached`, `ungrounded_cycle`, `selected_substitution_leaves` |

The detailed document specifies the correspondence to the questions in its section “Formal verification and its relation to the questions.” The Q2 machine-checked witness uses a bounded position observable and a rectangle indicator; the text also proves a smooth-observable witness. The Q3 formalization proves the differential/Gibbs equivalence on an open connected coordinate domain; the text applies uniqueness of smooth integral curves to obtain the local-flow correspondence. The mapping of the source article's statements to the premise system is given with the quoted equations and source locations in the detailed document.

## 日本語

この証明資産はQ1〜Q5の数学的根拠に対応する。上表から各定義・仮定・結論・証明へ進める。解析系と論理系の2セッションを、上記の命令で検証する。

Q2の機械検証では有界な位置観測量と長方形の指示関数を用いる。本文は滑らかな観測量対も構成している。Q3では、開連結な座標領域上の微分条件とGibbs形の同値を形式化し、本文で積分曲線の一意性を適用して局所流との対応を得る。原論文の式・言明と前提系との対応は、詳細文書の原典位置を伴う分析に示す。
