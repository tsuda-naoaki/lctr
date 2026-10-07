LCTR source-survey finite computations

Run with Python 3 (standard library only):
    python3 verify.py --output computed.json
The result reproduces results.json. The default input is survey.json beside
verify.py; --input PATH selects another dataset of the same schema.

survey.json records the supplement's source numbers, time-content indices,
claim requirements, transfer incidences, result incidences and admissible
transfer sets. Its structural classifications and statement-cohort memberships
are the source-audit data stated in the paper.

The computations are:
* Local temporal reach: start with no time contents and apply a transfer when
  all its temporal inputs have been reached. Recorded claim and auxiliary
  conditions are available in this projection.
* A generation upper bound: restrict transfers to the declared initial claim
  subset, while granting auxiliary conditions. A zero upper bound certifies
  zero generated time contents. If even the unrestricted projection is empty,
  every claim-restricted projection is empty and an initial subset is redundant.
  A positive bound is reported as a bound; the exact generation total is null.
* Structure signatures: the positive-length transitive closure of the union
  of input/output pairs supplies dependency incidences. Member signatures use
  direct input/output incidences. Both include incidence in result inputs.
* Result support: each result uses its own admissible transfer set. The output
  reports whether the result's temporal inputs are reachable with no supplied
  time contents under the source-evidence projection.

Two implementations agree on each all-input closure (repeated scans and a
worklist) and each dependency closure (graph searches and a bit matrix).

For the accompanying dataset, the computations give 72 sources, 2266 time
contents, 820 transfers and 1411 results. All 72 sources contain certified
primitive time contents; 10 sources have local reach, totaling 57 contents.
Every generation upper bound is zero. Structural-type counts in schema order
are 642, 1313, 8, 284 and 19. Statement-cohort counts are 18 and 13.

日本語

本検査器は、補遺の時間内容・移送・結果の有限データから、局所到達、
生成の上限、構造署名および結果の時間的入力の到達性を計算する。
構造分類と資料の言明群への所属は、論文の資料監査で定めた入力データである。

局所到達は、資料の主張・補助条件を与え、時間内容を空集合から出発させて、
すべての時間的入力がそろった移送の出力を順次加えて求める。
生成の上限は、主張を生成初期集合へ制限し、補助条件を与えて計算する。
上限が0なら生成数は0と確定する。主張を制限しない射影でも空集合なら、
どの主張制限でも空集合なので生成初期集合の指定は不要である。
上限が正の場合は上限として報告し、生成数の確定値はnullとする。

構造署名の依存関係は、移送の時間入力と時間出力の直積の和をとり、
長さが正の経路について推移閉包を求める。構造の元の署名には直接の入出力、
依存項の署名にはこの経路関係を用い、双方に結果入力への出現を加える。
結果の到達判定は、各結果で許される移送集合を用いる。

全入力を必要とする閉包は反復走査と待ち行列、依存関係の閉包は経路探索と
ビット行列という各2方式で照合する。同梱データの計算結果は72資料、
2266時間内容、820移送、1411結果。72資料すべてに原始時間があり、
局所到達は10資料・57項目、生成の上限は全資料で0となる。
構造型の件数はスキーマ順に642・1313・8・284・19、言明群の件数は18・13。
