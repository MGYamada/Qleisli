# 有限コア仕様v0: 決定・適合状況・証明課題

状態: **全構文の規則とその理想健全性Q1〜Q3を紙上で整備、Rustの全受理経路・IR変換との一般的な対応は未証明**（2026-09-26）。[ロードマップ](../ROADMAP.md)のSPEC-0〜2の記録と、SPEC-3・4の進捗を含む。

## 今回の決定

| 項目 | v0として固定した内容 | 後続に置く内容 |
| --- | --- | --- |
| 対象 | `Unit`・`Bit`・有限積、非再帰、静的有限反復 | サイズ付き型、配列、動的反復 |
| 型と所有権 | 基底型と通常型を分離。型木は厳密に比較。`Q<Unit>` と混合タプルも線形 | 型レベルの状態・分離・成功条件の証拠 |
| 効果 | `Unitary ≤ Iso ≤ Observe`。呼び出しに宣言効果を使用。古典入力ごとの量子写像を分類 | 操作値・効果多相・厳密なモナド構造 |
| 基底計算 | 全域な有限表。`not > and > xor`。`do/pure` は捕捉のない単射リフト | 一般の継続、任意の振幅関数 |
| 古典分岐 | 両枝の型木・消費集合、結果位置と生存frameを対応させるφ | 一般の依存型・実行時に変わる資源インターフェース |
| 静的操作 | 同型の単一量子引数を持つ `unitary` の逆・制御・反復。位相を保持 | 操作パラメータ・古典引数付き変換・任意角度 |
| 補助証拠 | 展開後の補助上 `Z/T` 列または空列だけを構成的に認証 | `with0`、一般の借用・作業レジスタ・保存効果署名 |
| 観測 | 測定は所有権を消費して `CBit` のみ。resetは新しい論理ID。破棄は部分跡 | 非破壊測定・実機への割当 |
| stdlib | 封印APIを規範化。通常の同梱定義は同じ検査を通す | 一般の算法骨格と標準採用・互換性方針 |

[言語仕様](language-spec.md)が型・効果・所有権・意味・IR対応、[文法](syntax-v0.md)が字句と構文、[標準ライブラリ構成](standard-library.md)がファイル・モジュール・封印名を規定する。将来計画のメタ型や関数名はv0のAPIに読み替えない。

今回のソース規則は、既存の有限実装を監査して規範として採用したもの。処理系の機能追加は行わず、未決表記の解消と6件の適合テストを追加した。既存のA1〜A3/L0〜L3の成果を保持し、言語仕様優先へ順序を戻した。

## 規範と実装プロファイルの差

| 境界 | 現行実装と扱い |
| --- | --- |
| 有限のサイズ | 数学的な型は任意の有限積。処理系はレジスタ・基底表に12ビット、構文・展開に深さ64、内部型／値に4,096ノード・深さ64、合計作業に1,000,000の上限を置く。超過は診断。 |
| 反復回数 | 規範文法は先頭ゼロのない自然数リテラル。現行パーサの容量は0〜4,096。切り詰めて実行しない。 |
| 静的な制御 | 有限 `ApplyUnitary` への展開を使う。制御を含む合成レジスタも12ビットの上限を受ける。 |
| ファイルシステム | 現行ローダはソースルートを正規化し、配下のシンボリックリンクを拒否する。ソースは `.qli`、モジュールの各要素は予約語と単独 `_` を除くASCII識別子。OSごとのファイル配置は量子意味論の規則ではない。 |
| 検査と実行 | `check_project` は全宣言を検査し、入口の存在を要求しない。`compile_project` / `run` が閉じた `main` の条件を要求する。 |
| ソースと生IR | 生IRの保護付き作業レジスタ・古典演算などはソースv0の全APIではない。生IRが受理する構造をそのままソースで書けるとは限らない。 |
| 補助本体 | `h(h(a))` の恒等性や `adjoint(t,a)` の対角性を一般判定しない。これは容量差ではなく、v0自体が選んだ証拠形式の制限。 |
| 数値実行 | `f64` の非正規化純粋状態アンサンブルを使う。厳密な等式・ゼロ確率の証明ではない。[実行上限と誤差](ir-prototype.md)を参照。 |
| backend | 外部バックエンドは未実装。能力検査を必要条件として定めたことは、実機での実行保証ではない。 |

上限による拒否と型・効果・所有権による拒否を区別する。既知のv0規則はこのプロファイルと有限テストの範囲で照合した。全入力・全プログラムに対する実装適合を証明したものではない。

## 適合例と検証根拠

以下は実行したテストへの対応であり、網羅的な形式証明ではない。`finite_v0_` で始まる6件が今回の追加。

| 規則・意味 | 自動検査の根拠 |
| --- | --- |
| 字句、文法、基底演算の優先順位、構文上限 | [parser](../tests/parser.rs): `basis_operators_have_documented_precedence_and_left_associativity`、`invisible_separators_and_bad_bit_literals_have_precise_errors` 等 |
| import、pub、std封印、名前衝突と循環 | [project](../tests/project.rs): `import_cycles_and_name_collisions_are_rejected`、`unknown_sealed_name_is_not_reinterpreted_as_user_code` 等 |
| 型木の一致、裸のBit拒否、0ワイヤの線形性 | [compile](../tests/compile.rs): `finite_v0_type_shapes_and_zero_wire_ownership` |
| 古典情報の消去と量子効果、宣言効果の保守的な適用 | [compile](../tests/compile.rs): `finite_v0_effects_classify_quantum_maps_and_respect_declarations` |
| 混合値の移動、分解後の古典部分のコピー | [compile](../tests/compile.rs): `finite_v0_mixed_values_move_as_a_whole` |
| 単射性は入力型に依存、基底式の捕捉禁止 | [compile](../tests/compile.rs): `finite_v0_basis_lifts_are_injective_and_closed` |
| 補助上の展開後Z/T列、意味的には対角でも証拠形式外なら拒否 | [compile](../tests/compile.rs): `finite_v0_computed_blocks_require_the_structural_certificate` |
| 基底・静的操作での局所名の優先、移動後も続くスコープ | [compile](../tests/compile.rs): `finite_v0_local_names_shadow_static_callees` |
| 古典分岐の結果位置、枝内生成、呼び出し元のframe | [compile](../tests/compile.rs): `conditional_swap_pairs_different_input_registers`、`branch_created_wires_and_classical_results_merge`、`function_branch_preserves_the_callers_quantum_frame` |
| 測定後再利用・暗黙破棄・非単射・効果違反の拒否 | [compile](../tests/compile.rs): `invalid_source_is_rejected_before_execution`。生IRも [verify](../tests/verify.rs) で拒否検査 |
| Bell部分測定、破棄後の混合状態、resetの新規系 | [sim](../tests/sim.rs): `bell_half_measurement_and_feedback_corrects_other_half`、`discarding_entangled_half_keeps_mixed_residual`、`reset_breaks_bell_correlation_and_returns_new_zero_wire` |
| 静的逆・出力軸順序・制御下の全体位相、反復0も検査 | [static_operations](../tests/static_operations.rs): `inverse_reverses_noncommuting_gates_and_output_axis_reordering`、`computed_zero_width_phase_survives_inverse_and_control`、`static_forms_reject_bad_names_effects_types_and_ownership` 等 |
| 生成元に依存しない独立IR検査 | [verify](../tests/verify.rs) の27件と [static_operations](../tests/static_operations.rs) の `raw_finite_circuit_validation_rejects_forged_certificates` |
| 同梱定義の合成と算法ごとの契約 | [algorithms](../tests/algorithms.rs)、[static_operations](../tests/static_operations.rs)、[order_finding](../tests/order_finding.rs)。成功条件・参照系・前提外の反例を個別に検査 |

### 検査結果（2026-09-26）

- `cargo test --test compile finite_v0`: 追加6件成功。
- `cargo test --all-targets`: **108件成功**。compile 23、parser 8、project 8、verify 27、sim 13、algorithms 7、static_operations 12、order_finding 10。
- `cargo fmt --check`、`cargo clippy --all-targets -- -D warnings`、`git diff --check`: 成功。
- README・ROADMAP・AGENTS・docs内のMarkdownローカルリンク先を確認し、欠落なし。

## SPEC-3の資源規則と実装対応

[Source resource rules for finite core v0](source-resource-rules.md)を英語の正本として追加した。混合値、移動済み束縛、一時結果、関数の外側のframe、分岐の結果位置とφ、0ワイヤの所有権を一つの規則系にまとめた。新しい構文や受理規則は導入していない。[形式化の概要](formal-core.md)も英語化した。

| 項目 | 今回の到達点 | 残る境界 |
| --- | --- | --- |
| 資源判断 | 所有権の所在を束縛・一時結果・レジスタ対応の間の分割として定義 | ソース仕様・Rust実装との一般的な対応は未証明 |
| R1 | 明記した規則系の資源不変量と関数境界の帰結を紙上で証明。所有権計数の射影モデルは別途Leanで検証 | 紙上規則全体の機械検証、全Rust実行経路の形式検証ではない |
| φと補助 | 全生存スロットを覆うφの軸改名、限定Z/T証拠のゼロ復帰を局所補題として記述 | 一般のソース意味保存・量子的健全性は未完了 |
| 実装監査 | 規則・Rust関数・既存／追加検査の対応表を記録 | 有限例の照合は完全な対応証明ではない |

追加した `tests/compile.rs` の7件は `resource_rules_` で始まる。評価途中の混合引数・タプル要素とBell参照の保持、混合結果の位置対応、0ワイヤの結果と呼び出し元frameのφ、片側reset後の相関と古典履歴、入れ子の古典φを照合した。最後の検査には、消費集合の不一致・同名再束縛による暗黙喪失・`Q<Unit>`の破棄・混合値の複製・関数引数の未処理という6つの拒否例を含む。

検査結果（2026-09-26）:

- `cargo test --test compile resource_rules_`: 追加7件成功。
- `cargo test --all-targets`: **115件成功**。compile 30、parser 8、project 8、verify 27、sim 13、algorithms 7、static_operations 12、order_finding 10。
- `cargo fmt --check`、`cargo clippy --all-targets -- -D warnings`、`git diff --check`: 成功。
- README・ROADMAP・AGENTS・docsのローカルリンク239件に欠落なし。資源規則の対応表が参照する追加テスト7件の存在も確認。

紙上証明そのものをRustテストに合格したとは扱わない。上の108件は仕様v0確定時の履歴であり、今回の7件を含まない。

## Leanによる補助検証の区切り

[英語の定理台帳](lean-resource-proof.md)にRA-1〜RA-10の機械検証済みの範囲と前提を記録した。混合値・`Q<Unit>`、局所資源遷移、frame、全所有権を覆うφ、合成を対象とし、13件の境界補題を含む。Lean／Mathlibは4.30.0と依存コミットに固定し、ビルドと公理監査をCIへ追加した。CI定義の追加とGitHub上での実行成功は区別する。

名前・効果・古典スコープ・発行済みID履歴・Rust実装との対応・量子意味論は未移植であり、R1全体を機械検証済みとはしない。Leanは本題の言語仕様を支える補助とし、当面は対象を拡大せず、下記の仕様・意味論・IR対応を優先する。

ローカル検査（2026-09-26）: Leanビルドと449宣言の公理監査が成功。Rust全115件・fmt・Clippyも成功。文書リンク263件とLeanの5モジュールのimport網羅を確認した。独自公理・未証明穴・native評価の一時的な混入例は公理監査で拒否された。

## ソース意味論とIR対応の局所証明

[Source values, calls, and branch semantics](source-semantics.md)を追加し、混合値・字句環境・順序付き量子インターフェース・非正規化の古典量子状態を定義した。S1〜S4は、評価済み値の代入、相関するframe、古典分岐と同時φ、構造的IR変換についての前提付きの紙上証明である。部分式と各操作の正確な意味対応、資源・名前・スコープの前提を明示し、全ソース／Rust実行経路への一般化は未完了とした。

本番の規範文書[language-spec.md](language-spec.md)を英語化し、型・効果・所有権・受理／拒否・IR方針と状態を維持した。既存の日本語節アンカーも保持する。Leanは変更していない。

追加した[4件の回帰検査](../tests/source_semantics.rs)は、測定引数の評価回数と同じ古典IDを複数の仮引数へ渡すこと、呼び出し先の名前解決と外側束縛の復元、T/ZTの位相とBell相関、`Q<Unit>`を含む量子・古典φの順序独立性を確認する。独立に求めた確率分布と照合し、単なる処理系同士の一致で合格とはしない。実装の修正を要する不具合は今回の監査では見つからなかった。

検査結果（2026-09-26）:

- `cargo test --test source_semantics`: 追加4件成功。
- `cargo test --all-targets --quiet`: **119件成功**。既存115件に上記4件を追加。
- `cargo fmt --check`、`cargo clippy --all-targets -- -D warnings`、`git diff --check`: 成功。
- `python3 scripts/check_docs.py`: ローカルリンク285件と既存Leanの5モジュールのimport網羅を確認。
- 英語化した仕様の既存12アンカー（表題と11節）、仕様・意味論のMarkdown表を確認。

上の115件とLeanの公理監査は前の到達点の記録である。今回の数式は条件付きの紙上証明であり、RustテストやLeanで機械検証したとは扱わない。

## 有限静的変換の演算子対応

[Exact semantics of finite static transformations](static-semantics.md)のF1〜F5で、順序付き軸の再配置、平坦化と最終出力置換、限定補助計算の位相、逆・反復・量子制御について、位相を含む正確な演算子等式を紙上で示した。単一量子入出力・古典ポートなし・独立検証・対応する構成子への限定を前提とする。検証済み生IRのすべてを平坦化できるとは主張しない。

[静的操作の契約](static-operations.md)を英語の正本として整備し、対象名の解決を入力評価後の環境で行うこと、使い終わったローカル名も関数を隠すこと、正確な型木と宣言効果、ゼロ反復と両制御枝の検査、入力効果と待機中の所有権を推論規則へ明記した。以前の6アンカーと歴史的な検証記録を保持する。受理規則・公開API・Leanの対象範囲は変えていない。

[tests/static_semantics.rs](../tests/static_semantics.rs)は`Z[zeta,1/2]`の整数係数を用い、12個のコンパイル済み回路の38入力列・186行列成分を独立した解析式と厳密に比較する。非可換な位相と置換、非隣接軸への制御の再配置、3-cycleの返却順、ゼロ反復、入れ子の0/1制御、`Q<Unit>`のスカラー位相を含む。4件の演算子検査と1件の算術ヘルパー検査を追加した。処理系の逆変換や確率だけの一致を期待値に使っていない。

検査結果（2026-09-26）:

- `cargo test --test static_semantics`: 追加5件成功。
- `cargo test --all-targets --quiet`: **124件成功**。既存119件に上記5件を追加。
- `cargo fmt --check`、`cargo clippy --all-targets -- -D warnings`、`git diff --check`: 成功。
- `python3 scripts/check_docs.py`: ローカルリンク319件と既存Leanの5モジュールのimport網羅を確認。
- 英語化した静的契約の既存6アンカー、変更した8文書の表27個、演算子の対応表が参照する4テスト名を確認。

対象実装に修正を要する不具合は見つからなかった。これらは数学的アルゴリズムの条件付き紙上証明と有限のRust回帰検査であり、F1〜F5を機械検証した結果や全ソースの健全性証明ではない。119件以前の件数は各到達点の履歴として保持する。

## 型・効果・名前・スコープの推論規則

[Type, effect, name, and scope judgments](source-typing-rules.md)を英語の規範補遺として追加した。型形成、名前と宣言、全基底式、全通常式、引数列、パターン、文、ブロックを資源規則R1へ接続し、全AST構成子を対応表で照合した。型木、引数個数、宣言効果、消費済み名の隠蔽、calleeの定義元モジュール、完全なφ、補助計算の構造的証拠を明示する。新しい構文・API・受理規則は加えていない。

T1は基底式の型付き全域性と型の一意性、T2は結果型・構文的効果・残存束縛状態の一意性と消費済み外側所有権の非復活、T3は宣言効果の保守性と条件付きのIR効果上界を示す。生成IRの一意性は主張しない。レビューで、同じ古典値のφには再利用と新規出力の選択肢があることを確認し、定理の範囲を型・効果・束縛状態に限定した。いずれも紙上証明であり、Rust実装の形式検証や量子的健全性の完成とはしない。

[追加6テスト](../tests/source_judgments.rs)は、宣言効果の伝播、スコープとspent marker、厳密な積型と述語の左結合定義域、基底文脈の分離、補助計算の証拠、複数モジュールの名前解決を確認する。展開後にIRの効果が弱くなる例も照合し、独立IR検証がソースの宣言効果検査を代替するとは扱わない。実装修正が必要な不具合は見つからなかった。

検査結果（2026-09-26）:

- `cargo test --test source_judgments`: 追加6件成功。
- `cargo test --all-targets --quiet`: **130件成功**。既存124件に上記6件を追加。
- `cargo fmt --check`、`cargo clippy --all-targets -- -D warnings`、`git diff --check`: 成功。
- `python3 scripts/check_docs.py`: ローカルリンク351件と既存Leanの5モジュールのimport網羅を確認。
- 7種類のAST列挙型・全34構成子とBlockの対応、追加テスト名6件、変更した8文書の表29個、規範仕様の既存12アンカーを確認。

構文上の全場合を提示したことと、規則系・仕様・Rustの全受理経路の対応を証明したことは異なる。後者、量子意味論の一般定理、全ソースからIRへの意味保存は残件である。Leanは変更していない。以前の検査件数は各到達点の履歴として保持する。

## 数学的なソース導出の理想健全性

[Ideal soundness of the finite source derivation system](source-soundness.md)に、Q1（純粋な古典結果の決定性・等長性／ユニタリ性）、Q2（有限適応Kraus合成・公開結果への集約）、Q3（全ソース導出のインストルメント健全性）を追加した。型・資源規則の成功した数学的導出と正確な原始意味を対象とし、結果だけでなく残る環境とframeを含む完全なインターフェースで帰納する。任意の参照系、履歴ごとに異なる中間空間、確率ゼロの枝、古典情報の非可逆な処理も含む。

紙上定理は、Rustの受理と導出の対応や生成IRの意味保存を前提にして循環的に証明していない。これらの実装対応は別の残件である。静的な対象のユニタリ性は依存順の帰納から得て、単に「別のIRがユニタリと検証された」ことで元のソースと一致するとは扱わない。

[Kraus.lean](../lean/Qleisli/Kraus.lean)を追加し、有限の厳密な複素行列に対する5補題を検証した。`Complete A`は`sum_i A_i† A_i=I`であり、等長な出力対応と、第一結果に応じて後段が変わる適応合成が完全性を保つ。中間・出力の行列型は固定し、紙上定理の正値性・跡・参照系・ソース帰納まではLeanで証明していない。[定理台帳](lean-resource-proof.md)にKA-1〜KA-5と前提を記録した。

[追加4テスト](../tests/source_soundness.rs)は、7個のコンパイル例の解析的な分布と全確率を照合する。隠した履歴の位相を干渉させないこと、適応観測の非一様な結合分布と周辺分布、GHZ位相とreset後の喪失、実行されない確率ゼロの枝を検査した。許容誤差は`1e-12`で、比較前の再正規化は行わない。実装修正を要する不具合は見つからなかった。

検査結果（2026-09-26）:

- `cargo test --test source_soundness`: 追加4件成功。
- `cargo test --all-targets --quiet`: **134件成功**。既存130件に上記4件を追加。
- `cargo fmt --check`、`cargo clippy --all-targets -- -D warnings`、`git diff --check`: 成功。
- `lake build`と`lake env lean -DwarningAsError=true Audit.lean`: 成功。**456宣言**で許可された3公理のみを使用。
- `python3 scripts/check_docs.py`: ローカルリンク377件とLeanの6モジュールのroot import網羅を確認。
- 10文書の表32個、新規テスト名4件、Lean補題5件と台帳、規範仕様の既存12アンカーを確認。

Leanのツールチェーン・依存版、ソースの受理規則、言語形式・標準APIは変更していない。以前の「Leanは変更していない」と検査件数は、それぞれの過去の到達点を記したもの。現在の到達点は規則系の紙上健全性と限定した行列補題であり、Rust処理系全体の形式検証ではない。

## 次に証明すること

次の課題は仕様v0を変更せず、その契約を成立させる根拠を完成させる作業である。矛盾・反例が見つかった場合は仕様変更として明記する。

1. **推論規則と実装の対応:** 構文全体の型・効果・名前・スコープ規則と資源規則を、v0およびRustの全受理経路へ対応づける。T1〜T3と値・環境の意味論を基に、暗黙frame・束縛スナップショット・スコープの一般的な対応を示す。
2. **資源安全性の接続:** 規則系の紙上定理R1を、ソース検査器とIR検証器のすべての受理経路へ接続する。無断複製・暗黙喪失・測定後利用の不在を、処理系について証明済みとはまだしない。
3. **理想健全性の処理系への移送:** 明示した規則系にはQ1〜Q3の紙上定理を得た。Rustの全受理経路がその型・効果・資源・意味の前提を満たすことを示し、実装での健全性保証へ接続する。
4. **ソース→IRの意味保存:** 構造的変換の局所証明S1〜S4と静的変換F1〜F5を合成し、その型・効果・名前・軸順・証拠の前提を全経路で満たすことを示す。各数学的アルゴリズムの局所証明と、Rust実行経路への一般的な対応は区別する。
5. **実装への接続:** 検証器の各受理条件を証明の前提と対応づける。[有限IRの紙上証明](finite-core-proof.md)は前提付きの議論であり、Rust実装の正しさやソース全体の定理を自動的に与えない。

これらの完成前は、段階1全体を完了にせず、コンパイル成功を証明済みの物理的妥当性とも呼ばない。個別算法の正答・成功確率、ホスト後処理、実機のノイズと較正は、さらに別の検証対象である。
