# 有限コア仕様v0: 決定・適合状況・証明課題

状態: **規範仕様を確定、実装と有限例を照合、一般証明は未完了**（2026-09-26）。[ロードマップ](../ROADMAP.md)のSPEC-0〜2の記録。次の優先工程はSPEC-3・4である。

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

## 次に証明すること

次の課題は仕様v0を変更せず、その契約を成立させる根拠を完成させる作業である。矛盾・反例が見つかった場合は仕様変更として明記する。

1. **推論規則の完全化:** 古典文脈・基底文脈・線形束縛と一時結果の区別、関数引数への代入、混合タプル、frame、φの新規IDと位置対応を一つの形式体系へ展開する。
2. **資源安全性:** 型付けの導出から、各経路の一度だけの消費、無断複製・暗黙喪失・測定後利用の不在を示す。
3. **理想意味論の健全性:** 原始操作の正確な意味を仮定し、単射リフト・位相保持の静的操作・限定補助証拠・古典分岐・適応合成について、純粋操作の等長性／ユニタリ性とインストルメントの完全正性・総和の跡保存を示す。
4. **ソース→IRの意味保存:** 展開・軸順序・分岐のφ・静的操作変換が、相関するframeと外部参照系を含めた意味を保つことを示す。
5. **実装への接続:** 検証器の各受理条件を証明の前提と対応づける。[有限IRの紙上証明](finite-core-proof.md)は前提付きの議論であり、Rust実装の正しさやソース全体の定理を自動的に与えない。

これらの完成前は、段階1全体を完了にせず、コンパイル成功を証明済みの物理的妥当性とも呼ばない。個別算法の正答・成功確率、ホスト後処理、実機のノイズと較正は、さらに別の検証対象である。
