# L0: 同梱標準部品の契約台帳

状態: **文書形式v1・12公開定義を登録**（2026-09-26）。[第3層の計画](stdlib-roadmap.md)の最初の台帳。対象は同梱の通常 `.qli` 定義であり、封印されたAPIの一覧は[標準ライブラリ構成](standard-library.md)を参照する。機械可読スキーマと自動照合は未実装である。

## 共通項目

- **所属・版・成熟度:** 全項目は通常の `.qli` 定義、契約版1、実験的API。処理系と同じ版で同梱する。公開名・型・所有権・効果・位相・ビット順を変更するときは契約を改訂する。
- **検査の入口:** `check_project` / `compile_project`。全宣言を検査し、通常の量子関数は独立した `verify` に通す。同梱の出所は検査の免除条件にならない。
- **量子契約:** 引数の所有権を消費し、結果に含まれる所有権だけを返す。表に書かない参照系には恒等を掛ける。資源が別であることから積状態を仮定しない。
- **状態の区別:** 各本文は実装済み、下記の有限例は数値検証済み。ソース変換全体の意味保存と一般的なアルゴリズム保証の機械証明は未完了。数値は `f64`、アルゴリズム照合の許容誤差は `1e-12`。
- **容量と能力:** 有限表・レジスタは12ビットまで。静的変換は[展開予算](static-operations.md)を共有する。現行の参照実行が対象で、外部機器への合成費用や動作保証は未評価。

## 登録項目

`B2=(Bit,Bit)`、`B3=((Bit,Bit),Bit)`はこの文書だけの略記。いずれも実際のソース型は有限積である。

| ID・API | 型・効果 | 意味・前提・証拠 | 本文・契約 |
| --- | --- | --- | --- |
| B001 `std::basis::xor2` | `(Bit,Bit)->Bit`、基底関数 | 全入力で `x xor y`。全域だが非単射。基底での利用を許し、直接の量子リフトでは単射性を別検査。 | [basis.qli](../stdlib/src/basis.qli)、[初期仕様](standard-library.md) |
| B002 `std::basis::and2` | 同上 | 全入力で `x and y`。補助への可逆XOR計算の述語として使える。古典測定結果の生成ではない。 | [basis.qli](../stdlib/src/basis.qli)、[構文の基底演算](syntax-v0.md) |
| R001 `std::routines::hadamard2` | `Q<B2>->Q<B2>`、`Unitary` | `H⊗H`。追加の状態前提なし。別用途でGrover・BVから再利用。 | [routines.qli](../stdlib/src/routines.qli)、[部品契約](algorithm-routines.md) |
| R002 `std::routines::reflect_uniform2` | 同上 | `D=2∣s⟩⟨s∣-I`、`∣s⟩=H⊗H∣00⟩`。非公開の全域述語 `nonzero2` と保存するZ作用から補助のゼロ復帰を検査。 | 同上、[反射の位相](algorithm-routines.md#反射の位相) |
| R003 `std::routines::measure_x` | `Q<Bit>->CBit`、`Observe` | X固有値 `(-1)^b` を測定し対象を消費。残系と参照系を含むインストルメント。 | 同上、[部品契約](algorithm-routines.md) |
| R004 `std::routines::measure_z2` | `Q<B2>->(CBit,CBit)`、`Observe` | データ2本を消費。結果の順は左、右で、レジスタの整数重みは1、2。 | 同上 |
| R005 `std::routines::parity_zz` | `(Q<Bit>,Q<Bit>)->((Q<Bit>,Q<Bit>),CBit)`、`Observe` | `P_s=(I+(-1)^s Z⊗Z)/2` による射影測定。データ2本を返しメータを消費。パリティ部分空間内のコヒーレンスを保持。 | 同上、[全体系の意味](algorithm-routines.md#パリティ測定の全体系での意味) |
| F001 `std::transforms::qft2` | `Q<B2>->Q<B2>`、`Unitary` | `F_4∣x⟩=Σ_y exp(2πixy/4)∣y⟩/2`。全入力を対象とし、位相と出力のビット反転を含む。 | [transforms.qli](../stdlib/src/transforms.qli)、[静的操作・QPE](static-operations.md) |
| F002 `std::transforms::qft3` | `Q<B3>->Q<B3>`、`Unitary` | `F_8∣x⟩=Σ_y exp(2πixy/8)∣y⟩/√8`。`x=a+2b+4c`。一般サイズ・近似QFTのAPIではない。 | 同上 |

## 受理・拒否、費用、IR、検証根拠

| ID | 受理／拒否 | 論理費用とIRへの対応 | 検証根拠 |
| --- | --- | --- | --- |
| B001・B002 | 基底式と補助述語で受理。非単射な表の直接量子リフトは拒否。 | 4入力を有限評価。基底関数だけではIR操作を生成しない。利用時に `LiftBasis` または `ComputeUseUncompute` の表になる。 | [compile.rs](../tests/compile.rs)の `bundled_basis_functions_control_a_product_register` と拒否例。 |
| R001 | 2ビットで受理。型違い・再使用を拒否。 | Hを2回、追加補助なし。Split/Gate/Join。 | [algorithms.rs](../tests/algorithms.rs)のBV全隠れ列、Grover全対象。 |
| R002 | 正の一様反射として受理。型違い・資源再使用を拒否。 | Hを4回、述語計算・逆計算、Zを1回、論理補助1本。ComputeUseUncomputeの構造検査。参照実行では因子分解後の作用を使う。 | 同ファイルのGrover反復公式。[static_operations.rs](../tests/static_operations.rs)の `grover_reflection_and_its_negative_are_distinguished_under_control`。 |
| R003・R004 | 観測として受理。Unitaryからの呼び出しと測定後の旧所有権使用を拒否。 | R003はHと測定を各1回。R004は測定2回。MeasureZで対象の所有権を終える。 | algorithms.rsの全3例と `derived_routines_cannot_bypass_ownership_effect_or_basis_type_checks`。 |
| R005 | 別所有のデータで受理。同じ入力2回、返したデータの暗黙破棄を拒否。 | Init0を1回、CNOTを2回、測定1回。生存量子資源はデータ2本とメータ1本。 | algorithms.rsの `parity_measurement_keeps_coherence_within_each_parity_sector` と参照系付きビット反転訂正。 |
| F001・F002 | 指定した積型で受理。型違い、暗黙破棄、制御と標的の別名参照を拒否。 | F001はHを2回、制御付きTを2回、軸順の反転。F002はHを3回、制御付きTを5回、軸順の反転。補助なし。通常呼び出しとApplyUnitaryへ展開。逆・制御化時の軸置換表の費用も予算に算入。 | static_operations.rsのQPE全8位相・非整合位相分布・参照系・静的形式の拒否例。 |

量子アルゴリズムの成功率は、上記の個別操作の型から自動的には得られない。Groverの対象数、BVの線形オラクル、誤り訂正の誤りモデル、QPEの位相精度は、それぞれ[コーパス](algorithm-corpus.md)と例の契約で管理する。

この台帳は公開12定義を追跡する最初の形式である。一般化した `amplify`、`phase_estimate` 等の標準採用、複数の未知評価問題での評価、自動的な証拠スキーマ照合はL2以降の残件とする。
