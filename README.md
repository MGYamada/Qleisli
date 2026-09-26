# Qleisli

Qleisli は、Rust で処理系を構築する純粋関数型量子プログラミング言語です。量子データを複製不能な所有資源とし、プログラムを古典値と量子資源の、効果付きで合成可能な変換として捉えます。

**現状は設計と処理系の試作段階です。** [有限コア言語仕様v0](docs/language-spec.md)を確定し、実装プロファイルの容量上限内で、名前解決、型・効果・所有権検査、IR 生成、独立した IR 検証、参照実行を接続しました。Bell・位相オラクル・フィードバックに加え、[構造化した小規模Grover・Bernstein–Vazirani・ビット反転訂正](docs/algorithm-routines.md)を実行して期待分布を確認できます。同梱の通常定義は `stdlib/src/basis.qli`、`stdlib/src/routines.qli`、`stdlib/src/transforms.qli`、`stdlib/src/arithmetic.qli` です。[静的な逆・制御・有限反復と小規模QPE](docs/static-operations.md)も実装しました。[対応範囲](docs/frontend-v0.md)には制限があり、処理系全体の健全性証明や外部バックエンドは未完成です。

## 現在の優先順位: 言語仕様

ロードマップを**段階1へ戻しました**。[資源規則R1](docs/source-resource-rules.md)、[型・効果・名前・スコープ規則](docs/source-typing-rules.md)、[ソースの局所意味論](docs/source-semantics.md)、[静的変換の証明](docs/static-semantics.md)を整え、[明示した数学的規則系の理想健全性Q1〜Q3](docs/source-soundness.md)を紙上で示しました。純粋操作の等長性／ユニタリ性と、観測・適応合成の完全正性・総和の跡保存を対象とします。

所有権モデルに加え、Kraus完全性の合成に関する5補題を[Leanで検証](docs/lean-resource-proof.md)しました。Leanは必要な局所補題を支える役割に留めます。[適合状況](docs/specification-status.md)には実装監査と回帰検査を記録しています。数学的規則とRustの全受理経路の対応、ソースからIRへの一般的な意味保存は未証明です。サイズ付き型・操作パラメータ化・アルゴリズムとstdlibの拡張は後続工程です。

## 第1開発目標: AI時代の量子言語

AI が生成したコードも人間が書いたコードも、同じ型・効果・所有権検査と IR 検証に通す。まず資源の安全性を、その上で理想意味論における量子操作の健全性を保証することを目指す。プロトコルやアルゴリズムの正しさ、実機での動作は別の検証対象とする。保証の条件と到達基準は[開発目標](docs/ai-era-goal.md)に記す。

## 第2開発目標: 量子アルゴリズムの構造化

「量子アルゴリズムは何によって構成されているか」を問い、**既存アルゴリズム → 共通構造 → 言語抽象化 → 新しいアルゴリズム**という循環を作る。可逆計算、反射、制御付き冪、有限反復、観測量、古典フィードバックを、型・所有権・効果・証拠の契約へつなぐ。

[初期コーパス20項目](docs/algorithm-corpus.md)と[設計契約・到達基準](docs/algorithm-structure-goal.md)を整え、最初の5部品と固定幅QFT2/3を通常の `.qli` として同梱しました。さらに[固定幅算術とN=15の位数推定・古典因数抽出](docs/arithmetic-order-finding.md)を実装しました。高階のコンビネータ、厳密なモナド構造、一般のQPE・Shor・VQE/QAOAは今後の課題です。

## 第3層の将来計画: 量子アルゴリズムの標準語彙

第1層の検証基盤、第2層の構造抽出を土台に、アルゴリズムの概念を**意味論的契約を持つ標準ライブラリ**へ育てます。原始操作、構造コンビネータ、量子データ構造、算術、変換、アルゴリズム骨格、ハイブリッド計画の7領域を整理します。

[将来計画](docs/stdlib-roadmap.md)に、`amplify`・`phase_estimate`・`simulate`・`estimate` の契約案、標準への採用基準、AIが提案したパターンの検証経路、着手条件を記しました。同梱12公開定義の[契約台帳v1](docs/stdlib-contracts.md)と有限な静的操作を整備しました。一般化したアルゴリズム骨格のAPIは未実装です。

## 設計の境界

- 自由ベクトル空間モナドはコヒーレントな計算の数学的な由来です。資源と効果を追うプログラム合成は Kleisli 的に設計しますが、任意の `bind` を安全な実行 API として公開しません。
- `Q<A>` は量子レジスタの操作権です。すべての効果で線形に扱い、暗黙の破棄を許しません。基底添字の共有は、全体の写像が等長なら許します。
- 測定、リセット、破棄は `observe` 効果に置きます。初期版の測定は量子ハンドルを消費して古典結果だけを返します。補助量子ビットの純粋な解放には、全入力に対するゼロ復帰の静的証拠が必要です。
- [未解決の中核課題](docs/design-philosophy.md)は、所有権による操作権の管理と、絡み合った全体系について必要な証拠をどう合成するかです。
- Rust の借用検査は処理系のメモリ安全性を担います。Qleisli の所有権・効果・構成子の条件は専用のフロントエンドと IR 検証器が検査します。検査器実装の一般的な正しさの証明は別の課題です。

## 文書

1. [設計思想](docs/design-philosophy.md): 固定する原理と、構文に残す自由度。
2. [AI時代の量子言語という開発目標](docs/ai-era-goal.md): 健全性の階層と証明目標。
3. [ROADMAP.md](ROADMAP.md): 段階0から実装までの順序と完了条件。
4. [量子言語としての成立条件](docs/quantum-language-requirements.md): 仕様と実装が満たすべき条件。
5. [`.qli` と標準ライブラリの構成](docs/standard-library.md): 段階0の構成決定。
6. [有限コア言語仕様v0](docs/language-spec.md): 規範となる型・効果・所有権・意味論。
7. [有限コアの形式化](docs/formal-core.md): 定理の形、構成子の意味、証明の残件。
8. [`.qli` 構文v0](docs/syntax-v0.md): 規範文法、名前とスコープ、静的な拒否例。
9. [Rust IR 検証器の試作](docs/ir-prototype.md): 実装済みの検査、信頼境界、未達成の保証。
10. [有限 IR の紙上証明](docs/finite-core-proof.md): 現行構成子の量子意味と、実装との対応に残る検証義務。
11. [`.qli` フロントエンドの初期実装](docs/frontend-v0.md): 実行できる部分集合、検査規則、診断、実行例。
12. [量子アルゴリズムの構造化という第2目標](docs/algorithm-structure-goal.md): 共通構造、型・合成の契約、実装順。
13. [アルゴリズム構造のコーパス](docs/algorithm-corpus.md): 20項目の一次資料、入力モデル、前提、未対応部分。
14. [有限のアルゴリズム部品](docs/algorithm-routines.md): 同梱API、3つの構造化例、数式とテストの対応。
15. [第3層・標準ライブラリの将来計画](docs/stdlib-roadmap.md): 7領域、意味論的契約、採用・保守・AI探索への還流。
16. [有限の静的操作とQPE](docs/static-operations.md): 逆・制御・反復、有限IR、固定幅QFTとQPEの検証。
17. [同梱部品の契約台帳](docs/stdlib-contracts.md): 公開12定義の状態・前提・意味・IR・費用・検証根拠。
18. [有限算術と位数推定](docs/arithmetic-order-finding.md): 全空間上の可逆演算、N=15、古典再構成と再試行。
19. [仕様v0の適合状況](docs/specification-status.md): 確定事項、実装上限、検証根拠、証明の残件。
20. [ソース資源判断と紙上証明](docs/source-resource-rules.md): 英語の規則系、混合値と一時結果、関数のframe、φ、資源不変量R1と実装監査。
21. [Leanの資源・Kraus証明台帳](docs/lean-resource-proof.md): 機械検証した所有権モデルと局所行列補題、その前提・未移植部分・再現手順。
22. [ソースの値・環境・関数・分岐の意味論](docs/source-semantics.md): 混合値、評価済み値の代入、相関するframe、φの局所証明とIR対応。
23. [有限の静的変換の正確な意味](docs/static-semantics.md): 平坦化・軸順・逆・制御・反復・限定補助位相の紙上証明、Rust対応、厳密行列の回帰検査。
24. [型・効果・名前・スコープの推論規則](docs/source-typing-rules.md): 全AST構成子の規則、基底計算の全域性、束縛の射影、宣言効果、実装との対応と残件。
25. [ソース規則系の理想健全性](docs/source-soundness.md): 純粋性・等長性／ユニタリ性、観測・適応合成・履歴の隠蔽、参照系を含む紙上証明Q1〜Q3。

## Rust 開発環境

Rust 2024 edition に対応する **Rust 1.85 以降**と、Cargo・rustfmt・Clippy を使用します。この crate は現在外部依存を持ちません。リポジトリのルートで次を実行します。

```sh
cargo test --all-targets
cargo fmt --check
cargo clippy --all-targets -- -D warnings
```

`Cargo.lock` と `target/` は生成物として Git から除外します。テストはパーサ、モジュール解決、ソースコンパイラ、IR 検証器、参照シミュレータを対象とします。有限例のコンパイルと数値実行の一致は、一般の健全性証明を意味しません。

```sh
cargo run --bin qleisli -- check examples/bell
cargo run --bin qleisli -- run examples/bell
cargo run --bin qleisli -- run examples/phase_oracle
cargo run --bin qleisli -- run examples/feedback
cargo run --bin qleisli -- run examples/grover
cargo run --bin qleisli -- run examples/bernstein_vazirani
cargo run --bin qleisli -- run examples/bit_flip_code
cargo run --bin qleisli -- run examples/phase_estimation
cargo run --bin qleisli -- run examples/order_finding
cargo run --example shor15
```

段階0の構成と有限コアv0の規範を定めました。現在は段階1の証明と処理系との対応を優先します。外部パッケージ管理やハードウェア固有 API は初期版の範囲外です。
