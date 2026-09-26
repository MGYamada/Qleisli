# Qleisli

Qleisli は、Rust で処理系を構築する純粋関数型量子プログラミング言語です。量子データを複製不能な所有資源とし、プログラムを古典値と量子資源の、効果付きで合成可能な変換として捉えます。

**現状は設計と処理系の試作段階です。** 暫定 `.qli` 構文の部分集合について、名前解決、型・効果・所有権検査、IR 生成、独立した IR 検証、参照実行を接続しました。`examples/bell`、`examples/phase_oracle`、`examples/feedback` は実行して期待分布を確認できます。同梱の通常定義は `stdlib/src/basis.qli` です。[対応範囲](docs/frontend-v0.md)には制限があり、一般の健全性証明や外部バックエンドは未完成です。

## 開発目標の一つ: AI時代の量子言語

AI が生成したコードも人間が書いたコードも、同じ型・効果・所有権検査と IR 検証に通す。まず資源の安全性を、その上で理想意味論における量子操作の健全性を保証することを目指す。プロトコルやアルゴリズムの正しさ、実機での動作は別の検証対象とする。保証の条件と到達基準は[開発目標](docs/ai-era-goal.md)に記す。

## 設計の境界

- 自由ベクトル空間モナドはコヒーレントな計算の数学的な由来です。資源と効果を追うプログラム合成は Kleisli 的に設計しますが、任意の `bind` を安全な実行 API として公開しません。
- `Q<A>` は量子レジスタの操作権です。純粋領域では線形に扱い、暗黙の破棄を許しません。基底添字の共有は、全体の写像が等長なら許します。
- 測定、リセット、破棄は `observe` 効果に置きます。初期版の測定は量子ハンドルを消費して古典結果だけを返します。補助量子ビットの純粋な解放には、全入力に対するゼロ復帰の静的証拠が必要です。
- [未解決の中核課題](docs/design-philosophy.md)は、所有権による操作権の管理と、絡み合った全体系について必要な証拠をどう合成するかです。
- Rust の借用検査は処理系のメモリ安全性を担います。Qleisli の所有権・効果・構成子の条件は専用のフロントエンドと IR 検証器が検査します。検査器実装の一般的な正しさの証明は別の課題です。

## 文書

1. [設計思想](docs/design-philosophy.md): 固定する原理と、構文に残す自由度。
2. [AI時代の量子言語という開発目標](docs/ai-era-goal.md): 健全性の階層と証明目標。
3. [ROADMAP.md](ROADMAP.md): 段階0から実装までの順序と完了条件。
4. [量子言語としての成立条件](docs/quantum-language-requirements.md): 仕様と実装が満たすべき条件。
5. [`.qli` と標準ライブラリの構成](docs/standard-library.md): 段階0の構成決定。
6. [言語仕様草案](docs/language-spec.md): 段階1に向けた型・意味論の検討資料。
7. [有限コアの形式化](docs/formal-core.md): 定理の形、構成子の意味、証明の残件。
8. [`.qli` 構文 v0 案](docs/syntax-v0.md): 暫定文法、名前とスコープ、静的な拒否例。
9. [Rust IR 検証器の試作](docs/ir-prototype.md): 実装済みの検査、信頼境界、未達成の保証。
10. [有限 IR の紙上証明](docs/finite-core-proof.md): 現行構成子の量子意味と、実装との対応に残る検証義務。
11. [`.qli` フロントエンドの初期実装](docs/frontend-v0.md): 実行できる部分集合、検査規則、診断、実行例。

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
```

段階0ではソースファイル、モジュール、標準ライブラリと組み込み操作の境界を先に決めます。その後に構文・型規則・意味論を固定します。外部パッケージ管理やハードウェア固有 API は初期版の範囲外です。
