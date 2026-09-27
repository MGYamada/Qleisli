# Qleisli

**Current version: 0.1.1** · [0.1.1 release notes](docs/releases/v0.1.1.md) · [GitHub release record](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.1) · [Apache-2.0](LICENSE) · [Changelog](CHANGELOG.md) · [Versioning policy](docs/versioning.md)

**v0.1.1は互換修正のリリースです。** Claudeレビューから確認した契約再利用・診断・数値実行・厳密算術の改善と回帰検査を収めます。Rust 1.98.1／1.85.0の全target検査、Lean build／公理監査、代表例と配布候補の再ビルドを確認しました。[ロードマップ](ROADMAP.md#v011-release-roadmap)に検証と公開の条件を、GitHubのリリース記録に実際のコミット・CI・公開状態を記録します。

Qleisli は、Rust で処理系を構築する純粋関数型量子プログラミング言語です。量子データを複製不能な所有資源とし、プログラムを古典値と量子資源の、効果付きで合成可能な変換として捉えます。

**現状は設計と処理系の試作段階です。** [有限コア言語仕様v0](docs/language-spec.md)を確定し、実装プロファイルの容量上限内で、名前解決、型・効果・所有権検査、IR 生成、独立した IR 検証、参照実行を接続しました。Bell・位相オラクル・フィードバックに加え、[構造化した小規模Grover・Bernstein–Vazirani・ビット反転訂正](docs/algorithm-routines.md)を実行して期待分布を確認できます。同梱の通常定義は `stdlib/src/basis.qli`、`stdlib/src/routines.qli`、`stdlib/src/transforms.qli`、`stdlib/src/arithmetic.qli` です。[静的な逆・制御・有限反復と小規模QPE](docs/static-operations.md)も実装しました。[対応範囲](docs/frontend-v0.md)には制限があり、処理系全体の健全性証明や外部バックエンドは未完成です。

## North starとリリース到達条件

**north star（2026-09-27採用）:**

> 人間が量子アルゴリズムについて考えるときの言葉と、プログラムを書くときの言葉を一致させる。

状態準備、オラクル、反射、位相推定、逆計算などの概念とその組み合わせを、意味を保ったプログラムの語彙にします。**v1ではShor・QPE・Groverが教科書のアルゴリズム構造のまま読めること**を、その具体的な到達条件とします。

[設計メモ「量子の帳尻は言語が引き受ける」](docs/quantum-bookkeeping.md)に、この原理から所有権・補助回収・制御化・位相の検査を結ぶ考えと、QPE→振幅増幅→Shorを言語設計の試金石にする提案をまとめました。

その最低基盤として、**v0.1では `U E_in = E_out u` による意味契約を合成・再利用し、実際のIRまで独立検査できること**を必須にします。同じ契約を満たす複数の実装を、利用側を変えずに交換でき、位相・所有権・補助の厳密なゼロ復帰を保持するところまでが到達条件です。

v1では準備、オラクル、反射、制御付き冪、位相推定、位数再構成を、共有する部品とパラメータから構成します。実際にコンパイル・検証・実行できる三つのアルゴリズムで評価し、既存の固定サイズ例や疑似コードだけでは達成としません。[英語の到達条件](docs/release-milestones.md)を正本とし、この節は日本語の要約です。**v0.1の宣言した有限プロファイルは実装・検査を完了し、v1は未達成**です。crateの版番号や処理系全体の証明完了とは区別します。

**v0.2.0へ進む前提として、仮想Qleisli 1.0の理想コードを先に書きます。** QPE・Grover・amplitude estimation・Shor・quantum walk・QSVTの構造を、まだコンパイルできなくてもコードで表し、必要な意味契約・能力・未解決事項を洗い出します。初稿をそろえてからv0.2.0向けの一般化・新機能実装とリリースへ進みます。[英語正本の前提条件](docs/release-milestones.md#pre-v020-imaginary-v1-code)を採用済みですが、コード群の作成は未完了です。仮想コードは改訂可能な設計資料であり、v1達成の証拠とは区別します。

<a id="現在の優先順位-言語仕様"></a>

## 現在の優先順位: v0.1の言語仕様と意味契約

[有限意味契約の経路](docs/semantic-contracts-v0.1.md)を実装しました。厳密算術の独立検査器と、論理操作を明示する`with_computed(q,f,u){|d,a| body}`を接続し、位相オラクル・補助H;H・データと補助の同時Xを同じ規則で検査します。[関数境界](docs/function-contracts-v0.1.md)では`apply_contract(実装,仕様,入力)`によって利用側が意味を要求し、検査済み証拠を逆・制御・反復の後も最終IRに保持します。[実装を交換できる実行例](examples/function_contracts/README.md)を同梱しています。達成根拠と残る信頼境界は[適合記録](docs/specification-status.md)に記します。

v0.1の基盤となる**段階1の言語仕様とIR対応**を進めています。[資源規則R1](docs/source-resource-rules.md)、[型・効果・名前・スコープ規則](docs/source-typing-rules.md)、[ソースの局所意味論](docs/source-semantics.md)、[静的変換の証明](docs/static-semantics.md)を整え、[明示した数学的規則系の理想健全性Q1〜Q3](docs/source-soundness.md)を紙上で示しました。純粋操作の等長性／ユニタリ性と、観測・適応合成の完全正性・総和の跡保存を対象とします。

所有権モデルに加え、Kraus完全性の合成に関する5補題を[Leanで検証](docs/lean-resource-proof.md)しました。Leanは必要な局所補題を支える役割に留めます。[適合状況](docs/specification-status.md)には実装監査と回帰検査を記録しています。数学的規則とRustの全受理経路の対応、ソースからIRへの一般的な意味保存は未証明です。この基盤へv0.1の有限な意味契約・証拠検査を接続し、その後v1へ向けてサイズ付き型・操作パラメータ化・必要なアルゴリズムとstdlibを一般化します。

[ソース→IR変換契約C1〜C5](docs/source-ir-correspondence.md)で、基底表の符号化、原始操作、補助証拠、完全なφを具体化し、その数学的変換について前提付きの意味保存を紙上で示しました。既存の局所証明を接続した到達点であり、Rustの全成功経路がこの契約を満たす一般的な証明は残っています。

[スコープ終了の実装対応](docs/lowering-state-refinement.md)では、Rustの環境射影を独立した関数へ切り出し、同じ場合分けのLeanモデルで古典束縛の復元、消費済み束縛の非復活、量子所有権の保存を証明しました。再束縛の同一性を扱う有限モデルとソース回帰でも照合しています。ブロックに至る全実行経路や暗黙frameとの対応は次の課題です。

レビュー改訂で、`do (a,b) <- q; pure (a,a xor b)` の積パターンと、通常式の `true`・`false : CBit`、`not`・`and`・`xor` を実装しました。古典演算は両辺を左から右に評価し、量子所有権と効果を保持します。`true`・`false` は新予約語です。[改訂内容と検証結果](docs/specification-status.md)を参照してください。

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
26. [実装の責務と保守方針](docs/implementation-architecture.md): モジュールの依存方向、検証境界、loweringの不変条件、仕様・実装・回帰検査の対応。
27. [用語と表記](docs/terminology.md): 英語の規範文書と日本語の補助文書の関係、所有権・frame・保護領域の用語、量子状態の表記。
28. [ソース→IR変換契約](docs/source-ir-correspondence.md): 基底符号化・原始操作・補助証拠・完全φの局所導出、前提付き意味保存C1〜C5、Rustと独立検証器の対応義務。
29. [lowering状態とスコープの実装対応](docs/lowering-state-refinement.md): 値・環境・registerの対応、スコープ射影のLean定理、入力・移動・束縛・呼出し・分岐の残る証明前提。
30. [リリース到達条件とnorth star](docs/release-milestones.md): v0.1の意味契約・独立検査と、v1でShor・QPE・Groverを教科書の構造として読むための完了基準。
31. [有限な意味契約](docs/semantic-contracts-v0.1.md)と[関数境界](docs/function-contracts-v0.1.md): 厳密な演算子等式、補助ゼロ復帰、公開された意味と実装の対応、最終IRでの証拠の再利用。

## Rust 開発環境

Rust 2024 edition に対応する **Rust 1.85 以降**と、Cargo・rustfmt・Clippy を使用します。この crate は現在外部依存を持ちません。リポジトリのルートで次を実行します。

```sh
cargo test --all-targets
cargo fmt --check
cargo clippy --all-targets -- -D warnings
python3 scripts/check_docs.py
python3 scripts/test_check_docs.py
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

CLIのビット列は戻り値の古典タプルを左から右にたどった順です。位相推定の例では位相レジスタを低位ビットから返すため、`100`は整数1を表します。確率は浮動小数の近似値であり、丸めによる微小な正の値も表示します。[出力順と数値実行の規約](docs/frontend-v0.md)を参照してください。

段階0の構成と有限コアv0の規範を定めました。現在は段階1の証明と処理系との対応を優先します。外部パッケージ管理やハードウェア固有 API は初期版の範囲外です。

## License and contributions

Copyright 2026 Masahiko G. Yamada.

Unless otherwise stated in an individual file, Qleisli's own source code,
standard library, examples, tests, scripts, Lean proofs, and documentation
are licensed under the [Apache License, Version 2.0](LICENSE).
See [NOTICE](NOTICE) and the [contribution policy](CONTRIBUTING.md).
Third-party material and dependencies retain their own licenses and notices.
This license covers Qleisli's files; it does not purport to license independently
authored programs merely because they are written in or compiled with Qleisli.
