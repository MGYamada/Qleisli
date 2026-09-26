# 段階0: `.qli` と標準ライブラリの構成

状態: **段階0の構成決定**（2026-09-26）。[設計思想](design-philosophy.md)に従い、ファイル規則、初期 API、組み込み境界を文書上で選定した。現在は[初期フロントエンド](frontend-v0.md)が暫定構文の部分集合を検査し、[有限 IR](ir-prototype.md)へ変換する。以下は構成を説明する例であり、実行を確認したプロジェクトは `examples/bell`、`examples/phase_oracle`、`examples/feedback` に置く。

## `.qli` が表すもの

`.qli` は UTF-8 の **Qleisli ソースファイル**であり、量子状態データ、回路のバイナリ、IR、実行結果ではない。1 ファイルを 1 モジュールとする。トップレベルには `basis fn`、`iso fn`、`unitary fn`、`observe fn` と `use` だけを置き、ロード時の実行、グローバルな可変状態、I/O、暗黙の量子ビット確保を設けない。`let` は値への名前付けであり、可変セルではない。

| 項目 | 初期版の選択 |
| --- | --- |
| モジュール名 | ソースルートからの相対パスで決める。ファイル内の `module` 宣言は置かない。 |
| ソースルート | CLI に渡すディレクトリ。慣例上は `src/`。ルートの絶対パスが変わっても、各 `.qli` のルートからの相対パスが同じならモジュール名は同じ。 |
| ローカル import | `use oracle::phase_oracle;` はルート内の `oracle.qli` の公開宣言を参照する。`foo::bar::name` は `foo/bar.qli` に対応する。すべてルート基準の絶対モジュールパスとし、呼び出し元基準の相対 import は初期版に置かない。 |
| 標準 import | `std::` は処理系に同梱した標準ライブラリ専用の接頭辞。ローカルファイルで上書きできない。 |
| 可視性 | 宣言は既定でモジュール内限定。`pub` を付けた宣言だけを他ファイルから参照できる。 |
| import の形 | 初期版は名前を指定する `use path::name;` のみ。ワイルドカード、暗黙の再公開、循環 import を認めない。 |
| 入口 | 実行時はルート直下の `main.qli` に `observe fn main() -> T` を 1 つ置く。`T` は有限の古典結果型で、終了時に量子所有権を残さない。ライブラリのみなら `main.qli` は不要。 |
| パッケージ | 初期版は外部依存とマニフェストを持たない。処理系は指定されたソースルート内の `.qli` と同梱 `std` だけを解決する。 |

CLI は `qleisli check src` と `qleisli run src`。`check` はルート内の `.qli` を型・効果・所有権まで検査し、各通常関数の生成 IR を再検証する。`run` は全宣言を検査した上で `main.qli` の閉じたプログラムを参照実行する。現在の[対応範囲](frontend-v0.md)を越える機能は診断する。実行結果の表示、反復回数の指定、機器への送信はホスト側の責務とする。`src/lib.qli` は任意のライブラリ用慣例名である。`foo.qli` と `foo/bar.qli` はそれぞれ `foo` と `foo::bar` という別モジュールで、暗黙の親子可視性はない。モジュールの循環 import と関数の再帰呼び出しは別の規則として検査する。

見つからない import、非公開名、名前の衝突、循環 import は、ファイル位置付きのコンパイル診断にする。モジュールの動的読み込みはない。実機の能力不足やホスト I/O の失敗は `.qli` の純粋関数の値に混ぜず、実行前の診断またはホスト側の失敗として扱う。

`Unit`、`Bit`、`CBit`、`Q<A>` と `if`、`do/pure` などの言語形式は import なしで使える。`Iso<A,B>` と `Unitary<A,B>` は初期版では関数宣言の静的分類であり、受け渡しできる第一級の値型ではない。基底式の `not`、`xor`、`and` も基本演算とする。`Bit` と `CBit` の間に暗黙変換はない。暗黙に開く `std::prelude` モジュールは設けず、標準ライブラリの関数は明示的に import する。

## 標準ライブラリの最小構成

| モジュール | 選定した初期 API | 実装の境界 |
| --- | --- | --- |
| `std::basis` | `xor2`、`and2` などの有限基底関数 | 通常の `.qli`。非単射な関数も基底関数として定義できるが、`Q` に直接適用する `lift` は単射性検査を通す。 |
| `std::quantum` | `init0`、`h`、`x`、`z`、`t`、`cnot`、`toffoli`、`split`、`join` | 最小の原始操作と所有権の構造操作は封印された組み込み。`s(q) = t(t(q))` のような派生操作は通常の `.qli`。 |
| `std::observe` | `measure_z`、`reset`、`discard` | 原始操作は封印された組み込み。`measure_x(q) = measure_z(h(q))` のような派生操作は通常の `.qli`。 |

主要 API の公開名、型の形、所有権と効果は次を段階0の契約とする。`Q<A>` は所有する量子資源の型であり、各引数を線形に受け渡す。表の `Iso`、`Unitary`、`Observe` は操作の分類・効果である。正確なシグネチャ文法と型規則は段階1で定める。

| API | 型の形 | 効果・所有権 |
| --- | --- | --- |
| `basis::xor2`、`basis::and2` | `(Bit, Bit) -> Bit` | 全域な基底関数。単射である必要はない。 |
| `quantum::init0` | `() -> Q<Bit>` | `Iso`。新しい `|0〉` ワイヤを返す。 |
| `quantum::{h,x,z,t}` | `Q<Bit> -> Q<Bit>` | `Unitary`。同じ論理ワイヤの所有権を返す。 |
| `quantum::cnot` | `(Q<Bit>, Q<Bit>) -> (Q<Bit>, Q<Bit>)` | `Unitary`。異なるワイヤを要求する。 |
| `quantum::toffoli` | `(Q<Bit>, Q<Bit>, Q<Bit>) -> ((Q<Bit>, Q<Bit>), Q<Bit>)` | `Unitary`。3 本とも異なるワイヤを要求する。3 引数を取り、v0 の二要素タプルで入れ子にした 3 結果を返す。 |
| `quantum::split` / `join` | `Q<(A,B)> <-> (Q<A>, Q<B>)` | 所有権の構造操作。振幅を変えず、絡み合いを保つ。 |
| `observe::measure_z` | `Q<Bit> -> CBit` | `Observe`。測定対象の論理ワイヤを消費し、古典結果だけを返す。 |
| `observe::reset` | `Q<Bit> -> Q<Bit>` | `Observe`。旧所有権と相関を捨て、新しい論理 ID の `|0〉` ワイヤを返す。 |
| `observe::discard` | `Q<A> -> Unit` | `Observe`。部分跡でワイヤを消費する。 |

`std::` はコンパイラと同じ版として配布し、初期版で利用者による置換や外部パッケージの読み込みを行わない。原始ゲートの行列、測定の意味、所有権を変える操作は、名前が `std` にあっても通常の `.qli` 本文で偽装できない。通常の標準ライブラリ定義には利用者コードと同じ型・効果規則を適用する。

`measure_z` 後に同じ論理ワイヤを操作することはできない。必要なら `init0` で新しい論理ワイヤを準備し、測定結果で古典制御する。バックエンドは条件を満たすとき、新しい論理ワイヤを測定済みの物理素子に割り当ててもよい。

選定した配置は `stdlib/src/basis.qli`、`stdlib/src/quantum.qli`、`stdlib/src/observe.qli` とする。現在は `basis.qli` の通常定義だけを同梱し、`std::quantum` と `std::observe` の封印された公開名は Rust のモジュール解決器に登録している。原始操作の公開シグネチャをこれらのモジュール ID に結び付け、派生定義だけを通常の `.qli` 本文に置く。表の公開契約は固定し、シグネチャの記法とコンパイラ内部での結合方法は段階1で確定する。

`lift(e)` の単射性検査、`qif`、`adjoint`、`with_computed` は静的に検査する**言語形式**とする。初期版は高階の操作値を定義しないので、これらを任意の関数値を受け取る通常のライブラリ関数として約束しない。`release0` は証拠を伴う内部操作で、無条件の公開 API にはしない。ハードウェアのバックエンドも標準ライブラリには入れない。

## 複数ファイルの設計例

次のパスと `use` は上の解決規則に従う。**現在は実行できない構文例**である。

### Bell 状態

`examples/bell/src/bell.qli`:

```qli
pub iso fn entangle(q: Q<Bit>) -> Q<(Bit, Bit)> {
    do x <- q;
    pure (x, x)
}
```

`examples/bell/src/main.qli`:

```qli
use bell::entangle;
use std::quantum::h;
use std::quantum::init0;
use std::quantum::split;
use std::observe::measure_z;

observe fn main() -> (CBit, CBit) {
    let pair = entangle(h(init0()));
    let (left, right) = split(pair);
    let a = measure_z(left);
    let b = measure_z(right);
    (a, b)
}
```

期待する結果は `(0,0)` と `(1,1)` が各 `1/2`。`bell.qli` は量子資源を複製せず、`x -> (x,x)` の単射性を型検査する。

### 位相オラクル

`examples/oracle/src/oracle.qli`:

```qli
use std::quantum::z;

basis fn predicate(x: Bit) -> Bit { not x }

pub unitary fn phase_oracle(q: Q<Bit>) -> Q<Bit> {
    with_computed(q, predicate) { |a| z(a) }
}
```

`examples/oracle/src/main.qli`:

```qli
use oracle::phase_oracle;
use std::quantum::h;
use std::quantum::init0;
use std::observe::measure_z;

observe fn main() -> CBit {
    let prepared = h(init0());
    let marked = phase_oracle(prepared);
    measure_z(h(marked))
}
```

`predicate(x) = not x` なので `phase_oracle` の行列は `-Z`。この閉じた例の測定結果は `1` である。`with_computed` が計算元のコヒーレントな借用をブロックにどう公開するか、および一般の作業レジスタをどう返すかは段階1で構文と型を確定する。

`std::basis::xor2 : (Bit,Bit) -> Bit` のような非単射の基底関数を `lift(xor2)` として `Q<(Bit,Bit)>` に直接適用するコードは拒否する。`(q,q)` も、同じ所有権を二度使うので拒否する。標準モジュールにあるという理由で量子条件を緩めない。

## 段階1へ渡す未決事項

- 正確な文法、演算子の優先順位、`with_computed` の借用束縛、`qif` の枝表記。
- サイズ付きレジスタ、静的な反復、回転角の表現。
- 高階関数、外部パッケージ、マニフェスト、追加の標準モジュール。

これらを決めるときも [量子言語としての成立条件](quantum-language-requirements.md) を満たす必要がある。
