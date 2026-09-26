# 構造化アルゴリズムの有限部品

状態: **通常の `.qli` 定義として実装・有限例で検証**（2026-09-26）。[第2開発目標](algorithm-structure-goal.md)のA1に対応する。`stdlib/src/routines.qli`の`std::routines`は、固定幅の5つの公開関数を持つ。同梱ソースも利用者ソースと同じ型・効果・所有権検査、本文の展開、独立したIR検証を受ける。新しい原始操作・表層構文・第一級コンビネータは追加していない。名前と幅の一般化は今後の設計対象。

## 公開APIの契約

表の量子引数はすべて消費し、返した値だけを再使用できる。別所有権から積状態を仮定しない。表示しない参照系には恒等を掛けて解釈する。`Bit`の組`(a,b)`はIRのビット添字で`a+2b`、測定結果の表示では左から`ab`の順。

| 名前・所属 | 入出力型・効果・意味 | 受理例／拒否例 | IRへの変換 |
| --- | --- | --- | --- |
| `hadamard2`／通常の`.qli`定義 | `Q<(Bit,Bit)> -> Q<(Bit,Bit)>`、`Unitary`。`H⊗H`。全所有権を返す。 | 受理: 2ビットの積レジスタ。拒否: `Q<Bit>`、消費済み入力。 | `Split; H; H; Join`。 |
| `reflect_uniform2`／通常の`.qli`定義 | 同じ型、`Unitary`。`D=2∣s⟩⟨s∣-I`、`∣s⟩=H⊗H∣00⟩`。 | 受理: Groverステップの反射。拒否: 単一ビット、同じ所有権の再使用。 | `hadamard2`、`ComputeUseUncompute`、`hadamard2`を展開。位相を以下の等式で固定する。 |
| `measure_x`／通常の`.qli`定義 | `Q<Bit> -> CBit`、`Observe`。X固有値`(-1)^b`を測り、対象の所有権を消費。 | 受理: `measure_x(h(init0()))`は0。拒否: `unitary`本文での呼び出し、測定後の旧入力。 | `H; MeasureZ`。 |
| `measure_z2`／通常の`.qli`定義 | `Q<(Bit,Bit)> -> (CBit,CBit)`、`Observe`。両対象を消費。 | 受理: Bell対では00/11。拒否: 単一ビット、測定後の旧レジスタ。 | `Split; MeasureZ; MeasureZ`、左の結果を先に返す。 |
| `parity_zz`／通常の`.qli`定義 | `(Q<Bit>,Q<Bit>) -> ((Q<Bit>,Q<Bit>),CBit)`、`Observe`。別所有のデータ2本を返し、内部測定用ワイヤを消費。 | 受理: 相関したデータのZZパリティ測定。拒否: `parity_zz(q,q)`、返ったデータの暗黙破棄、`Unitary`としての使用。 | `Init0; Cnot(a,m); Cnot(b,m); MeasureZ(m)`。 |

非公開の`nonzero2 : (Bit,Bit) -> Bit`も通常の`.qli`基底関数。全域で、`00`に0、それ以外に1を返す。全域性は有限列挙で検査する。この表は非単射でよく、補助へのXOR計算を持つ`with_computed`の述語に使う。`Q<(Bit,Bit)>`から`Q<Bit>`へ直接リフトする契約ではない。

### 反射の位相

`with_computed(q,nonzero2) { |a| z(a) }`は基底`|ab⟩`に`(-1)^nonzero2(a,b)`を掛けるので、

```text
R0 = diag(1, -1, -1, -1) = 2|00⟩⟨00| - I
D  = (H⊗H) R0 (H⊗H) = 2|s⟩⟨s| - I
```

となる。`00`だけを負にする位相オラクルなら結果は`-D`になるため、この選択を明記する。演算子の符号は上の定義と本文の構成で固定する。今回の閉じた測定例だけでは全体位相は観測できず、A2で追加した[制御化による符号テスト](static-operations.md#確認した結果)では `D` と `-D` を区別した。

### パリティ測定の全体系での意味

`parity_zz`の結果`s`に対応する非正規化の残系は

```text
P_s = (I + (-1)^s Z_a Z_b) / 2
E_s(ρ) = (P_s ⊗ I_R) ρ (P_s ⊗ I_R),  s ∈ {0,1}
```

である。`P_0+P_1=I`で全枝の和は跡保存。パリティ部分空間の内部の重ね合わせを保持する。各データをZ測定してから結果をXORする操作とは残系が異なる。`|++⟩`入力からは、結果0で`(|00⟩+|11⟩)/√2`、結果1で`(|01⟩+|10⟩)/√2`を各1/2で得る。これはデータ測定を置き換えた場合に壊れるX相関で検査する。

## 組み立てたアルゴリズム

### Grover: オラクル・反射・有限反復

[`examples/grover`](../examples/grover/main.qli)は、状態準備、`oracle::mark`、`search::step`、測定をモジュールで分ける。述語`marked(a,b)=a and b`の位相オラクルは`O=I-2|11⟩⟨11|`。ステップは`G=D O`で、`search_one`は`|s⟩`へ1回適用する。

- `oracle::mark`、`search::step`は通常定義、`Q<(Bit,Bit)> -> Q<(Bit,Bit)>`の`Unitary`。
- `search::search_one`は通常定義、`() -> Q<(Bit,Bit)>`の`Iso`。新しいデータ2本を返す。
- `marked`は全域な通常の基底関数`(Bit,Bit)->Bit`。対象数1という性質は個別アルゴリズムの前提である。
- すべて通常呼び出しとして既存の準備・ゲート・補助計算IRへ展開。受理例は公開main、拒否例はステップへ同じ資源を二重に渡す式や測定済み入力。

1対象・4候補では`θ=arcsin(1/2)=π/6`、`k`反復の成功確率は`sin²((2k+1)θ)`。テストは全4対象、`k=0..4`を照合し、反復すれば常に成功率が上がるという誤った仕様を避ける。このGrover例の有限反復テストは明示した呼び出し列を使う。A2では別途 `repeat_static` の静的展開を実装した。

### Bernstein–Vazirani: 同じ準備と異なる干渉の組み立て

[`examples/bernstein_vazirani`](../examples/bernstein_vazirani/main.qli)は`hadamard2`と`measure_z2`をGroverと共有する。`O_s|x⟩=(-1)^(s·x)|x⟩`に対して`(H⊗H)O_s(H⊗H)|00⟩=|s⟩`を使う。

- `oracle::mark`は通常定義、2ビットレジスタの`Unitary`。全域な通常の基底関数`linear(a,b)=a`が隠れ列`10`を表す。
- `interference::recover_secret`は通常定義、`() -> Q<(Bit,Bit)>`の`Iso`。新規準備・オラクル・Hadamardを展開し、所有権を返す。
- 受理例は公開main、拒否例は型違い・所有権再使用。線形関数という約束は型検査の保証ではない。

テストは全4隠れ列を照合する。これは位相オラクルへのアクセスを前提とする有限例であり、大規模オラクルの合成コストを測ったものではない。

### ビット反転訂正: シンドローム・古典フィードバック

[`examples/bit_flip_code`](../examples/bit_flip_code/main.qli)は**3量子ビット反復符号、理想操作、高々1箇所のX誤り**に限定する。コード空間は`α|000⟩+β|111⟩`。一般の量子誤り訂正や耐故障性は主張しない。

| 通常の`.qli`定義 | 型・所有権・効果 | 意味とIR |
| --- | --- | --- |
| `code::encode` | `Q<Bit> -> Q<((Bit,Bit),Bit)>`、`Iso`。入力を消費し2本増えたレジスタを返す。 | 単射基底写像`b -> ((b,b),b)`の`LiftBasis`。未知状態のコピーではなく符号化`V`。 |
| `code::recover` | `Q<((Bit,Bit),Bit)> -> (Q<((Bit,Bit),Bit)>,(CBit,CBit))`、`Observe`。データを返し、内部メータを測定・消費。 | `parity_zz(a,b)`、`parity_zz(b,c)`、シンドロームに応じたXを`ClassicalBranch`へ展開。 |
| `code::decode` | `Q<((Bit,Bit),Bit)> -> (Q<Bit>,(Q<Bit>,Q<Bit>))`、`Unitary`。全3本の所有権を返す。 | `Cnot(a,b); Cnot(a,c)`。補助2本がゼロでも暗黙解放せず、呼び出し元で測定等により消費する。 |

`(s_ab,s_bc)`は、無誤り・`X_a`・`X_b`・`X_c`に対してそれぞれ`00,10,11,01`。対応する補正を`C_s`、復号を`D_dec`とすると、各`E∈{I,X_a,X_b,X_c}`について

```text
D_dec C_s E V |ψ⟩ = |ψ⟩ ⊗ |00⟩
```

であり、同じ線形等式を参照系へ恒等拡張できる。シンドロームは論理値に依存しない。この回路についての等式と、コンパイラ全体の一般的な健全性証明は別である。

テストは論理入力を外部参照とBell対にして、4種の誤り後の相関、シンドローム、復号補助のゼロを照合する。Z誤り・2箇所のX誤りでは論理誤りが残ることも確認する。符号空間と誤りモデルの前提は現在の`Q<...>`型には符号化されておらず、前提外の入力を型検査で拒否するとは主張しない。資源の二重使用・返されたデータの暗黙破棄・観測の`unitary`内への混入は拒否する。

## 実行と検証

```sh
cargo run --bin qleisli -- run examples/grover
cargo run --bin qleisli -- run examples/bernstein_vazirani
cargo run --bin qleisli -- run examples/bit_flip_code
cargo test --test algorithms --test project
```

期待するmainの出力は順に`11`、`10`、`11000`が確率1。最後はシンドローム`11`、論理X測定`0`、復号補助のZ測定`00`の順。参照シミュレータは`f64`近似であり、テスト許容誤差は`1e-12`。これらは一般の健全性定理、実機の訂正能力、大規模での計算量を検証するものではない。
