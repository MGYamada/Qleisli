# `.qli` 表層構文 v0

状態: **有限コアv0の規範文法**（2026-09-26）。[言語仕様v0](language-spec.md)の字句・文法・名前とスコープを定める。[モジュール規則](standard-library.md)と合わせて読む。構文受理、型・効果・証拠の受理、実装上限内での実行を区別する。[適合状況](specification-status.md)を別に記録する。

## 構文と組み込みの境界

| 記法 | 所属 | 型・所有権・効果の要点 | IR への変換方針 |
| --- | --- | --- | --- |
| `use`、`pub`、四種類の `fn`、`let`、`if` | 言語形式 | `basis` は全域の有限基底関数。`iso` は純粋な等長、`unitary` は純粋なユニタリ、`observe` は観測を含められる。`let` は線形所有権を再束縛し、`if` は `CBit` で排他的に分岐する。 | 宣言・import は名前解決へ、`let` は SSA の束縛、`if` は `ClassicalBranch` へ。 |
| `do x <- q; pure e` | 言語形式 | 入力 `q:Q<A>` を一度消費し、基底式 `e(x):B` が全域・単射の場合だけ `Q<B>` を作る純粋等長操作。`x` は測定結果ではない。 | 有限真理値表を検査して `LiftBasis` へ。 |
| `with_computed(q, f) { \|a\| body }` | 言語形式 | `q:Q<A>`、全域な `f:A -> Bit`、`a:Q<Bit>`。`body` は一時所有権 `a` を返し、通常関数の展開後に補助上の `Z/T` 列または空列だけを持つ。外側の結果は元の `Q<A>`。 | `ComputeUseUncompute` という一つの検証対象へ。独立した `Release0` は作らない。 |
| `adjoint(u,q)`、`repeat_static(n,u,q)` | 言語形式 | 静的に解決した同型のユニタリの逆・有限反復。量子所有権は一度消費し返す。 | [有限の静的操作](static-operations.md)に従いApplyUnitaryへ変換・再検証する。 |
| `qif(c,q) { 0 => u0, 1 => u1 }` | 言語形式 | 制御と標的を消費し両方を返す。別所有権、同型の静的ユニタリ枝を要求。 | 制御付きの平坦なApplyUnitary列。枝位相を保持する。 |
| `init0`、ゲート、`split/join`、`measure_z/reset/discard` | 封印された組み込み操作 | [段階0の公開契約](standard-library.md)に従う。観測操作は `observe` 効果、`measure_z` は `CBit` だけを返す。 | 公開名を、意味を固定した IR 構成子へ解決する。 |
| `xor2`、`and2`、`s`、`measure_x` など | 通常の `.qli` 定義 | 利用者の定義と同じ規則で型・効果・所有権を検査する。 | 本文を検査し、呼び出しまたは展開した IR へ。 |

`Q<A>` は所有権型であり、上表の `iso` 等は関数の静的分類である。`Iso<A,B>` や `Unitary<A,B>` を第一級の値型として導入する案ではない。
既存文書の `lift(e)` は `LiftBasis` の意味を表す記法として読み、この v0 表層では `do x <- q; pure e(x)` だけをその導入構文とする。直接の `lift(e)` ソース構文はv0に含めない。

## 字句と文法

`.qli` は UTF-8。識別子は v0 では ASCII の `[A-Za-z_][A-Za-z0-9_]*`。単独の `_` はワイルドカードパターンとして予約する。トークンを区切る空白は ASCII スペース・タブ・LF・CR だけとし、`//` コメントは LF または CR で終わる。コメント内の日本語など通常の非 ASCII 文字は許すが、コメント内外とも双方向制御文字（U+061C、U+200E/F、U+202A–E、U+2066–9）、LF/CR 以外の行終端（VT、FF、U+0085、U+2028/2029）、その他の制御文字は拒否する。その他の Unicode 空白もコメント内外とも拒否する。診断位置は UTF-8 バイト範囲である。予約語は `use`、`pub`、`basis`、`iso`、`unitary`、`observe`、`fn`、`let`、`if`、`else`、`do`、`pure`、`with_computed`、`adjoint`、`repeat_static`、`qif`、`not`、`xor`、`and`、`Unit`、`Bit`、`CBit`、`Q`。基底 `Bit` のリテラルは `0` と `1` のみとする。`repeat_static` の回数位置だけは十進自然数を認め、0を除く先頭ゼロを拒否する。現行の実装プロファイルは0〜4,096に制限し、超過を診断する。連続した数字を一つのトークンとし、基底式の `10` や `2` は引き続き拒否する。文字列、浮動小数点、配列、一般再帰、ユーザー定義の演算子はv0に含めない。

Rust パーサはスタックを守るため、再帰する構文と左結合の基底演算子列に実装上の 64 段の上限を置く。これは言語の数学的意味の上限ではなく、超過は位置付きエラーにする。

次は EBNF に近い表記で、`*` は 0 回以上、`?` は省略可能、`|` は選択を表す。終端の引用符は字句上の文字そのもの。`Name` は現在のモジュールで見える単一の識別子である。式の末尾にセミコロンは付けず、文だけに付ける。引数・パラメータ・タプル・`qif` の枝に末尾のカンマは認めない。通常の式には `CBit` リテラルや `not/xor/and` を置かず、これらのリテラル・演算は基底式に限る。

```ebnf
Module       ::= (Use | Decl)*
Use          ::= "use" Path "::" Ident ";"
Path         ::= Ident ("::" Ident)* | "std" "::" ("basis" | "observe")
Decl         ::= "pub"? (BasisDecl | QuantumDecl)
BasisDecl    ::= "basis" "fn" Ident "(" BasisParams? ")"
                 "->" BasisType BasisBlock
QuantumDecl  ::= Kind "fn" Ident "(" Params? ")" "->" Type Block
Kind         ::= "iso" | "unitary" | "observe"
BasisParams  ::= BasisParam ("," BasisParam)*
BasisParam   ::= Ident ":" BasisType
Params       ::= Param ("," Param)*
Param        ::= Ident ":" Type
Type         ::= BasisType | "CBit" | "Q" "<" BasisType ">"
               | "(" Type "," Type ")"
BasisType    ::= "Unit" | "Bit" | "(" BasisType "," BasisType ")"
ClassicalType ::= "Unit" | "CBit" | "(" ClassicalType "," ClassicalType ")"
Block        ::= "{" Stmt* Expr "}"
BasisBlock   ::= "{" BasisExpr "}"
Stmt         ::= "let" Pattern "=" Expr ";" | Expr ";"
Pattern      ::= Ident | "_" | "(" Pattern "," Pattern ")"
Expr         ::= Name | "()" | "(" Expr ")" | "(" Expr "," Expr ")"
               | Call | If | CoherentLift | WithComputed | Adjoint | Repeat | Qif
Adjoint      ::= "adjoint" "(" Name "," Expr ")"
Repeat       ::= "repeat_static" "(" StaticNat "," Name "," Expr ")"
StaticNat    ::= "0" | NonzeroDigit Digit*
Qif          ::= "qif" "(" Expr "," Expr ")"
                 "{" "0" "=>" Name "," "1" "=>" Name "}"
Call         ::= Name "(" Args? ")"
Args         ::= Expr ("," Expr)*
If           ::= "if" Expr Block "else" Block
CoherentLift ::= "do" Ident "<-" Expr ";" "pure" BasisExpr
WithComputed ::= "with_computed" "(" Expr "," Name ")"
                 "{" "|" Ident "|" Stmt* Expr "}"
BasisExpr    ::= XorExpr
XorExpr      ::= AndExpr ("xor" AndExpr)*
AndExpr      ::= UnaryExpr ("and" UnaryExpr)*
UnaryExpr    ::= "not" UnaryExpr | BasisAtom
BasisAtom    ::= Ident | "0" | "1" | "()" | "(" BasisExpr ")"
               | "(" BasisExpr "," BasisExpr ")"
               | BasisCall
BasisCall    ::= Name "(" BasisArgs? ")"
BasisArgs    ::= BasisExpr ("," BasisExpr)*
```

`std::basis` と `std::observe` の第 2 要素だけは、宣言用の予約語をモジュール名として使う特例である。import する末尾の名前やローカルモジュール名には予約語を使えない。`not` は `and` より強く、`and` は `xor` より強く結合する。両二項演算子は左結合とする。呼び出し引数と `let` の右辺は左から右に評価し、関数本体の文は記載順に評価する。`if` は条件を先に評価し、選んだ片方の枝だけを評価する。すべての関数は非再帰で、反復は静的な有限展開だけを認める。`repeat_static` は対象を先に検査し、回数0でも不正な本文を隠せない。

`basis fn` の引数・結果は `BasisType` だけで、本文は全域の `BasisExpr` に限る。`0` と `1` は `Bit`、`()` は `Unit`。`not : Bit -> Bit`、`xor : (Bit,Bit) -> Bit`、`and : (Bit,Bit) -> Bit` は基底式の基本演算である。`std::basis::and2` もこの演算で通常定義する。いずれも有限型上の全域演算だが、`Q` への直接リフトでは写像全体の単射性を別途検査する。例えば `basis fn and2(x: Bit, y: Bit) -> Bit { x and y }` は基底関数として有効。複数の基底引数の意味論上の定義域はその積型とし、`with_computed(q, and2)` では `q:Q<(Bit,Bit)>` を要求する。`and2` を量子レジスタ全体に単純にリフトすることは非単射なので認めない。

`Type` の文法は構文上は広めであり、役割は分類規則で絞る。通常の `iso`、`unitary`、`observe` の引数と結果に裸の `Bit` は置かない。`Bit` は `basis fn` の引数・結果、`Q<...>` の添字、`do/pure` 内の基底添字に現れる。`CBit` は測定などの観測結果または関数の古典引数としてだけ生成・導入され、`Bit` からの暗黙変換はない。複数の引数または結果はタプルで表す。`_` に `Q<A>` を束縛して捨てること、量子所有権を返す式を単なる `Expr;` にして捨てることは、構文上書けても資源検査で拒否する。

## 名前とスコープ

- 1 ファイル 1 モジュールとルート相対のモジュール名は段階0の規則どおり。`use foo::bar::name;` は `foo/bar.qli` の `pub` 宣言を `name` として束縛する。`std::` は同梱の標準ライブラリ専用。`use` はトップレベルにだけ置き、別名、ワイルドカード、再公開、相対パス、循環 import は置かない。定義と import の同名衝突は位置付きエラーとする。
- 実行時の入口はルート直下の `main.qli` にある唯一の `observe fn main() -> T` で、`T` は上記 `ClassicalType`、終了時の量子所有権は空とする。ライブラリ用モジュールは `main` を必要としない。
- 関数名は宣言順に依存せず解決するが、関数呼び出しグラフの循環を拒否する。通常の関数呼び出しは `Name(args)`。操作値を通常の引数として渡さない。静的操作形式の関数名はコンパイル時に解決し、呼び出しグラフへ含める。`with_computed` の第 2 項は `basis fn` の**名前**として静的に解決し、実行時の関数値ではない。
- 関数引数と `let` 束縛は字句スコープを持つ。`let q = h(q);` では右辺が旧 `q` を消費した後、新しい `q` がスコープに入る。束縛を隠したことで未消費の旧 `Q` が残るならエラーにする。量子値の同一性は綴りではなく所有権トークンと論理ワイヤ ID で追う。
- `if` の枝内の名前は枝の外に出ない。両枝は同じ入力線形文脈を排他的に受け、式の結果の型と量子所有権の形を合流させる。結果位置・残るframe・外側の消費集合に基づく[合流規則](language-spec.md#7-古典分岐の合流)を使い、枝内で新規に確保したワイヤも IR の `φ` で対応させる。
- `do` の束縛名 `x` は後続の一つの `BasisExpr` 内だけで有効な**コヒーレントな基底添字**である。この式の静的文脈は `x` だけで、外側の古典値も量子値も捕捉しない。トップレベルの基底関数は呼び出せる。`pure` は一般の return 構文でも古典値の生成構文でもない。
- `with_computed` の束縛名 `a` は本体内だけの一時的な `Q<Bit>` 所有権である。第 1 項の元レジスタはブロックの間保護し、本文には公開しない。他の外側の量子値も捕捉できず、外側の古典値だけを利用できる。ブロックの最終式は更新後の `a:Q<Bit>` を返す。元レジスタをコヒーレント制御としてブロックへ明示的に公開する束縛構文、および一般の作業レジスタを扱う構文はv0の範囲外である。

## 構文受理と静的拒否の例

次の例は import を省略した**v0の受理・拒否例**である。対応する複数ファイルの実行例と、実装済みの型・所有権規則は[初期フロントエンド](frontend-v0.md)を参照する。

```qli
iso fn entangle(q: Q<Bit>) -> Q<(Bit, Bit)> {
    do x <- q;
    pure (x, x)
}

basis fn predicate(x: Bit) -> Bit { not x }

unitary fn phase_oracle(q: Q<Bit>) -> Q<Bit> {
    with_computed(q, predicate) { |a| z(a) }
}

observe fn feedback(q: Q<Bit>, r: Q<Bit>) -> (CBit, Q<Bit>) {
    let b = measure_z(q);
    let r1 = if b { x(r) } else { r };
    (b, r1)
}

observe fn bell_result() -> (CBit, CBit) {
    let pair = entangle(h(init0()));
    let (left, right) = split(pair);
    let a = measure_z(left);
    let b = measure_z(right);
    (a, b)
}
```

ここでは `z`、`measure_z`、`x`、`h`、`init0`、`split` を適切に `use` したものとする。`entangle` の `x -> (x,x)` は単射、`phase_oracle` の `z(a)` は保護中の `a` の基底ラベルを保存する。`feedback` の `if` は両枝で同じ入力 `r` を排他的に使う。`measure_z` は旧 `q` を消費して `CBit` だけを返す。`bell_result` の二回の測定は、`split` された両方の論理ワイヤを消費する。

| 断片 | 構文 | 静的判定の理由 |
| --- | --- | --- |
| `do x <- q; pure (x,x)` | 有効 | `x -> (x,x)` が単射なら受理。 |
| `do x <- q; pure 0` | 有効 | `Bit -> Bit` の定数写像は非単射なので拒否。 |
| `let pair = (q,q); pair` | 有効 | 同一 `Q` の二重使用なので拒否。 |
| `let b = measure_z(q); h(q)` | 有効 | `measure_z` で消費した旧 `q` を再使用するので拒否。 |
| `iso fn bad(q: Q<Bit>) -> CBit { measure_z(q) }` | 有効 | `observe` 効果を `iso` に入れられず拒否。 |
| `with_computed(q, predicate) { \|a\| h(a) }` | 有効 | `H` は `a` の基底ラベルを保存せず、ゼロ復帰の規則に反するので拒否。 |
| `do x <- q; let y = x; pure y` | 無効 | v0 の `do` は単一の `pure BasisExpr` だけを取る。 |
| `use oracle::*;` | 無効 | ワイルドカード import は置かない。 |

## 構文を保留する項目

- 静的操作の第一級値への一般化、古典パラメータ付き操作、異なる基底型の間の逆変換。現在の `qif`・`adjoint`・`repeat_static` は関数名を静的に解決し、古典引数なしの `Q<A> -> Q<A>` だけを対象とする。
- 元レジスタを借用して作業レジスタ `R` を操作する一般の `with_computed`、サイズ付きレジスタ、量子引数を取る高階関数、動的反復、実行時の真理値表生成はこの文法にない。これらを追加するときは保護するワイヤ ID 集合、効果と検査可能な証拠を同時に定める。

### 証明と後続仕様

文法・優先順位・有限版の型規則・分岐合流はv0として固定する。完全な形式体系での資源安全性と意味保存の証明は[段階1の残件](specification-status.md)。一般の保存効果を署名・証拠として受け渡す規則は後続仕様とし、v0の `with_computed` は限定された構造証拠を使う。
