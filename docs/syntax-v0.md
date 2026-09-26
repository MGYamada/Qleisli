# `.qli` 表層構文 v0 案

状態: **段階1の提案**（2026-09-26）。Rust の暫定パーサはこの構文の一部を実装したが、確定文法ではない。[段階0のファイル・モジュール規則](standard-library.md)と[言語仕様草案](language-spec.md)の Bell、位相オラクル、測定後フィードバックを同じ構文で読めるようにする案である。型・効果・証拠の判定は構文の受理と別であり、下の「構文上有効」は実行可能という意味ではない。

## 構文と組み込みの境界

| 記法 | 所属 | 型・所有権・効果の要点 | IR への変換方針 |
| --- | --- | --- | --- |
| `use`、`pub`、四種類の `fn`、`let`、`if` | 言語形式 | `basis` は全域の有限基底関数。`iso` は純粋な等長、`unitary` は純粋なユニタリ、`observe` は観測を含められる。`let` は線形所有権を再束縛し、`if` は `CBit` で排他的に分岐する。 | 宣言・import は名前解決へ、`let` は SSA の束縛、`if` は `ClassicalBranch` へ。 |
| `do x <- q; pure e` | 言語形式 | 入力 `q:Q<A>` を一度消費し、基底式 `e(x):B` が全域・単射の場合だけ `Q<B>` を作る純粋等長操作。`x` は測定結果ではない。 | 有限真理値表を検査して `LiftBasis` へ。 |
| `with_computed(q, f) { \|a\| body }` | 言語形式 | `q:Q<A>`、全域な `f:A -> Bit`、`a:Q<Bit>`。`body` は一時所有権 `a` を一度受け渡して返す、保護中の基底ラベルを保存するユニタリに限る。外側の結果は元の `Q<A>`。 | `ComputeUseUncompute` という一つの検証対象へ。独立した `Release0` は作らない。 |
| `init0`、ゲート、`split/join`、`measure_z/reset/discard` | 封印された組み込み操作 | [段階0の公開契約](standard-library.md)に従う。観測操作は `observe` 効果、`measure_z` は `CBit` だけを返す。 | 公開名を、意味を固定した IR 構成子へ解決する。 |
| `xor2`、`and2`、`s`、`measure_x` など | 通常の `.qli` 定義 | 利用者の定義と同じ規則で型・効果・所有権を検査する。 | 本文を検査し、呼び出しまたは展開した IR へ。 |

`Q<A>` は所有権型であり、上表の `iso` 等は関数の静的分類である。`Iso<A,B>` や `Unitary<A,B>` を第一級の値型として導入する案ではない。
既存文書の `lift(e)` は `LiftBasis` の意味を表す記法として読み、この v0 表層案では `do x <- q; pure e(x)` だけをその導入構文とする。直接の `lift(e)` ソース構文を追加するかは未決である。

## 字句と文法

`.qli` は UTF-8。識別子は v0 では ASCII の `[A-Za-z_][A-Za-z0-9_]*`、空白と改行はトークンを区切る。単独の `_` はワイルドカードパターンとして予約する。`//` から行末までをコメントとする案を採る。予約語は `use`、`pub`、`basis`、`iso`、`unitary`、`observe`、`fn`、`let`、`if`、`else`、`do`、`pure`、`with_computed`、`not`、`xor`、`and`、`Unit`、`Bit`、`CBit`、`Q`。数値リテラルは基底 `Bit` の `0` と `1` のみを置く。文字列、浮動小数点、配列、一般再帰、ユーザー定義の演算子はこの案に含めない。

次は EBNF に近い表記で、`*` は 0 回以上、`?` は省略可能、`|` は選択を表す。終端の引用符は字句上の文字そのもの。`Name` は現在のモジュールで見える単一の識別子である。式の末尾にセミコロンは付けず、文だけに付ける。

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
               | Call | If | CoherentLift | WithComputed
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

`std::basis` と `std::observe` の第 2 要素だけは、宣言用の予約語をモジュール名として使う特例である。import する末尾の名前やローカルモジュール名には予約語を使えない。`not` は `and` より強く、`and` は `xor` より強く結合する。両二項演算子は左結合とする。呼び出し引数と `let` の右辺は左から右に評価し、関数本体の文は記載順に評価する。`if` は条件を先に評価し、選んだ片方の枝だけを評価する。すべての関数は非再帰で、v0 の式にループはない。

`basis fn` の引数・結果は `BasisType` だけで、本文は全域の `BasisExpr` に限る。`0` と `1` は `Bit`、`()` は `Unit`。`not : Bit -> Bit`、`xor : (Bit,Bit) -> Bit`、`and : (Bit,Bit) -> Bit` は基底式の基本演算である。`and` を入れる理由は、段階0で選定済みの `std::basis::and2` を通常の `.qli` 定義として記述できるようにするためである。いずれも有限型上の全域演算だが、`Q` への直接リフトでは写像全体の単射性を別途検査する。例えば `basis fn and2(x: Bit, y: Bit) -> Bit { x and y }` は基底関数として有効。複数の基底引数の意味論上の定義域はその積型とし、`with_computed(q, and2)` では `q:Q<(Bit,Bit)>` を要求する。`and2` を量子レジスタ全体に単純にリフトすることは非単射なので認めない。

`Type` の文法は構文上は広めであり、役割は分類規則で絞る。通常の `iso`、`unitary`、`observe` の引数と結果に裸の `Bit` は置かない。`Bit` は `basis fn` の引数・結果、`Q<...>` の添字、`do/pure` 内の基底添字に現れる。`CBit` は測定などの観測結果または関数の古典引数としてだけ生成・導入され、`Bit` からの暗黙変換はない。複数の引数または結果はタプルで表す。`_` に `Q<A>` を束縛して捨てること、量子所有権を返す式を単なる `Expr;` にして捨てることは、構文上書けても資源検査で拒否する。

## 名前とスコープ

- 1 ファイル 1 モジュールとルート相対のモジュール名は段階0の規則どおり。`use foo::bar::name;` は `foo/bar.qli` の `pub` 宣言を `name` として束縛する。`std::` は同梱の標準ライブラリ専用。`use` はトップレベルにだけ置き、別名、ワイルドカード、再公開、相対パス、循環 import は置かない。定義と import の同名衝突は位置付きエラーとする。
- 実行時の入口はルート直下の `main.qli` にある唯一の `observe fn main() -> T` で、`T` は上記 `ClassicalType`、終了時の量子所有権は空とする。ライブラリ用モジュールは `main` を必要としない。
- 関数名は宣言順に依存せず解決するが、関数呼び出しグラフの循環を拒否する。通常の関数呼び出しは `Name(args)`。操作値を引数として渡さない。`with_computed` の第 2 項は `basis fn` の**名前**として静的に解決し、実行時の関数値ではない。
- 関数引数と `let` 束縛は字句スコープを持つ。`let q = h(q);` では右辺が旧 `q` を消費した後、新しい `q` がスコープに入る。束縛を隠したことで未消費の旧 `Q` が残るならエラーにする。量子値の同一性は綴りではなく所有権トークンと論理ワイヤ ID で追う。
- `if` の枝内の名前は枝の外に出ない。両枝は同じ入力線形文脈を排他的に受け、式の結果の型と量子所有権の形を合流させる。枝内で新規に確保したワイヤ ID の対応づけは IR の `φ` とし、完全な規則はまだ未確定。
- `do` の束縛名 `x` は後続の一つの `BasisExpr` 内だけで有効な**コヒーレントな基底添字**である。この式は外側の `Q` を捕捉しない。`pure` は一般の return 構文でも古典値の生成構文でもない。
- `with_computed` の束縛名 `a` は本体内だけの一時的な `Q<Bit>` 所有権である。第 1 項の元レジスタはブロックの間、基底ラベルを変えない借用として保護し、本文から通常の `Q` 操作へ渡せない。ブロックの最終式は更新後の `a:Q<Bit>` を返す。元レジスタをコヒーレント制御としてブロックへ明示的に公開する束縛構文、および一般の作業レジスタを扱う構文は未決である。

## 構文受理と静的拒否の例

次の例は**提案構文の検査例**であり、まだ実行できない。import を含む複数ファイル例は[段階0文書](standard-library.md)を参照する。

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

- `qif` は[意味論](language-spec.md)で `|0⟩⟨0|⊗U₀ + |1⟩⟨1|⊗U₁` と定める方向だが、`qif(control,target) { 0 => U0, 1 => U1 }` の `U0/U1` を第一級の値として扱うか、静的な関数名・枝本体として扱うかは未決である。v0 文法には入れず、制御元と標的の所有権を一度ずつ扱う具体的な枝構文と位相を保つ IR 変換を定めてから追加する。Bell 例は `entangle`、位相オラクル例は `with_computed` で書ける。
- `adjoint` は分類済み `unitary fn` の静的な逆演算として計画されている。構文、古典引数、呼び出しグラフ上の展開規則を決めるまで表層文法には入れない。
- 元レジスタを借用して作業レジスタ `R` を操作する一般の `with_computed`、静的反復、サイズ付きレジスタ、量子引数を取る高階関数、実行時の真理値表生成はこの文法にない。これらを追加するときは保護するワイヤ ID 集合、効果と検査可能な証拠を同時に定める。

### 残る整合確認

1. `std::basis::and2` を通常の `.qli` として実装するには、`not/xor` だけでは不十分である。基底 `and` をこの案に加え、[段階0文書](standard-library.md)と[言語仕様草案](language-spec.md)にも同期した。最終文法に採用するときに型と優先順位を固定する。
2. `with_computed` 本体に呼べる操作の保存効果を、関数境界を越えてどの署名・証拠で受け渡すか未確定。v0 の Bell・位相オラクルに必要な `z(a)` は組み込みの既知の位相ゲートとして判定できる。
3. `if` の枝で新たに作った量子ワイヤの ID と所有権トークンを合流させる形式規則、および `qif`・`adjoint` の表層構文は未確定。確定するまでは Stage 1 の文法・型規則の完了条件を満たさない。
