extern crate qleisli;
use qleisli::frontend::sized::ParsedProgram;
use std::collections::BTreeMap;
fn main() {
    for name in ["n", "Q", "Bits", "CBits", "Op", "Unit", "Bit", "CBit"] {
        let source = format!("pub unitary fn f[static {name}: Nat](q: Q<Bit>) -> Q<Bit> {{ if static {name} < 2 {{ q }} else {{ q }} }}");
        let result = ParsedProgram::parse(BTreeMap::from([("main".into(), source.clone())]))
            .and_then(|program| program.instantiate("main::f", BTreeMap::from([(name.into(), 1)]), BTreeMap::new()))
            .and_then(|instance| instance.elaborate()).map(|_| ());
        println!("{name}\t{}", result.map_or_else(|e| format!("REJECT: {e}"), |_| "ACCEPT".into()));
    }
}
