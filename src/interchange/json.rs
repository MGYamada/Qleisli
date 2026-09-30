//! Strict bounded JSON for untrusted finite artifacts, with no code execution.
use super::{Error, Result};
use std::collections::BTreeMap;

pub(crate) const MAX_BYTES: usize = 16 << 20;
const MAX_VALUES: usize = 1_000_000;
const MAX_DEPTH: usize = 128;

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Value {
    Null,
    Bool(bool),
    Number(u64),
    String(String),
    Array(Vec<Value>),
    Object(BTreeMap<String, Value>),
}

impl Value {
    pub fn object(entries: impl IntoIterator<Item = (impl Into<String>, Value)>) -> Self {
        Self::Object(entries.into_iter().map(|(k, v)| (k.into(), v)).collect())
    }
    pub fn fields(&self, names: &[&str]) -> Result<&BTreeMap<String, Value>> {
        let Self::Object(fields) = self else {
            return Err(Error::format("expected object"));
        };
        if fields.len() != names.len() || names.iter().any(|k| !fields.contains_key(*k)) {
            return Err(Error::format(format!(
                "expected exactly fields {}",
                names.join(",")
            )));
        }
        Ok(fields)
    }
    pub fn field(&self, name: &str) -> Result<&Self> {
        match self {
            Self::Object(o) => o
                .get(name)
                .ok_or_else(|| Error::format(format!("missing field {name}"))),
            _ => Err(Error::format("expected object")),
        }
    }
    pub fn text(&self) -> Result<&str> {
        match self {
            Self::String(s) => Ok(s),
            _ => Err(Error::format("expected string")),
        }
    }
    pub fn number(&self) -> Result<u64> {
        match self {
            Self::Number(n) => Ok(*n),
            _ => Err(Error::format("expected unsigned integer")),
        }
    }
    pub fn boolean(&self) -> Result<bool> {
        match self {
            Self::Bool(b) => Ok(*b),
            _ => Err(Error::format("expected boolean")),
        }
    }
    pub fn array(&self) -> Result<&[Self]> {
        match self {
            Self::Array(a) => Ok(a),
            _ => Err(Error::format("expected array")),
        }
    }
}

struct Parser<'a> {
    source: &'a str,
    pos: usize,
    remaining: usize,
}
impl Parser<'_> {
    fn ws(&mut self) {
        while self
            .source
            .as_bytes()
            .get(self.pos)
            .is_some_and(|b| matches!(b, b' ' | b'\n' | b'\r' | b'\t'))
        {
            self.pos += 1;
        }
    }
    fn byte(&mut self, b: u8) -> Result<()> {
        self.ws();
        if self.source.as_bytes().get(self.pos) != Some(&b) {
            return Err(Error::format(format!(
                "expected byte {} at offset {}",
                b, self.pos
            )));
        }
        self.pos += 1;
        Ok(())
    }
    fn hex(&mut self) -> Result<u16> {
        let bytes = self
            .source
            .as_bytes()
            .get(self.pos..self.pos + 4)
            .ok_or_else(|| Error::format("truncated Unicode escape"))?;
        let mut value = 0;
        for &b in bytes {
            let digit = match b {
                b'0'..=b'9' => b - b'0',
                b'a'..=b'f' => b - b'a' + 10,
                b'A'..=b'F' => b - b'A' + 10,
                _ => return Err(Error::format("invalid Unicode escape")),
            };
            value = (value << 4) | u16::from(digit);
        }
        self.pos += 4;
        Ok(value)
    }
    fn string(&mut self) -> Result<String> {
        self.byte(b'"')?;
        let mut result = String::new();
        loop {
            let ch = self
                .source
                .get(self.pos..)
                .and_then(|s| s.chars().next())
                .ok_or_else(|| Error::format("unterminated string"))?;
            self.pos += ch.len_utf8();
            match ch {
                '"' => return Ok(result),
                '\\' => {
                    let b = *self
                        .source
                        .as_bytes()
                        .get(self.pos)
                        .ok_or_else(|| Error::format("truncated escape"))?;
                    self.pos += 1;
                    result.push(match b {
                        b'"' => '"',
                        b'\\' => '\\',
                        b'/' => '/',
                        b'b' => '\u{8}',
                        b'f' => '\u{c}',
                        b'n' => '\n',
                        b'r' => '\r',
                        b't' => '\t',
                        b'u' => {
                            let first = self.hex()?;
                            let scalar = if (0xd800..=0xdbff).contains(&first) {
                                if self.source.as_bytes().get(self.pos..self.pos + 2)
                                    != Some(b"\\u")
                                {
                                    return Err(Error::format("missing low surrogate"));
                                }
                                self.pos += 2;
                                let second = self.hex()?;
                                if !(0xdc00..=0xdfff).contains(&second) {
                                    return Err(Error::format("invalid low surrogate"));
                                }
                                0x10000
                                    + ((u32::from(first) - 0xd800) << 10)
                                    + (u32::from(second) - 0xdc00)
                            } else {
                                u32::from(first)
                            };
                            char::from_u32(scalar)
                                .ok_or_else(|| Error::format("invalid Unicode scalar"))?
                        }
                        _ => return Err(Error::format("invalid string escape")),
                    });
                }
                '\u{0}'..='\u{1f}' => return Err(Error::format("unescaped control character")),
                ch => result.push(ch),
            }
        }
    }
    fn value(&mut self, depth: usize) -> Result<Value> {
        if depth > MAX_DEPTH {
            return Err(Error::limit("JSON nesting exceeds 128"));
        }
        self.remaining = self
            .remaining
            .checked_sub(1)
            .ok_or_else(|| Error::limit("JSON exceeds one million values"))?;
        self.ws();
        let b = *self
            .source
            .as_bytes()
            .get(self.pos)
            .ok_or_else(|| Error::format("unexpected end of JSON"))?;
        match b {
            b'"' => Ok(Value::String(self.string()?)),
            b'[' => {
                self.pos += 1;
                self.ws();
                let mut a = Vec::new();
                if self.source.as_bytes().get(self.pos) == Some(&b']') {
                    self.pos += 1;
                    return Ok(Value::Array(a));
                }
                loop {
                    a.push(self.value(depth + 1)?);
                    self.ws();
                    if self.source.as_bytes().get(self.pos) == Some(&b']') {
                        self.pos += 1;
                        break;
                    }
                    self.byte(b',')?;
                }
                Ok(Value::Array(a))
            }
            b'{' => {
                self.pos += 1;
                self.ws();
                let mut o = BTreeMap::new();
                if self.source.as_bytes().get(self.pos) == Some(&b'}') {
                    self.pos += 1;
                    return Ok(Value::Object(o));
                }
                loop {
                    let key = self.string()?;
                    self.byte(b':')?;
                    let value = self.value(depth + 1)?;
                    if o.insert(key, value).is_some() {
                        return Err(Error::format("duplicate object key"));
                    }
                    self.ws();
                    if self.source.as_bytes().get(self.pos) == Some(&b'}') {
                        self.pos += 1;
                        break;
                    }
                    self.byte(b',')?;
                }
                Ok(Value::Object(o))
            }
            b'0'..=b'9' => {
                let start = self.pos;
                while self
                    .source
                    .as_bytes()
                    .get(self.pos)
                    .is_some_and(u8::is_ascii_digit)
                {
                    self.pos += 1;
                }
                let token = &self.source[start..self.pos];
                if token.len() > 1 && token.starts_with('0') {
                    return Err(Error::format("leading zero in integer"));
                }
                Ok(Value::Number(
                    token
                        .parse()
                        .map_err(|_| Error::format("integer exceeds u64"))?,
                ))
            }
            _ => {
                for (word, value) in [
                    ("null", Value::Null),
                    ("false", Value::Bool(false)),
                    ("true", Value::Bool(true)),
                ] {
                    if self.source[self.pos..].starts_with(word) {
                        self.pos += word.len();
                        return Ok(value);
                    }
                }
                Err(Error::format(
                    "expected JSON value (integer fields cannot contain floats, signs or exponents)",
                ))
            }
        }
    }
}

pub(crate) fn parse(bytes: &[u8]) -> Result<Value> {
    if bytes.len() > MAX_BYTES {
        return Err(Error::limit("artifact exceeds 16 MiB"));
    }
    let source = std::str::from_utf8(bytes).map_err(|_| Error::format("invalid UTF-8"))?;
    let mut parser = Parser {
        source,
        pos: 0,
        remaining: MAX_VALUES,
    };
    let result = parser.value(0)?;
    parser.ws();
    if parser.pos != source.len() {
        return Err(Error::format("trailing JSON data"));
    }
    Ok(result)
}

pub(crate) fn encode(value: &Value) -> Result<Vec<u8>> {
    use std::fmt::Write;
    fn quoted(s: &str, out: &mut String) {
        out.push('"');
        for c in s.chars() {
            match c {
                '"' => out.push_str("\\\""),
                '\\' => out.push_str("\\\\"),
                '\u{0}'..='\u{1f}' => write!(out, "\\u{:04x}", c as u32).unwrap(),
                _ => out.push(c),
            }
        }
        out.push('"');
    }
    fn write(v: &Value, out: &mut String, depth: usize) -> Result<()> {
        if depth > MAX_DEPTH {
            return Err(Error::limit("JSON nesting exceeds 128"));
        }
        match v {
            Value::Null => out.push_str("null"),
            Value::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Value::Number(n) => write!(out, "{n}").unwrap(),
            Value::String(s) => quoted(s, out),
            Value::Array(a) => {
                out.push('[');
                for (i, v) in a.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    write(v, out, depth + 1)?;
                }
                out.push(']');
            }
            Value::Object(o) => {
                out.push('{');
                for (i, (k, v)) in o.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    quoted(k, out);
                    out.push(':');
                    write(v, out, depth + 1)?;
                }
                out.push('}');
            }
        }
        if out.len() > MAX_BYTES {
            return Err(Error::limit("artifact exceeds 16 MiB"));
        }
        Ok(())
    }
    let mut out = String::new();
    write(value, &mut out, 0)?;
    out.push('\n');
    if out.len() > MAX_BYTES {
        return Err(Error::limit("artifact exceeds 16 MiB"));
    }
    Ok(out.into_bytes())
}
