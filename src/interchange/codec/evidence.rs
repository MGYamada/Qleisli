//! Type trees and references to independently reconstructed evidence.
use super::{Codec, Decoder, Encoder, Error, Result, Value};
use crate::contract::{BasisType, FunctionEvidence};
use std::sync::Arc;

impl Codec for BasisType {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        c.charge(1)?;
        Ok(match self {
            Self::Unit => Value::object([("tag", Value::String("unit".into()))]),
            Self::Bit => Value::object([("tag", Value::String("bit".into()))]),
            Self::Bits(width) => Value::object([
                ("tag", Value::String("bits".into())),
                ("width", width.write(c)?),
            ]),
            Self::Pair(a, b) => Value::object([
                ("tag", Value::String("pair".into())),
                ("left", a.write(c)?),
                ("right", b.write(c)?),
            ]),
            Self::Tuple(fields) => {
                if fields.len() < 3 {
                    return Err(Error::format("tuple type requires at least three fields"));
                }
                Value::object([
                    ("tag", Value::String("tuple".into())),
                    ("fields", fields.write(c)?),
                ])
            }
        })
    }
    fn read(v: &Value, _c: &Decoder<'_>) -> Result<Self> {
        match v.field("tag")?.text()? {
            "unit" => {
                v.fields(&["tag"])?;
                Ok(Self::Unit)
            }
            "bit" => {
                v.fields(&["tag"])?;
                Ok(Self::Bit)
            }
            "bits" => {
                v.fields(&["tag", "width"])?;
                Ok(Self::Bits(u32::read(v.field("width")?, _c)?))
            }
            "pair" => {
                v.fields(&["tag", "left", "right"])?;
                Ok(Self::pair(
                    Self::read(v.field("left")?, _c)?,
                    Self::read(v.field("right")?, _c)?,
                ))
            }
            "tuple" => {
                v.fields(&["tag", "fields"])?;
                let fields = Vec::<Self>::read(v.field("fields")?, _c)?;
                if fields.len() < 3 {
                    return Err(Error::format("tuple type requires at least three fields"));
                }
                Ok(Self::Tuple(fields))
            }
            _ => Err(Error::format("unknown basis type")),
        }
    }
}
impl Codec for Arc<FunctionEvidence> {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        Ok(Value::Number(c.evidence(self)? as u64))
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        let i = usize::read(v, c)?;
        c.evidence
            .get(i)
            .and_then(Option::as_ref)
            .cloned()
            .ok_or_else(|| Error::format("unchecked or invalid evidence reference"))
    }
}
