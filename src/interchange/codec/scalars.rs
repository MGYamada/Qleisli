//! Primitive wire values with explicit spellings and bounded integers.
use super::{Codec, Decoder, Encoder, Error, Result, Value};
use crate::ir::{ClassicalId, Effect, ProtectedRegion, ScalarPhase, SingleGate, TokenId, WireId};

impl Codec for bool {
    fn write(&self, _: &mut Encoder) -> Result<Value> {
        Ok(Value::Bool(*self))
    }
    fn read(v: &Value, _: &Decoder<'_>) -> Result<Self> {
        v.boolean()
    }
}
// The wire integer is u32 regardless of the host integer width. Check that
// bound before narrowing a field so the existing diagnostics retain precedence.
macro_rules! integer_codec {
    ($($ty:ty),+ $(,)?) => {$(
        impl Codec for $ty {
            fn write(&self, _: &mut Encoder) -> Result<Value> {
                let n = u32::try_from(*self)
                    .map_err(|_| Error::format("integer exceeds wire u32"))?;
                Ok(Value::Number(u64::from(n)))
            }
            fn read(v: &Value, _: &Decoder<'_>) -> Result<Self> {
                let n = u32::try_from(v.number()?)
                    .map_err(|_| Error::format("integer exceeds wire u32"))?;
                Self::try_from(n).map_err(|_| Error::format("integer outside field range"))
            }
        }
    )+};
}
integer_codec!(u8, u16, u32, usize);

impl Codec for TokenId {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        self.0.write(c)
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        Ok(Self(u32::read(v, c)?))
    }
}
impl Codec for WireId {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        self.0.write(c)
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        Ok(Self(u32::read(v, c)?))
    }
}
impl Codec for ClassicalId {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        self.0.write(c)
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        Ok(Self(u32::read(v, c)?))
    }
}
// Explicit wire spellings remain independent of Rust variant names.
macro_rules! enum_codec {
    ($ty:ty { $($variant:ident => $name:literal),+ $(,)? }) => {
        impl Codec for $ty {
            fn write(&self, _: &mut Encoder) -> Result<Value> {
                Ok(Value::String(match self { $(Self::$variant => $name),+ }.into()))
            }
            fn read(v: &Value, _: &Decoder<'_>) -> Result<Self> {
                match v.text()? {
                    $($name => Ok(Self::$variant),)+
                    _ => Err(Error::format("unknown enum spelling")),
                }
            }
        }
    };
}
enum_codec!(Effect { Unitary => "unitary", Iso => "iso", Observe => "observe" });
enum_codec!(SingleGate { H => "h", X => "x", Z => "z", T => "t" });
enum_codec!(ScalarPhase { MinusOne => "minus_one", EighthTurn => "eighth_turn" });
enum_codec!(ProtectedRegion { Source => "source", Ancilla => "ancilla" });
