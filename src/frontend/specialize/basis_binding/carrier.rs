//! Source-bound descriptions for the existing untrusted carrier request.
//! No logical map, accepted handle or execution capability is produced here.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;
use crate::frontend::types::{Kind, nominal::Body};
use crate::interchange::carrier::{Atom, Origin};

impl BasisBinding {
    /// Describe this exact closed source tree for an untrusted finite-carrier
    /// request. Names, declaration order, original source bytes and zero-width
    /// nodes remain explicit. This does not validate a logical map or authorize
    /// execution; the complete request still requires fresh native checking.
    /// The existing carrier profile permits six physical bits, 128 nodes and
    /// prefix depth 32. Preparation retains its 100000-cell work limit,
    /// independently of the broader host-binding and native metadata limits.
    pub fn carrier_description(&self) -> Result<Vec<Atom>> {
        let mut remaining = 100_000usize;
        describe(&self.ty, &mut |span, cells| {
            remaining = remaining.checked_sub(cells).ok_or_else(|| {
                Error::new("limit", span, "carrier preparation exceeds 100000 cells")
            })?;
            Ok(())
        })
    }
}

/// Preflight every retained copy before allocating the output description.
/// Physical widths only bound storage; they never substitute for cardinality,
/// nominal identity, logical coordinates or a native code-space equation.
pub(in crate::frontend) fn describe(
    ty: &SourceType,
    charge: &mut impl FnMut(Span, usize) -> Result<()>,
) -> Result<Vec<Atom>> {
    let span = Span::default();
    charge(span, 1)?;
    let mut pending = vec![(ty, 0usize)];
    let (mut nodes, mut bits) = (0usize, 0usize);
    while let Some((ty, depth)) = pending.pop() {
        charge(span, 2)?;
        nodes += 1;
        if depth > 32 || nodes > 128 {
            return Err(Error::new(
                "limit",
                span,
                "carrier tree exceeds 128 nodes or depth 32",
            ));
        }
        let width = match &ty.kind {
            Kind::Unit => 0,
            Kind::Bit => 1,
            Kind::Bits(n) => *n as usize,
            Kind::Tuple(fields) => {
                charge(span, fields.len())?;
                pending.extend(fields.iter().rev().map(|field| (field, depth + 1)));
                0
            }
            Kind::Nominal(nominal) => {
                // Includes complete source bytes and all names copied below.
                charge(span, nominal.metadata_cells() + nominal.fields().len())?;
                match &nominal.body {
                    Body::Enum(variants) => {
                        if variants.is_empty() || variants.len() > 64 {
                            return Err(Error::new(
                                "limit",
                                span,
                                "carrier enum requires 1 through 64 variants",
                            ));
                        }
                        usize::BITS as usize - (variants.len() - 1).leading_zeros() as usize
                    }
                    Body::Record(fields) => {
                        pending.extend(fields.iter().rev().map(|field| (&field.ty, depth + 1)));
                        0
                    }
                }
            }
            Kind::Q(_) | Kind::Parameter(_) => {
                return Err(Error::new(
                    "type",
                    span,
                    "carrier description requires an ordinary closed Basis",
                ));
            }
        };
        bits = bits
            .checked_add(width)
            .ok_or_else(|| Error::new("limit", span, "carrier width overflow"))?;
        if bits > 6 {
            return Err(Error::new(
                "limit",
                span,
                "carrier profile exceeds six physical bits",
            ));
        }
    }
    charge(span, nodes * 2)?;
    let mut result = Vec::with_capacity(nodes);
    let mut pending = vec![ty];
    while let Some(ty) = pending.pop() {
        result.push(match &ty.kind {
            Kind::Unit => Atom::Unit,
            Kind::Bit => Atom::Bit,
            Kind::Bits(n) => Atom::Bits(*n),
            Kind::Tuple(fields) => {
                pending.extend(fields.iter().rev());
                if fields.len() == 2 {
                    Atom::Pair
                } else {
                    Atom::Tuple(fields.len() as u32)
                }
            }
            Kind::Nominal(nominal) => {
                let origin = Arc::new(Origin {
                    module: nominal.origin.module.clone(),
                    declaration: nominal.origin.name.clone(),
                    source: nominal.origin.source.to_string(),
                });
                match &nominal.body {
                    Body::Enum(variants) => Atom::Enum(origin, variants.clone()),
                    Body::Record(fields) => {
                        pending.extend(fields.iter().rev().map(|field| &field.ty));
                        Atom::Record(
                            origin,
                            fields.iter().map(|field| field.name.clone()).collect(),
                        )
                    }
                }
            }
            Kind::Q(_) | Kind::Parameter(_) => unreachable!("closed Basis preflight"),
        });
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn original_aliases_record_order_and_zero_width_nominals_are_retained() {
        let source = "pub enum Tri{A,B,C} pub enum One{Only} pub struct Empty{}\n\
            static fn previous[const n:Nat]()->Nat requires n>=1{n-1}\n\
            pub struct Packet{pub tag:Tri,bit:Bit,zero:Bits<previous[1]()>}\n\
            pub struct Reversed{bit:Bit,pub tag:Tri,zero:Bits<0>}";
        let program = ParsedProgram::parse(
            crate::edition::Edition::E2026,
            BTreeMap::from([
                ("labels".into(), source.into()),
                ("facade".into(), "pub use labels::Packet;".into()),
            ]),
        )
        .unwrap();
        let packet = program
            .basis_binding("facade::Packet")
            .unwrap()
            .carrier_description()
            .unwrap();
        let Atom::Record(origin, fields) = &packet[0] else {
            panic!("original record")
        };
        assert_eq!(origin.module, "labels");
        assert_eq!(origin.declaration, "Packet");
        assert_eq!(origin.source, source);
        assert_eq!(fields, &["tag", "bit", "zero"]);
        assert!(
            matches!(&packet[1], Atom::Enum(origin, variants) if origin.module=="labels" && variants==&["A","B","C"])
        );
        assert_eq!(&packet[2..], &[Atom::Bit, Atom::Bits(0)]);
        assert_eq!(
            packet,
            program
                .basis_binding("labels::Packet")
                .unwrap()
                .carrier_description()
                .unwrap()
        );
        let reversed = program
            .basis_binding("labels::Reversed")
            .unwrap()
            .carrier_description()
            .unwrap();
        assert_eq!(reversed[1], Atom::Bit);
        assert!(matches!(&reversed[2], Atom::Enum(_, _)));
        assert_ne!(packet, reversed);
        let one = program
            .basis_binding("labels::One")
            .unwrap()
            .carrier_description()
            .unwrap();
        let empty = program
            .basis_binding("labels::Empty")
            .unwrap()
            .carrier_description()
            .unwrap();
        assert!(matches!(&one[..], [Atom::Enum(_, variants)] if variants==&["Only"]));
        assert!(matches!(&empty[..], [Atom::Record(_, fields)] if fields.is_empty()));
        assert_ne!(one, empty);
        assert_ne!(
            one,
            BasisBinding::parse("Unit")
                .unwrap()
                .carrier_description()
                .unwrap()
        );
        assert_ne!(
            empty,
            BasisBinding::parse("Bits<0>")
                .unwrap()
                .carrier_description()
                .unwrap()
        );
    }

    #[test]
    fn full_tuple_shape_and_existing_carrier_capacity_are_distinct_from_host_capacity() {
        assert_eq!(
            BasisBinding::parse("((Unit,Bit),Bits<0>)")
                .unwrap()
                .carrier_description()
                .unwrap(),
            [Atom::Pair, Atom::Pair, Atom::Unit, Atom::Bit, Atom::Bits(0)]
        );
        assert_eq!(
            BasisBinding::parse("(Unit,Bit,Bits<0>)")
                .unwrap()
                .carrier_description()
                .unwrap(),
            [Atom::Tuple(3), Atom::Unit, Atom::Bit, Atom::Bits(0)]
        );
        assert_eq!(
            BasisBinding::parse("Bits<6>")
                .unwrap()
                .carrier_description()
                .unwrap(),
            [Atom::Bits(6)]
        );
        assert_eq!(
            BasisBinding::parse("Bits<7>")
                .unwrap()
                .carrier_description()
                .unwrap_err()
                .code,
            "limit"
        );
        let mut nested = "Unit".to_owned();
        for _ in 0..32 {
            nested = format!("(Unit,{nested})");
        }
        assert_eq!(
            BasisBinding::parse(&nested)
                .unwrap()
                .carrier_description()
                .unwrap()
                .len(),
            65
        );
        nested = format!("(Unit,{nested})");
        assert_eq!(
            BasisBinding::parse(&nested)
                .unwrap()
                .carrier_description()
                .unwrap_err()
                .code,
            "limit"
        );
        fn balanced(leaves: usize) -> String {
            if leaves == 1 {
                "Unit".into()
            } else {
                format!(
                    "({},{})",
                    balanced(leaves / 2),
                    balanced(leaves - leaves / 2)
                )
            }
        }
        assert_eq!(
            BasisBinding::parse(&balanced(64))
                .unwrap()
                .carrier_description()
                .unwrap()
                .len(),
            127
        );
        assert_eq!(
            BasisBinding::parse(&balanced(65))
                .unwrap()
                .carrier_description()
                .unwrap_err()
                .code,
            "limit"
        );
    }

    #[test]
    fn complete_original_source_bytes_are_charged_before_output_copies() {
        let source = format!("// {}\npub enum One{{Only}}", "x".repeat(2048));
        let program = ParsedProgram::parse(
            crate::edition::Edition::E2026,
            BTreeMap::from([("labels".into(), source.clone())]),
        )
        .unwrap();
        let binding = program.basis_binding("labels::One").unwrap();
        let mut remaining = source.len() - 1;
        let error = describe(&binding.ty, &mut |span, cells| {
            remaining = remaining
                .checked_sub(cells)
                .ok_or_else(|| Error::new("limit", span, "bounded producer refusal"))?;
            Ok(())
        })
        .unwrap_err();
        assert_eq!(error.code, "limit");
        assert!(matches!(&binding.carrier_description().unwrap()[..],
            [Atom::Enum(origin,_)] if origin.source==source));
    }
}
