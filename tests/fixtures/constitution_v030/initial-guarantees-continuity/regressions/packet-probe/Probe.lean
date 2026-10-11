import Protocol.Validity

-- A 13-byte QLV1 packet with one body byte and no request.
#eval QleisliKernel.Protocol.Validity.packet { data := #[81,76,86,49,1,0,0,0,0,0,0,0,120] }
