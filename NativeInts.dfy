newtype {:nativeType "int"} i32 = x | -0x8000_0000 <= x < 0x8000_0000
newtype {:nativeType "uint"} u32 = x | 0 <= x < 0x1_0000_0000
newtype {:nativeType "ulong"} u64 = x | 0 <= x < 0x1_0000_0000_0000_0000

newtype {:nativeType "int"} ArrayIndex = x | 0 <= x < 0x7FF0_0000
newtype {:nativeType "int"} ArrayLength = x | 0 <= x < 0x7FF0_0001


class NativeIntConstants {
    static const MaxArrayLengthInt := 0x7FF0_0000;
    static const MaxArrayIndexInt := 0x7FEF_FFFF;
    static const MaxArrayIndex: ArrayIndex := MaxArrayIndexInt as ArrayIndex;
    static const MaxArrayLength: ArrayLength := MaxArrayLengthInt as ArrayLength;

    ghost method checks() {
        assert MaxArrayIndexInt + 1 == MaxArrayLengthInt;
    }
}