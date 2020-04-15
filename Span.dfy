include "NativeInts.dfy"

class Span<T>
{
    var Array: array<T>;
    var Offset: ArrayIndex;
    var Count: ArrayLength;

    constructor(a: array<T>, offset: ArrayIndex, count: ArrayLength)
        requires ValidRange(a, offset, count)
        ensures Array == a && Offset == offset && Count == count
        ensures Array.Length == a.Length
        ensures forall i :: 0 <= i < Array.Length ==> Array[i] == a[i]
        ensures Valid()
    {
        Array := a;
        Offset := offset;
        Count := count;
    }

    static predicate ValidRange(a: array<T>, offset: ArrayIndex, count: ArrayLength)
    {
        (0 <= offset as int < a.Length) &&
        (0 <= offset as int < a.Length) &&
        (offset as int + count as int <= a.Length) &&
        (offset <= NativeIntConstants.MaxArrayIndex) &&
        (count <= NativeIntConstants.MaxArrayLength) &&
        (offset as int + count as int <= NativeIntConstants.MaxArrayLengthInt)
    }

    predicate Valid()
        reads this
    {
        ValidRange(Array, Offset, Count)
    }

    function before() : (s: seq<T>)
        requires Valid()
        reads this, this.Array
    {
        Array[..Offset]
    }

    static function index_offset(i: ArrayIndex, o: ArrayLength) : (ii: ArrayIndex)
        requires o as int <= NativeIntConstants.MaxArrayIndexInt
        requires (i as int) + (o as int) <= NativeIntConstants.MaxArrayIndexInt
        ensures (ii as int) == (i as int) + (o as int)
    {
        i+(o as ArrayIndex)
    }

    function after() : (s: seq<T>)
        requires Valid()
        reads this, this.Array
    {
        if (NativeIntConstants.MaxArrayLength - Count == Offset as ArrayLength)
            then []
            else Array[index_offset(Offset, Count)..]
    }

    function sequence() : (s: seq<T>)
        requires Valid()
        reads this, this.Array
        ensures |s| == Count as int
        ensures forall i :: 0 <= i < Count as int ==> s[i] == Array[i + Offset as int]
    {
        if (NativeIntConstants.MaxArrayLength - Count == Offset as ArrayLength)
            then Array[Offset..NativeIntConstants.MaxArrayLengthInt]
            else Array[Offset..index_offset(Offset, Count)]
    }

    function method get(idx: ArrayIndex) : (v: T)
        requires Valid()
        requires 0 <= idx as int < Count as int
        reads this, this.Array
        ensures this.Array[Offset+idx] == v
    {
        Array[Offset+idx]
    }

    method put(idx: ArrayIndex, v: T)
        requires Valid()
        requires 0 <= idx as int < Count as int
        modifies this.Array
        ensures old(Array.Length) == Array.Length
        ensures old(before()) == before()
        ensures old(sequence()[..idx]) == sequence()[..idx]
        ensures v == sequence()[idx]
        ensures idx == NativeIntConstants.MaxArrayIndex || old(sequence()[idx+1..]) == sequence()[idx+1..]
        ensures old(after()) == after()
    {
        Array[Offset+idx] := v;
    }

    method subspan(i: ArrayIndex, c: ArrayLength) returns (s: Span<T>)
        requires Valid()
        requires 0 <= i as int < Count as int
        requires 0 <= c < Count
        requires ValidRange(Array, Offset + i, c)
        requires 0 <= i as int + c as int <= Count as int
        ensures fresh(s)
        ensures s.Array == this.Array
        ensures s.Offset == this.Offset + i
        ensures s.Count == c
        ensures s.Valid()
        ensures s.sequence() == this.sequence()[i..i as int + c as int]
    {
        s := new Span<T>(Array, Offset + i, c);
    }
}

method SpanTest()
{
    var a := new i32[4];
    a[0 as ArrayIndex] := 0 as i32;
    a[1 as ArrayIndex] := 1 as i32;
    a[2 as ArrayIndex] := 2 as i32;
    a[3 as ArrayIndex] := 3 as i32;

    var s1 := new Span<i32>(a, 0, 1);
    assert s1.sequence() == [0];

    var s2 := new Span<i32>(a, 2, 2);
    assert s2.sequence() == [2,3];

    var s3 := s2.subspan(1,1);
    assert s3.sequence() == [3];
}