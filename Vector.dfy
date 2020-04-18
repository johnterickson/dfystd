include "Option.dfy"
include "NativeInts.dfy"

class Vector<T>
{
    var cells: array?<T>;
    var length: ArrayLength;

    constructor ()
        ensures Valid()
        ensures this.length == 0
        ensures this.cells == null
    {
        this.length := 0;
        this.cells := null;
    }

    predicate Valid()
        reads this
    {
        if this.cells == null then
            this.length == 0
        else (
            (0 < this.cells.Length) &&
            (this.cells.Length <= NativeIntConstants.MaxArrayLengthInt) &&
            (0 <= length <= cells.Length as ArrayLength)
        )
    }

    function method MaxIndex() : (i: ArrayIndex)
        requires this.length > 0
        requires Valid()
        reads this
        ensures i as int < this.cells.Length
    {
        (this.length - 1) as ArrayIndex
    }

    function method Length() : (l: ArrayLength)
        requires Valid()
        reads this
        ensures l == this.length
        ensures l as int == |this.sequence()|
    {
        this.length
    }

    method try_pop() returns (value: Option<T>)
        requires Valid()
        modifies this, this.cells
        ensures Valid()
        ensures old(this.cells) == this.cells
        ensures if old(this.length) > 0 then (
            (this.length == (old(this.length) - 1)) &&
            (value == Some(old(this.cells[this.length-1]))) &&
            (old(this.sequence()[..this.length-1]) == this.sequence()[..this.length])
        ) else (
            (this.length == old(this.length)) &&
            (value == None) &&
            (old(this.sequence()) == this.sequence())
        )
    {
        if (this.cells != null && this.length > 0) {
            this.length := this.length - 1;
            return Some(this.cells[this.length]);
        } else {
            return None;
        }
    }

    method allocOrGrow(value: T)
        requires Valid()
        requires this.cells == null || (
            this.length as int == this.cells.Length &&
            this.cells.Length < NativeIntConstants.MaxArrayLengthInt
            )
        modifies this
        ensures Valid()
        ensures old(this.length) == this.length
        ensures this.cells != null
        ensures fresh(this.cells)
        ensures old(this.sequence()) == this.sequence()[..this.length]
        ensures this.cells.Length > this.length as int
    {
        if (this.cells == null) {
            this.cells := new T[1](_ => value);
        } else {
            this.grow(value);
        }
    }

    method grow(filler: T)
        requires Valid()
        requires this.cells != null
        requires this.length as int == this.cells.Length
        requires this.cells.Length < NativeIntConstants.MaxArrayLengthInt
        modifies this
        ensures Valid()
        ensures old(length) == length
        ensures this.cells != null
        ensures fresh(this.cells)
        ensures this.cells.Length > old(this.cells.Length)
        ensures old(this.cells[..]) == this.cells[..old(this.cells.Length)]
    {
        var len := this.cells.Length as ArrayLength;

        var newLen: ArrayLength;
        if (len < NativeIntConstants.MaxArrayLength / (2 as ArrayLength)) {
            newLen := len * 2;
        } else {
            newLen := NativeIntConstants.MaxArrayLength;
        }

        var a := new T[newLen]((ii: int) reads this,cells => (
            assume 0 <= ii <= NativeIntConstants.MaxArrayIndex as int;
            var i: ArrayIndex := ii as ArrayIndex;
            assume cells == null || len as int == cells.Length;
            if cells == null then
                filler
            else if (i as ArrayLength) < len then
                cells[i]
            else
                filler
        ));

        this.cells := a;
    }

    method {:tailrecursion} bubble_up(idx: ArrayIndex, count: ArrayLength)
        decreases count
        requires Valid()
        requires count >= 2
        requires idx as int + count  as int <= this.Length() as int
        modifies this.cells
        ensures Valid()
        ensures old(this.cells) == this.cells
        ensures old(this.sequence()[..idx+1]) == this.sequence()[..idx+1]
        ensures old(this.sequence()[idx..idx as ArrayLength+count-1]) == this.sequence()[idx+1..idx as ArrayLength+count]
        ensures old(this.sequence()[idx as ArrayLength+count..]) == this.sequence()[idx as ArrayLength+count..]
    {
        ghost var orig_seq := this.sequence();
        var dst := idx as ArrayLength + count - 1;
        assert orig_seq[..idx+1] == this.sequence()[..idx+1];
        this.cells[dst] := this.cells[dst-1];
        if (count >= 3) {
            bubble_up(idx, count - 1);
            assert orig_seq[idx..dst-1] == this.sequence()[idx+1..dst];
            assert orig_seq[dst-1..dst] == this.sequence()[dst..dst+1];
            assert orig_seq[idx..dst-1] + orig_seq[dst-1..dst] == orig_seq[idx..dst];
            assert orig_seq[idx..dst] == this.sequence()[idx+1..dst+1];
        } else {
            assert orig_seq[idx..idx as ArrayLength+count-1] == this.sequence()[idx+1..idx as ArrayLength+count];
        }
    }

    method insert_at(idx: ArrayIndex, value: T)
        requires Valid()
        requires this.length < NativeIntConstants.MaxArrayLength
        requires 0 <= idx as ArrayLength < this.Length()
        modifies this, this.cells
        ensures Valid()
        ensures (old(this.cells) != this.cells) ==> fresh(this.cells)
        ensures old(|this.sequence()|) + 1 == |this.sequence()|
        ensures old(this.sequence()[..idx]) == this.sequence()[..idx]
        ensures value == this.sequence()[idx]
        ensures old(this.sequence()[idx..]) == this.sequence()[idx+1..]
        ensures old(this.sequence()[..idx] + [value] + this.sequence()[idx..]) == this.sequence()[..]
    {
        if (cells == null || length == cells.Length as ArrayLength)
        {
            this.allocOrGrow(value);
        }

        ghost var orig_seq := this.sequence();

        this.length := this.length + 1;
        assert orig_seq[..] == this.sequence()[..|orig_seq|];

        var count := this.length - idx as ArrayLength;
        bubble_up(idx, count);
        assert orig_seq[..idx] == this.sequence()[..idx];
        this.cells[idx] := value;
        
        assert |this.sequence()| == this.length as int;
        assert this.sequence()[idx+1..] == this.sequence()[idx+1..this.length];
        assert |orig_seq[idx..this.length-1]| == |this.sequence()[idx+1..this.length]|;
        assert orig_seq[idx..this.length-1] == this.sequence()[idx+1..this.length];
        assert orig_seq[idx..this.length-1] == this.sequence()[idx+1..];
    }

    method push(value: T)
        requires Valid()
        requires this.length < NativeIntConstants.MaxArrayLength
        modifies this, this.cells
        ensures Valid()
        ensures this.cells != null
        ensures (old(this.cells) != this.cells) ==> fresh(this.cells)
        ensures old(this.length) + 1 == this.length
        ensures old(this.cells == null) || old(this.cells[..this.length]) == this.cells[..(this.length-1)]
        ensures this.cells[this.length - 1] == value
    {
        if (cells == null || length == cells.Length as ArrayLength)
        {
            this.allocOrGrow(value);
        }

        this.cells[length] := value;
        length := length + 1 as ArrayLength;
    }

    function sequence() : (s: seq<T>)
        requires Valid()
        reads this, this.cells
        ensures |s| <= NativeIntConstants.MaxArrayLengthInt
        ensures |s| as ArrayLength == this.length
        ensures forall i :: 0 <= i < |s| ==> s[i..] == s[i..this.length]
    {
        if this.cells == null then [] else this.cells[..this.length]
    }

    function method get(i: ArrayIndex) : T
        requires Valid()
        requires i as ArrayLength < this.length
        reads this, this.cells
    {
        this.cells[i]
    }
}

method VectorTests()
{
    var v := new Vector<int>();
    assert [] == v.sequence();

    v.push(0);
    assert [0] == v.sequence();

    v.push(2);
    assert [0, 2] == v.sequence();

    v.insert_at(1, 1);
    assert [0, 1, 2] == v.sequence();

    var i := v.try_pop();
    assert Some(2) == i;
    assert [0, 1] == v.sequence();

    i := v.try_pop();
    assert Some(1) == i;
    assert [0] == v.sequence();

    i := v.try_pop();
    assert Some(0) == i;

    i := v.try_pop();
    assert None == i;
    assert [] == v.sequence();
}