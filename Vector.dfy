include "Option.dfy"
include "NativeInts.dfy"

class Vector<T>
{
    var cells: array?<T>;
    var used: ArrayLength;

    constructor ()
        ensures Valid()
        ensures this.used == 0
        ensures this.cells == null
    {
        this.used := 0;
        this.cells := null;
    }

    predicate Valid()
        reads this
    {
        if this.cells == null then
            this.used == 0
        else (
            (0 < this.cells.Length) &&
            (this.cells.Length <= NativeIntConstants.MaxArrayLengthInt) &&
            (0 <= used <= cells.Length as ArrayLength)
        )
    }

    function method MaxIndex() : (i: ArrayIndex)
        requires this.used > 0
        requires Valid()
        reads this
        ensures i as int < this.cells.Length
    {
        (this.used - 1) as ArrayIndex
    }

    function Length() : ArrayLength
        reads this
    {
        this.used
    }

    method try_pop() returns (value: Option<T>)
        requires Valid()
        modifies this, this.cells
        ensures Valid()
        ensures old(this.cells) == this.cells
        ensures if old(this.used) > 0 then (
            (this.used == (old(this.used) - 1)) &&
            (value == Some(old(this.cells[this.used-1]))) &&
            (old(this.sequence()[..this.used-1]) == this.sequence()[..this.used])
        ) else (
            (this.used == old(this.used)) &&
            (value == None) &&
            (old(this.sequence()) == this.sequence())
        )
    {
        if (this.cells != null && this.used > 0) {
            this.used := this.used - 1;
            return Some(this.cells[this.used]);
        } else {
            return None;
        }
    }

    method alloc(value: T)
        requires Valid()
        requires this.cells == null
        modifies this
        ensures Valid()
        ensures old(used) == used
        ensures this.cells != null && this.cells[..] == [value]
        ensures fresh(this.cells)
    {
        this.cells := new T[1](_ => value);
    }

    method allocOrGrow(value: T)
        requires Valid()
        requires this.cells == null || (
            this.used as int == this.cells.Length &&
            this.cells.Length < NativeIntConstants.MaxArrayLengthInt
            )
        modifies this
        ensures Valid()
        ensures old(this.used) == this.used
        ensures this.cells != null
        ensures fresh(this.cells)
        ensures old(this.sequence()) == this.sequence()[..this.used]
        ensures this.cells.Length > this.used as int
    {
        if (this.cells == null) {
            this.alloc(value);
        } else {
            this.grow(value);
        }
    }

    method grow(filler: T)
        requires Valid()
        requires this.cells != null
        requires this.used as int == this.cells.Length
        requires this.cells.Length < NativeIntConstants.MaxArrayLengthInt
        modifies this
        ensures Valid()
        ensures old(used) == used
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

    method insert_at(idx: ArrayIndex, value: T)
        requires Valid()
        requires this.used < NativeIntConstants.MaxArrayLength
        requires 0 <= idx as ArrayLength < this.Length()
        modifies this, this.cells
        ensures Valid()
        ensures this.cells != null
        ensures (old(this.cells) != this.cells) ==> fresh(this.cells)
        ensures old(this.used) + 1 == this.used
        ensures old(this.cells == null) ==> (
            this.cells.Length == 1 &&
            this.cells[0] == value
        )
        ensures old(this.cells != null) ==> (
            (old(this.cells.Length) <= this.cells.Length) &&
            (old(this.cells[..idx]) == this.cells[..idx]) &&
            (old(this.cells[idx..this.used]) == this.cells[idx+1..this.used])
        )
        ensures this.cells[idx] == value
    {
        ghost var orig := this.cells[..];

        if (cells == null || used == cells.Length as ArrayLength)
        {
            this.allocOrGrow(value);
            assert orig[..idx] == this.cells[..idx];
        }

        assert orig[..idx] == this.cells[..idx];

        this.used := this.used + 1;
        var dst := this.MaxIndex();
        assert idx <= dst;
        while dst > idx
            decreases dst as int - idx as int
            modifies this.cells
            invariant Valid()
            invariant this.cells != null
            invariant orig[..idx] == this.cells[..idx]
            invariant orig[used..] == this.cells[used..]
            invariant idx as int <= dst as int < this.used as int <= this.cells.Length
        {
            this.cells[dst] := this.cells[dst - 1];
            dst := dst - 1;
        }

        assert this.cells != null;

        this.cells[idx] := value;
    }

    method push(value: T)
        requires Valid()
        requires this.used < NativeIntConstants.MaxArrayLength
        modifies this, this.cells
        ensures Valid()
        ensures this.cells != null
        ensures (old(this.cells) != this.cells) ==> fresh(this.cells)
        ensures old(this.used) + 1 == this.used
        ensures old(this.cells == null) || old(this.cells[..this.used]) == this.cells[..(this.used-1)]
        ensures this.cells[this.used - 1] == value
    {
        if (cells == null || used == cells.Length as ArrayLength)
        {
            this.allocOrGrow(value);
        }

        this.cells[used] := value;
        used := used + 1 as ArrayLength;
    }

    function sequence() : (s: seq<T>)
        requires Valid()
        reads this, this.cells
        ensures |s| <= NativeIntConstants.MaxArrayLengthInt
        ensures |s| as ArrayLength == this.used
    {
        if this.cells == null then [] else this.cells[..this.used]
    }

    function method get(i: ArrayIndex) : T
        requires Valid()
        requires i as ArrayLength < this.used
        reads this, this.cells
    {
        this.cells[i]
    }
}

// method vector_test()
// {
//     var v := new Vector<int>();

//     assert [] == v.sequence();

//     v.push(0);
//     assert [0] == v.sequence();

//     v.push(1);
//     assert [0, 1] == v.sequence();

//     var i := v.try_pop();
//     assert Some(1) == i;

//     i := v.try_pop();
//     assert Some(0) == i;

//     i := v.try_pop();
//     assert None == i;
// }