include "./Option.dfy"
include "./NativeInts.dfy"

class ListEntry<T>
{
    constructor Single(v: T)
        ensures this.value == v;
        ensures this.next == null;
        ensures this.Contents == [v]
        ensures this.Repr == {this}
        ensures Valid()
    {
        this.value := v;
        this.next := null;
        this.Contents := [v];
        this.Repr := {this};
    }

    constructor Prepend(v: T, n: ListEntry<T>)
        requires n.Valid()
        ensures this.value == v;
        ensures this.next == n;
        ensures this.Contents == [v] + n.Contents
        ensures this.Repr == {this} + n.Repr
        ensures Valid()
    {
        this.value := v;
        this.next := n;
        this.Contents := [v] + n.Contents;
        this.Repr := {this} + n.Repr;
    }

    var value: T;
    var next: ListEntry?<T>;

    ghost var Contents: seq<T>
    ghost var Repr: set<object>

    predicate Valid()
        reads this, Repr
        decreases Repr
    {
        this in Repr &&
        1 <= |Contents| && Contents[0] == value &&
        (next == null ==> |Contents| == 1) &&
        (next != null ==> 
            next in Repr &&
            Repr > next.Repr &&
            this !in next.Repr && // not a loop
            next.Valid() &&
            next.Contents == Contents[1..]
        )
    }

    function Tail() : ListEntry<T>
        requires Valid()
        reads this, this.Repr
        decreases this.Repr //if this.next == null then {} else this.Repr
    {
        if this.next == null
            then this
            else this.next.Tail()
    }
}

class List<T>
{
    var first: ListEntry?<T>;
    var last: ListEntry?<T>;

    predicate Valid() 
        reads this,
            first, if first != null then first.Repr else {},
            last, if last != null then last.Repr else {}
    {
        ((first == null) ==> 
            last == null
        ) &&
        ((first != null) ==> 
            first.Valid() &&
            this !in first.Repr &&
            last != null && 
            last.Valid() &&
            this !in last.Repr &&
            last.next == null &&
            this.first.Tail() == last
        )

    }

    constructor()
        ensures Valid()
    {
        this.first := null;
        this.last := null;
    }

    constructor from(v: T)
        ensures Valid()
    {
        this.first := new ListEntry<T>.Single(v);
        this.last := this.first;
    }

    function Sequence() : seq<T>
        reads this, this.first
    {
        if this.first == null then [] else this.first.Contents
    }

    method prepend(v: T)
        requires Valid()
        modifies this
        ensures Valid()
        ensures [v] + old(this.Sequence()) == this.Sequence()
    {
        var n : ListEntry<T>;
        if (this.first == null) {
            n := new ListEntry<T>.Single(v);
            this.first := n;
            this.last := n;
        } else {
            n := new ListEntry<T>.Prepend(v, this.first);
            this.first := n;
        }
    }

    // method append(v: T)
    //     requires Valid()
    //     modifies this, this.last
    //     ensures Valid()
    // {
    //     var n := new ListEntry<T>.Single(v);
    //     if (this.first == null) {
    //         this.first := n;
    //         this.last := n;
    //     } else {
    //         this.last.next := n;
    //     }
    // }
}

method ListTest()
{
    var l := new List<int>();
    l.prepend(3);
    l.prepend(2);
    l.prepend(1);
}