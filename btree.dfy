
type Key = int
type PageNumber = int
datatype Option<T> = None | Some(value: T)
datatype LeafCell<T> = LeafCell(key: Key, value: T)
datatype InnerCell = InnerCell(key: Key, child: PageNumber)
datatype Cell<T> = Cell(key: Key, value: T)

class Span<T>
{
    var Array: array<T>;
    var Offset: int;
    var Count: int;

    function Valid() : bool 
        reads this
    {
        (0 <= Offset < Array.Length) &&
        (0 <= Count < Array.Length) &&
        (Offset + Count <= Array.Length)
    }

    // function method LastIndex() : (i: int)
    //     requires Valid()
    //     requires Count > 0
    //     reads this
    //     ensures i == (Offset + Count - 1)
    // {
    //     Offset + Count - 1
    // }

    function before() : (s: seq<T>)
        requires Valid()
        reads this, this.Array
    {
        Array[..Offset]
    }

    function after() : (s: seq<T>)
        requires Valid()
        reads this, this.Array
    {
        Array[Offset+Count..]
    }

    function method sequence() : (s: seq<T>)
        requires Valid()
        reads this, this.Array
    {
        Array[Offset..Offset+Count]
    }

    function method get(idx: int) : (v: T)
        requires Valid()
        requires 0 <= idx < Count
        reads this, this.Array
        ensures this.Array[Offset+idx] == v
    {
        Array[Offset+idx]
    }

    method put(idx: int, v: T)
        requires Valid()
        requires 0 <= idx < Count
        modifies this.Array
        ensures old(Array.Length) == Array.Length
        ensures old(before()) == before()
        ensures old(sequence()[..idx]) == sequence()[..idx]
        ensures v == sequence()[idx]
        ensures old(sequence()[idx+1..]) == sequence()[idx+1..]
        ensures old(after()) == after()
    {
        Array[Offset+idx] := v;
    }

}

method rotate_one<T>(s: Span<T>)
    requires s.Valid()
    requires s.Count > 1
    modifies s.Array
    ensures old(s.Array.Length) == s.Array.Length
    ensures old(s.before()) == s.before()
    ensures old(s.sequence()[..(s.Count-1)]) == s.sequence()[1..]
    ensures old(s.sequence()[s.Count-1]) == s.sequence()[0]
    ensures old(s.after()) == s.after()
{
    ghost var orig := s.sequence();

    var wrapped := s.Array[s.Offset+s.Count-1];

    var doneIdx := s.Count;
    while doneIdx > 1 
        decreases doneIdx
        invariant old(s.before()) == s.before()
        invariant old(s.after()) == s.after()
        invariant 1 <= doneIdx <= s.Count
        invariant orig[..doneIdx] == s.sequence()[..doneIdx]
        invariant orig[(doneIdx-1)..s.Count-1] == s.sequence()[doneIdx..s.Count]
    {
        assert orig[(doneIdx-1)..s.Count-1] == s.sequence()[doneIdx..s.Count];
        doneIdx := doneIdx - 1;
        assert orig[doneIdx..s.Count-1] == s.sequence()[(doneIdx+1)..s.Count];
        ghost var x := s.sequence();
        s.put(doneIdx, s.get(doneIdx-1));
        assert orig[doneIdx..s.Count-1] == s.sequence()[(doneIdx+1)..s.Count];
        assert orig[(doneIdx-1)] == s.sequence()[doneIdx-1];
        assert orig[(doneIdx-1)] == s.sequence()[doneIdx];
        assert |orig[(doneIdx-1)..s.Count-1]| == |s.sequence()[doneIdx..s.Count]|;
        assert orig[(doneIdx-1)..s.Count-1] == s.sequence()[doneIdx..s.Count];
    }

    assert |orig[..(s.Count-1)]| == |s.sequence()[1..]|;
    assert orig[..(s.Count-1)] == s.sequence()[1..];

    s.Array[s.Offset] := wrapped;
}

// method insert_at<T>(cells: array<T>, idx: int, value: T)
//     requires 0 <= idx < cells.Length
//     modifies cells
//     ensures old(cells.Length) == cells.Length
//     ensures old(cells[..idx]) == cells[..idx]
//     ensures cells[idx] == value
//     ensures old(cells[idx..(cells.Length-1)]) == cells[(idx+1)..]
// {
//     ghost var orig := cells[..];

//     var dst := cells.Length - 1;
//     while dst > idx 
//         decreases dst - idx
//         invariant 0 <= idx <= dst < cells.Length
//         invariant orig[..idx] == cells[..idx]
//         invariant orig[..dst] == cells[..dst]
//         invariant orig[dst..(cells.Length-1)] == cells[(dst+1)..]
//     {
//         cells[dst] := cells[dst-1];
//         dst := dst - 1;
//     }

//     assert dst == idx;

//     cells[idx] := value;
// }


// class Node<T> {
//     var cells: array<Option<Cell<T>>>;
//     var used: int;

//     constructor ()
//         ensures invariants()
//     {
//         var len := 10;
//         var c := new Option<Cell<T>>[len];
//         forall (i | 0 <= i < len) {
//             c[i] := None;
//         }
//         cells := c;
//         used := 0;
//     }

//     function invariants() : bool
//         reads this, this.cells
//     {
//         (0 <= used <= cells.Length) &&
//         (forall i :: 0 <= i < used ==> cells[i] != None) &&
//         (forall i :: used <= i < cells.Length ==> cells[i] == None) &&
//         (forall i :: 0 <= i < used ==> 
//             (forall j :: 0 <= j < i ==> cells[j].value.key < cells[i].value.key)
//         )
//     }


//     method insert(key: Key, value: T) returns (idx: int)
//         requires invariants()
//         requires used < cells.Length
//         modifies this, cells
//         ensures invariants()
//         ensures idx < used
//         ensures old(cells.Length) == cells.Length
//         ensures idx >= 0 ==> 
//             (old(used) + 1 == used) &&
//             (old(cells[0..idx]) == cells[0..idx]) &&
//             (forall i :: 0 <= i < idx ==> cells[i].value.key < key) && 
//             (cells[idx] == Some(Cell(key,value))) &&
//             (old(cells[idx..(cells.Length-1)]) == cells[(idx+1)..]) &&
//             (forall i :: idx < i < used ==> key < cells[i].value.key)   
//         ensures idx < 0 ==>
//             (old(cells[..]) == cells[..]) &&
//             (old(used) == used)
//     {
//         ghost var orig := cells[..];

//         idx := 0;
//         while idx < used && cells[idx].value.key < key
//             decreases used - idx
//             invariant orig[..] == cells[..]
//             invariant 0 <= idx < cells.Length
//             invariant idx <= used
//             invariant forall j :: 0 <= j < idx ==> cells[j] != None && cells[j].value.key < key
//         {
//             idx := idx + 1;
//         }

//         assert forall j :: 0 <= j < idx ==> cells[j] != None && cells[j].value.key < key;
//         if (idx == used) // add to end
//         {
//             assert cells[idx] == None;
//             cells[idx] := Some(Cell(key, value));
//             used := used + 1;
//             return idx;
//         }

//         assert idx < used;
//         assert cells[idx] != None;
//         if (cells[idx].value.key == key) // conflict
//         {
//             return -1;
//         }

//         assert invariants();
//         used := used + 1;
//         insert_at(cells, idx, Some(Cell(key,value)));
//         return idx;
//     }
// }

// class LeafNode<T>
// {
//     var cells: Node<LeafCell<T>>;

//     function invariants() : bool
//         reads this, this.cells, this.cells.cells
//     {
//         cells.invariants()
//     }

//     constructor()
//     {
//         cells := new Node<LeafCell<T>>();
//     }
// }

// class InnerNode {
//     var cells: Node<InnerCell>;

//     function invariants() : bool
//         reads this, this.cells, this.cells.cells
//     {
//         cells.invariants()
//     }

//     constructor()
//     {
//         cells := new Node<InnerCell>();
//     }
// }

