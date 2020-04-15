include "Option.dfy"
include "NativeInts.dfy"
include "Vector.dfy"

type Key = int
type PageNumber = int
datatype LeafCell<T> = LeafCell(key: Key, value: T)
datatype InnerCell = InnerCell(key: Key, child: PageNumber)
datatype Cell<T> = Cell(key: Key, value: T)



// method push_front<T>(s: Span<T>, v: T)
//     requires s.Valid()
//     requires s.Count > 1
//     modifies s.Array
//     ensures old(s.Count) + 1 == s.Count
//     ensures old(s.before()) == s.before()
//     ensures v == s.sequence()[0]
//     ensures old(s.sequence()[..]) == s.sequence()[1..]
//     ensures old(s.after()) == s.after()
// {
//     ghost var orig := s.sequence();


//     var doneIdx := s.Count;
//     while doneIdx > 1 
//         decreases doneIdx
//         invariant old(s.before()) == s.before()
//         invariant old(s.after()) == s.after()
//         invariant 1 <= doneIdx <= s.Count
//         invariant orig[..doneIdx] == s.sequence()[..doneIdx]
//         invariant orig[(doneIdx-1)..s.Count-1] == s.sequence()[doneIdx..s.Count]
//     {
//         assert orig[(doneIdx-1)..s.Count-1] == s.sequence()[doneIdx..s.Count];
//         doneIdx := doneIdx - 1;
//         assert orig[doneIdx..s.Count-1] == s.sequence()[(doneIdx+1)..s.Count];
//         ghost var x := s.sequence();
//         s.put(doneIdx, s.get(doneIdx-1));
//         assert orig[doneIdx..s.Count-1] == s.sequence()[(doneIdx+1)..s.Count];
//         assert orig[(doneIdx-1)] == s.sequence()[doneIdx-1];
//         assert orig[(doneIdx-1)] == s.sequence()[doneIdx];
//         assert |orig[(doneIdx-1)..s.Count-1]| == |s.sequence()[doneIdx..s.Count]|;
//         assert orig[(doneIdx-1)..s.Count-1] == s.sequence()[doneIdx..s.Count];
//     }

//     assert |orig[..(s.Count-1)]| == |s.sequence()[1..]|;
//     assert orig[..(s.Count-1)] == s.sequence()[1..];
// }

// method insert_at<T>(cells: Span<T>, idx: int, value: T)
//     requires 0 <= idx < cells.Count
//     modifies cells.Array
//     ensures old(cells.before()) == cells.before()
//     ensures cells.get(idx) == value
//     ensures old(cells.after()) == cells.after()
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


class Node<T> {
    var cells: Vector<Cell<T>>;

    constructor ()
        ensures Valid()
    {
        cells := new Vector<Cell<T>>();
    }

    predicate Valid()
        reads this, this.cells
    {
        (cells.Length() == 0) ||
        (forall i :: 0 <= i <= cells.MaxIndex() ==> 
            (forall j :: 0 <= j < i ==> cells.get(j).key < cells.get(i).key)
        )
    }


    method insert(key: Key, value: T) returns (idx: int)
        requires Valid()
        modifies this.cells
        ensures Valid()
        ensures idx < used
        ensures old(cells.Length) == cells.Length
        ensures idx >= 0 ==> 
            (old(used) + 1 == used) &&
            (old(cells[0..idx]) == cells[0..idx]) &&
            (forall i :: 0 <= i < idx ==> cells[i].value.key < key) && 
            (cells[idx] == Some(Cell(key,value))) &&
            (old(cells[idx..(cells.Length-1)]) == cells[(idx+1)..]) &&
            (forall i :: idx < i < used ==> key < cells[i].value.key)   
        ensures idx < 0 ==>
            (old(cells[..]) == cells[..]) &&
            (old(used) == used)
    {
        ghost var orig := cells[..];

        idx := 0;
        while idx < used && cells[idx].value.key < key
            decreases used - idx
            invariant orig[..] == cells[..]
            invariant 0 <= idx < cells.Length
            invariant idx <= used
            invariant forall j :: 0 <= j < idx ==> cells[j] != None && cells[j].value.key < key
        {
            idx := idx + 1;
        }

        assert forall j :: 0 <= j < idx ==> cells[j] != None && cells[j].value.key < key;
        if (idx == used) // add to end
        {
            assert cells[idx] == None;
            cells[idx] := Some(Cell(key, value));
            used := used + 1;
            return idx;
        }

        assert idx < used;
        assert cells[idx] != None;
        if (cells[idx].value.key == key) // conflict
        {
            return -1;
        }

        assert invariants();
        used := used + 1;
        insert_at(cells, idx, Some(Cell(key,value)));
        return idx;
    }
}

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

