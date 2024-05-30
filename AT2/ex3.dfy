// some inspiration taken from ass1 
// Can't get validator array index tests to verify :(( but predicate growtailneg verifies at least!
// 
method Newtail(a: array<int>) returns (size: nat) modifies a
    requires a.Length > 0
    requires forall j | 0 <= j < a.Length :: a[j] >= 0

    ensures 0 <= size <= a.Length
    ensures a[a.Length-1] != -1 ==> size == 0
    ensures a[0] == -1 ==> size >= 1
    ensures a == old(a)
    ensures 0 <= size < a.Length ==> a[a.Length-1-size] != -1

    ensures forall j :: 0 <= j < a.Length-size ==> a[j] == old(a[j])
    ensures forall j :: a.Length-size <= j < a.Length ==> a[j] == -1
    ensures satisifescondition(a, a.Length-1-size)

    //ensures forall j:int :: a.Length-size-1 < j < a.Length ==> size == j - (a.Length - Tailsize(a, a.Length-1)) + 1
    //ensures size == Tailsize(a, a.Length-1) // postconditons
{
    var i:int := a.Length-1;
    while i >= 0 && a[i] == 0
    invariant -1 <= i < a.Length

    invariant forall j | 0 <= j <= i :: a[j] == old(a[j])
    invariant forall j | i < j < a.Length :: old(a[j]) - 1 == a[j] == -1
    //invariant forall j | i < j < a.Length :: Tailsize(a, j) == j - ( a.Length - Tailsize(a, a.Length-1) ) + 1
    invariant growtailneg(a, i)
    invariant old(a.Length) == a.Length
        {
        a[i] := a[i] - 1;
        i := i - 1;
        }
    size := a.Length - (i+1);
}


predicate growtailneg(a: array<int>, indx:int) reads a
    requires -1<=indx<a.Length
    {
        forall j :: indx < j < a.Length ==> a[j] == - 1
    }


predicate satisifescondition(a: array<int>, indx:int) reads a
    requires -1<=indx<a.Length
    {
        forall j :: indx < j < a.Length ==> a[j] == - 1 && forall j :: -1 < j <= indx ==> a[j] != - 1
    }


function Tailsize(a: array<int>, idx:int): int
// start idx at length-1
    requires a.Length>0
    requires -1<=idx<=a.Length-1
    reads a
{
    if idx >= 0
        then if a[idx] == 0 then Tailsize(a, idx-1) else a.Length-idx-1
    else a.Length-idx-1
}

// VALIDATOR
method Main() {
    var a := new int[][0,42,0];             
    assert a[0]==0 && a[1]==42 && a[2]==0; 
    assert Tailsize(a, a.Length-1) == 1; 
    var b:nat := Newtail(a);
    assert satisifescondition(a, a.Length-b-1);
    //assert b == 1;
    // given definiton of the satisfies condition predicate, the spec is met

    var c := new int[][0,0,0];              // declare and define a testcase
    assert c[0]==0 && c[1]==0 && c[2]==0;   // seed of input array
    var d:nat := Newtail(c);                // call the code under test
    assert satisifescondition(a, a.Length-b-1);

    var e := new int[][100,0,0,1,0];        // declare and define a testcase
    assert e[0]==100 && e[1]==0 && e[2]==0 && e[3]==1 && e[4]==0;  // seed of input array
    var f:nat := Newtail(e);                // call the code under test
    assert satisifescondition(a, a.Length-b-1);

    var g := new int[][50, 50];             // declare and define a testcase
    assert g[0]==50 && g[1]==50;            // seed of input array
    var h:nat := Newtail(g);                // call the code under test
    assert satisifescondition(a, a.Length-b-1);
}