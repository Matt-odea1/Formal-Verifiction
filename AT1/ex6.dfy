method Tailsize(a: array<int>) returns (size: nat) 
    requires 0 < a.Length
    ensures 0 <= size <= a.Length
    ensures forall x :: (a.Length-size <= x <= a.Length-1) ==> a[x] == 0 || size == 0 
    {

    var index:int := a.Length - 1;
    size := 0;

    if a[index] != 0 { return 0; }

    // checking
    assert a[index] == 0;
    assert -1 < index;
    assert index < a.Length;

    while (-1 < index < a.Length) && (a[index] == 0)

    // unsure why dafny doesn't think loop will terminate?
    invariant forall j :: index <= j <= a.Length-1 ==> a[j] == 0
    invariant -1 < index < a.Length
        {
        index := index - 1;
        size := size + 1;
        }
    return size;
}

    // Recursive solution for validation
    //ensures size == recursiveValidate(a, a.Length - 1, 0);

/*
function recursiveValidate (a: array<int>, index:nat, currsize:nat):nat 
    requires 0 <= currsize
    //ensures 0 <= currsize <= a.Length
    reads a
    {
    if index == 0 && a[0] == 0 then currsize+1
    else if index == 0 && a[0] != 0 then currsize

    else if a[index] != 0 then currsize
    else recursiveValidate(a, index-1, currsize+1)
}
*/

method Validate()
       {
          var a := new int[][0,42,0];            // declare and define a testcase
          assert a[0]==0 && a[1]==42 && a[2]==0; // seed
          var s:nat := Tailsize(a);
          print s;              // call the code under test
          assert s == 1;                         // verify the result
}

/*
method ValidateRecursiveTest()
       {
          var a := new int[][0,42,0];            // declare and define a testcase
          assert a[0]==0 && a[1]==42 && a[2]==0; // seed
          var s:nat := recursiveValidate(a, a.Length-1, 0);              // call the code under test
          assert s == 1;                         // verify the result
}
*/
