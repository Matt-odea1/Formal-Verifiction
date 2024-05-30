// Strictmax
predicate ismax(s:seq<int>, max:int, lim:nat)
    requires |s| > 0
    requires 0<=lim<|s|
{
    forall j | 0<=j<=lim :: s[j] <= max &&
    exists j :: 0<=j<=lim && s[j] == max
}

method hasdup(s:seq<int>, idx:int) returns (outcome: bool)
    requires 0<=idx<|s|
    requires |s| > 0
    requires ismax(s, s[idx], |s|-1)
    ensures outcome == true <==> exists j :: 0 <= j < |s| && idx != j && s[idx] == s[j]
{
    var t := s[..idx] + s[idx+1..];
    assert |t| == |s| - 1;
    if |t| == 0 {return false;}
    if (s[idx] in t)
        {return true;}
    return false;
}

method Findmax(s: seq<int>) returns (max: int, idx: int)
    requires |s| > 0
    ensures 0 <= idx < |s|
    ensures ismax(s, max, |s|-1)
    ensures ismax(s, s[idx], |s|-1)
    ensures max == s[idx]

{
    var i:nat := 1;
    idx := 0;
    max := s[0];
    while (i < |s|)
    invariant 0 <= i <= |s|
    invariant 0 <= idx < i
    invariant ismax(s, max, i-1)
    invariant max == s[idx]
    {  
        if (s[i] > max)
            { 
                max := s[i];
                idx := i;
            }
        i := i + 1;
    }
    return max, idx;
}

method Strictmax(s:seq<int>) returns(max:int, idx:int)
    requires |s| > 0
    ensures -1<=idx<|s|
    ensures ismax(s, max, |s|-1)

    ensures idx == -1 <==> exists j,k :: 0 <= j < |s| && 0 <= k < |s| && k != j && s[k] == s[j] 
        && (ismax(s, s[k], |s|-1) && ismax(s, s[j], |s|-1))
    
    ensures 0<=idx<|s| ==> max == s[idx]
    ensures forall k :: 0 <= k < |s| ==> s[k] <= max
{
    max, idx := Findmax(s);
    var dup: bool := hasdup(s, idx);
    if dup { idx := -1; }

    return max, idx;
}

// VALIDATOR WORKS BUT IT NEEDS TERMS TO TRIGGER ON
method Main() {
    var s1:seq<int> := [0,1,2,3,5,2,5,3];
    var max1, idx1 := Strictmax(s1);
    assert max1 >= s1[4];
    assert max1 >= s1[6];
    assert max1 == 5;
    assert idx1 == -1;

    var s2:seq<int> := [4,2,10];
    var max2, idx2 := Strictmax(s2);
    assert max2 >= s2[2];
    assert max2 == 10;
    assert idx2 == 2;
    
    var s3:seq<int> := [3,3,3];
    var max3, idx3 := Strictmax(s3);
    assert max3 >= s3[0];
    assert max3 >= s3[1];
    assert max3 >= s3[2];
    assert max3 == 3;
    assert idx3 == -1;

    var s4:seq<int> := [-10, -5, 0, 0];
    var max4, idx4 := Strictmax(s4);
    assert max4 >= s4[3];
    assert max4 >= s4[2];
    assert max4 == 0;
    assert idx4 == -1;

    var s5:seq<int> := [1];
    var max5, idx5 := Strictmax(s5);
    assert max5 >= s5[0];
    assert max5 == 1;
    assert idx5 == 0;   
}