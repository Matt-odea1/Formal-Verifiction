// fastmul
method Fastmul(x:nat, y:nat) returns (product:nat)
    ensures product == x*y
{
    var halfx:nat := x;
    var douby:nat := y;
    product := 0;

    while halfx != 0

    invariant 0<=halfx<=x
    invariant y<=douby
    invariant product == x*y - douby*halfx
    decreases halfx

    {
        if (halfx%2 == 1) {product := product + douby;}
        halfx := halfx/2;
        douby := douby + douby;
    }

    return product;
}


method Main() {
    var a := Fastmul(0,0);
    var b := Fastmul(0,1);
    var c := Fastmul(1,0);
    var d := Fastmul(13, 8);
    var e := Fastmul(42, 10);
    var f := Fastmul(7, 3);
    //print d;
    assert a == 0;
    assert b == 0;
    assert c == 0;
    assert d == 104;
    assert e == 420;
    assert f == 21;
}