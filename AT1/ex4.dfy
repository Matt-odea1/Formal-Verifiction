predicate no42(x:int)
    requires x != 42;
    { 0 < x < 100 }

predicate pete(x:int)
    // Ex4 Q1
    requires (x != 32 && x !=- 32)
    { if x > 0 then no42(x + 10) else no42(10 -x) }


method TruePete()
{
    assert forall x:int :: (0 < x < 90 && x != 32) ==> pete(x);
    assert forall x:int :: (-90 < x <=0 && x != -32) ==> pete(x);
    assert pete(89);
    assert pete(-89);
    assert pete(0);
}

method FalsePete()
{
    assert forall x:int :: (x <= -90) ==> !pete(x);
    assert forall x:int :: (x >= 90) ==> !pete(x);
    assert !pete(90);
    assert !pete(-90);
    // Note 32 and -32 are not worth testing, given they violate the wp
}
