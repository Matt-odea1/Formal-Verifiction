method SumTonDown(n:int) returns (s:int)
    requires n >= 0
    ensures s == 0
    {
    var k:=n;
    s := k * (k + 1)/2;
    while k >= 0
    invariant -1 <= k <= n && s == (k + 1) * (k / 2)
        {
        s := s - k;
        k := k - 1;
    }
}
// change so that it iterates down from n to 0