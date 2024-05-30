// The Product Rule of Exponentiation (PRE) is written xmxn = xm+n, 
// where we let x, m and n be natural numbers for this exercise. 
// For example, 2223 = 22+3 = 25 = 32 and 2020 = 20+0 = 1.

function powx(x:nat, n:nat):nat //recursive
{
if n==0 then 1 else x * powx(x, n-1)
}

lemma {:induction false} LemmaPRE(x:nat, m:nat, n:nat)
ensures powx(x,m)*powx(x,n) == powx(x, m+n)
decreases n
{
    if (n == 0)
        { assert powx(x,0)*powx(x,m) == powx(x, m+n); }
    else { LemmaPRE(x, m+1, n-1); }
}

//The “Greater-Than” Rule of Exponentiation (GRT) says that given natural numbers x and y, where x > y,
// and a natural number k,if k > 0 then x^k > y^k, and if k=0 then xk = yk = 1. For example, 
// give nx=3 and y=2,if k==4 then 34 > 24 and if k=0 then 3^0 = 2^0 = 1.

lemma {:induction false} LemmaGRT(x:nat, y:nat, k:nat)
requires x > y
ensures k != 0 ==> powx(x,k) > powx(y,k)
ensures k == 0 ==> powx(x,k) == powx(y,k) == 1
ensures x > y && k!= 0 <==> powx(x,k) > powx(y,k)
decreases k
{
    LemmaPRE(x, k, 1);
    LemmaPRE(y, k, 1);
    if (k==0)
        { assert powx(x,k) == 1 && powx(y,k) == 1; }
    else if (y == 0)
        {
        LemmaNotZero(x, k);
        assert powx(y,k) == 0;
        assert powx(x,k) != 0;
        assert powx(x,k) > powx(y,k);
        }
    else if (k==1)
        { assert powx(x,k) > powx(y,k); }
    else
        {
        LemmaGRT(x, y, k-1);
        assert powx(x, k) == powx(x, k-1)*x;
        assert powx(y, k) == powx(y, k-1)*y;
        LemmaGreaterThan(powx(x, k-1), powx(y, k-1), x, y);
        assert x*powx(x,k-1) > y*powx(y,k-1);
        assert powx(x,k) > powx(y,k);
        }
}

// sub lemma to prove if x>y and k1>k2, then x*k1 > y*k2
lemma LemmaGreaterThan(x:nat, y:nat, k1:nat, k2:nat)
    requires x > y && k2 != 0
    requires k1 > k2
    ensures k1 > k2 <==> x*k1 > y*k2
{
    assert x > y;
    assert k1 > k2;
    assert x*k1 > x*k2;
    assert x*(k2) > y*(k2);
    assert x*k1 > y*k2;
}

// sub lemma to prove if x!=0, x^n > 0 for nat numbers
lemma LemmaNotZero(x:nat, k:nat)
    ensures (x > 0) ==> powx(x,k) > 0
{
    if (x > 0) { assert powx(x,k) > 0; }
}

// Write a general validator for each lemma. Give the two validators different names of course.
method LemmaPREValidator()
{
    var n: nat;
    var m: nat;
    var x: nat;
    LemmaPRE(x,m,n);
    assert powx(x,m)*powx(x,n) == powx(x, m+n);
}

method LemmaGRTValidator ()
{
    var x:nat, y: nat :| x > y;
    var k: nat;
    k :| k > 0;
    LemmaGRT(x,y,k);
    assert powx(x,k) > powx(y,k);
    var k1 := 0;
    assert powx(x,k1) == powx(y,k1) == 1;
}
