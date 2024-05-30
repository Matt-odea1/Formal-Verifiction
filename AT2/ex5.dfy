// ex5
lemma {:induction false} LemmaCUBE(n: nat)
    ensures sumCube(n) == getSum(n)*getSum(n)
{
    SumtoN(n);
    if (n == 0)
        { assert sumCube(n) == getSum(n)*getSum(n) == 0; }
    else if (n == 1)
        { assert sumCube(n) == getSum(n)*getSum(n) == 1; }
    else if (n > 0)
        { 
        LemmaCUBE(n-1);
        assert 2*getSum(n) == (n)*(n+1);
        assert 4*getSum(n-1)*getSum(n-1) == (n*n)*(n-1)*(n-1);

        assert 4*(sumCube(n-1) + n*n*n) == (n*n) * (n+1)*(n+1);
        assert 4*sumCube(n-1) == (n*n) * (n+1)*(n+1) - 4*n*n*n;
        assert 4*sumCube(n-1) == (n*n) * ((n+1)*(n+1) - 4*n);
        assert 4*sumCube(n-1) == (n*n) * (n*n - 2*n + 1);
        assert 4*sumCube(n-1) == (n*n) * (n-1)*(n-1);
        assert sumCube(n-1) == getSum(n-1) * getSum(n-1);
        }
}

lemma SumtoN(n: nat)
    ensures 2*getSum(n) == n*(n+1)
{}

function getSum(n:nat):nat
{
    if n == 0 then n
    else n + getSum(n-1) 
}

function sumCube(n:nat):nat
{
    if n == 0 then n
    else n*n*n + sumCube(n-1)
}
