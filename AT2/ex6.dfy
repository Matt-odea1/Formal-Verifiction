    // D O  N O T  C H A N G E  A N Y T H I N G  A B O V E  T H I S  L I N E
method Hash(z:nat) modifies this`shadow, this.buf
    requires Valid()
    requires m <= z+m-1 < n
    requires n-m >= 1
    // code
    ensures n == old(n)
    ensures m == old(m)
    ensures buf[z+m-1] == '#'
    ensures buf == old(buf)
    ensures forall i :: 0 <= i < z+m-1 ==> buf[i] == old(buf[i])
    ensures forall i :: z+m-1 < i < buf.Length-1 ==> buf[i] == old(buf[i]) 
    // have tried validating this using slicing also, works in postcondition but doesn't make asserts verify
    // shadow
    ensures |shadow| == |old(shadow)|
    ensures shadow[0..z-1] == old(shadow[0..z-1])
    ensures shadow[z-1] == '#'
    ensures shadow[z..] == old(shadow[z..])
    ensures Valid()
    {
        buf[z+m-1] := '#';
        shadow := shadow[z-1 := '#'];
    }

} // end of Quack class

method BasicValidator() // YOU MAY CHANGE THE VALIDATOR
{
   var q := new Quack(5); // plenty of room
   q.Push('A');
   q.Push('B');
   q.Push('C');
   q.Hash(1);             // zap A at location 1

   var c : char;
   c := q.Pop(); assert c=='C'; // top element
   // :( can't validate the array after elements below #
    c := q.Qop(); assert c=='#'; // bottom element
   c := q.Pop(); assert c=='B'; // last element

   var e: bool;
   e := q.Empty(); assert e; // check empty
}