method Reverse(s: string)
decreases |s|
{
    if s!= [] {
        Reverse(s[1..]);
        print s[0];
    }
}


method Main() {
    var str: string 
    str := "Hello!\n";
    var output: string
    output := Reverse(str);
    print output;
}