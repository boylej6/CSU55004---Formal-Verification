method isPrefix(pre:string, str:string) returns(res:bool)
    requires 0 <= |pre| <= |str| // This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 13: "str[i] != pre[i]"
{
    // Initialising the index variable
    var i := 0;

    //Iterating through the first |pre| elements in str
    while (i < |pre|)
        decreases |pre| - i //Specifying that the loop will terminate
    {
        //If an element does not match, return false
        if (str[i] != pre[i]) {
            //Debug print
            print str[i], " != ", pre[i], "\n";

            res := false;
            //Return once mismatch detected, no point in iterating any further
            return res;
        }
        //Else loop until mismatch found or we have reached the end of pre
        else{
            //Debug pront
            print str[i], " == ", pre[i], "\n";

            res := true;
            i := i + 1;
        }
    }
    return res;
}

method isSubstring(sub:string, str:string) returns(res:bool)
    requires 0 <= |sub| <= |str| //This line states that this method requires that sub is less than or equal in length to str
{
    //Initialising the index variable
    var j := 0;

    //This variable stores the difference in length between the two strings
    var n := (|str| - |sub|);

    //Here, we want to re-use the "isPrefix" method above, so with each iteration of the search, we are passing an offset of str - effectively trimming a character off the front of str and passing it to isPrefix
    
    //example 1 (sub found in str): 
    //str = door & sub = or
    //iteration 1: isPrefix(or, door), returns false, trim & iterate again
    //iteration 2: isprefix(or, oor), returns false, trim & iterate again
    //iteration 3: isPrefix(or, or), returns true, return

    //example 2 (sub not found in str):
    //str = doom & sub = or
    //iteration 1: isPrefix(or, doom), returns false, trim & iterate again
    //iteration 2: isprefix(or, oom), returns false, trim & iterate again
    //iteration 3: isPrefix(or, om), returns false, str is has not been "trimmed" to the same length as sub, so we stop iterating

    while(j < n+1)
        decreases n - j //Specifying that the loop will terminate
    {
        //Debug print to show what is being passed to isPrefix with each iteration
        print "\n", sub, ", ", str[j..|str|], "\n";

        res := isPrefix(sub, str[j..|str|]);

        //Return once the substring is found, no point in iterating any further
        if(res == true){
            return res;
        }
        //Else loop until sub is found, or we have reached the end of str
        else{
            j := j+1;
        }
    }
    return res;
}

method Main(){
    // isPrefix test
    var prefix:string := "pre";
    var str_1:string := "prehistoric";
    var result:bool;

    result := isPrefix(prefix, str_1);

    if(result == true){
        print "TRUE: ", prefix,  " is a prefix of the string ", str_1, "\n";
    }
    else{
        print "FALSE: ", prefix,  " is not a prefix of the string ", str_1, "\n";
    }

    // isSubstring test
    var substring := "and";
    var str_2 := "operand";

    result := isSubstring(substring, str_2);

    if(result == true){
        print "TRUE: ", substring,  " is a substring of the string ", str_2, "\n";
    }
    else{
        print "FALSE: ", substring,  " is not a substring of the string ", str_2, "\n";
    }
}
