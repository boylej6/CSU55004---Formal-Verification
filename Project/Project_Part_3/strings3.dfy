predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && 
	pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || 
	pre != str[..|pre|]
}

lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)
{
	//Initialising the index variable
    var i := 0;

	if(|pre| > |str|){
		return false;
	}

    //Iterating through the first |pre| elements in str
    while (i < |pre|)
        invariant 0 <= i <= |pre|                               //Specifying the range of the while loop
        decreases |pre| - i                                     //Specifying that the while loop will terminate
        invariant pre[..i] == str[..i]
    {
        //If an element does not match, return false
        if (str[i] != pre[i]) {
            //Debug print
            print str[i], " != ", pre[i], "\n";

            //Return once mismatch detected, no point in iterating any further
            return false;
        }
        //Else loop until mismatch found or we have reached the end of pre
        else{
            //Debug pront
            print str[i], " == ", pre[i], "\n";

            i := i + 1;
        }
    }
    return true;
}
predicate isSubstringPred(sub:string, str:string)
{
	(exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res <==> isSubstringPred(sub, str)
	//ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
	//Initialising the index variable
    var i := 0;

    //This variable stores the difference in length between the two strings
    var n := (|str| - |sub|);

	if( |sub| > |str| ){
		return false;
	}


    //Here, we want to re-use the "isPrefix" method above, so with each iteration of the search, we are passing an offset of str - effectively trimming a character off the front of str and passing it to isPrefix


    while(i <= n)
        invariant 0 <= i <= n+1     //Specifying the range of the while loop
        decreases n - i             //Specifying that the while loop will terminate
        invariant forall j :: 0 <= j < i ==> isNotPrefixPred( sub, str[j..] )
    {
        //Debug print to show what is being passed to isPrefix with each iteration
        print "\n", sub, ", ", str[i..], "\n";

        var result:= isPrefix(sub, str[i..]);

        //Return once the substring is found, no point in iterating any further
        if(result == true){
            assert( isPrefixPred( sub, str[i..]) );
            return true;
        }
        //Else loop until sub is found, or we have reached the end of str
        else{
            i := i+1;
        }
    }
    return false;

}
predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
	//Initialising the index variable
    var i := 0;

    //This variable is used to define the end condition of the while loop
    var n := |str1|-k;

    //Here, we want to re-use the "isSubstring" method above, so with each iteration of the search, we are passing a substring of str1 with length k and searching for this substring in str2. If the k-length substring is not found, we "slide" the length-k substring "window" along and search again
        //example:
        //str1 = operation, str2 = rational, k = 5
        //Iteration 1: isSubstring(opera, rational), returns false, slide the substring & iterate again
        //Iteration 2: isSubstring(perat, rational), returns false, slide the substring & iterate again
        //Iteration 3: isSubstring(erati, rational), returns false, slide the substring & iterate again
        //Iteration 4: isSubstring(ratio, rational), returns true, stop iterating

	if ( k > |str1| || k > |str2| ){
		return false;
	}


    while(i <= n)
        invariant 0 <= i <= n + 1
        decreases n - i //Specifying that the loop will terminate
        invariant forall j, l :: 0 <= j < i && l == j + k ==> isNotSubstringPred( str1[j..l], str2 )
    {
        //Debug print to show what is being passed to isSubstring with each iteration
        print "\n", str1[i..][..k], ", ", str2, "\n";
		var m := i + k;
        var result := isSubstring(str1[i..m], str2);

        //Return once the length-k substring is found, no point in iterating any further
        if(result == true){
            return true;
        }
        //Else loop until the length-k substring is found, or we have reached the end condition
        else{
            i:=i+1;
        }
    }
    return false;
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{
    //This variable is used to store the result of calling haveCommonKSubstring
    var result:bool;
    
    //We want the longest common substring between str1 and str2, so the starting point is going to be the shorter of the two strings.
    var i:= |str1|;

    //Here, we want to re-use the "haveKCommonSubstring" method above, so with each iteration of the search, we pass a decreasing value of k until a common substring of this length is found. If no common substring is found, we return 0.
    while (i > 0)
        invariant 0 <= i <= |str1|
        decreases i
        invariant forall j :: i < j <= |str1| ==> !haveCommonKSubstringPred(j, str1, str2)
    {
        print str1, ", ", str2, " k = ", i, "\n";
        
        result := haveCommonKSubstring(i, str1, str2);

        if(result == true){
            assert(forall k :: i < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2));
            assert(haveCommonKSubstringPred(i, str1, str2));
            return i;
        }
        else{
            i := i - 1;
        }
    }

    len := 0;

    assert isPrefixPred(str1[0..0], str2[0..]);
    return 0;
}


