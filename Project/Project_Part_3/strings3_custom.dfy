predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || pre != str[..|pre|]
}

lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)
	requires |pre| <= |str|
{
	if (pre == str[..|pre|]){
		return true;
	}
	else {
		return false;
	}
}

predicate isSubstringPred(sub:string, str:string)
{
	//(exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
	exists i :: 0 <= i < |str| - |sub| && isPrefixPred(sub, str[i..])
}

predicate isNotSubstringPred(sub:string, str:string)
{
	//(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
	forall i :: 0 <= i < |str| - |sub| ==> isNotPrefixPred(sub, str[i..])
}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
	requires 0 < |sub| <= |str|
	ensures  res <==> isSubstringPred(sub, str)
	ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
    var i := 0;

    var n := (|str| - |sub|);

    while(i < n)
        invariant 0 <= i <= n+1
        decreases n - i
        invariant forall j :: 0 <= j < i ==> isNotPrefixPred( sub, str[j..] )
    {
        var result:= isPrefix(sub, str[i..]);

        if(result == true){
            assert( isPrefixPred( sub, str[i..]) );
            return true;
        }
        else{
            i := i+1;
        }
    }
    return false;
}


predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	//exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
	exists i :: (0 <= i <= |str1| - k) && (0 <= k <= |str1|) && (0 < k <= |str2|) && isSubstringPred(str1[i..][..k], str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	//forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
	forall i :: (0 <= i <= |str1| - k) && (0 <= k <= |str1|) && (0 < k <= |str2|) ==> isNotSubstringPred(str1[i..][..k], str2)
}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	requires 0 < k <= |str1| &&  0 < k <= |str2|
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
	ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
    var i := 0;

    var n := |str1|-k;

    while(i <= n)
        invariant 0 <= i <= n + 1
        decreases n - i 
        invariant forall j :: 0 <= j < i ==> isNotSubstringPred( str1[j..][..k], str2 )
    {
        var result := isSubstring(str1[i..][..k], str2);

        if(result == true){
            return true;
        }
        else{
            i:=i+1;
        }
    }
    return false;
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures len != 0 ==> haveCommonKSubstringPred(len, str1, str2) && haveNotCommonKSubstringPred(len + 1, str1, str2)
{
    var result:bool;
    
    var i:= |str1|;
    if(|str2| < |str1|){
        i := |str2|;
    }

    while (i > 0)
        invariant 0 <= i <= |str1| && 0 <= i <= |str2|
        decreases i - 0
        invariant forall j :: i < j <= |str1| && i < j <= |str2| ==> haveNotCommonKSubstringPred(j, str1, str2)
    {
        result := haveCommonKSubstring(i, str1, str2);

        if(result == true){
            assert(haveNotCommonKSubstringPred(i + 1, str1, str2));
            assert(haveCommonKSubstringPred(i, str1, str2));
            return i;
        }
        else{
            i := i - 1;
        }
    }

    return 0;
}
