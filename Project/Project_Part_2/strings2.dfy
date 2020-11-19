predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	// TODO: your formula should not contain &&
	(|pre| > |str|) || pre != str[..|pre|]
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}


predicate isSubstringPred(sub:string, str:string)
{
	exists x :: 0 <= x < |str| - |sub| && isPrefixPred(sub, str[x..])
}

predicate isNotSubstringPred(sub:string, str:string)
{
	forall x :: 0 <= x < |str| - |sub| ==> isNotPrefixPred(sub, str[x..])
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}


predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	//TODO
	// exists x, j :: 0 <= x < |str1| - k && k <= |str1| && k <= |str2| && j == x + k && isSubstringPred(str1[x..j], str2)
	// 
	exists x :: 0 <= x < |str1| - k && k <= |str1| && k <= |str2| && isSubstringPred(str1[x..][..k], str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	//TODO: your FOL formula should start with a forall
	// Alternative
	// forall x :: ( 0 <= x < |str1| - k && k <= |str1| && k <= |str2| ) ==> exists j :: ( j == x + k && isNotSubstringPred( str1[x..j], str2 ) )
	// forall x, j :: 0 <= x < |str1| - k && k <= |str1| && k <= |str2| && j == x + k ==> isNotSubstringPred(str1[x..j], str2)
	forall x :: 0 <= x < |str1| - k && k <= |str1| && k <= |str2| ==> isNotSubstringPred(str1[x..][..k], str2)
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==> haveNotCommonKSubstringPred(k,str1,str2)
{}

