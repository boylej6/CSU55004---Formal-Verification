// True iff pre is a prefix of str
predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && pre == str[..|pre|]
}

// True iff pre is not a prefix of str
predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || pre != str[..|pre|]
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

// True iff sub is a substring of str
predicate isSubstringPred(sub:string, str:string)
{
  	exists i :: 0 <= i < |str| - |sub| && isPrefixPred(sub, str[i..])
}

// True iff sub is not s substring of str
predicate isNotSubstringPred(sub:string, str:string)
{
    forall i :: 0 <= i < |str| - |sub| ==> isNotPrefixPred(sub, str[i..])
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

// True iff str1 and str2 have a common substring of length k
predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	exists i :: (0 <= i <= |str1| - k) && (0 <= k <= |str1|) && (0 < k <= |str2|) && isSubstringPred(str1[i..][..k], str2)
}

// True iff str1 and str2 do not have a common substring of length k
predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	forall i :: (0 <= i <= |str1| - k) && (0 <= k <= |str1|) && (0 < k <= |str2|) ==> isNotSubstringPred(str1[i..][..k], str2)
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==> haveNotCommonKSubstringPred(k,str1,str2)
{}
