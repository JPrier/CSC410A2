
// Helper function to give the functional specification
function sum(s : seq<int>) : int
{
    if s == [] then 0 else sum(s[..|s| -1]) + s[|s| - 1]
}

// The code of Maximum Tail Sum (MTS) computation

method MTS(a: array<int>) returns (mts: int)
    ensures forall i :: 0 <= i < a.Length  ==> sum(a[i..]) <= mts // postcondition for part (a)
    ensures exists i :: 0 <= i <= a.Length  && sum(a[i..]) == mts // postcondition for part (b)
{
   var i := 0;  
   mts := 0;

   while i < a.Length
   {
       mts := if mts + a[i] > 0 then mts + a[i]  else 0;        
       i := i + 1; 
   }
}
