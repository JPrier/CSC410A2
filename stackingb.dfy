method Game(n: nat) returns (score: nat)
    requires n > 0
    ensures score == n * (n - 1) / 2
{
    var stacks := [n];
    score := 0;

    while |stacks| > 0
        // invariant for LHS error in else part of loop
        invariant forall i :: 0 <= i < |stacks| ==> 1 <= stacks[i] <= n
        
        // score invariant
        invariant score == (n * (n - 1) / 2) - scoreCalcSum(stacks)
        
        // termination
        invariant score <= n * (n - 1) / 2
        decreases n * (n - 1) / 2 - score, |stacks|
    {
        var i :| 0 <= i < |stacks|;
        if stacks[i] == 1 {
            stacks := stacks[..i] + stacks[i + 1..];
        } else {
            var j, k :| stacks[i] == j + k && j > 0 && k > 0;
            score := score + j * k;
            stacks := [j, k] + stacks[..i] + stacks[i + 1..];
        }
    }
    return;
}

function scoreCalcSum(stacks: seq<nat>): nat
    requires forall i :: 0 <= i < |stacks| ==> 1 <= stacks[i]
    decreases |stacks|
{   
    if |stacks| == 0 then 0
    else scoreCalcSum(stacks[1..]) + (stacks[0] * (stacks[0] - 1) / 2)
}
