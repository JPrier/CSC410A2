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
        invariant forall i,j,k :: 1 < i <= n && 1 < i == j+k && j > 0 && k > 0 ==> scoreCalc(j) + scoreCalc(k) + (j*k) == scoreCalc(i)
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

function scoreCalc(n: nat): nat
{
    n * (n - 1) / 2
}