method Game(n: nat) returns (score: nat)
    requires n > 0
    ensures score == n * (n - 1) / 2
{
    var stacks := [n];
    ghost var stacks' := stacks;
    score := 0;

    while |stacks| > 0
        invariant forall i :: 0 <= i < |stacks| ==> |stacks| == |stacks[..i] + stacks[i..]|
        invariant forall i :: 0 <= i < |stacks| ==> |stacks| >= |stacks[..i] + stacks[i+1..]| && |stacks| - 1 == |stacks[..i] + stacks[i+1..]|
        invariant forall i :: 0 <= i < |stacks| ==> forall j,k :: stacks[i] == j + k && j>0 && k>0 ==> |stacks| + 1 == |[j, k] + stacks[..i] + stacks[i + 1..]|
        invariant 0 <= |stacks| <= n
        invariant 0 <= |stacks| <= sum(stacks) <= n
        
        decreases sum(stacks), |stacks|
        
    {
        var i :| 0 <= i < |stacks|;
        if stacks[i] == 1 {
            stacks' := stacks;
            stacks := stacks[..i] + stacks[i + 1..];
        } else {
            assume stacks[i] > 1;
            var j, k :| stacks[i] == j + k && j > 0 && k > 0;
            score := score + j * k;
            stacks' := stacks;
            stacks := [j, k] + stacks[..i] + stacks[i + 1..];
        }
    }

    return;
}

function sum(list: seq<nat>): nat
    decreases |list|
{
    if |list| == 0 then 0  else list[0] + sum(list[1..])
}
