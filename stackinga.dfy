method Game(n: nat) returns (score: nat)
    requires n > 0
    ensures score == n * (n - 1) / 2
{
    if n == 1 {
        score := 1 * (n-1) / 2;
        assert score == 0;
        return;
    }


    var stacks := [n];
    var stacks' := [n-1];
    score := 0;
    var score' := 0;

    while |stacks| > 0
        invariant forall i :: 0 <= i < |stacks| ==> 1 <= stacks[i] <= n
        invariant forall i' :: 0 <= i' < |stacks'| ==> 1 <= stacks'[i'] <= n-1
        invariant 0 <= sum(stacks) <= n
        invariant sumdecreases(stacks)
        decreases sum(stacks), |stacks|
    {
        var i :| 0 <= i < |stacks|;
        if stacks[i] == 1 {
            stacks := stacks[..i] + stacks[i + 1..];
        } else {
            var j, k :| stacks[i] == j + k && j > 0 && k > 0;
            score := score + j * k;
            stacks := [j, k] + stacks[..i] + stacks[i + 1..];
        }

        // var i' :| 0 <= i' < |stacks'|;
        // if stacks'[i'] == 1{
        //    stacks' := stacks'[..i] + stacks'[i + 1..];
        // } else {
        //     var j, k :| stacks'[i] == j + k && j > 0 && k > 0;
        //     score' := score' + j * k;
        //     stacks' := [j, k] + stacks'[..i] + stacks'[i + 1..];
        // }

    }

    calc {
        score;
        n * (n-1) / 2;
        (n-2+2) * (n-1) / 2;
        ((n-2) * (n-1) + 2 * (n-1)) / 2;
        ((n-1) * (n-2) / 2) + (2*(n-1)) / 2;
        ((n-1) * (n-2) / 2) + (n-1);
        score' + (n-1);
    }

    return;
}

function sum(list: seq<nat>): nat
    decreases |list|
{
    if |list| == 0 then 0  else list[0] + sum(list[1..])
}

function sumdecreases(stacks: seq<nat>): bool
    decreases sum(stacks)
{
    if stacks[0] == 1 then sumdecreases
}