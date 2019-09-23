function method unpair(n: nat): (nat, nat)
{
    // Add an implementation for this
}

function method pick(i: nat): nat
{
  var (x, y) := unpair(i);
  x + i * y
}

method catchTheSpy(a: nat, b: nat)
{
var t := 0;
  // prove that this loop terminates and therefore the spy is caught
  while a + t * b != pick(t)
    { t := t + 1; }
}
