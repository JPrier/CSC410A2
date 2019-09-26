//recursively choosing pairs according to the given nat
function method unpair(n: nat): (nat, nat)
{
  if n == 0 then
    (0,0)
  else
    var (x,y) := unpair(n-1);
    if y != 0 then
      (x+1, y-1)
    else
      (y, x+1)
}

// Show that unpair is correctly choosing pairs
function unpairCorrect(x: nat, y: nat): nat
  ensures unpair(unpairCorrect(x,y)) == (x,y)
  decreases x+y, x
{
  if x == 0 && y == 0 then
    0
  else if x > 0 then
    unpairCorrect(x-1, y+1) + 1
  else
    unpairCorrect(y-1, 0) + 1
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
      invariant t <= unpairCorrect(a, b)
      decreases unpairCorrect(a,b) - t // Termination
    { t := t + 1; }
}
