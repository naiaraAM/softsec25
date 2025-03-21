method FindMin(a: seq<int>) returns (s: int)
  requires 0 < |a|
  ensures forall i :: 0 <= i < |a| ==> s <= a[i]
  ensures exists i :: 0 <= i < |a| && s == a[i]
{
  s := a[0];
  var k := 1;
  while k < |a|
  {
    if a[k] < s
    { s := a[k]; }
    k := k + 1;
  }
}
