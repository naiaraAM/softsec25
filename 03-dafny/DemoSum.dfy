function sumto(n: nat): nat
{
  if (n == 0) then 0 else n + sumto(n-1)
}

method SumTo(n : nat) returns (s: nat)
ensures s == sumto(n)
{
  return n * (n+1) / 2;
}
