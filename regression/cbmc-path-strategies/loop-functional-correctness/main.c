int main()
{
  int x;
  __CPROVER_assume(x > 0);

  while(x)
    --x;

  assert(x);
}
