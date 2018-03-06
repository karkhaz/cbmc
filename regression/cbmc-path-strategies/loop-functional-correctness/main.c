int main()
{
  int x;
  __CPROVER_assume(x == 1);

  while(x)
    --x;

  assert(x);
}
