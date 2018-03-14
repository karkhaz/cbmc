int bar()
{
  int x;
}

int foo()
{
  int x;
  bar();
}

int main()
{
  int x;
  foo();
}
