int bar()
{
  int x;
  foo();
}

int foo()
{
  bar();
  int x;
}

int main()
{
  foo();
}
