int bar()
{
  foo();
}

int foo()
{
  bar();
}

int main()
{
  foo();
}
