enum Colour
{
  PINK,
  RED,
  BLUE
};

void do_red()
{
  int a1;
  int a2;
  int a3;
  int a4;
  int a5;
  int a6;
  int a7;
  int a8;
  int a9;
  int a10;
  int a11;
  int a12;
  int a13;
  int a14;
  int a15;
  int a16;
  int a17;
  int a18;
  int a19;
  int a20;
}

void do_blue()
{
  int a1;
  int a2;
  int a3;
  int a4;
  int a5;
  int a6;
  int a7;
  int a8;
  int a9;
  int a10;
  int a11;
  int a12;
  int a13;
  int a14;
  int a15;
  int a16;
  int a17;
  int a18;
  int a19;
  int a20;
}

void do_pink()
{
  int a1;
  int a2;
  int a3;
  int a4;
  int a5;
  int a6;
  int a7;
  int a8;
  int a9;
  int a10;
  int a11;
  int a12;
  int a13;
  int a14;
  int a15;
  int a16;
  int a17;
  int a18;
  int a19;
  int a20;
}

enum Colour pop()
{
  int x, y;
  if(x)
    return PINK;
  else if(y)
    return RED;
  else
    return BLUE;
}

void dispatch()
{
  int x, y;
  while(1)
  {
    switch(pop())
    {
    case PINK:
      if(x)
      {
        do_pink();
        break;
      }
    case RED:
      if(y)
        do_red();
      break;
    case BLUE:
      do_blue();
      break;
    }
  }
}

int main()
{
  dispatch();
  return 0;
}
