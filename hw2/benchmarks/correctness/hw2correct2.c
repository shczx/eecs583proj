#include <stdio.h>

int main()
{
	int x = 2;
	int y = 3;
	int z = 4;
	if (x == 2)
	{
		z = y;
	}
	else
	{
		y = 6;
	}
	z = y;
	return 0;
}
