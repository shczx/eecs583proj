#include <stdio.h>

int main(){
	int x = 2;
	int y = 3;
	int z = 1;
	if (x == 5)
	{
		z = x;
		if (y == 3)
		{
			z = y;
		}
		else {
			z = 0;
		}
	}
	else {
		z = y;
		if (y == 2)
		{
			z = y;
		}
		else {
			z = 0;
		}
	}
	printf("x: %i, y: %i, z: %i", x, y, z);
	return z;
}
