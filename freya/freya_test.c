#include "stdio.h"
#include "stdlib.h"

int main()
{
	void* m = malloc(105);
	malloc(202);
	free(m);
	malloc(401);
}