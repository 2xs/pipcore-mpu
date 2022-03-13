#include <stddef.h>

void *memcpy(void *dest, const void *src, size_t len)
{
	char *d = dest;
	const char *s = src;

	while (len--)
	{
		*d++ = *s++;
	}

	return dest;
}

void *memset(void *dest, int val, size_t len)
{
	unsigned char *ptr = dest;

	while (len-- > 0)
	{
		*ptr++ = val;
	}

	return dest;
}

size_t strlen(char *str)
{
	const char *s;

	for (s = str; *s; ++s);

	return (s - str);
}
/*
void vsnprintf(void)
{
	// TODO
	return;
}*/
