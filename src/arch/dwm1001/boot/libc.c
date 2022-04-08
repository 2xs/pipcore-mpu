#include <stddef.h>
#include <stdarg.h>

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

size_t strlen(const char *str)
{
	const char *s;

	for (s = str; *s; ++s);

	return (s - str);
}

int vsnprintf(char * s, size_t n, const char * format, va_list arg)
{
	/* TODO */
	(void) s;
	(void) n;
	(void) format;
	(void) arg;
	return 0;
}
