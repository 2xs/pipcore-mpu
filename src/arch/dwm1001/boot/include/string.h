#ifndef __STRING_H__
#define __STRING_H__

void *memcpy(void *dest, const void *src, size_t len);

void *memset(void *dest, int val, size_t len);

size_t strlen(const char *str);

#endif /* __STRING_H__ */
