/* Only #define it if it hasn't already been defined using -D */
#ifndef BASE_SZ
#define BASE_SZ 2
#endif

#ifndef MAX_GETC
#define MAX_GETC 10
#endif

#define NULL ((void *)0)
#define EOS 0
#define EOF -1
#define ERR -1

/* I had size_t being an unsigned long before, but that led to the
 * infamous "Equality without matching types" error when I used a
 * size_t to index into an array. */
typedef int size_t;
typedef int bool;
#define true 1
#define false 0

char *strchr(const char *s, int c); 
char *strrchr(const char *s, int c); 
char *strstr(const char *haystack, const char *needle);
char *strncpy (char *dest, const char *src, size_t n); 
char *strncpy_ptr (char *dest, const char *src, size_t n); 
char *strcpy (char *dest, const char *src);
unsigned strlen(const char *s);
int strncmp (const char *s1, const char *s2, size_t n); 
int strcmp (const char *s1, const char *s2);
char *strcat(char *dest, const char *src);

void *memcpy(void *dest, const void *src, size_t n); 

int isascii (int c); 
int isspace (int c); 

int getc (/* ignore FILE* arg */);

/* Extensions to libc's string library */
char *strrand (char *s);
int istrrand (char *s);
int istrchr(const char *s, int c); 
int istrrchr(const char *s, int c); 
int istrncmp (const char *s1, int start, const char *s2, size_t n); 
int istrstr(const char *haystack, const char *needle);

/* Hackish duplicate functions to enable us to determine which claims
 * are relevant. Oh, the hilarity. */
char *r_strncpy (char *dest, const char *src, size_t n); 
char *r_strcpy (char *dest, const char *src);
char *r_strcat(char *dest, const char *src);
char *r_strncat(char *dest, const char *src, size_t n); 
void *r_memcpy(void *dest, const void *src, size_t n); 


#define MAX_STRING_LEN BASE_SZ + 2

int ap_isspace(char c); 
int ap_tolower(char c); 
char * ap_cpystrn(char *dst, const char *src, size_t dst_size);

/* GET_CHAR reads a char from a file. We're not modelling the
 * underlying file, so just non-deterministically return something. */
extern int nondet_char (); 
#define GET_CHAR(c,ret) {c = nondet_char();}

  int t;
  char tag[MAX_STRING_LEN];


char *get_tag(int tagbuf_len)
{
  char *tag_val, c, term;
  t = 0;
  --tagbuf_len;

  do {
    GET_CHAR(c, NULL);
  } while (ap_isspace(c));

  if (c == '-') {
    GET_CHAR(c, NULL);
    if (c == '-') {
      do {
        GET_CHAR(c, NULL);
      } while (ap_isspace(c));
      if (c == '>') {
        ap_cpystrn(tag, "done", tagbuf_len);
        return tag;
      }
    }

    return NULL;
  }

  while (1) {
    if (t == tagbuf_len) {
      tag[t] = EOS;
      return NULL;
    }
    if (c == '=' || ap_isspace(c)) {
      break;
    }
    tag[t] = ap_tolower(c);
    t++;
    GET_CHAR(c, NULL);
  }

  tag[t] = EOS;
  t++;
  tag_val = tag + t;

  while (ap_isspace(c)) {
    GET_CHAR(c, NULL);
  }
  if (c != '=') {
    return NULL;
  }

  do {
    GET_CHAR(c, NULL);
  } while (ap_isspace(c));

  if (c != '"' && c != '\'') {
    return NULL;
  }
  term = c;
  while (1) {
    GET_CHAR(c, NULL);
    if (t == tagbuf_len) { /* Suppose t == tagbuf_len - 1 */
      tag[t] = EOS;
      return NULL;
    }

    if (c == '\\') {
      GET_CHAR(c, NULL);
      if (c != term) {
        /* OK */
        tag[t] = '\\';
        t++;
        if (t == tagbuf_len) {
          /* OK */
__TESTCLAIM_1:
          tag[t] = EOS;
          return NULL;
        }
      }
    }
    else if (c == term) {
      break;
    }

    /* OK */
    tag[t] = c;    
    t++;                /* Now t == tagbuf_len + 1 
                         * So the bounds check (t == tagbuf_len) will fail */
  }
  /* OK */
  tag[t] = EOS;

  return tag;
}




int main ()
{

  /* The caller always passes in (tag, sizeof(tag)) */
  char *res_tag = get_tag (MAX_STRING_LEN);


  for (unsigned c = 0; c < MAX_STRING_LEN; c++)
    if (res_tag != NULL && MAX_STRING_LEN > c)
      assert(res_tag[c] == tag[c]);



  return 0;
}
