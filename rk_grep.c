//Rabin-Karp Substring Matching
#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <getopt.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include <assert.h>
#include <time.h>
#include <ctype.h>

#include "rkgrep.h"
#include "bloom.h"

#define PRIME 961748941

// calculate modulo addition
long long
madd(long long a, long long b)
{
  return (a + b) % PRIME;
}

// calculate modulo substraction
long long
msub(long long a, long long b)
{
  return (a > b) ? (a - b) : (a + PRIME - b);
}

// calculate modulo multiplication
long long
mmul(long long a, long long b)
{
  return (a * b) % PRIME;
}

int naive_substring_match(const char *pattern, const char *doc, int *first_match_ind)
{
  int m = strlen(pattern);
  int n = strlen(doc);
  int count = 0;
  for (int i = 0; i <= (n - m); i++)
  {
    int numUnequal = 0;
    for (int j = 0; j < m; j++)
    {
      char *target1 = doc + i + j; //Target char from doc
      char *target2 = pattern + j; //Target char from pattern

      //If any two doesn't match make numUnequal as 1
      if (*target1 != *target2)
        numUnequal = 1;
    }

    //Case when pattern matched
    if (numUnequal == 0)
    {
      count++;
      if (count == 1)
        *first_match_ind = i;
    }
  }
  return count;
}

//get 256^x, x<m
long long pow(long long x, long long *list)
{
  if (x == 0)
  {
    *list = 1;
    return (long long)1;
  }
  else
  {
    long long p = pow(x - 1, list); //Get 256^(x-1)
    *(list + x) = mmul(((long long)256), p);
    return *(list + x);
  }
}

//  initialize the Rabin-karp hash computation by calculating
//  and returning the RK hash over a charbuf of m characters,

long long
rkhash_init(const char *charbuf, int m, long long *h)
{
  //Get the powers list
  long long powerL[m]; //A list of 256 pow
  for (int i = 0; i < m; i++)
    powerL[i] = 0;
  pow(m - 1, &(powerL[0]));

  long long init = 0;
  //Get the sum
  for (int j = 0; j <= m - 1; j++)
  {
    init = madd(init, mmul(powerL[m - 1 - j], *(charbuf + j)));
  }
  *h = mmul(powerL[m - 1], 256);
  return init;
}

//  Given the rabin-karp hash value (curr_hash) over substring Y[i],Y[i+1],...,Y[i+m-1]
//  calculate the hash value over Y[i+1],Y[i+2],...,Y[i+m] = curr_hash * 256 - leftmost * h + rightmost
//  where h is 256 raised to the power m (and given as an argument).
//  Note that *,-,+ refers to modular arithematic so you should use mmul, msub, madd.

long long
rkhash_next(long long curr_hash, long long h, char leftmost, char rightmost)
{
  curr_hash = mmul(curr_hash, 256);
  curr_hash = msub(curr_hash, mmul(leftmost, h));
  curr_hash = madd(curr_hash, rightmost);
  return curr_hash;
}

//Check if string x length m euqals y length m
//No Condition Check!!!
//0 for Equal; 1 o.w.
int equal(char *x, char *y, int m)
{
  int boo = 0;
  for (int j = 0; j < m; j++)
  {
    char *target1 = x + j;
    char *target2 = y + j;
    if (*target1 != *target2)
      boo = 1;
  }
  return boo;
}

int rk_substring_match(const char *pattern, const char *doc, int *first_match_ind)
{
  long long x = 0;
  long long *p = &x;
  int m = strlen(pattern);
  int n = strlen(doc);
  int count = 0;

  //Get 256^m
  long long h = 0;
  long long *hp = &h;

  //Initialize target hash and hashlist
  long long target = rkhash_init(pattern, m, p);
  long long hashlist[n];
  for (int i = 0; i < n; i++)
    hashlist[i] = (long long)0;

  //Loop thru the doc
  for (int i = 0; i <= n - m; i++)
  {

    //Local var of this loopthru
    long long current = 0;
    char *patternp = pattern;
    char *docp = doc + i;
    //get each hash value of the substr
    if (i == 0)
      current = rkhash_init(docp, m, hp);
    else
      current = rkhash_next(hashlist[i - 1], *hp, *(docp - 1), *(docp + m - 1));
    hashlist[i] = current;

    //Judge Equality, count++, first match
    if (current == target)
      if (equal(patternp, docp, m) == 0)
      {
        count++;
        if (count == 1)
          *first_match_ind = i;
      }
  }
  return count;
}

//Return 2^n, n<=7
char power(char n)
{
  if (n == 0)
    return 1;
  return 2 * power(n - 1);
}

//Mark the pos-th digit (start from 0) on the right
//as 1
void mark(char *c, int pos)
{
  char target = *c;
  target <<= (pos);
  target &= 128;
  //Case when the digit is already 1
  if (target != 0)
    return;
  //Else add 2^(7-pos)
  (*c) += (power(7 - pos));
}

//See if the pos-th digit is marked
bool isMark(char *c, int pos)
{
  char target = *c;
  target <<= (pos);
  target &= 128;
  //Case when the digit is already 1
  if (target != 0)
    return true;
  return false;
}

// rk_create_doc_bloom returns a pointer to a newly created bloom_filter.
//  The new bloom filter is populated with all n-m+1 rabin-karp hashes for
//  all the substrings of length m in "doc".
//  Hint: use the provided bloom_init() and your implementation of bloom_add() here.

bloom_filter *
rk_create_doc_bloom(int m, const char *doc, int bloom_size)
{
  //Get 256^m
  long long h = 0;
  long long *hp = &h;
  int n = strlen(doc);
  bloom_filter *bf = bloom_init(n - m + 1);
  //Get all hashings
  //Initialize target hash and hashlist
  long long hashlist[n];
  for (int i = 0; i < n; i++)
    hashlist[i] = (long long)0;

  //Get all the rkhash values
  for (int i = 0; i <= n - m; i++)
  {
    long long current = 0;
    char *docp = doc + i;
    if (i == 0)
      current = rkhash_init(docp, m, hp);
    else
      current = rkhash_next(hashlist[i - 1], *hp, *(docp - 1), *(docp + m - 1));
    hashlist[i] = current;
  }

  //add bloom
  for (int i = 0; i <= n - m; i++)
    bloom_add(bf, hashlist[i]);
  return bf;
}

int rk_substring_match_using_bloom(const char *pattern, const char *doc, bloom_filter *bf, int *first_match_ind)
{

  return 0;
}
