#ifndef MSRE_HASH_H
#define MSRE_HASH_H

#include <string.h>
#include <sstream>

#include <boost/tuple/tuple.hpp>

#ifndef MSRE_HASH_SALT
#define MSRE_HASH_SALT 0
#endif

using namespace std;
using namespace boost::tuples;


#define MSRE_PRIME1 1319
#define MSRE_PRIME2 7919
#define MSRE_PRIME3 13259
#define MSRE_PRIME4 31547
#define MSRE_PRIME5 53173
#define MSRE_PRIME6 72577
#define MSRE_PRIME7 91099
#define MSRE_PRIME8 103421
#define MSRE_PRIME9 224737
#define MSRE_PRIME10 350377

namespace msre {

inline size_t hash(const char* s) {
	size_t h = MSRE_HASH_SALT;
	while (*s) {
		h = h * 101 + (unsigned char) *s++;
	}
	return h;
}

inline size_t hash(string s) {
	return hash(s.c_str());
}

inline size_t hash(int x) {
	return x + MSRE_HASH_SALT;
}

inline size_t hash(float f) {
	return f * MSRE_PRIME7 + MSRE_HASH_SALT;
}

inline size_t hash(char c) {
	return (unsigned char) c;
}


template <typename T1, typename T2>
inline size_t hash(tuple<T1,T2> t) {
	T1 t1; T2 t2;
	tie(t1,t2) = t;
	return MSRE_HASH_SALT + hash(t1) * MSRE_PRIME1 + hash(t2) * MSRE_PRIME2;
}

template <typename T1, typename T2, typename T3>
inline size_t hash(tuple<T1,T2,T3> t) {
	T1 t1; T2 t2; T3 t3;
	tie(t1,t2,t3) = t;
	return MSRE_HASH_SALT + hash(t1) * MSRE_PRIME1 + hash(t2) * MSRE_PRIME2 + hash(t3) * MSRE_PRIME3;
}

template <typename T1, typename T2, typename T3, typename T4>
inline size_t hash(tuple<T1,T2,T3,T4> t) {
	T1 t1; T2 t2; T3 t3; T4 t4;
	tie(t1,t2,t3,t4) = t;
	return MSRE_HASH_SALT + hash(t1) * MSRE_PRIME1 + hash(t2) * MSRE_PRIME2 + hash(t3) * MSRE_PRIME3 + hash(t4) * MSRE_PRIME4;
}

template <typename T1, typename T2, typename T3, typename T4, typename T5>
inline size_t hash(tuple<T1,T2,T3,T4,T5> t) {
	T1 t1; T2 t2; T3 t3; T4 t4; T5 t5;
	tie(t1,t2,t3,t4,t5) = t;
	return MSRE_HASH_SALT + hash(t1) * MSRE_PRIME1 + hash(t2) * MSRE_PRIME2 + hash(t3) * MSRE_PRIME3 +
               hash(t4) * MSRE_PRIME4 + hash(t5) * MSRE_PRIME5;
}


template <typename T>
inline size_t hash(list<T> ls) {
	size_t h = MSRE_HASH_SALT;
	int seed = 0;
	for(typename list<T>::iterator it=ls.begin(); it != ls.end(); it++) {
		switch(seed % 10) {
			case 0: h += hash(*it) * MSRE_PRIME1; break;
			case 1: h += hash(*it) * MSRE_PRIME2; break;
			case 2: h += hash(*it) * MSRE_PRIME3; break;
			case 3: h += hash(*it) * MSRE_PRIME4; break;
			case 4: h += hash(*it) * MSRE_PRIME5; break;
			case 5: h += hash(*it) * MSRE_PRIME6; break;
			case 6: h += hash(*it) * MSRE_PRIME7; break;
			case 7: h += hash(*it) * MSRE_PRIME8; break;
			case 8: h += hash(*it) * MSRE_PRIME9; break;
			case 9: h += hash(*it) * MSRE_PRIME10; break;
		}
		seed++;
	}
	return h;
}

}


#endif /* MSRE_HASH_H */

