#ifndef MSRE_EXTERN_H
#define MSRE_EXTERN_H

#include <sstream>
#include <list>
#include <algorithm>

#include <boost/mpi.hpp>
#include <boost/tuple/tuple.hpp>

using namespace std;
using namespace boost;
using namespace boost::tuples;

template <typename T>
int len(std::list<T>& ls) {
	return ls.size();
}

template <typename T>
tuple<list<T>,list<T> > split(list<T>& ls) {
	list<T> ls1, ls2;
	int ls1_size = ls.size() / 2;
	int count = 0;
	for(typename list<T>::iterator it=ls.begin(); it != ls.end() ; it++) {
		if (count < ls1_size) {
			ls1.push_back( *it );
		} else {
			ls2.push_back( *it );
		}
		count++;
	}
	return make_tuple(ls1,ls2);
}

template <typename T>
list<T> merge(list<T>& ls1, list<T>& ls2) {
	typename list<T>::iterator it1 = ls1.begin();
	typename list<T>::iterator it2 = ls2.begin();
	list<T> ls3;
	while(it1 != ls1.end() || it2 != ls2.end()) {
		if(it1 != ls1.end() && it2 != ls2.end()) {
			if (*it1 < *it2) {
				ls3.push_back( *it1 );
				it1++;
			} else {
				ls3.push_back( *it2 );
				it2++;
			}
		} else if(it1 != ls1.end()) {
			ls3.push_back( *it1 );
			it1++;
		} else {
			ls3.push_back( *it2 );
			it2++;
		}
	}
	return ls3;
}

template <typename T>
list<T> sort(list<T>& ls) {
	if (ls.size() > 1) {
		list<T> ls1, ls2;
		tie(ls1,ls2) = split(ls);
		list<T> ls3 = sort(ls1);
		list<T> ls4 = sort(ls2);
		list<T> s_ls = merge(ls3, ls4);
		return s_ls;
	} else {
		return ls;
	}
}

template <typename T>
T first(list<T>& ls) {
	return *(ls.begin());
}

template <typename T>
T computemedian(list<T>& ls) {
	int count = ls.size() / 2;
	typename list<T>::iterator it = ls.begin();
	while(count > 0) { it++; count--; }
	return *it;
}

template <typename T>
tuple<list<T>,list<T> > partition(list<T>& ls, T pv) {
	list<T> ls1, ls2;
	for(typename list<T>::iterator it=ls.begin(); it != ls.end(); it++) {
		if (*it <= pv) {
			ls1.push_back( *it );
		} else {
			ls2.push_back( *it );
		}
	}
	return make_tuple(ls1, ls2);
}

template <typename T>
list<tuple<T,T> > zip(list<T>& ls1, list<T>& ls2) {
	typename list<T>::iterator it1 = ls1.begin();
	typename list<T>::iterator it2 = ls2.begin();
	list<tuple<T,T> > ls;
	while(it1 != ls1.end() and it2 != ls2.end()) {
		ls.push_back( make_tuple(*it1,*it2) );
		it1++; it2++;
	}
	return ls;
}

template <typename T>
list<T> union_it(list<T>& ls1, list<T>& ls2) {
	list<T> ls;
	for(typename list<T>::iterator it=ls1.begin(); it!=ls1.end(); it++) {
		ls.push_back(*it);
	}
	for(typename list<T>::iterator it=ls2.begin(); it!=ls2.end(); it++) {
		ls.push_back(*it);
	}
	return ls;
}

template <typename T>
bool contains(list<T> ls, T a) {
	for(typename list<T>::iterator it=ls.begin(); it!=ls.end(); it++) {
		if(*it == a) {
			return true;
		}
	}
	return false;
}

template <typename T>
T pickone(list<T>& ls) {
	for(typename list<T>::iterator it=ls.begin(); it!=ls.end(); it++) {
		return *it;
	}
}

template <typename T>
tuple<T,T,int> reduce_min(list<tuple<T,T,int> >& ls) {
	int curr_min = 1000000000;
	tuple<T,T,int> curr_elem;
	for(typename list<tuple<T,T,int> >::iterator it=ls.begin(); it!=ls.end(); it++) {
		T t1; T t2; int val;
		tie(t1,t2,val) = *it;
		if (curr_min >= val) {
			curr_min  = val;
			curr_elem = *it;
		}
	}
	return curr_elem;
}

#endif /* MSRE_EXTERN */

