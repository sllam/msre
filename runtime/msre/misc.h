#ifndef MSRE_MISC_H
#define MSRE_MISC_H

#include <sstream>
#include <list>

#include <boost/mpi.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/container/map.hpp>

#include <boost/archive/text_oarchive.hpp>
#include <boost/archive/text_iarchive.hpp>

#include <boost/preprocessor/repetition.hpp>
#include <boost/tuple/tuple_comparison.hpp>
#include <boost/tuple/tuple_io.hpp>

using namespace std;
using namespace boost;
using namespace boost::tuples;

namespace bcont = boost::container;

namespace boost { namespace serialization {

    template<typename Archive, typename T1>

    void serialize(Archive & ar,
                   boost::tuples::cons<T1,boost::tuples::null_type> & t,

                   const unsigned int)
    {
      ar & boost::serialization::make_nvp("head",t.head);
    }

    template<typename Archive, typename T1, typename T2>

    void serialize(Archive & ar,
                   boost::tuples::cons<T1,T2> & t,

                   const unsigned int)
    {
      ar & boost::serialization::make_nvp("head",t.head);

      ar & boost::serialization::make_nvp("tail",t.tail);
    }

    template<typename Archive, typename T1>
    void serialize(Archive & ar,

                   boost::tuple<T1> & t,
                   const unsigned int)
    {
      ar & boost::serialization::make_nvp("head",t.head);
    }

#define GENERATE_TUPLE_SERIALIZE(z,nargs,unused)                            \
    template< typename Archive, BOOST_PP_ENUM_PARAMS(nargs,typename T) > \
    void serialize(Archive & ar,                                        \
                   boost::tuple< BOOST_PP_ENUM_PARAMS(nargs,T) > & t,   \
                   const unsigned int version)                          \
    {                                                                   \
      ar & boost::serialization::make_nvp("head",t.head);               \
      ar & boost::serialization::make_nvp("tail",t.tail);               \
    }


    BOOST_PP_REPEAT_FROM_TO(2,6,GENERATE_TUPLE_SERIALIZE,~);

}}


class Pretty {
	public: virtual std::string pretty() = 0;
};

class HTML {
	public: virtual std::string markdown(bcont::map<int,string> node_aliases) = 0;
	public: virtual std::string markdown() = 0;
};

template<typename T>
T reduce_sum(T value, int src_rank = 0) {
	boost::mpi::communicator world;
	if (world.rank() == src_rank) {
		T aggr;
		boost::mpi::reduce(world, value, aggr, std::plus<T>(), src_rank);
		return aggr;
	} else {
		boost::mpi::reduce(world, value, std::plus<T>(), src_rank);
		return 0;
	}	
}

template<typename T>
T reduce_max(T value, int src_rank = 0) {
	boost::mpi::communicator world;
	if (world.rank() == src_rank) {
		T aggr;
		boost::mpi::reduce(world, value, aggr, boost::mpi::maximum<T>(), src_rank);
		return aggr;
	} else {
		boost::mpi::reduce(world, value, boost::mpi::maximum<T>(), src_rank);
		return 0;
	}	
}

template<int N>
bool all_eq_sum(int ns1[N], int ns2[N], int src_rank=0, int tag=100) {
	const boost::mpi::communicator world;
	bool eqs [N];
	for(int x=0; x < N; x++) {
		int n1 = reduce_sum<int>(ns1[x], src_rank);
		int n2 = reduce_sum<int>(ns2[x], src_rank);
		eqs[x] = n1 == n2; 
		if (world.rank() == src_rank) { std::cout << n1 << " " << n2 << std::endl; }
	}
	int my_rank = world.rank();
	if (my_rank == src_rank) {
		int quiescence = 1;
		for(int x=0; x < N; x++) {
			if (not eqs[x]) {
				quiescence = 0;
				break;
			}
		}
		for (int target_rank=0; target_rank < world.size(); target_rank++) {
			if ( src_rank != target_rank ) { world.isend(target_rank, tag, quiescence); }
		} 
		return quiescence;
	} else {
		int quiescence;
		world.recv(src_rank, tag, quiescence);
		return quiescence;		
	}
}

/*
template <typename T>
std::string pretty_list(std::list<T> ls) {
	if(ls.size() == 0) { return "[]"; }
	std::stringstream ss;
	int count = 1;
	ss << "[";
	for(typename std::list<T>::iterator it = ls.begin(); it != ls.end(); it++) {
		if(count < ls.size()) {
			ss << (*it) << ",";
			count++;
		} else {
			ss << (*it) << "]";
		}
	}
	return ss.str();
}
*/

// Equality functions

inline bool is_eq(int i1, int i2) {
	return i1 == i2;
}

inline bool is_eq(char c1, char c2) {
	return c1 == c2;
}

inline bool is_eq(float f1, float f2) {
	return f1 == f2;
}

inline bool is_eq(string s1, string s2) {
	return s1 == s2;
}

template<typename T1, typename T2>
inline bool is_eq(tuple<T1,T2> ta, tuple<T1,T2> tb){
	T1 ta1; T2 ta2;
	T1 tb1; T2 tb2;
	tie(ta1,ta2) = ta;
	tie(tb1,tb2) = tb;
	return is_eq(ta1,tb1) && is_eq(ta2, tb2);
}

template<typename T1, typename T2, typename T3>
inline bool is_eq(tuple<T1,T2,T3> ta, tuple<T1,T2,T3> tb){
	T1 ta1; T2 ta2; T3 ta3;
	T1 tb1; T2 tb2; T3 tb3;
	tie(ta1,ta2,ta3) = ta;
	tie(tb1,tb2,tb3) = tb;
	return is_eq(ta1,tb1) && is_eq(ta2,tb2) && is_eq(ta3,tb3);
}

template<typename T1, typename T2, typename T3, typename T4>
inline bool is_eq(tuple<T1,T2,T3,T4> ta, tuple<T1,T2,T3,T4> tb){
	T1 ta1; T2 ta2; T3 ta3; T4 ta4;
	T1 tb1; T2 tb2; T3 tb3; T4 tb4;
	tie(ta1,ta2,ta3,ta4) = ta;
	tie(tb1,tb2,tb3,tb4) = tb;
	return is_eq(ta1,tb1) && is_eq(ta2,tb2) && is_eq(ta3,tb3) && is_eq(ta4,tb4);
}

template<typename T1, typename T2, typename T3, typename T4, typename T5>
inline bool is_eq(tuple<T1,T2,T3,T4,T5> ta, tuple<T1,T2,T3,T4,T5> tb){
	T1 ta1; T2 ta2; T3 ta3; T4 ta4; T5 ta5;
	T1 tb1; T2 tb2; T3 tb3; T4 tb4; T5 tb5;
	tie(ta1,ta2,ta3,ta4,ta5) = ta;
	tie(tb1,tb2,tb3,tb4,tb5) = tb;
	return is_eq(ta1,tb1) && is_eq(ta2,tb2) && is_eq(ta3,tb3) && is_eq(ta4,tb4) && is_eq(ta5,tb5);
}

template <typename T>
inline bool is_eq(list<T>& ls1, list<T>& ls2) {
	if(ls1.size() != ls2.size()) { return false; }
	typename list<T>::iterator it1 = ls1.begin();
	typename list<T>::iterator it2 = ls2.begin();
	while(it1 != ls1.end()) {
		if(!is_eq(*it1,*it2)) { return false; }
		it1++; it2++;
	}
	return true;
}


// To String functions

inline std::string to_str(int i) {
	std::stringstream ss;
	ss << i;
	return ss.str();
}

inline std::string to_str(float f) {
	std::stringstream ss;
	ss << f;
	return ss.str();
}

inline std::string to_str(char c) {
	std::stringstream ss;
	ss << c;
	return ss.str();
}

inline std::string to_str(std::string s) {
	return s;
}

template <typename T1, typename T2>
inline std::string to_str(tuple<T1,T2> t) {
	T1 t1; T2 t2;
	tie(t1,t2) = t;
	std::stringstream ss;
	ss << "(" << to_str(t1) << "," << to_str(t2) << ")";
	return ss.str();
}

template <typename T1, typename T2, typename T3>
inline std::string to_str(tuple<T1,T2,T3> t) {
	T1 t1; T2 t2; T3 t3;
	tie(t1,t2,t3) = t;
	std::stringstream ss;
	ss << "(" << to_str(t1) << "," << to_str(t2) << "," << to_str(t3) << ")";
	return ss.str();
}

template <typename T1, typename T2, typename T3, typename T4>
inline std::string to_str(tuple<T1,T2,T3,T4> t) {
	T1 t1; T2 t2; T3 t3; T4 t4;
	tie(t1,t2,t3,t4) = t;
	std::stringstream ss;
	ss << "(" << to_str(t1) << "," << to_str(t2) << "," << to_str(t3) << "," << to_str(t4) << ")";
	return ss.str();
}

template <typename T1, typename T2, typename T3, typename T4, typename T5>
inline std::string to_str(tuple<T1,T2,T3,T4,T5> t) {
	T1 t1; T2 t2; T3 t3; T4 t4; T5 t5;
	tie(t1,t2,t3,t4,t5) = t;
	std::stringstream ss;
	ss << "(" << to_str(t1) << "," << to_str(t2) << "," << to_str(t3) << "," << to_str(t4) << "," << to_str(t5) << ")";
	return ss.str();
}

template <typename T>
inline std::string to_str(std::list<T> ls) {
	if(ls.size() == 0) { return "[]"; }
	std::stringstream ss;
	int count = 1;
	ss << "[";
	for(typename std::list<T>::iterator it = ls.begin(); it != ls.end(); it++) {
		if(count < ls.size()) {
			ss << to_str(*it) << ",";
			count++;
		} else {
			ss << to_str(*it) << "]";
		}
	}
	return ss.str();
}

// Deep Copy function.

inline int dcopy(int i) {
	return i;
}

inline char dcopy(char c) {
	return c;
}

inline float dcopy(float f) {
	return f;
}

inline std::string dcopy(std::string s) {
	stringstream ss;
	ss << s;
	return ss.str();
} 

/*
template<typename T1, typename T2>
inline cons<T1,T2> dcopy(cons<T1,T2> t) {
	cons<T1,T2> new_t;
	new_t.head = dcopy( t.head );
	new_t.tail = dcopy( t.tail );
	return new_t;
} */

template<typename T1>
inline tuple<T1> dcopy(tuple<T1> t) {
	T1 t1;
	tie(t1) = t;
	return make_tuple(dcopy(t1));
}

template<typename T1, typename T2>
inline tuple<T1,T2> dcopy(tuple<T1,T2> t) {
	T1 t1; T2 t2;
	tie(t1,t2) = t;
	return make_tuple(dcopy(t1),dcopy(t2));
}

template<typename T1, typename T2, typename T3>
inline tuple<T1,T2,T3> dcopy(tuple<T1,T2,T3> t) {
	T1 t1; T2 t2; T3 t3;
	tie(t1,t2,t3) = t;
	return make_tuple(dcopy(t1),dcopy(t2),dcopy(t3));
}

template<typename T1, typename T2, typename T3, typename T4>
inline tuple<T1,T2,T3,T4> dcopy(tuple<T1,T2,T3,T4> t) {
	T1 t1; T2 t2; T3 t3; T4 t4;
	tie(t1,t2,t3,t4) = t;
	return make_tuple(dcopy(t1),dcopy(t2),dcopy(t3),dcopy(t4));
}

template<typename T1, typename T2, typename T3, typename T4, typename T5>
inline tuple<T1,T2,T3,T4,T5> dcopy(tuple<T1,T2,T3,T4,T5> t) {
	T1 t1; T2 t2; T3 t3; T4 t4; T5 t5;
	tie(t1,t2,t3,t4,t5) = t;
	return make_tuple(dcopy(t1),dcopy(t2),dcopy(t3),dcopy(t4),dcopy(t5));
}

template <typename T>
inline list<T> dcopy(list<T> ls) {
	list<T> new_ls;
	for(typename list<T>::iterator it=ls.begin(); it != ls.end(); it++) {
		new_ls.push_back( dcopy(*it) );
	}
	return new_ls;
}

// List operations.


template<typename T>
inline list<T> tolist(T is[], int length) {
	list<T> ls;
	for (int i=0; i < length; i++) {
		ls.push_back( is[i] );
	}
	return ls;
}

inline string print_markdown(bcont::map<int,string> aliases, int node_id) {
	bcont::map<int,string>::iterator it = aliases.find( node_id );
	if(it == aliases.end()) {
		return (format("Nd%s") % node_id).str();
	}
	return it->second;
}

#endif /* MSRE_MISC */
