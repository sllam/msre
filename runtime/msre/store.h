#ifndef MSRE_STORE_H
#define MSRE_STORE_H

#include <list>

#include <string>
#include <sstream>

#include <boost/container/map.hpp>
#include <boost/unordered_map.hpp>
#include <boost/functional/hash/hash.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/format.hpp>
#include <boost/uuid/uuid.hpp>            // uuid class
#include <boost/uuid/uuid_generators.hpp> // generators
#include <boost/uuid/uuid_io.hpp>         // streaming operators etc.

#include <boost/mpi.hpp>

#include "boost/tuple/tuple.hpp"

#include <boost/format.hpp>
#include "misc.h"
#include "logger.h"

using namespace std;
using namespace boost;
using namespace boost::tuples;

namespace bcont = boost::container;

// Abstract Classes

template<class E>
class StoreIter : public LoggerUser {
	virtual optional<E*> get_next() = 0;
};

// Comprehension Iterator

template<class E>
class CompreIter : public StoreIter<E> {

	list<E*>  accumulator;
	list<E*>* store;
	typename list<E*>::iterator start;
	typename list<E*>::iterator end;

	public: CompreIter() { }

	public: void add(E* e) {
		accumulator.push_front( e );
	}

	public: void init_iter() {
		store = &accumulator;
		start = accumulator.begin();
		end   = accumulator.end();
	}

	public: bool contains(E* e) {

		typename list<E*>::iterator local_start;
		typename list<E*>::iterator local_end;
		local_start = (*store).begin();
		local_end   = (*store).end();
		while(local_start != local_end) {
			E* temp = *local_start;
			if (temp->is_alive() && (e->identity() == temp->identity())) {
				return true;
			}
			local_start++;
		}
		return false;

	}

	public: optional<E*> get_next_alive() {
		if (start != end) {
			E* ptr = *start;
			// cout << "Entered ListIter Delink" << endl;
			while(not (ptr->alive)) {
				typename list<E*>::iterator temp = start;
				start++;
				LOG_STORE( record( (format("Delinking %s") % (**temp).pretty()).str() , THIS_SRC) );
				store->erase( temp );
				if(start == end) { return optional<E*>(); }
				ptr = *start;
			}
			// cout << "Exited ListIter Delink" << endl;
			start++;
			return optional<E*>( ptr );
		}
		return optional<E*>();
	}

	public: optional<E*> get_next() {
		if (start != end) {
			E* ptr = *start;
			start++;
			return optional<E*>( ptr );
		}
		return optional<E*>();
	}

};

// Store Iterator Implementations

template<class E>
class ListIter : public StoreIter<E> {

	list<E*>* store;
	typename list<E*>::iterator start;
	typename list<E*>::iterator end;

	public: ListIter(list<E*>& st) {
		store = &st;
		start = st.begin();
		end   = st.end();
	}

	public: void init_iter() {
		start = (*store).begin();
		end   = (*store).end();
	}

	public: bool contains(E* e) {

		typename list<E*>::iterator local_start;
		typename list<E*>::iterator local_end;
		local_start = (*store).begin();
		local_end   = (*store).end();
		while(local_start != local_end) {
			E* curr = *local_start;
			if (curr->is_alive() && (e->identity() == curr->identity())) {
				return true;
			}
			local_start++;
		}
		return false;

	}

	public: optional<E*> get_next_alive() {
		if (start != end) {
			E* ptr = *start;
			// cout << "Entered ListIter Delink" << endl;
			while(not (ptr->alive)) {
				typename list<E*>::iterator temp = start;
				start++;
				LOG_STORE( record( (format("Delinking %s") % (**temp).pretty()).str() , THIS_SRC) );
				store->erase( temp );
				if(start == end) { return optional<E*>(); }
				ptr = *start;
			}
			// cout << "Exited ListIter Delink" << endl;
			start++;
			return optional<E*>( ptr );
		}
		return optional<E*>();
	}

	public: optional<E*> get_next() {
		if (start != end) {
			E* ptr = *start;
			start++;
			return optional<E*>( ptr );
		}
		return optional<E*>();
	}

};


template<class E>
class MultimapIter : public StoreIter<E> {

	size_t kp;
	unordered_multimap<size_t,E*>* store;
	typename unordered_multimap<size_t,E*>::iterator start;
	typename unordered_multimap<size_t,E*>::iterator end;

	public: MultimapIter(unordered_multimap<size_t,E*>& st, size_t k) {
		store = &st;
		kp    = k;
		typename unordered_multimap<size_t,E*>::iterator fst;
		typename unordered_multimap<size_t,E*>::iterator snd;
		tie(fst,snd) = st.equal_range(k);
		start = fst;
		end   = snd;
	}

	public: void init_iter() {
		typename unordered_multimap<size_t,E*>::iterator fst;
		typename unordered_multimap<size_t,E*>::iterator snd;
		tie(fst,snd) = (*store).equal_range(kp);
		start = fst;
		end   = snd;
	}

	public: bool contains(E* e) {

		typename unordered_multimap<size_t,E*>::iterator local_start;
		typename unordered_multimap<size_t,E*>::iterator local_end;
		tie(local_start,local_end) = (*store).equal_range(kp);
		while(local_start != local_end) {
			E* curr = *local_start;
			if (curr->is_alive() && (e->identity() == curr->identity())) {
				return true;
			}
			local_start++;
		}
		return false;

	}

	public: optional<E*> get_next_alive() {
		if (start != end) {
			E* ptr = start->second;
			// cout << "Entered MultimapIter Delink" << endl;
			while(not (ptr->alive)) {
				// cout << ((*ptr)).pretty() << endl;
				typename unordered_multimap<size_t,E*>::iterator temp = start;
				start++;
				LOG_STORE( record( (format("Delinking %s") % (temp->second)->pretty()).str() , THIS_SRC) );
				store->erase( temp );
				if(start == end) { return optional<E*>(); }
				ptr = start->second;
			}
			// cout << "Exit MultimapIter Delink" << endl;
			start++;
			return optional<E*>( ptr );
		}
		return optional<E*>();
	}

	public: optional<E*> get_next() {
		if (start != end) {
			E* ptr = start->second;
			start++;
			return optional<E*>( ptr );
		}
		return optional<E*>();
	}

};

// Store class

class Store : public Pretty, public HTML {

	public: virtual void set_name(string n) = 0;
	public: virtual string get_name() = 0;
	public: virtual void purge() = 0;
	public: virtual int size()   = 0;
	public: virtual int actual_size() = 0;

	public: int sum_size() {
		mpi::communicator world;
		int my_size = size();
		if (world.rank() == 0) {
			int sum;
			mpi::reduce(world, my_size, sum, plus<int>(), 0);
			return sum;
		} else {
			reduce(world, my_size, plus<int>(), 0);
			return 0;
		}
	}

	public: string pretty_sum() {
		stringstream ss;
		ss << "Sum of all " << get_name() << " facts: " << sum_size() << endl;
		return ss.str();
	}

};


// Store Implementations

template<class E>
class ListStore: public Store, public LoggerUser {
	
	list<E*> store;
	string name;

	public: ListStore() { }

	public: void set_name(string n) { name = n; }

	public: string get_name() { return name; }

	public: void add(E* elem) {
		store.push_back( elem );
		LOG_STORE( record( (format("Stored new fact %s") % elem->pretty()).str(), THIS_SRC) );
	}

	public: void remove(E* elem) {
		// elem->alive = false;
		elem->set_dead();
		LOG_STORE( record( (format("Logically deleted %s") % elem->pretty()).str(), THIS_SRC) );
	}

	public: ListIter<E> lookup_candidates() {
		ListIter<E> it = ListIter<E>( store );
		LOG_STORE(
			it.set_logger(logger);
			stringstream ss;
			uuids::uuid uuid = uuids::random_generator()();
			ss << logging_context << "->Iter" << uuid ;
			it.set_logging_context(ss.str());
		);
		return it;
	}

	public: void purge() {
		typename list<E*>::iterator start = store.begin();
		LOG_STORE( 
			record( "Purging dead facts", THIS_SRC);
			int count = 0; 
		);
		while(start != store.end()) {
			if( not (**start).alive ) { 
				typename list<E*>::iterator temp = start;
				start++;
				store.erase( temp );
				LOG_STORE( count++; );
			} else {
				start++;
			}
		}
		LOG_STORE( record( (format("Delinked %s facts.") % count).str() , THIS_SRC) );
	}

	public: int actual_size() {
		return store.size();
	}

	public: int size() {
		typename list<E*>::iterator start = store.begin();
		int count = 0;
		while(start != store.end()) {
			if( (**start).alive ) { count++; }
			start++;
		}
		return count;
	}

	public: string pretty() {
		typename list<E*>::iterator start = store.begin();
		stringstream ss;
		ss << format("------------------- %s -------------------\n") % name ;
		while( start != store.end() ) {
			if ( (**start).alive ) {
				ss << (**start).pretty() << " ";
			} 
			start++;
		}
		ss << format("\n------ Logical size: %s, Actual size: %s ------\n") % size() % actual_size();
		ss << "--------------------------------------------------\n";
		return ss.str();
	}



	public: string markdown(bcont::map<int,string> aliases) {
		typename list<E*>::iterator start = store.begin();
		stringstream ss;
		ss << format("%s\n------------------------------------\n") % name ;
		while( start != store.end() ) {
			if ( (**start).alive ) {
				ss << (**start).markdown(aliases) << " ";
			} 
			start++;
		}
		ss << "\n";
		return ss.str();
	}

	public: string markdown() {
		bcont::map<int,string> aliases;
		return markdown(aliases);
	}

};


template<class E>
class MultimapStore : public Store, public LoggerUser {
	
	unordered_multimap<size_t,E*> store;
	string name;

	public: MultimapStore() { }

	public: void set_name(string n) { name = n; }

	public: string get_name() { return name; }

	public: void add(E* elem, size_t key) {
		store.insert( make_pair(key,elem) );
		LOG_STORE( record( (format("Stored new fact %s as key %s") % elem->pretty() % key).str(), THIS_SRC) );
	}

	public: void remove(E* elem) {
		// elem->alive = false;
		elem->set_dead();
		LOG_STORE( record( (format("Logically deleted %s") % elem->pretty()).str(), THIS_SRC) );
	}

	public: MultimapIter<E> lookup_candidates(size_t key) {
		MultimapIter<E> it = MultimapIter<E>(store, key);
		LOG_STORE(
			it.set_logger(logger);
			stringstream ss;
			uuids::uuid uuid = uuids::random_generator()();
			ss << logging_context << "->Iter" << uuid ;
			it.set_logging_context(ss.str());
		);
		return it;
	}

	public: void purge() {
		typename unordered_multimap<size_t,E*>::iterator start = store.begin();
		LOG_STORE( 
			record( "Purging dead facts", THIS_SRC);
			int count = 0; 
		);
		while(start != store.end()) {
			if (not (start->second)->alive) { 
				typename unordered_multimap<size_t,E*>::iterator temp = start;
				start++;
				store.erase( temp );
				LOG_STORE( count++; );
			} else {
				start++;
			}
		}
		LOG_STORE( record( (format("Delinked %s facts.") % count).str() , THIS_SRC) );
	}

	public: int actual_size() {
		return store.size();
	}

	public: int size() {
		typename unordered_multimap<size_t,E*>::iterator start = store.begin();
		int count = 0;
		while(start != store.end()) {
			if ((start->second)->alive) { count++; }
			start++;
		}
		return count;
	}

	public: string pretty() {
		typename unordered_multimap<size_t,E*>::iterator start = store.begin();
		stringstream ss;
		ss << format("------------------- %s -------------------\n") % name;
		while( start != store.end() ) {
			if ((start->second)->alive) {
				ss << (*(*start).second).pretty() << " ";
			} 
			start++;
		}
		ss << format("\n------ Logical size: %s, Actual size: %s ------\n") % size() % actual_size();
		ss << "----------------------------------------------------\n";
		return ss.str();
	}

	public: string markdown(bcont::map<int,string> aliases) {
		typename unordered_multimap<size_t,E*>::iterator start = store.begin();
		stringstream ss;
		ss << format("%s\n---------------------------------------\n") % name;
		while( start != store.end() ) {
			if ((start->second)->alive) {
				ss << (*(*start).second).markdown(aliases) << " ";
			} 
			start++;
		}
		ss << "\n";
		return ss.str();
	}

	public: string markdown() {
		bcont::map<int,string> aliases;
		return markdown(aliases);
	}

};

#endif /* MSRE_STORE_H */
