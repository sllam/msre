#ifndef MSRE_DIRECTORY_H
#define MSRE_DIRECTORY_H

#include <sstream>
#include <queue>

#include <boost/mpi.hpp>
#include <boost/mpi/status.hpp>
#include <boost/container/map.hpp>
#include <boost/container/set.hpp>

#include "misc.h"

using namespace std;
using namespace boost;
namespace bcont = boost::container;

class Directory : public Pretty {

	protected: mpi::communicator world;
	protected: int next_node_id;

	public: virtual void add_node(int node_id) = 0;
	public: virtual void add_edge(int src_id, int dest_id) = 0;
	public: virtual void init() = 0;
	public: virtual int get_rank(int node_id) = 0;
	public: virtual int new_node() = 0;

	public: void reg_node(int node_id) {
		while(next_node_id <= node_id) {
			next_node_id += world.size();
		}
	}

	public: int new_node_id() {
		int new_id = next_node_id;
		next_node_id += world.size();
		return new_id;
	}

};

// Maps MSRE nodes directly to MPI ranks
class IdentDirectory: public Directory {

	public: IdentDirectory(int s) {
		next_node_id = world.rank();
	}

	public: void add_node(int node_id) { reg_node( node_id ); }
	public: void add_edge(int src_id, int dest_id) {}
	public: void init() {}
	public: int get_rank(int node_id) { return node_id; }
	public: int new_node() { return new_node_id(); }
	public: string pretty() {
		stringstream ss;
		ss << "----------------- Directory ---------------------" << endl;
		ss << "x --> x" << endl;
		ss << "-------------------------------------------------" << endl;
		return ss.str();
	}

};

// Maps all MSRE nodes to a single MPI rank, default rank 0
class UniDirectory: public Directory {

	int rank;

	public: UniDirectory(int s, int r=0) : rank(r) { 
		next_node_id = world.rank();
	}

	public: void add_node(int node_id) { reg_node( node_id ); }
	public: void add_edge(int src_id, int dest_id) {}
	public: void init() {}
	public: int get_rank(int node_id) { return rank; }
	public: int new_node() { return new_node_id(); }
	public: string pretty() {
		stringstream ss;
		ss << "----------------- Directory ---------------------" << endl;
		ss << "x --> " << rank << endl;
		ss << "-------------------------------------------------" << endl;
		return ss.str();
	}
};

/*
class RankNodeCount {

	int rank;
	int inv_count;

	public: RankNodeCount(int r) : rank(r), inv_count(0) {}

	public: int get_rank() { return rank; }

	public: int get_count() { return -inv_count; }

	public: void incr_count() { inv_count--; }

};

class CompareCount {

	public: bool operator()(RankNodeCount& c1, RankNodeCount& c2) {
		return c1.get_count() < c2.get_count();
	}

};
*/

// Maps MSRE nodes to ranks by 'modulo rank distribution'. Hence, this
// ignores any static topology infered from the initial program. 
class ModuloDistDirectory: public Directory {

	// bcont::map<int,int> node_ids;
	int rank_size;

	public: ModuloDistDirectory(int s) : rank_size(s) {
		next_node_id = world.rank();
	}

	public: void add_node(int node_id) {
		// int rank = node_id % rank_size;
		// pair<bcont::map<int,int>::iterator,bool> res = node_ids.insert( make_pair(node_id,rank) );
		reg_node( node_id );
	}
	public: void add_edge(int src_id, int dest_id) {}
	public: void init() {}
	public: int get_rank(int node_id) {
		// bcont::map<int,int>::iterator it = node_ids.find( node_id );
		// return it->second;
		return node_id % rank_size;
	}
	public: int new_node() {
		// int new_id = new_node_id();
		// node_ids.insert( make_pair(new_id,new_id % rank_size) );
		// return new_id;
		return new_node_id();
	}
	public: string pretty() {
		stringstream ss;
		ss << "----------------- Directory ---------------------" << endl;
		/*
		for(bcont::map<int,int>::iterator start = node_ids.begin(); start != node_ids.end(); start++) {
			ss << start->first << " --> " << start->second << endl;
		} */
		ss << "x --> x `mod` " << rank_size << endl;
		ss << "-------------------------------------------------" << endl;
		return ss.str();
	}

};

// Maps MSRE nodes to ranks by 'node value proximity', i.e try to keep nodes of the same value
// in the same rank. Like Modulo distribution this ignores any static topology infered from the 
// initial program. 
class NodeProxyDirectory: public Directory {

	bcont::set<int> temp;
	bcont::map<int,int> node_ids;
	int rank_size;

	public: NodeProxyDirectory(int s) : rank_size(s) {
		next_node_id = world.rank();
	}

	public: void add_node(int node_id) {
		pair<bcont::set<int>::iterator,bool> res = temp.insert( node_id );
		reg_node( node_id );
	}
	public: void add_edge(int src_id, int dest_id) {}
	public: void init() {
		int node_size = temp.size();
		int group_size = node_size / rank_size;
		int rank = 0;
		int node_id = 0;
		while(rank < rank_size) {
			int count = 0;
			while(count < group_size) {
				node_ids.insert( make_pair(node_id,rank) );
				node_id++;
				count++;
			}
			rank++;
		}
		rank--;
		while(node_id < node_size) {
			node_ids.insert( make_pair(node_id,rank) );
			node_id++;	
		}
	}
	public: int get_rank(int node_id) {
		bcont::map<int,int>::iterator it = node_ids.find( node_id );
		if(it == node_ids.end()) {
			int node_rank = node_id % rank_size;
			node_ids.insert( make_pair(node_id,node_rank) );
			return node_rank;
		}
		return it->second;
	}
	public: int new_node() {
		int new_id = new_node_id();
		node_ids.insert( make_pair(new_id,new_id % rank_size) );
		return new_id;
	}
	public: string pretty() {
		stringstream ss;
		ss << "----------------- Directory ---------------------" << endl;
		for(bcont::map<int,int>::iterator start = node_ids.begin(); start != node_ids.end(); start++) {
			ss << start->first << " --> " << start->second << endl;
		}
		ss << "-------------------------------------------------" << endl;
		return ss.str();
	}

};

#endif /* MSRE_DIRECTORY_H */
