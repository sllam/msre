#ifndef MSRE_NODE_H
#define MSRE_NODE_H

#include <sstream>

#include "misc.h"

using namespace std;

class Node : public Pretty {

	int rank;
	int id;

	public: Node(int n) : id(n) {}

	public: void set_rank(int r) { rank = r; }

	public: int get_node() { return id; }
	public: int get_rank() { return rank; }

	public: bool operator==(Node& other) {
		return id == other.get_node();
	}

	public: string pretty() {
		stringstream ss;
		ss << id;
		return ss.str();
	}

	friend class boost::serialization::access;
	
	template<class Archive>
	void serialize(Archive & ar, const unsigned int version) {
		ar & rank;
		ar & id;
	}

};

#endif /* MSRE_NODE_H */

