#ifndef MSRE_GOALS_H
#define MSRE_GOALS_H

#include <list>

#include <string>
#include <sstream>
#include <queue>

#include <boost/format.hpp>
#include "boost/tuple/tuple.hpp"

#include "misc.h"
#include "logger.h"

using namespace std;
using namespace boost::tuples;

template<typename G>
class Goals : public LoggerUser, public Pretty {

	public: virtual bool has_goals()      = 0;
	public: virtual G* next()             = 0;
	public: virtual void add(G* g)        = 0;
	public: virtual void add(G* g, int p) = 0;

};

template<typename G>
class ListGoals : public Goals<G> {

	list<G*> goals;

	public: ListGoals() { }

	public: bool has_goals() { 
		return not goals.empty();
	}

	public: G* next() {
		G* g = goals.front();
		goals.pop_front();
		return g;
	}

	public: void add(G* g) {
		goals.push_front( g );
		LOG_GOALS( record((format("Added new goal: %s") % g->pretty()).str(), THIS_SRC) );
	}

	public: void add(G* g, int p) {
		add(g);
	}

	public: string pretty() {
		stringstream ss;
		ss << "----------------- Goals -----------------\n";
		typename list<G*>::iterator gs = goals.begin();
		while( gs != goals.end() ) {
			ss << (**gs).pretty() << " ";
			gs++;
		}
		ss << "\n-----------------------------------------\n";
		return ss.str();
	}


};

template<typename G>
class OrderedGoal {

	G* goal;
	int prior;

	public: OrderedGoal(G* g, int p) : goal(g), prior(p) { }

	public: G* item() { return goal; }

	public: int priority() { return prior; }

};

template<typename G>
class CompareGoal {

	public: bool operator()(OrderedGoal<G>& g1, OrderedGoal<G>& g2) {
		return g1.priority() < g2.priority();
	}

};

template<typename G>
class OrderedGoals : public Goals<G> {

	public: priority_queue<OrderedGoal<G>, vector<OrderedGoal<G> >, CompareGoal<G> > goals;

	public: OrderedGoals() { }

	public: bool has_goals() { 
		return not goals.empty();
	}

	public: G* next() {
		OrderedGoal<G> g = goals.top();
		goals.pop();
		return g.item();
	}

	public: void add(G* g, int p) {
		OrderedGoal<G> og = OrderedGoal<G>(g, p);
		goals.push( og );
		LOG_GOALS( record((format("Added new goal: %s") % g->pretty()).str(), THIS_SRC) );
	}

	public: void add(G* g) {
		add(g, g->priority());
	}

	public: tuple<G*,int> next__() {
		OrderedGoal<G> g = goals.top();
		goals.pop();
		return make_tuple(g.item(),g.priority());
	}


	public: string pretty() {
		priority_queue<OrderedGoal<G>, vector<OrderedGoal<G> >, CompareGoal<G> > temp_goals;
		stringstream ss;
		ss << "----------------- Goals -----------------\n";
		while( has_goals() ) {
			G* g; int p;
			tie(g,p) = next__();
			ss << g->pretty() << " ";
			temp_goals.push( OrderedGoal<G>(g, p) );
		}
		ss << "\n-----------------------------------------\n";
		goals = temp_goals;
		return ss.str(); 
	}


};

#endif /* MSRE_GOALS_H */
