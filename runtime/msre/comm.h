
#include <list>

#include <boost/mpi.hpp>
#include <boost/mpi/status.hpp>
#include <boost/mpi/collectives.hpp>

#include "boost/tuple/tuple.hpp"

#include <sstream>
#include <boost/format.hpp>
#include "logger.h"

using namespace std;
using namespace boost;
using namespace boost::tuples;
// namespace mpi = boost::mpi;

#define PRIMARY_RANK 0
#define ADMIN_COMM_TAG 0 
#define KILL_SIGNAL -1
#define WAKE_SIGNAL -2
#define SLEEP_SIGNAL -3
#define TERMINAL_SIGNAL -4

class MPICommAdmin : public LoggerUser {

	protected: const mpi::communicator world;

	protected: int sleeper_count, rank;
	protected: bool* rank_activity;

	protected: bool has_recv;
	protected: int msg;
	protected: mpi::request reqs[2];
	protected: optional<std::pair<mpi::status,mpi::request*> > opt;

	public: MPICommAdmin() : sleeper_count(0), has_recv(false) { 
		rank = world.rank();
		if (rank == PRIMARY_RANK) {
			rank_activity = new bool[world.size()];
			for (int x=0; x < world.size() ; x++) {
				rank_activity[x] = true;
			}
		}
	}

	public: void send(int dest, int msg) {
		LOG_NETWORK( record( (format("Sending %s to rank %s") % msg % dest).str(), THIS_SRC) );
		reqs[0] = world.isend(dest, ADMIN_COMM_TAG, msg);
		mpi::wait_all(reqs, reqs + 1);
		// LOG_NETWORK( record( (format("Sent %s to rank %s") % msg % dest).str(), THIS_SRC) );
	}

	public: void wake(int target_rank) { 
		send(target_rank, target_rank);
		if (rank == PRIMARY_RANK) { 
			rank_activity[target_rank] = true;
		}
	}

	public: bool has_active() {
		if (rank == PRIMARY_RANK) {
			for (int x=0; x < world.size() ; x++) {
				if ((x != PRIMARY_RANK) && rank_activity[x]) { return true; }
			}
			return false;
		} else { return true; }
	}

	public: void init_receive() { 
		if ( not has_recv ) { 
			reqs[1] = world.irecv(mpi::any_source, ADMIN_COMM_TAG, msg);
			has_recv = true; 
		}
	}

	private: boost::optional<pair<int,int> > receive() {
		LOG_NETWORK( record( "Receiving...", THIS_SRC) );
		opt = mpi::test_any(reqs + 1, reqs + 2);
		int count = 0;
		if(opt) {
			int recv   = msg;
			int source = (opt->first).source();
			// reqs[1] = world.irecv(mpi::any_source, ADMIN_COMM_TAG, msg);
			// opt = mpi::test_any(reqs + 1, reqs + 2);
			LOG_NETWORK( record( (format("Received %s from rank %s") % recv % source).str(), THIS_SRC) );
			return boost::optional<pair<int,int> >( make_pair(source,recv) )  ;
		}
		LOG_NETWORK( record( "Received nothing", THIS_SRC) );
		return boost::optional<pair<int,int> >();
	}

	public: list<pair<int,int> > flush() {
		list<pair<int,int> > res;
		init_receive();
		boost::optional<pair<int,int> > recv = receive();
		while(recv) { 
			res.push_back( *recv );
			reqs[1] = world.irecv(mpi::any_source, ADMIN_COMM_TAG, msg);
			recv = receive(); 
			// cout << recv << endl;
			// sleep(1);
		}
		// cout << "out" << endl;
		// reqs[1].cancel();
		return res;
	}

	public: void kill() {
		send(PRIMARY_RANK, KILL_SIGNAL);
	}

	public: bool reset() {
		if (rank == PRIMARY_RANK) {
			for (int x=0; x < world.size() ; x++) {
				rank_activity[x] = true;
			}
			sleeper_count = 0;
		}
	}

	public: bool standby() {
		if (rank != PRIMARY_RANK) {
			int i;
			// sleep(1);
			LOG_NETWORK( record( (format("Rank %s going to sleep.") % rank ).str() , THIS_SRC ) );
			send(PRIMARY_RANK, SLEEP_SIGNAL);
			world.recv(mpi::any_source, ADMIN_COMM_TAG, i);
			send(PRIMARY_RANK, WAKE_SIGNAL);
			LOG_NETWORK( record( (format("Rank %s awoken.") % rank ).str() , THIS_SRC ) );

			list<pair<int,int> > other_msgs = flush();
			reqs[1].cancel();
			has_recv = false;
			for (list<pair<int,int> >::iterator it = other_msgs.begin(); it != other_msgs.end(); it++) {
				if ( it->second == TERMINAL_SIGNAL ) { return false; }
			}
			return (i != TERMINAL_SIGNAL);
		} else {
			// sleeper_count++;
			int size = world.size() - 1;
			LOG_NETWORK( record( (format("Primary sleeping, count: %s") % sleeper_count ).str() , THIS_SRC) );
			// if(sleeper_count == size ) { return false; }
			bool wake = false;
			int tries = 0;
			while( true ) {
				list<pair<int,int> > res = flush();
				for (list<pair<int,int> >::iterator it = res.begin(); it != res.end(); it++) {
					int source = it->first;
					// int m   = it->second;
					switch ( it->second ) {
						case KILL_SIGNAL:  { 
							sleeper_count++;
							rank_activity[source] = false;
							LOG_NETWORK( record( (format("Kill received from %s, count: %s") % source % sleeper_count ).str() 
                                                                   , THIS_SRC) ); 
							break; 
						};
						case SLEEP_SIGNAL:  { 
							sleeper_count++;
							rank_activity[source] = false;
							LOG_NETWORK( record( (format("Sleep received from %s, count: %s") % source % sleeper_count ).str() 
                                                                   , THIS_SRC) ); 
							break; 
						};
						case WAKE_SIGNAL:  { 
							sleeper_count--; 
							rank_activity[source] = true;
							LOG_NETWORK( record( (format("Wake received from %s, count: %s") % source % sleeper_count ).str() 
                                                                   , THIS_SRC) );
							break; 
						};
						case PRIMARY_RANK: { 			
							LOG_NETWORK( record( (format("Primary awoken at %s") % sleeper_count ).str() , THIS_SRC) );
							// if (not wake) { sleeper_count--; }
							wake = true; 
							break; 
						};
					}
				}
				if (wake) { break; }
				if (not has_active()) { // (sleeper_count == size) { 
					if ( tries >= 5 ) { break; }
					else { tries++; sleep(0.5); }
				} else { tries = 0; }
				// sleep(0.5);
			}
			// bool cont = wake or (sleeper_count < size);
			bool cont = wake or has_active();
			LOG_NETWORK( record( (format("Primary awoken, continue? %s") % cont ).str() , THIS_SRC) );
			if ( not cont ) {
				// mpi::broadcast<int>(world, TERMINAL_SIGNAL, PRIMARY_RANK);
				for (int target_rank=0; target_rank <= size; target_rank++) {
					if (target_rank != PRIMARY_RANK) { send(target_rank, TERMINAL_SIGNAL); }
				} 
			}
			return cont;
		}
	}

};


template<typename T>
class MPIComm : public LoggerUser {

	virtual void init_send() = 0;
	virtual void send(int dest, T msg) = 0;
	virtual void send(T msg) = 0;
	virtual void init_receive() = 0;
	virtual optional<list<T*> > receive() = 0;
	virtual int* get_send_counter() = 0;
	virtual int* get_recv_counter() = 0;

};

template<typename T>
class MPICommBasic : public LoggerUser { // : public MPIComm<T> {

	protected: mpi::communicator world;

	protected: T msg;
	protected: mpi::request reqs[2];
	protected: int fact_tag, max_size;
	protected: optional<std::pair<mpi::status,mpi::request*> > opt;

	protected: int send_counts, recv_counts;

	protected: bool has_admin;
	protected: MPICommAdmin* admin_comm;

	public: MPICommBasic() { }

	public: MPICommBasic(int c, int m=100000) 
                    : fact_tag(c), max_size(m), send_counts(0), recv_counts(0), has_admin(false) { }

	public: void set_admin_comm(MPICommAdmin* a_comm) {
		admin_comm = a_comm;
		has_admin = true;
	}

	public: void init_send() { }

	public: void send(int dest, T msg) {
		LOG_NETWORK( record( (format("Sending %s to rank %s") % msg.pretty() % dest).str(), THIS_SRC) );
		reqs[0] = world.isend(dest, fact_tag, msg);
		mpi::wait_all(reqs, reqs + 1);
		LOG_NETWORK( record( (format("Sent %s to rank %s") % msg.pretty() % dest).str(), THIS_SRC) );
		send_counts++;
		if( has_admin ) { admin_comm->wake(dest); }
	}

	public: void send(T msg) {
		LOG_NETWORK( record( (format("Sending %s to rank %s") % msg.pretty() % msg.node_id()).str(), THIS_SRC) );
		reqs[0] = world.isend(msg.node_id(), fact_tag, msg);
		mpi::wait_all(reqs, reqs + 1);
		LOG_NETWORK( record( (format("Sent %s to rank %s") % msg.pretty() % msg.node_id()).str(), THIS_SRC) );
		send_counts++;
		if( has_admin ) { admin_comm->wake( msg.node_id() ); }
	}

	public: void init_receive() {
		reqs[1] = world.irecv(mpi::any_source, fact_tag, msg);
	}

	public: optional<list<T*> > receive() {
		LOG_NETWORK( record( "Receiving...", THIS_SRC) );
		opt = mpi::test_any(reqs + 1, reqs + 2);
		int count = 0;
		if(opt) {
			list<T*> received;
			while(opt) {
				received.push_back(msg.clone());
				recv_counts++;
				reqs[1] = world.irecv(mpi::any_source, fact_tag, msg);
				if(count >= max_size - 1) { break; }
				opt = mpi::test_any(reqs + 1, reqs + 2);
				count++;
				LOG_NETWORK( record( (format("Received %s from rank %s") % msg.pretty() % msg.node_id()).str(), THIS_SRC) );
			}
			LOG_NETWORK( record( (format("Received %s facts") % count).str(), THIS_SRC) );
			return optional<list<T*> >( received )  ;
		}
		LOG_NETWORK( record( "Received nothing", THIS_SRC) );
		return optional<list<T*> >();
	}

	public: int* get_send_counter() { return &send_counts; }

	public: int* get_recv_counter() { return &recv_counts; }
	
};

