
#include <sys/resource.h>
#include <iostream>
#include <sstream>
#include <fstream>

#include <boost/mpi.hpp>
#include <boost/container/map.hpp>

#include "boost/date_time/posix_time/posix_time.hpp"

#include "logger.h"
#include "misc.h"
#include "store.h"
#include "fact.h"
#include "directory.h"


#define LOCAL_STEPS 5 
#define FACTOR_STEPS 2

using namespace boost;
using namespace boost::posix_time;
using namespace boost::gregorian;

namespace bcont = boost::container;

class Counter : public Pretty {

	protected: string name;
	protected: int* count;

	public: Counter(string n, int* c) {
		name = n; 
		count = c;
	}

	public: string pretty() {
		stringstream ss;
		ss << "Number of " << name << ": " << *count << endl;
		return ss.str();
	}

	public: string pretty_sum() {
		stringstream ss;
		ss << "Sum of all " << name << ": " << reduce_sum<int>(*count) << endl;
		return ss.str();
	}

	public: int max() {
		return reduce_max<int>(*count);
	}

};

class MSRENode : public LoggerUser, public Pretty, public HTML {

	protected: Directory* dir;

	protected: list<Store*> store_components;
	protected: list<Pretty*> pretty_components;
	protected: list<Counter*> counter_components;
	protected: list<Store*> repr_components;

	protected: bool ran;
	protected: ptime time_start, time_end;
	protected: ptime ad_start, ad_end;
	protected: time_duration active_duration;
	protected: int exist_counter;

	protected: bcont::map<int,string> node_aliases;

	protected: virtual bool rewrite() = 0;
	protected: virtual bool rewrite(int max_steps) = 0;
	protected: virtual void rewrite_loop() = 0;
	protected: virtual bool receive() = 0;
	protected: virtual bool globally_quiescence() = 0;

	public: string next_exist_id(int seed) {
		stringstream ss;
		ss << seed << "-" << exist_counter;
		exist_counter++;
		return ss.str();
	}

	public: string next_exist_id(string prefix, int seed) {
		stringstream ss;
		ss << prefix << "_" << seed << "-" << exist_counter;
		exist_counter++;
		return ss.str();
	}

	public: int reg_node_alias(int node_id, string alias) {
		node_aliases.insert( make_pair(node_id, alias) );
		return node_id;
	}

	public: void run() {
		time_start = ptime(microsec_clock::local_time());
		rewrite_loop();
		time_end = ptime(microsec_clock::local_time());
		ran = true;
	}

	public: string run_stat() {
		return run_stat("");
	}

	public: string run_stat(string selected_log_name) {
		mpi::communicator world;

		run();

		std::srand(std::time(0));
		string log_name = "";
		if (selected_log_name.length() > 0) {
			log_name = (format("%s") % selected_log_name).str();
		} else {
			log_name = "output";
		}

		Logger output_logger = Logger(log_name, log_name);
		string output = pretty_brief();
		LOG_VERBOSE_ONLY(output = pretty());
		output_logger.record_forced( output, (format("Rank %s") % world.rank()).str(), THIS_SRC );

		world.barrier();

		string sum_output = markdown();
		ptime global_time_end(microsec_clock::local_time());
		time_duration duration(global_time_end - time_start);	

		purge();

		string active_time_str = (format("Time taken by Rank %s (active): %s") % world.rank() % active_duration).str();
		output_logger.record_forced( active_time_str, (format("Rank %s") % world.rank()).str(), THIS_SRC );		
		cout << "Rank " << world.rank() << " Stat:" << endl << output << endl;

		world.barrier();

		struct rusage usage;
		getrusage(RUSAGE_SELF, &usage);
		long total_memory = reduce_sum<long>(usage.ru_maxrss);

		if (world.rank() == 0) {
			stringstream ss;
			ss << sum_output << "Time Taken (including sleep): " << duration << endl;

			ss << "Total Memory usage: " << (total_memory / 1000000.0) << "GB(s)" << endl;
			output_logger.record_forced( ss.str(), "Rank 0", THIS_SRC );
			cout << ss.str() ;
			// cout << log_name << endl;

			write_markdown_to_file(selected_log_name);

		}		
		output_logger.close();	
		
		return log_name;
	}

	public: void write_markdown_to_file(string selected_log_name) {
		const char* out_file_name = (selected_log_name + ".html").c_str();
		ofstream* out_file = new ofstream(out_file_name, std::ofstream::out | std::ofstream::app);
		(*out_file) << "Final State of the Ensemble:\n============================\n\n" << markdown() << endl;
		out_file->flush();
		out_file->close();
	}

	public: bool receive(int retries, int sleep_time, int factor) {
		int count = 0;
		while (count < retries) {
			if (receive()) {
				return true;
			} else {
				LOG_REWRITE_LOOP( record((format("Received nothing. Going to sleep for %ss") % sleep_time).str(), THIS_SRC) );
				sleep(sleep_time);
				sleep_time *= factor;
			}
			count++;
		}
		return false;
	}


	public: void set_dir(Directory* d) { dir = d; }

	public: void add_node(int id) { dir->add_node(id); }

	public: void init() { 
		dir->init(); 
		// exist_counter = 0;
	}
	
	protected: int lookup_dir(int node_id) { return dir->get_rank(node_id); }

	protected: void reset_active_duration() {
		ptime dummy_time = ptime(microsec_clock::local_time());
		active_duration = dummy_time - dummy_time;
	}

	protected: void start_active_duration() {
		ad_start = ptime(microsec_clock::local_time());
	}

	protected: void end_active_duration() {
		ad_end = ptime(microsec_clock::local_time());
		active_duration += ad_end - ad_start;
	}

	public: void set_store_component(Store* store) {
		store_components.push_back( store );
	}

	public: void set_repr_component(Store* store) {
		repr_components.push_back( store );
	}

	public: void set_pretty_component(Pretty* pretty) {
		pretty_components.push_back( pretty );
	}

	public: Counter* set_pretty_counter(string name, int* count) {
		Counter* counter = new Counter(name, count);
		// pretty_components.push_back( counter );
		counter_components.push_back( counter );
		return counter;
	}

	public: string markdown() {
		return markdown(node_aliases);
	}

	public: string markdown(bcont::map<int,string> aliases) {
		stringstream ss;
		ss << endl;
		for(list<Store*>::iterator it = repr_components.begin(); it != repr_components.end(); it++) {
			ss << (*it)->markdown(aliases);
		}
		if (ran) {
			time_duration duration(time_end - time_start);
			// ss << "\nProgram execution time (including sleep): " << duration << " (s)\n" << endl;
			ss << "\nProfiling summary:\n" << endl; 
			ss << "\nProgram execution time (native C++ runtime): " << active_duration.total_nanoseconds() / 1000000000.0 << " s" << endl;
		}
		return ss.str();
	}

	public: string pretty() {
		stringstream ss;
		ss << endl;
		for(list<Pretty*>::iterator it = pretty_components.begin(); it != pretty_components.end(); it++) {
			ss << (*it)->pretty();
		}
		for(list<Store*>::iterator it = store_components.begin(); it != store_components.end(); it++) {
			ss << (*it)->pretty();
		}
		for(list<Counter*>::iterator it = counter_components.begin(); it != counter_components.end(); it++) {
			ss << (*it)->pretty();
		}
		if (ran) {
			time_duration duration(time_end - time_start);
			ss << "Time Taken (including sleep): " << duration << endl;
			ss << "Time Taken (active): " << active_duration << endl;
		}
		return ss.str();
	}	

	public: string pretty_brief() {
		stringstream ss;
		ss << endl;
		for(list<Store*>::iterator it = store_components.begin(); it != store_components.end(); it++) {
			ss << "Size of " << (*it)->get_name() << ": " << (*it)->size() << endl;
		}
		for(list<Counter*>::iterator it = counter_components.begin(); it != counter_components.end(); it++) {
			ss << (*it)->pretty();
		}
		if (ran) {
			time_duration duration(time_end - time_start);
			ss << "Time Taken (including sleep): " << duration << endl;
			ss << "Time Taken (active): " << active_duration << endl;
		}
		return ss.str();
	}

	public: string pretty_sums() {
		stringstream ss;
		ss << endl;
		for(list<Store*>::iterator it = store_components.begin(); it != store_components.end(); it++) {
			ss << (*it)->pretty_sum();
		}
		for(list<Counter*>::iterator it = counter_components.begin(); it != counter_components.end(); it++) {
			ss << (*it)->pretty_sum();
		}
		return ss.str();
	}

	public: void purge() {
		for(list<Store*>::iterator it = store_components.begin(); it != store_components.end(); it++) {
			(*it)->purge();
		}
	}

};


class SoloMSRENode : public MSRENode {
	public: void rewrite_loop() { 
		LOG_REWRITE_LOOP( record( "Begin exhaustive rewrite", THIS_SRC) );
		start_active_duration();
		rewrite(); 
		end_active_duration();
		LOG_REWRITE_LOOP( record( "Quiescence reached", THIS_SRC) );
	}
};

template <int RETRIES=3, int SLEEP_TIME=1, int FACTOR=2>
class LocalQuiescenceMSRENode : public MSRENode {


	protected: MPICommAdmin admin_comm;

	int rewrite_restarts;

	public: void rewrite_loop() { 
		// rewrite_restarts = 0;
		// set_pretty_counter("Rewrite restarts", &rewrite_restarts);
		mpi::communicator world;
		while (true) {
			rewrite_restarts++;
			LOG_REWRITE_LOOP( record( "Begin exhaustive rewrite", THIS_SRC) );
			start_active_duration();
			rewrite();
			end_active_duration();
			LOG_REWRITE_LOOP( record( "Quiescence reached", THIS_SRC) );
			// if (not receive(RETRIES, SLEEP_TIME, FACTOR)) { break; }
			if (not receive()) { 
				purge();
				bool cont = admin_comm.standby(); 	
				if (not cont) {
					// cout << " Here " << endl; 
					
					if ( globally_quiescence() ) { 
						admin_comm.reset();
						break; 
					} 
					// break;
					// world.barrier();
					// cout << " Out " << endl; 
				}	
			}
		}
	}
};

template <int RETRIES=4, int SLEEP_TIME=1, int FACTOR=2>
class ExpoBackoffMSRENode : public MSRENode {

	int rewrite_restarts;

	public: void rewrite_loop() { 
		int curr_local_steps = LOCAL_STEPS;
		bool done_something = false;
		rewrite_restarts = 0;
		set_pretty_counter("Rewrite restarts", &rewrite_restarts);
		while (true) {
			LOG_REWRITE_LOOP( record( (format("Begin %s step rewrite") % curr_local_steps).str() , THIS_SRC) );
			start_active_duration();
			done_something = rewrite(curr_local_steps); 
			end_active_duration();
			rewrite_restarts++;
			LOG_REWRITE_LOOP( record( (format("%s steps completed") % curr_local_steps).str() , THIS_SRC) );

			if (not receive()) { 
				LOG_REWRITE_LOOP( record( "Received nothing" , THIS_SRC) );
				curr_local_steps *= FACTOR_STEPS;
			} else {
				purge();
				curr_local_steps = LOCAL_STEPS;
				done_something = true;
			}

			if (not done_something) {
				LOG_REWRITE_LOOP( record( "No activity, engaging sleep protocol" , THIS_SRC) );
				if (not receive(RETRIES, SLEEP_TIME, FACTOR)) { break; }
			}
		}
	}
};


class AdminExpoBackoffMSRENode : public MSRENode {

	protected: MPICommAdmin admin_comm;

	int rewrite_restarts;

	public: void rewrite_loop() { 
		int curr_local_steps = LOCAL_STEPS;
		rewrite_restarts = 0;
		set_pretty_counter("Rewrite restarts", &rewrite_restarts);
		while ( true ) {
			LOG_REWRITE_LOOP( record( (format("Begin %s step rewrite") % curr_local_steps).str() , THIS_SRC) );
			rewrite_restarts++;

			bool received_msgs = false;
			if (not receive()) { 
				LOG_REWRITE_LOOP( record( "Received nothing" , THIS_SRC) );
				curr_local_steps *= FACTOR_STEPS;
			} else {
				curr_local_steps = LOCAL_STEPS;
				received_msgs = true;
			}

			start_active_duration();
			bool rewritten = rewrite(curr_local_steps); 
			end_active_duration();
			LOG_REWRITE_LOOP( record( (format("%s steps completed") % curr_local_steps).str() , THIS_SRC) );

			if (not rewritten and not received_msgs) {
				purge();
				LOG_REWRITE_LOOP( record( "No activity, engaging sleep protocol" , THIS_SRC) );
				if ( globally_quiescence() ) { 
					// admin_comm.reset();
					break; 
				}
				/*
				bool cont = admin_comm.standby(); 	
				if (not cont) {
					if ( globally_quiescence() ) { 
						admin_comm.reset();
						break; 
					} 
				} */			
			}
		}
	}
};



