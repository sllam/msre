#ifndef MSRE_LOGGER_H
#define MSRE_LOGGER_H

#include <list>
#include <time.h>

#include <iostream>
#include <fstream>
#include <sstream>
#include <string>


using namespace std;
using namespace boost;

#ifdef MSRE_ENABLE_COUNTERS
	#define COUNTER( stmt ) stmt
#else
	#define COUNTER( stmt )
#endif

/* Enables the logging feature of the MSRE runtime */
#ifdef MSRE_ENABLE_LOG
	#define LOG( stmt ) stmt
	#ifdef MSRE_CONFIG_LOG 
		#ifdef MSRE_NETWORK_LOG
			#define LOG_NETWORK( stmt ) stmt
		#else
			#define LOG_NETWORK( stmt )
		#endif /* MSRE_NETWORK_LOG */
		#ifdef MSRE_RULE_APP_LOG
			#define LOG_RULE_APP( stmt ) stmt
		#else
			#define LOG_RULE_APP( stmt )
		#endif /* MSRE_RULE_APP_LOG */
		#ifdef MSRE_GOALS_LOG
			#define LOG_GOALS( stmt ) stmt
		#else
			#define LOG_GOALS( stmt )
		#endif /* MSRE_GOALS_LOG */
		#ifdef MSRE_STORE_LOG
			#define LOG_STORE( stmt ) stmt
		#else
			#define LOG_STORE( stmt )
		#endif /* MSRE_STORE_LOG */
		#ifdef MSRE_REWRITE_LOOP_LOG
			#define LOG_REWRITE_LOOP( stmt ) stmt
		#else
			#define LOG_REWRITE_LOOP( stmt )
		#endif /* MSRE_REWRITE_LOOP_LOG */
	#else
		/* The default logging directives */
		#define LOG_NETWORK( stmt ) stmt
		#define LOG_RULE_APP( stmt )
		#define LOG_GOALS( stmt )
		#define LOG_STORE( stmt )
		#define LOG_REWRITE_LOOP( stmt )
	#endif /* MSRE_CONFIG_LOG */

	#ifdef MSRE_NO_FILE
		#define FOUT( stmt )
	#else
		#define FOUT( stmt ) stmt
	#endif

	#ifdef MSRE_PTR_SCREEN
		#define SOUT( stmt ) stmt
	#else
		#define SOUT( stmt )
	#endif

	#ifdef MSRE_VERBOSE
		#define LOG_VERBOSE_ONLY( stmt ) stmt
	#else
		#define LOG_VERBOSE_ONLY( stmt )
	#endif

#else
	#define LOG( stmt ) 
	#define LOG_NETWORK( stmt )
	#define LOG_RULE_APP( stmt )
	#define LOG_GOALS( stmt )
	#define LOG_STORE( stmt )
	#define LOG_REWRITE_LOOP( stmt )
	#define LOG_VERBOSE_ONLY( stmt )
	#define FOUT( stmt )
	#define SOUT( stmt )
#endif /* MSRE_ENABLE_LOG */

#define THIS_SRC src(__FILE__,__LINE__)

void print_log_pref() {
	cout << "MSRE Logging Enabled: ";
	#ifdef MSRE_ENABLE_LOG
		cout << "Yes" << endl;

		cout << "Logging to STD Out: ";
		#ifdef MSRE_VERBOSE
			cout << "Yes" << endl;
		#else
			cout << "No" << endl;
		#endif /* MSRE_VERBOSE */
		cout << "Logging to File: ";
		#ifdef MSRE_NO_FILE
			cout << "No" << endl;
		#else
			cout << "Yes" << endl;
		#endif /* MSRE_NO_FILE */
	
		cout << "Logging Options:" << endl;
		#ifdef MSRE_NETWORK_LOG
			cout << " - Log networking activities." << endl;
		#endif /* MSRE_NETWORK_LOG */
		#ifdef MSRE_RULE_APP_LOG
			cout << " - Log rule instance applications." << endl;
		#endif /* MSRE_RULE_APP_LOG */
		#ifdef MSRE_GOALS_LOG
			cout << " - Log goal activities." << endl;
		#endif /* MSRE_GOALS_LOG */
		#ifdef MSRE_STORE_LOG
			cout << " - Log store activities." << endl;
		#endif /* MSRE_STORE_LOG */
		#ifdef MSRE_REWRITE_LOOP_LOG
			cout << " - Log rewrite loop activities." << endl;
		#endif /* MSRE_REWRITE_LOOP_LOG */

	#else
		cout << "No" << endl;
	#endif /* MSRE_ENABLE_LOG */
}

string get_time_str() {
	time_t rawtime;
	struct tm * timeinfo;
	char buffer [80];
	time(&rawtime);
	timeinfo = localtime(&rawtime);
	strftime (buffer,80,"%F %T",timeinfo);
	stringstream ss;
	ss << buffer;
	return ss.str();
}

struct SourceInfo {
	int line_no;
	string file_name;

	public: SourceInfo(string f, int l) : line_no(l), file_name(f) { }

	public: string to_string() {
		stringstream ss;
		ss << "[" << file_name << ":" << line_no << "]";
		return ss.str();
	}
};

SourceInfo src(string fname, int line_no) {
	return SourceInfo(fname, line_no);
}

class Logger {

	string logger_name;
	const char* out_file_name;
	ofstream* out_file;

	public: Logger(string lname, string fname) {
		logger_name   = lname;
		out_file_name = (fname + ".log").c_str();
		out_file = new ofstream(out_file_name, std::ofstream::out | std::ofstream::app);
	}

	public: string format_log_msg(string log_type, string msg, string context, optional<SourceInfo> srcinfo) {
		stringstream ms;
		ms << "[" << logger_name << ":" << log_type << "] [" << context << "] " ;
		if (srcinfo) {
			ms << srcinfo->to_string() << " ";
		}
		ms << "[" << get_time_str() << "] " << msg;
		return ms.str();
	}

	public: void record(string msg, string context, optional<SourceInfo> srcinfo ) {
		string log_entry = format_log_msg("info", msg, context, srcinfo);
		SOUT( cout << log_entry << endl );
		FOUT({ 
			(*out_file) << log_entry << endl;
			out_file->flush();
		});
	}

	public: void record(string msg) {
		record(msg, "",  optional<SourceInfo>());
	}

	public: void record(stringstream& ss, string context, optional<SourceInfo> srcinfo ) {
		record(ss.str(), context, srcinfo);
	}

	public: void record(stringstream& ss) {
		record(ss, "",  optional<SourceInfo>());
	}

	public: void record_forced(string msg, string context, optional<SourceInfo> srcinfo ) {
		string log_entry = format_log_msg("info", msg, context, srcinfo);
		// cout << log_entry << endl;
		(*out_file) << log_entry << endl;
		out_file->flush();
	}

	public: void close() {
		FOUT( out_file->close() );
	}

};

class LoggerUser {
	protected: Logger* logger;
	list<LoggerUser*> log_children;
	protected: string logging_context;

	public: void init_logger(string name, string file, string context) {
		logger = new Logger(name, file);
		logging_context = context;
		for(list<LoggerUser*>::iterator cs = log_children.begin(); cs != log_children.end() ; cs++) {
			(*cs)->set_logger( logger );
		}
	}
	public: void set_logger(Logger* lg) {
		logger = lg;
		for(list<LoggerUser*>::iterator cs = log_children.begin(); cs != log_children.end() ; cs++) {
			(*cs)->set_logger( logger );
		}
	}
	public: void set_logging_context(string context) {
		logging_context = context;
	}
	public: void set_logger_child(LoggerUser* lgu, string child_context) {
		lgu->set_logger(logger);
		stringstream ss;
		ss << logging_context << "->" << child_context;
		lgu->set_logging_context( ss.str() );
		log_children.push_front( lgu );
	}
	public: void record(string msg, optional<SourceInfo> srcinfo = optional<SourceInfo>() ) {
		logger->record(msg, logging_context, srcinfo);
	}
	public: void record(stringstream& ss, optional<SourceInfo> srcinfo = optional<SourceInfo>() ) {
		logger->record(ss.str(), logging_context, srcinfo);
	}

	public: void close() {
		LOG( logger->close() );
	}
};

#endif /* MSRE_LOGGER_H */
