'''
This file is part of MSR Ensemble (MSRE-X).

MSRE-X is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

MSRE-X is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with MSRE-X. If not, see <http://www.gnu.org/licenses/>.

MSR Ensemble (MSRE-X) Version 0.5, Prototype Alpha

Authors:
Edmund S. L. Lam      sllam@qatar.cmu.edu
Iliano Cervesato      iliano@cmu.edu

* This implementation was made possible by an NPRP grant (NPRP 09-667-1-100, Effective Programming 
for Large Distributed Ensembles) from the Qatar National Research Fund (a member of the Qatar 
Foundation). The statements made herein are solely the responsibility of the authors.
'''


import sys
import time

from uuid import uuid4

from array import array
from mpi4py import MPI
from json import dumps, loads

from multiprocessing import Process, Queue

# from msr_ensemble.misc.debug import debug
from msre.misc.msr_logging import init_logger, get_logger, log_debug, log_info, log_warn, log_error, log_critical

# This module implements Python multiprocessing within MPI nodes.
# Each MPI node consist of a master process and several worker processes.
# Master process deals with MPI communication between worker processes,
# which can be within the MPI node (between 2 workers of the same node)
# or external to the MPI node (between 2 workers of different MPI nodes)



# MPI Asynchronous send and receive
# 
# WARNING: These operations are meant only to be used by master process,
# they are not thread safe! Only one process should ever be access them.

FACT_TAG    = 10
#BUFFER_SIZE = '\0'*128
BUFFER_SIZE = '\0'*512

comm = MPI.COMM_WORLD

def send_facts(facts):
	for fact in facts:
		send_fact(fact)

def send_fact(fact):
	req = comm.Isend([dumps(fact),MPI.CHAR], dest=fact['rank'], tag=FACT_TAG)
	req.wait()

def receive_fact_future_mpi():
	buf = array('c',BUFFER_SIZE)
	req = comm.Irecv([buf,MPI.CHAR], source=MPI.ANY_SOURCE, tag=FACT_TAG)
	status = MPI.Status()
	def future():
		(received,_) = req.test(status)
		if received:
			n = status.Get_count(MPI.CHAR)
			return loads(buf[:n].tostring())
		else:
			return None
	return future

# Auxiliary Functions

CREATE_WORKER = 0
DELIVER_MSG   = 1
KILL_SELF     = 2

# Generate a unique process id
def gen_proc_id():
	return str(uuid4())

# Master Process
# The class that represents a master process. A Master process has the following responsibilities:
#       - Creating new worker processes
#       - Receiving external MPI messages and forwarding to the addressed worker
#       - Receiving internal worker messages and forwarding to either the addressed co-worker,
#         or to the addressed worker from another MPI node
# Each worker has a work queue, in which messages are passed to it by the master process. The master
# process on the other hand, has a dedicated queue where workers pass requests to the master process.
# Requests can be either:
#       - Deliver message request
#	- Create new worker request
# Workers are addressed by unique id, that is either:
#       - A uuid (RFC 4122) 
#       - Rank of the MPI node (For the first worker of each MPI node)
# Note that in either case, rank of the MPI node is required for addressing.
class MasterProcess:

	# Initialize the master process. Arguments as follows:
	#   - rank: Rank of the MPI node
	#   - sleep_length: Base length of each sleep cycle
        #   - sleep_factor: Base multiplier of each sleep cycle
        #   - sleep_limit: Number of consecutive sleeps before sleep length saturates 
	def initialize(self, rank, sleep_length=0.1, sleep_factor=2, sleep_limit=4, init_workers=1, file_logging=False):
		
		self.rank = rank
		self.master_channel  = Queue()
		self.worker_procs    = {}
		self.worker_channels = {}

		self.sleep_length    = sleep_length
		self.sleep_factor    = sleep_factor
		self.sleep_limit     = sleep_limit

		self.curr_sleep_length = sleep_length
		self.curr_sleep_limit  = sleep_limit

		self.init_workers = init_workers
		self.file_logging = file_logging

		if file_logging:
			master_log_file = "master_%s.log" % rank
		else:
			master_log_file = None
		self.logger = init_logger("master_%s" % rank, log_file=master_log_file)

	# Returns true iff:
	#   - All worker processes are not alive
	#   - Sleep limit has been reached
	def is_alive(self):
		'''
		procs = self.worker_procs
		for proc_id in procs:
			proc = procs[proc_id]
			if proc.is_alive():
				return True
		'''
		if len(self.worker_procs) > 0:
			return True

		# debug("Master %s finds all workers Dead!" % self.rank)
		log_info(self.logger,"All workers Dead!")

		if self.curr_sleep_limit > 0:
			return True
		else:
			return False

	# Sleep for specified amount of time. Increments next sleep cycle
	def sleep(self):
		log_info(self.logger, "Sleeping: %s" % self.curr_sleep_limit )
		time.sleep(self.curr_sleep_length)
		if self.curr_sleep_limit > 0:
			self.curr_sleep_length *= self.sleep_factor
			self.curr_sleep_limit -= 1

	# Reset sleep cycle to original base values
	def reset_sleep(self):
		self.curr_sleep_length = self.sleep_length
		self.curr_sleep_limit  = self.sleep_limit

	# Add to master's own work queue, an order to create a new worker 
	def create_new_worker(self, proc_id=None):
		if proc_id == None:
			proc_id = gen_proc_id()
		self.master_channel.put({ 'task':CREATE_WORKER, 'proc_id':proc_id })
		return proc_id

	# Main master process loop. First initializes a number of worker processes (as indicated by init_workers) and
	# begins to run a loop that manages communications between workers and MPI nodes. In each cycle, it does the following:
	#    - Does an asynchronous read from MPI interface for any message and forwards it to the addressed worker
	#    - Reads from request queue (master_channel) and process either a message delivery request, or worker creation
	#      request.
	# Loop continues, until liveness condition is no more (see is_alive method for details)
	def start(self):
		log_info(self.logger, "Started")
		master_channel  = self.master_channel
		worker_channels = self.worker_channels

		self.create_new_worker(str(self.rank))
		for _ in range(0,self.init_workers-1):
			self.create_new_worker()

		done_something = False
		recv_future = receive_fact_future_mpi()
		while self.is_alive():

			if not master_channel.empty():
				int_msg = master_channel.get()
				task_type = int_msg['task']
				if task_type == DELIVER_MSG:
					msgs = int_msg['msgs']
					log_info(self.logger, "Delivering messages %s" % msgs)
					for data in msgs:
						if data['rank'] == self.rank:
							log_info(self.logger, "Internal message, sending to worker %s" % data['proc_id'])
							worker_channels[data['proc_id']].put( data )
						else:
							log_info(self.logger, "External message, sending to MPI rank %s" % data['rank'])
							send_fact( data )
				elif task_type == CREATE_WORKER:
					proc_id = int_msg['proc_id']
					log_info(self.logger, "Creating worker %s" % proc_id)
					worker_channel = Queue()
					worker_channels[proc_id] = worker_channel
					p = self.new_worker(self.rank, proc_id, worker_channel, master_channel)
					p.start()
					self.worker_procs[proc_id] = p
				elif task_type == KILL_SELF:
					proc_id = int_msg['proc_id']
					log_info(self.logger, "Killing worker %s" % proc_id)
					# self.worker_procs[proc_id].terminate()
					del self.worker_channels[proc_id]
					del self.worker_procs[proc_id]
				done_something = True
	
			mpi_msg = recv_future()
			
			if mpi_msg != None:
				worker_channels[mpi_msg['proc_id']].put( mpi_msg )
				done_something = True
				recv_future = receive_fact_future_mpi()

			if done_something:
				done_something = False
				self.reset_sleep()
			else:
				self.sleep()
		log_info(self.logger,"Shutting Down")

	# Returns a new worker process. This method is to be overwritten 
	def new_worker(self, rank, proc_id, worker_channel, master_channel):
		return WorkerProcess(rank, proc_id, worker_channel, master_channel, file_logging=self.file_logging)

# Worker Process
# The class that represents the worker process. Workers are meant only to be created by
# the master process class. A class that inherits this worker class should be instantiated
# in the 'new_worker' method of the Master process class. 
class WorkerProcess:

	def initialize(self, rank, proc_id, worker_channel, master_channel, file_logging=False):
		self.rank    = rank
		self.proc_id = proc_id
		self.worker_channel = worker_channel
		self.master_channel = master_channel
		self.proc = None

		if file_logging:
			worker_log_file = "worker_%s_%s.log" % (rank,proc_id)
		else:
			worker_log_file = None
		self.logger = init_logger("worker_%s_%s" % (rank,proc_id), log_file=worker_log_file)

	# Start the worker process. This method creates a process (from multiprocessing module)
	# and runs the method 'routine' of this class.
	def start(self):
		self.proc = Process(target=run_worker_routine, args=(self,) )
		self.proc.start()		

	# Returns true iff process running the worker routine is alive.
	def is_alive(self):
		log_info(self.logger,"Testing liveness: %s" % (self.proc_id,self.proc.is_alive()))
		return self.proc.is_alive()

	def terminate(self):
		if self.proc.is_alive():
			self.proc.terminate()

	# Returns true iff the worker message channel is empty
	def has_no_msgs(self):
		return self.worker_channel.empty()

	# Returns a message from the worker message channel, None otherwise.
	def get_msg(self):
		if not self.has_no_msgs():
			return self.worker_channel.get()
		else:
			return None

	# Send a message 'data'. 
	def send_msg(self, data):
		self.master_channel.put({ 'task':DELIVER_MSG, 'msgs':[data] })

	def send_msgs(self, ds):
		self.master_channel.put({ 'task':DELIVER_MSG, 'msgs':ds })

	# Send a request to create a new worker, and return this worker's process id.
	def create_new_worker(self, proc_id=None):
		if proc_id == None:
			proc_id = gen_proc_id()
		self.master_channel.put({ 'task':CREATE_WORKER, 'proc_id':proc_id })
		return proc_id

	def kill(self):
		self.master_channel.put({ 'task':KILL_SELF, 'proc_id':self.proc_id })

	# Main worker routine. This method is to be overwritten
	def routine(self):
		pass

def run_worker_routine(work_proc):
	work_proc.routine()
	work_proc.worker_channel.close()
	work_proc.kill()

