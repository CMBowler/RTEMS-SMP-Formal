/* SPDX-License-Identifier: BSD-2-Clause */

/*
 * task-mgr-model.pml
 *
 * Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/*
 * We need to output annotations for any #define we use.
 * It is simplest to keep them all together,
 * and use an inline to output them.
 */

#include "../common/rtems.pml"

/*
 * We need to output annotations for any #define we use.
 * It is simplest to keep them all together,
 * and use an inline to output them.
 */

// Event Sets - we only support 4 events, rather than 32
#define NO_OF_EVENTS 4
#define EVTS_NONE 0
#define EVTS_PENDING 0
#define EVT_0 1
#define EVT_1 2
#define EVT_2 4
#define EVT_3 8
#define EVTS_ALL 15
#define NO_TIMEOUT 0

#define MAX_PRIO 255
#define BAD_PRIO MAX_PRIO
#define DEFUALT_PRIO 5

// We use two semaphores to synchronise the tasks
#define SEMA_MAX 3

#define SEMA_TASKCONTROL 	(0)
#define SEMA_TASK_START_0 	(1)
#define SEMA_CREATEDELETE 	(2)

// System
#define TIMOUT_VAL 100

/* The following inlines are not given here as atomic,
 * but are intended to be used in an atomic context.
*/

inline nl() { printf("\n") } // Useful shorthand


/*
 * Running Orders (maintained by simple global sync counter):
 *   Receive;;Send  =  Receive;Release(1) || Obtain(1);Send
 * Here ;; is "sequential" composition of *different* threads
 */
bool semaphore[SEMA_MAX]; // Semaphore

/*
 * Synchronisation Mechanisms
 *  Obtain(sem_id)   - call that waits to obtain semaphore `sem_id`
 *  Release(sem_id)  - call that releases semaphore `sem_id`
 *  Released(sem_id) - simulates ecosystem behaviour releases `sem_id`
 *
 * Binary semaphores:  True means available, False means in use.
 */
inline Obtain(sem_id){
  atomic{
    printf("@@@ %d WAIT %d\n",_pid,sem_id);
    semaphore[sem_id] ;        // wait until available
    semaphore[sem_id] = false; // set as in use
    printf("@@@ %d LOG WAIT %d Over\n",_pid,sem_id);
  }
}

inline Release(sem_id){
  atomic{
    printf("@@@ %d SIGNAL %d\n",_pid,sem_id);
    semaphore[sem_id] = true ; // release
  }
}

inline Released(sem_id)
{
  semaphore[sem_id] = true ;
}

// We envisage two RTEMS tasks involved, at most.
#define TASK_MAX 5 // These are the "RTEMS" tasks only, numbered 1 & 2
                   // We reserve 0 to model NULL pointers


#define CLEAR_TASKS 255
byte task_control = CLEAR_TASKS;

// A task may exist in one of the following five states:

  //  executing - Currently scheduled to the CPU

  //  ready - May be scheduled to the CPU

  //  blocked - Unable to be scheduled to the CPU

  //  dormant - Created task that is not started

  //  non-existent - Uncreated or deleted task

mtype = {
  executing, ready, blocked, dormant, non
};

inline outputDefines () {
	printf("@@@ %d DEF NO_OF_EVENTS %d\n",_pid,NO_OF_EVENTS);
	printf("@@@ %d DEF EVTS_NONE %d\n",_pid,EVTS_NONE);
	printf("@@@ %d DEF EVTS_PENDING %d\n",_pid,EVTS_PENDING);

	printf("@@@ %d DEF EVT_0 %d\n",_pid,EVT_0);
	printf("@@@ %d DEF EVT_1 %d\n",_pid,EVT_1);
	printf("@@@ %d DEF EVT_2 %d\n",_pid,EVT_2);
	printf("@@@ %d DEF EVT_3 %d\n",_pid,EVT_3);
	printf("@@@ %d DEF EVTS_ALL %d\n",_pid,EVTS_ALL);
	printf("@@@ %d DEF NO_TIMEOUT %d\n",_pid,NO_TIMEOUT);

	printf("@@@ %d DEF TASK_MAX %d\n",_pid,TASK_MAX);
	printf("@@@ %d DEF BAD_ID %d\n",_pid,BAD_ID);
	printf("@@@ %d DEF SEMA_MAX %d\n",_pid,SEMA_MAX);
	
	printf("@@@ %d DEF RC_OK RTEMS_SUCCESSFUL\n",_pid);
	printf("@@@ %d DEF RC_InvId RTEMS_INVALID_ID\n",_pid);
	printf("@@@ %d DEF RC_InvAddr RTEMS_INVALID_ADDRESS\n",_pid);
	printf("@@@ %d DEF RC_Unsat RTEMS_UNSATISFIED\n",_pid);
	printf("@@@ %d DEF RC_Timeout RTEMS_TIMEOUT\n",_pid);
}

typedef Mode {
    bool preempt;
    bool timeslice;
    bool ASR;
    int isr_lvl;
}
// Tasks
typedef Task {
  int start;    // Starting address
  byte nodeid;  // So we can spot remote calls
  byte pmlid;   // Promela process id
  mtype state = non ; // {Ready,EventWait,TickWait,OtherWait}
  Mode mode;    // Contains information about the task mode.
  byte prio ;   // lower number is higher priority
  int ticks;    //
  bool tout;    // true if woken by a timeout
  bool isr;     // If task is woken from Interrupt context
};

Task tasks[TASK_MAX]; // tasks[0] models a NULL dereference

byte sendrc;            // Sender global variable
byte recrc;             // Receiver global variable
byte recout[TASK_MAX] ; // models receive 'out' location.

byte createRC;
byte startRC;
byte deleteRC;

byte task_id[TASK_MAX] ;

inline outputDeclarations () {
  printf("@@@ %d DECL byte createRC 0\n",_pid);
  printf("@@@ %d DECL byte startRC 0\n",_pid);
  printf("@@@ %d DECL byte deleteRC 0\n",_pid);
  // Rather than refine an entire Task array, we refine array 'slices'
  //printf("@@@ %d DCLARRAY EvtSet pending TASK_MAX\n",_pid);
  //printf("@@@ %d DCLARRAY byte recout TASK_MAX\n",_pid);
  printf("@@@ %d DCLARRAY byte taskID TASK_MAX\n", _pid);
  printf("@@@ %d DCLARRAY Task tasks TASK_MAX\n",_pid);
  printf("@@@ %d DCLARRAY Semaphore semaphore SEMA_MAX\n",_pid);
}


inline isNameValid(name, rc) {
    if
    ::  name == 0 ->
            rc = false;
    ::  else -> 
            rc = true;
    fi
}

inline setTask(tid, rc) {
    byte raw_tid;
    Obtain(SEMA_TASKCONTROL);
    raw_tid = task_control & (~task_control + 1);
    task_control = task_control - raw_tid;
    Release(SEMA_TASKCONTROL);
    rc = true;
    if
    ::  raw_tid == 2 ->
            tid = 1;
    ::  raw_tid == 4 ->
            tid = 2;
    ::  raw_tid == 8 ->
            tid = 3;
    ::  raw_tid == 16 ->
            tid = 4;
/*    
	::  raw_tid == 32 ->
            tid = 5;
    ::  raw_tid == 64 ->
            tid = 6;
    ::  raw_tid == 128 ->
            tid = 7;
*/
    ::  else ->
            tid = 1;
            rc = false;
    fi
}
///*
inline task_create(nid, name, prio, preempt, tid, tidRC, rc) {
    atomic {
        if
		::	name == 0 ->
				rc = RC_InvName;
        ::  prio == 0 ->
                rc = RC_InvPrio
        ::  prio >= BAD_PRIO ->
                rc = RC_InvPrio
		::  tidRC == false ->
                rc = RC_TooMany;
		::	tid == 0 ->
				rc = RC_InvAddr;
        ::  else ->
				tasks[tid].nodeid = nid;
				tasks[tid].pmlid = _pid;
				tasks[tid].prio = prio;
				tasks[tid].mode.preempt = preempt;
				tasks[tid].state = dormant;
        fi
    }
}
//*/

///*
inline task_start(tid, entry, rc) {
    atomic {
        if
        ::  tasks[tid].state == non ->
                printf("@@@ %d LOG Start NULL out.\n",_pid);
                rc = RC_InvId;
		:: 	else ->
				if
				::  tasks[tid].state != dormant ->
						rc = RC_IncState;
				:: 	else ->
						if 
						::  entry == 0 -> rc = RC_InvId;
						::  else ->
							tasks[tid].state = ready;
							tasks[tid].start = entry;
							// Start Task Model
							Release(entry);
							rc = RC_OK;
						fi
				fi
        fi
    }
}
//*/

/*
inline task_suspend(self, tid, rc) {
    atomic {
        if
        ::  tasks[tid].state == non ->
                printf("@@@ %d LOG Suspend NULL out.\n",_pid);
                rc = RC_InvId;
        ::  tasks[tid].state == dormant ->
                rc = RC_AlrSuspd;
        ::  else ->
                task[tid].state = dormant; ->
                rc = RC_OK;
        fi
    }
}
//*/

/*
inline task_resume(self, tid, rc) {
    atomic {
        if
        ::  tasks[tid].state == non ->
            printf("@@@ %d LOG Resume NULL out.\n",_pid);
            rc = RC_InvId;
        :: tasks[tid].state != suspended ->
            rc = RC_IncState;
        :: else ->
            tasks[tid].state = suspended ->
            rc = RC_OK;
        fi
    }
}
//*/

inline removeTask(tid, rc) {
    byte raw_tid = 1 << tid;
    Obtain(SEMA_TASKCONTROL);
    if
    ::  (task_control & raw_tid) != raw_tid ->
            task_control = task_control + raw_tid;
            rc = true;
    ::  (task_control & raw_tid) == raw_tid ->
            rc = false;
    fi
    Release(SEMA_TASKCONTROL);
}

///*
inline task_delete(tid, rc) {
    assert(tid < TASK_MAX);
    atomic {
        if
        ::  tasks[tid].state == non ->
                rc = RC_InvId;
        ::  else ->
                if
                ::  tasks[tid].isr == true ->
                        rc = RC_FrmIsr;
                ::  else ->
                        bool isremoved;
                        removeTask(tid, isremoved);
                        if
                        ::  isremoved == false ->
                                rc = RC_InvId;
                        ::  else ->
                                tasks[tid].state = non;
                                tasks[tid].start = 0;
                                rc = RC_OK;
                        fi
                fi
        fi
    }
}
//*/

//mtype = {Resume, Suspend, ResSpnd, SpndRes, ResRes, SpndSpnd}

// Task Create
bool task_1_name;
byte insertId
byte createPrio;
bool createValID;

bool createTask;

// Task Start
byte taskEntry;
bool startValID;
bool doubleStart;

bool startTask;

// Task Delete
byte deleteId;

bool deleteTask;




mtype = {CreateAndDestroy, TooMany, Invalid, ISRctx, InvEntry, IncState MultiCore}
mtype scenario;

inline chooseScenario() {

    // Defaults
    task_control = 30;	// 0001 1110
    task_1_name = 1;
    createTask = true;
	createPrio = DEFUALT_PRIO;
	createValID = true;

    startTask = false;
	startValID = true;
	doubleStart = false;
	taskEntry = SEMA_TASK_START_0;

	deleteTask = false;

    if
    ::  scenario = CreateAndDestroy;
    //::  scenario = TooMany;
    //::  scenario = Invalid;
    //::  scenario = ISRctx;
    //::  scenario = InvEntry;
	//::	scenario = IncState;
    fi
    atomic{printf("@@@ %d LOG scenario ",_pid); printm(scenario); nl()} ;

    if
    ::  scenario == CreateAndDestroy ->
            startTask = true;
			deleteTask = true;
    ::  scenario == TooMany ->
            task_control = 0;
    ::  scenario == Invalid ->
            if
            ::  task_1_name = 0;
            ::  createPrio = 0;
            ::  createPrio = MAX_PRIO;
            ::  deleteId = BAD_ID; createTask = false; deleteTask = true;
			::	createValID = false;
			::	startValID = false; startTask = true; deleteTask = true;
            fi
    //::  scenario == ISRctx -> skip;
    ::  scenario == InvEntry ->
			startTask = true;
            taskEntry = 0;
			deleteTask = true;
	::	scenario == IncState ->
			startTask = true;
			doubleStart = true;
			deleteTask = true;
    ::  else    // go with defaults
    fi
}

/*
proctype SuspendResume (byte nid, taskid) {

    byte sc;
    printf( "@@@ %d DECL byte sc\n", _pid );
    byte prio ;
    printf( "@@@ %d DECL byte prio\n", _pid );

    tasks[taskid].nodeid = nid;
    tasks[taskid].pmlid = _pid;
    tasks[taskid].state = Ready;
    printf("@@@ %d TASK Worker\n",_pid);

    if
    :: doSuspend ->
        task_suspend(taskid, target, sc);
        printf("@@@ %d SCALAR Suspend rc %d\n",_pid,rc);
    :: else ->
        task_resume(taskid, target, sc);
    fi
    

}
//*/

bool stopclock = false;

/*
 * We need a process that periodically wakes up blocked processes.
 * This is modelling background behaviour of the system,
 * such as ISRs and scheduling.
 * We visit all tasks in round-robin order (to prevent starvation)
 * and make them ready if waiting on "other" things.
 * Tasks waiting for events or timeouts are not touched
 * This terminates when all tasks are zombies.
 */
proctype System () {
  byte taskid ;
  bool liveSeen;
  int tout_cnt = 0;

  printf("@@@ %d LOG System running...\n",_pid);

  loop:
  taskid = 1;
  liveSeen = false;

/*
  printf("@@@ %d LOG Loop through tasks...\n",_pid);
  atomic {
    printf("@@@ %d LOG Scenario is ",_pid);
    printm(scenario); nl();
  }
*/
  do   // while taskid < TASK_MAX ....
  ::  taskid ==  TASK_MAX -> break;
  ::  else ->
/*
      atomic {
        printf("@@@ %d LOG Task %d state is ",_pid,taskid);
        printm(tasks[taskid].state); nl()
      }
*/
      if
      :: tasks[taskid].state == non -> taskid++
      :: else ->
         if
         ::  tasks[taskid].state == OtherWait
             -> tasks[taskid].state = Ready
                printf("@@@ %d STATE %d Ready\n",_pid,taskid)
         ::  else -> skip
         fi
         liveSeen = true;
         taskid++
      fi
  od

  //printf("@@@ %d LOG ...all visited, live:%d\n",_pid,liveSeen);

  if
  ::  liveSeen -> 
  		tout_cnt = tout_cnt + 1;
		if	
		::	tout_cnt > TIMOUT_VAL ->
				goto loop
		:: else
		fi
  ::  else
  fi
  printf("@@@ %d LOG All are Zombies, game over.\n",_pid);
  stopclock = true;
}


/*
 * We need a process that handles a clock tick,
 * by decrementing the tick count for tasks waiting on a timeout.
 * Such a task whose ticks become zero is then made Ready,
 * and its timer status is flagged as a timeout
 * This terminates when all tasks are zombies
 * (as signalled by System via `stopclock`).
 */
proctype Clock () {
  int tid, tix;
  printf("@@@ %d LOG Clock Started\n",_pid)

  do
  ::  stopclock  -> goto stopped
  ::  !stopclock ->
      //printf(" (tick) \n");
      tid = 1;
      do
      ::  tid == TASK_MAX -> break
      ::  else ->
          //atomic{printf("Clock: tid=%d, state=",tid); printm(tasks[tid].state); nl()};
          if
          ::  tasks[tid].state == TimeWait ->
              tix = tasks[tid].ticks - 1;
              // printf("Clock: ticks=%d, tix=%d\n",tasks[tid].ticks,tix);
              if
              ::  tix == 0
                  tasks[tid].tout = true
                  tasks[tid].state = Ready
                  printf("@@@ %d STATE %d Ready\n",_pid,tid)
              ::  else
                  tasks[tid].ticks = tix
              fi
          ::  else // state != TimeWait
          fi
          tid = tid + 1
      od
  od
stopped:
  printf("@@@ %d LOG Clock Stopped\n",_pid);
}

proctype Runner(byte nid) {
    /*
    if
    :: multicore ->
        // printf("@@@ %d CALL RunnerScheduler %d\n", _pid, rcvCore);
        printf("@@@ %d CALL SetProcessor %d\n", _pid, rcvCore);
    :: else
    fi
    */
	// Task 0 Create Params
	byte name = task_1_name;
    byte prio = createPrio;
    byte preempt = true;
	byte mode = 0;
	byte attr = 0;
	bool setRC;
	
	// Task 0 Start Params 
	byte entry = taskEntry;
	bool doubleDone = false;
	byte startId;
	//byte args = 0;

    if 
    ::  createTask == true ->
		if
		::	createValID == true ->
				setTask(insertId, setRC);
				if 
				::	setRC == false ->
						printf("@@@ %d CALL TooMany\n", _pid);
				:: 	else
				fi
		::	else ->
				insertId = 0;
				setRC = true;
		fi

		printf("@@@ %d CALL task_create %d %d %d %d %d createRC\n", 
				_pid, name, prio, mode, attr, insertId);

        task_create(nid, name, prio, preempt, insertId, setRC, createRC);
		
		printf("@@@ %d SCALAR createRC %d\n", _pid, createRC);
        if 
        ::  createRC == RC_OK ->
repeat_start:
				if
				::	startValID == false ->
						startId = 0;
				:: 	else -> 
						startId = insertId;
				fi

                task_start(startId, entry, startRC);
				printf("@@@ %d CALL task_start %d %d startRC\n", 
						_pid, startId, entry);
				printf("@@@ %d CALL startRC %d\n", _pid, startRC);
				if
				::	startRC != RC_OK ->
						Release(SEMA_CREATEDELETE);
				:: 	doubleStart == true ->
						if 
						::	doubleDone == false ->
							doubleDone = true;
							goto repeat_start;
						:: else
						fi
				:: else
				fi
        ::  else -> skip
        fi
    ::  else
    fi

}

proctype Worker(byte delId) {
    /*
    if
    :: multicore ->
        // printf("@@@ %d CALL RunnerScheduler %d\n", _pid, rcvCore);
        printf("@@@ %d CALL SetProcessor %d\n", _pid, rcvCore);
    :: else
    fi
    */
	if 
	::	startTask == true ->
	    	Obtain(SEMA_CREATEDELETE);
	::	else
	fi

    if
    ::  createTask == true ->
            deleteId = insertId;
    ::  else
    fi

    if
    ::  deleteTask == true -> 
			printf( "@@@ %d CALL task_delete %d deleteRC\n", _pid, deleteId);
			
            task_delete(deleteId, deleteRC);

            printf("@@@ %d SCALAR delRC %d\n", _pid, deleteRC);
    ::  else 
    fi
}

// global task variables

byte x = 0;

proctype Task0() {
    if
    ::  startTask == true && scenario != InvEntry ->
            Obtain(SEMA_TASK_START_0);

            x = x + 1;

            printf("%d\n", x);

            // Release Semaphores
            Release(SEMA_TASK_START_0);
			Release(SEMA_CREATEDELETE);
    ::  else -> skip
    fi
}

init {
	pid nr;

	printf("Task Manager Model running.\n");
	printf("Setup...\n");

	printf("@@@ %d NAME Task_Manager_TestGen\n",_pid)

	outputDefines();
	outputDeclarations();

	chooseScenario();
	printf("@@@ %d INIT\n",_pid);

	printf("Run...\n");

	
	run Runner(0);
	run Worker(0);
	run Task0();

//	run System();
//	run Clock();

	Release(SEMA_TASKCONTROL);

	_nr_pr == 1;

	#ifdef TEST_GEN
	assert(false);
	#endif

	printf("Task Manager Model finished !\n")
}
