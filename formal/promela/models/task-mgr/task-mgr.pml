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
#define TASK_MAX 5 
#define SEMA_MAX 4
#include "../common/model.pml"

#define NUM_PROC 5

// We use two semaphores to synchronise the tasks
#define INVALID_ENTRY       (0)
#define SEMA_CREATEDELETE 	(0) // Model Specific Lock
#define SEMA_TASK_START_0 	(1)
#define SEMA_TASK_START_1  	(2)
#define SEMA_LOCK           (3)

/*
 * We need to output annotations for any #define we use.
 * It is simplest to keep them all together,
 * and use an inline to output them.
 */

#define MAX_PRIO 255
#define BAD_PRIO MAX_PRIO
#define CURRENT_PRIO 0
#define LOW_PRIO 1
#define MED_PRIO 5
#define HIGH_PRIO 10

#define INVALID_ID 0
#define RUNNER_ID 1
#define TASK0_ID 2
#define TASK1_ID 3

#define CLEAR_TASKS 255
byte task_control = CLEAR_TASKS;

/*
 * Running Orders (maintained by simple global sync counter):
 *   Receive;;Send  =  Receive;TestSyncRelease(1) || TestSyncObtain(1);Send
 * Here ;; is "sequential" composition of *different* threads
 */
bool semaphore[SEMA_MAX]; // Semaphore

inline ObtainMutex(tid, sid) {
    TestSyncObtain(sid);
    tasks[tid].mutexs[sid] = 1;
}

inline ReleaseMutex(tid, sid) { 
    if
    ::  tasks[tid].mutexs[sid] == 1 ->
            TestSyncRelease(sid);
            //rc = true;
    ::  else //-> rc = false
    fi
}

inline outputDefines () {

	printf("@@@ %d DEF TASK_MAX %d\n",_pid,TASK_MAX);
	printf("@@@ %d DEF INVALID_ID %d\n",_pid,INVALID_ID);
	printf("@@@ %d DEF SEMA_MAX %d\n",_pid,SEMA_MAX);

    // Priority inversion
    printf("@@@ %d DEF LOW_PRIO %d\n",_pid,HIGH_PRIO);
    printf("@@@ %d DEF MED_PRIO %d\n",_pid,MED_PRIO);
    printf("@@@ %d DEF HIGH_PRIO %d\n",_pid,LOW_PRIO);
	
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
  mtype state = Zombie ; // {Ready,EventWait,TickWait,OtherWait}
  Mode mode;    // Contains information about the task mode.
  byte prio ;   // lower number is higher priority
  int ticks;    //
  bool tout;    // true if woken by a timeout
  bool isr;     // If task is woken from Interrupt context
  bool mutexs[SEMA_MAX]; // List of Semaphores the task is currently holding.
};

Task tasks[TASK_MAX]; // tasks[0] models a NULL dereference

byte sendrc;            // Sender global variable
byte recrc;             // Receiver global variable
byte recout[TASK_MAX] ; // models receive 'out' location.

byte createRC;
byte startRC;
byte deleteRC;
byte suspendRC;
byte isSuspendRC;
byte resumeRC;

byte task_id[TASK_MAX] ;

/*
inline isTaskHolding(tid) {
    
}
//*/

inline outputDeclarations () {
  printf("@@@ %d DECL byte createRC 0\n",_pid);
  printf("@@@ %d DECL byte startRC 0\n",_pid);
  printf("@@@ %d DECL byte deleteRC 0\n",_pid);
  printf("@@@ %d DECL byte suspendRC 0\n",_pid);
  printf("@@@ %d DECL byte isSuspendRC 0\n",_pid);
  printf("@@@ %d DECL byte resumeRC 0\n",_pid);
  printf("@@@ %d DECL byte setPriorityRC 0\n",_pid);
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
    //TestSyncObtain(SEMA_TASKCONTROL);
    raw_tid = task_control & (~task_control + 1);
    task_control = task_control - raw_tid;
    //TestSyncRelease(SEMA_TASKCONTROL);
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
                rc = RC_InvPrio;
        ::  prio >= BAD_PRIO ->
                rc = RC_InvPrio;
		::  tidRC == false ->
                rc = RC_TooMany;
		::	tid == 0 ->
				rc = RC_InvAddr;
        ::  else ->
				tasks[tid].nodeid = nid;
				tasks[tid].pmlid = _pid;
				tasks[tid].prio = prio;
				tasks[tid].mode.preempt = preempt;
				tasks[tid].state = Dormant;
        fi
    }
}
//*/

///*
inline task_start(tid, entry, rc) {
    atomic {
        if
        ::  tasks[tid].state == Zombie ->
                printf("@@@ %d LOG Start NULL out.\n",_pid);
                rc = RC_InvId;
		:: 	else ->
				if
				::  tasks[tid].state != Dormant ->
						rc = RC_IncState;
				:: 	else ->
						if 
						::  entry == 0 -> rc = RC_InvAddr;
						::  else ->
							tasks[tid].state = Ready;
							tasks[tid].start = entry;
							// Start Task Model
							TestSyncRelease(entry);
							rc = RC_OK;
						fi
				fi
        fi
    }
}
//*/


inline task_suspend(tid, rc) {
    atomic {
        if
        ::  tasks[tid].state == Zombie ->
                rc = RC_InvId;
        ::  tasks[tid].state == Blocked ->
                rc = RC_AlrSuspd;
        ::  else ->
                tasks[tid].state = Blocked;
                rc = RC_OK;
        fi
    }
}

inline task_isSuspend(tid, rc) {
    atomic {
        if
        ::  tasks[tid].state == Zombie ->
                rc = RC_InvId;
        ::  tasks[tid].state == Blocked ->
                rc = RC_AlrSuspd;
        ::  else ->
                rc = RC_OK;
        fi
    }
}

inline task_resume(tid, rc) {
    atomic {
        if
        ::  tasks[tid].state == Zombie ->
            rc = RC_InvId;
        ::  else ->
                if
                :: tasks[tid].state != Blocked ->
                    rc = RC_IncState;
                :: else ->
                    tasks[tid].state = Ready ->
                    rc = RC_OK;
                fi
        fi
    }
}

inline removeTask(tid, rc) {
    byte raw_tid = 1 << tid;
    //TestSyncObtain(SEMA_TASKCONTROL);
    if
    ::  (task_control & raw_tid) != raw_tid ->
            task_control = task_control + raw_tid;
            rc = true;
    ::  (task_control & raw_tid) == raw_tid ->
            rc = false;
    fi
    //TestSyncRelease(SEMA_TASKCONTROL);
}

///*
inline task_delete(tid, rc) {
    atomic {
        if
        ::  tid > TASK_MAX ->
                rc = RC_InvId;
        ::  tid == 0 ->
                rc = RC_InvId;
        ::  else ->
                if
                ::  tasks[tid].state == Zombie ->
                        rc = RC_IncState;
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
                                        tasks[tid].state = Zombie;
                                        tasks[tid].start = 0;
                                        rc = RC_OK;
                                fi
                        fi
                fi
        fi
    }
}
//*/


inline task_setPrio(tid, new, old, rc) {
    atomic {
        if
        ::  tasks[tid].state == Zombie ->
                rc = RC_InvId;
        ::  old == INVALID_ID ->
                rc = RC_InvAddr;
        ::  else ->
                if
                ::  new > MAX_PRIO ->
                        rc = RC_InvPrio;
                ::  new == CURRENT_PRIO ->
                        old = tasks[tid].prio;
                        rc = RC_OK;
                ::  else ->
                        old = tasks[tid].prio;
                        if
                        ::  new <= old -> skip
                        ::  else ->
                        // If the task is currently holding any binary semaphores 
                        // which use a locking protocol, then the task’s priority cannot be lowered immediately
                                
                        fi
                        tasks[tid].prio = new;
                        set_priority(tasks[tid].pmlid, new); //TODO
                        rc = RC_OK;
                fi
        fi
    }
}

//inline task_getPrio (tid, sched, prio)


//mtype = {Resume, Suspend, ResSpnd, SpndRes, ResRes, SpndSpnd}

// Task Create
bool task_0_name;
byte insertId
byte createPrio;
bool createValId;

bool createTask;

// Task Start
byte taskEntry;
bool startValId;
bool startValEntry;
bool doubleStart;

bool startTask;

// Task Delete
byte deleteId;

bool deleteTask;

// Task Suspend/Resume
byte suspendId;
byte resumeId;
bool suspValId;
bool resumeValId;
bool doubleSuspend;
bool suspendSelf;

bool suspendTask;

// Priority

byte task_1_name;
byte tsk1_ID;
byte task_1_Entry;

bool testPrio;


mtype = {CreateDestroy, TaskStart, SuspResume, ChangePrio}
mtype scenario;

inline chooseScenario() {

    // Defaults
    task_control = 28;	// 0001 1100 Task[1] reserved for runner.

    // Task Create
    createTask = true;
    task_0_name = 1;
	createPrio = MED_PRIO;
	createValId = true;

    // Start Task
    startTask = true;
	startValId = true;
    startValEntry = true;
	doubleStart = false;
	taskEntry = SEMA_TASK_START_0;

    // Delete Task
	deleteTask = true;
    deleteId = INVALID_ID;

    // Suspend
    suspendTask = false;
    suspendId = INVALID_ID;
    suspValId = true;
    doubleSuspend = false;
    suspendSelf = false;
    // Resume
    resumeId = INVALID_ID;
    resumeValId = true;

    // Priority
    task_1_name = 2;
    task_1_Entry = SEMA_TASK_START_1;

    testPrio = false;

    tasks[RUNNER_ID].state = Ready;

    if
    ::  scenario = CreateDestroy;
    ::  scenario = TaskStart;
    ::  scenario = SuspResume;
    ::  scenario = ChangePrio;
    fi

    atomic{printf("@@@ %d LOG scenario ",_pid); printm(scenario); nl()} ;

    // Create/Delete
    if
    ::  scenario == CreateDestroy ->
            startTask = false; 
            deleteTask = false;
            // Create/Delete
            if
            ::  task_0_name = 0; atomic{printf("@@@ %d LOG Invalid Name ",_pid); printm(scenario); nl()};
            ::  createPrio = 0;
            ::  createPrio = MAX_PRIO;
            ::  createValId = false;
//          ::  scenario = TooMany;
            ::  createTask = false; deleteTask = true;
            ::  deleteTask = true;
            fi
    ::  scenario == TaskStart ->
            startTask = false;
            // Start
            if
            ::  startValId = false;         atomic{printf("@@@ %d LOG Start: Invalid Id ",_pid); printm(scenario); nl()};
            ::  startValEntry = false;      atomic{printf("@@@ %d LOG Start: Invalid Entry ",_pid); printm(scenario); nl()};
            ::  doubleStart = true;         atomic{printf("@@@ %d LOG Start: Task Already Started ",_pid); printm(scenario); nl()};
            ::  startTask = true;           atomic{printf("@@@ %d LOG Start: Success ",_pid); printm(scenario); nl()};
            fi
    ::  scenario == SuspResume ->
            suspendTask = true;
            // Suspend
            if
            ::  startValEntry = false; startTask = false;
            ::  suspValId = false;                  // suspend -> RTEMS_INVALID_ID; resume -> RTEMS_INCORRECT_STATE
            ::  resumeValId = false;                // resume -> RTEMS_INVALID_ID
            ::  doubleSuspend = true;               // suspend -> RTEMS_SUCCESSFUL; suspend -> RTEMS_ALREADY_SUSPENDED;
            ::  suspendSelf = true; suspendTask = false;
            ::  skip;
            fi
    ::  scenario == ChangePrio ->
            testPrio = true;
            //suspendSelf = true;
    fi
}

inline SuspendResume(suspId, resumeId) {
    bool repeated = false;

suspRepeat:
    // Suspend
    printf("@@@ %d CALL task_suspend %d suspendRC\n", 
                _pid, suspId, suspendRC);
    task_suspend(suspId, suspendRC);
    printf("@@@ %d SCALAR suspendRC %d\n",_pid,suspendRC);

    if
    ::  doubleSuspend == true && repeated == false ->
            repeated = true;
            goto suspRepeat;
    ::  else
    fi
    //Check is suspended
    //...

    //Resume
    printf("@@@ %d CALL task_resume %d resumeRC\n", 
                _pid, resumeId, resumeRC);
    task_resume(resumeId, resumeRC);
    printf("@@@ %d SCALAR resumeRC %d\n",_pid,resumeRC);

}


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

//  printf("@@@ %d LOG Loop through tasks...\n",_pid);
//  atomic {
    //printf("@@@ %d LOG Scenario is ",_pid);
    //printm(scenario); nl();
//  }
  do   // while taskid < TASK_MAX ....
  ::  taskid == TASK_MAX -> break;
  ::  else ->
//      atomic {
        //printf("@@@ %d LOG Task %d state is ",_pid,taskid);
        //printm(tasks[taskid].state); nl()
//      }
      if
      :: tasks[taskid].state == Zombie -> taskid++
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
  ::  liveSeen -> goto loop
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

proctype Runner(byte nid, taskid) {
    assert(_priority == MED_PRIO)
    /*
    if
    :: multicore ->
        // printf("@@@ %d CALL RunnerScheduler %d\n", _pid, rcvCore);
        printf("@@@ %d CALL SetProcessor %d\n", _pid, rcvCore);
    :: else
    fi
    */
    // Runner Task Params
    tasks[taskid].nodeid = nid;
    tasks[taskid].pmlid = _pid;
    tasks[taskid].state = Ready;

	// Task 0 Create Params
	byte name = task_0_name;
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
		::	createValId == true ->
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
    ::  else
    fi


    if 
    ::  startTask == true ->
            if
            ::	startValId == true ->
                    startId = insertId;
            :: 	startValId == false ->
                    startId = INVALID_ID;
            fi

            if
            ::  startValEntry == true ->
                    entry = SEMA_TASK_START_0;
            ::  startValEntry == false ->
                    entry = INVALID_ENTRY;
            fi
repeat_start:
            task_start(startId, entry, startRC);
            printf("@@@ %d CALL task_start %d %d startRC\n", 
                    _pid, startId, entry);
            printf("@@@ %d CALL startRC %d\n", _pid, startRC);
            if
            ::	startRC != RC_OK ->
                    TestSyncRelease(SEMA_CREATEDELETE);
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

    if
    ::  testPrio == true ->
            // Create and Start New Task (1)
            setTask(tsk1_ID, setRC);
            printf("@@@ %d CALL task_create %d %d %d %d %d createRC\n", 
                    _pid, task_1_name, prio, mode, attr, tsk1_ID);
            task_create(nid, task_1_name, prio, preempt, tsk1_ID, setRC, createRC);
            printf("@@@ %d SCALAR createRC %d\n", _pid, createRC);
            //
            task_start(tsk1_ID, task_1_Entry, startRC);
            printf("@@@ %d CALL task_start %d %d startRC\n", 
                    _pid, tsk1_ID, task_1_Entry);
            printf("@@@ %d CALL startRC %d\n", _pid, startRC);
    ::  else -> skip
    fi

    if
    ::  suspendSelf == true ->
            //Resume
            // Wait for Task 0 to self Suspend
            printf("@@@ %d CALL WaitForSuspend %d resumeRC\n", 
                        _pid, insertId, resumeRC);
            do
            ::  isSuspendRC == RC_AlrSuspd -> break;
            ::  else -> 
                    task_isSuspend(insertId, isSuspendRC);
            od

            printf("@@@ %d CALL task_resume %d resumeRC\n", 
                        _pid, insertId, resumeRC);
            task_resume(insertId, resumeRC);
            printf("@@@ %d SCALAR resumeRC %d\n",_pid,resumeRC);
    ::  else
    fi

    if 
    ::	startTask == true ->
            TestSyncObtain(SEMA_CREATEDELETE);
    ::	else
    fi

    if
    ::  suspendTask == true ->
            if
            ::  suspValId == true ->
                    suspendId = insertId;
            ::  else // Set to 0
            fi
            if
            ::  resumeValId == true ->
                    resumeId = insertId;
            ::  else // Set to 0
            fi
            SuspendResume(suspendId, resumeId);
    ::  else 
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

            if
            ::  testPrio == true ->
                    printf( "@@@ %d CALL task_delete %d deleteRC\n", _pid, tsk1_ID);
			
                    task_delete(tsk1_ID, deleteRC);

                    printf("@@@ %d SCALAR delRC %d\n", _pid, deleteRC);
            ::  else
            fi
    ::  else 
    fi


    // Once done, free runner task model id:
    bool runRC;
    removeTask(taskid, runRC);
    if
    ::  runRC == true ->
            tasks[taskid].state = Zombie;
    ::  else
    fi

}

// global task variables

proctype Task0(byte taskid) priority MED_PRIO {
    assert(_priority == MED_PRIO)
    /*
    if
    :: multicore ->
        // printf("@@@ %d CALL RunnerScheduler %d\n", _pid, rcvCore);
        printf("@@@ %d CALL SetProcessor %d\n", _pid, rcvCore);
    :: else
    fi
    */

    if
    ::  startTask == true ->
            TestSyncObtain(SEMA_TASK_START_0);
            TestSyncRelease(SEMA_TASK_START_0);

            tasks[taskid].pmlid = _pid;
            //set_priority(_pid, tasks[taskid].prio)

            //Do Stuff

            // Priority Changing 
            if 
            ::  testPrio == true ->
                    // Obtain Mutex:
                    ObtainMutex(taskid, SEMA_LOCK);
            ::  else
            fi

            // Self Suspend:
            if
            ::  suspendSelf == true ->
                    // Suspend
                    printf("@@@ %d CALL task_suspend %d suspendRC\n", 
                                    _pid, insertId, suspendRC);
                    task_suspend(insertId, suspendRC);
                    printf("@@@ %d SCALAR suspendRC %d\n",_pid,suspendRC);
            ::  else 
            fi
            
            if
            ::  testPrio == true ->
                    byte setPriorityRC;
                    byte old_prio = 1;
                    
                    printf("@@@ %d DECL byte priority 0\n",_pid);


                    // Check Priority
                    printf("@@@ %d CALL task_setPriority %d %d %d setPriorityRC\n", 
                                            _pid, taskid, CURRENT_PRIO, old_prio, setPriorityRC);
                    task_setPrio(taskid, CURRENT_PRIO, old_prio, setPriorityRC);
                    printf("@@@ %d SCALAR setPriorityRC %d\n",_pid,setPriorityRC);

                    // Chage Priority to High
                    printf("@@@ %d CALL task_setPriority %d LOW_PRIO %d setPriorityRC\n", 
                                            _pid, taskid, LOW_PRIO, old_prio, setPriorityRC);
                    task_setPrio(taskid, LOW_PRIO, old_prio, setPriorityRC);
                    printf("@@@ %d SCALAR setPriorityRC %d\n",_pid,setPriorityRC);

                    // Check Priority
                    printf("@@@ %d CALL task_setPriority %d %d %d setPriorityRC\n", 
                                            _pid, taskid, CURRENT_PRIO, old_prio, setPriorityRC);
                    task_setPrio(taskid, CURRENT_PRIO, old_prio, setPriorityRC);
                    printf("@@@ %d SCALAR setPriorityRC %d\n",_pid,setPriorityRC);
            
                    // Release Mutex:
                    ReleaseMutex(taskid, SEMA_LOCK);         
            ::  else -> skip
            fi
            // Release Semaphores
            TestSyncRelease(SEMA_CREATEDELETE);
    ::  else -> skip
    fi
}

proctype Task1(byte taskid) {
    assert(_priority == MED_PRIO)
    if
    ::  testPrio == true ->
            byte setPriorityRC;
            byte old_prio = 1;

            TestSyncObtain(SEMA_TASK_START_1);
            TestSyncRelease(SEMA_TASK_START_1);

            tasks[taskid].pmlid = _pid;
            //set_priority(_pid, tasks[taskid].prio)
            
            printf("@@@ %d DECL byte priority 0\n",_pid);


            // Check Priority
            printf("@@@ %d CALL task_setPriority %d %d %d setPriorityRC\n", 
                                    _pid, taskid, CURRENT_PRIO, old_prio, setPriorityRC);
            task_setPrio(taskid, CURRENT_PRIO, old_prio, setPriorityRC);
            printf("@@@ %d SCALAR setPriorityRC %d\n",_pid,setPriorityRC);

            // Chage Priority to High
            printf("@@@ %d CALL task_setPriority %d HIGH_PRIO %d setPriorityRC\n", 
                                    _pid, taskid, HIGH_PRIO, old_prio, setPriorityRC);
            task_setPrio(taskid, HIGH_PRIO, old_prio, setPriorityRC);
            printf("@@@ %d SCALAR setPriorityRC %d\n",_pid,setPriorityRC);

            // Check Priority
            printf("@@@ %d CALL task_setPriority %d %d %d setPriorityRC\n", 
                                    _pid, taskid, CURRENT_PRIO, old_prio, setPriorityRC);
            task_setPrio(taskid, CURRENT_PRIO, old_prio, setPriorityRC);
            printf("@@@ %d SCALAR setPriorityRC %d\n",_pid,setPriorityRC);

            // Obtain Mutex:
            ObtainMutex(taskid, SEMA_LOCK);

            // Release Mutex:
            ReleaseMutex(taskid, SEMA_LOCK);
        
    ::  else
    fi
}

init priority MED_PRIO{
	pid nr;

	printf("Task Manager Model running.\n");
	printf("Setup...\n");

	printf("@@@ %d NAME Task_Manager_TestGen\n",_pid)

	outputDefines();
	outputDeclarations();

	chooseScenario();
	printf("@@@ %d INIT\n",_pid);

	printf("Run...\n");


    if 
    ::  startTask == true ->
            printf("@@@ %d DEF TASK_0 %d\n",_pid,startTask);
    ::  else
    fi
    if
    ::  testPrio == true ->
            printf("@@@ %d DEF TASK_1 %d\n",_pid,testPrio);
    ::  else
    fi

	run System();
	run Clock();

    TestSyncRelease(SEMA_LOCK);
	
    run Runner(0, RUNNER_ID) priority MED_PRIO;
    run Task0(TASK0_ID) priority MED_PRIO;
    run Task1(TASK1_ID) priority MED_PRIO;

	_nr_pr == 1;

	#ifdef TESTGEN
	assert(false);
	#endif

	printf("Task Manager Model finished !\n")
}
