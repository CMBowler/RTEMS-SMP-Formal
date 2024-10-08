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
#define SEMA_MAX 2

#define SEMA_TASKCONTROL 0
#define SEMA_CREATEDELETE 1

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
#define TASK_MAX 8 // These are the "RTEMS" tasks only, numbered 1 & 2
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
  Zombie, Ready, EventWait, TimeWait, OtherWait,
  executing, ready, blocked, dormant, non
};


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
  mtype state ; // {Ready,EventWait,TickWait,OtherWait}
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
    ::  raw_tid == 1 ->
            tid = 0;
    ::  raw_tid == 2 ->
            tid = 1;
    ::  raw_tid == 4 ->
            tid = 2;
    ::  raw_tid == 8 ->
            tid = 3;
    ::  raw_tid == 16 ->
            tid = 4;
    ::  raw_tid == 32 ->
            tid = 5;
    ::  raw_tid == 64 ->
            tid = 6;
    ::  raw_tid == 128 ->
            tid = 7;
    ::  else ->
            tid = TASK_MAX;
            rc = false;
    fi
}
///*
inline task_create(nid, prio, preempt, tid, rc) {
    atomic {
        if
        ::  prio == 0 ->
                rc = RC_InvPrio
        ::  prio >= BAD_PRIO ->
                rc = RC_InvPrio
        ::  else ->
                bool nameRC;
                isNameValid(name, nameRC);
                if
                ::  nameRC == false ->
                        rc = RC_InvName;
                ::  else ->
                        bool setRC;
                        setTask(tid, setRC);
                        if 
                        ::  setRC == false ->
                                rc = RC_TooMany;
                        ::  else ->
                                tasks[tid].nodeid = nid;
                                tasks[tid].pmlid = _pid;
                                tasks[tid].prio = prio;
                                tasks[tid].mode.preempt = preempt;
                                tasks[tid].state = dormant;
                        fi
                fi
        fi
    }
}
//*/

///*
inline task_start(self, tid, entry, arg, rc) {
    atomic {
        if
        ::  task[tid].state == non ->
                printf("@@@ %d LOG Start NULL out.\n",_pid);
                rc = RC_InvId;
        ::  else ->
            if 
            ::  entry == 0 -> RC_InvId
            ::  else ->
                tasks[tid].state = ready;
                task[tid].start = entry;
                rc = RC_OK;
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

bool name;
bool createTask, deleteTask;
byte deleteId, insertId;
byte createPrio;
mtype = {CreateAndDestroy, TooMany, Invalid, ISRctx, MultiCore}
mtype scenario;

inline chooseScenario() {

    // Defaults
    task_control = 255;
    name = true;
    createTask = true;
    deleteTask = true;

    if
    ::  scenario = CreateAndDestroy;
    ::  scenario = TooMany;
    ::  scenario = Invalid;
    ::  scenario = ISRctx;
    fi
    atomic{printf("@@@ %d LOG scenario ",_pid); printm(scenario); nl()} ;

    if
    ::  scenario == TooMany ->
            task_control = 0;
            deleteTask = false;
    ::  scenario == Invalid ->
            if
            ::  name = false;
            ::  createPrio = 0;
            ::  createPrio = MAX_PRIO;
            ::  deleteId = 0; createTask = false;
            fi
    ::  scenario == ISRctx ->
            skip;
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

proctype Creator(byte nid) {
    byte createRC;
    /*
    if
    :: multicore ->
        // printf("@@@ %d CALL RunnerScheduler %d\n", _pid, rcvCore);
        printf("@@@ %d CALL SetProcessor %d\n", _pid, rcvCore);
    :: else
    fi
    */

    byte prio = DEFUALT_PRIO;
    byte preempt = true;
    if 
    ::  createTask == true ->
        task_create(nid, prio, preempt, insertId, createRC);
    ::  else
    fi
    Release(SEMA_CREATEDELETE);

    printf("@@@ %d SCALAR createRC %d\n",_pid,createRC);


}

proctype Destroyer(byte delId) {
    /*
    if
    :: multicore ->
        // printf("@@@ %d CALL RunnerScheduler %d\n", _pid, rcvCore);
        printf("@@@ %d CALL SetProcessor %d\n", _pid, rcvCore);
    :: else
    fi
    */

    Obtain(SEMA_CREATEDELETE);

    if
    ::  createTask == true ->
            delId = insertId;
    ::  else
    fi

    if
    ::  deleteTask == true -> 
            byte deleteRC;
            task_delete(delId, deleteRC);
    ::  else 
    fi

    printf("@@@ %d SCALAR createRC %d\n",_pid,deleteRC);
}

init {
  pid nr;

  printf("Event Manager Model running.\n");
  printf("Setup...\n");

  printf("@@@ %d NAME Event_Manager_TestGen\n",_pid)
  //outputDefines();
  //outputDeclarations();

  printf("@@@ %d INIT\n",_pid);
  chooseScenario();



  printf("Run...\n");

  run System();
  run Clock();

  Released(SEMA_TASKCONTROL);

  run Creator(0);
  run Destroyer(0);


  _nr_pr == 1;

#ifdef TEST_GEN
  assert(false);
#endif

  printf("Task Manager Model finished !\n")
}
