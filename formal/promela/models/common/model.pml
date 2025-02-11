/* SPDX-License-Identifier: BSD-2-Clause */

/*
 * PML Modelling code common to all/most models
 *
 *  - Common Task Definition
 *  - Task State Changes
 *  - Simple Binary Semaphores for Test Synchronisation
 *
 * IMPORTANT: 
 *  a model must #define TASK_MAX and SEMA_MAX *before* #including this file.
 */




 /*
 *  Common Task Definition
 *
 *  need text here to explain usage
 */
typedef Task {
  byte nodeid; // So we can spot remote calls
  byte pmlid; // Promela process id
  byte tid; // Task ID
  mtype state = Zombie; // {Zombie,Dormant,Ready,TimeWait,OtherWait,...}
  byte start;
  bool preemptable;
  byte prio; // lower number is higher priority
  byte suspPrio; // Stores the tasks priority while suspended. 
  int ticks; // clock ticks to keep track of timeout
  bool tout; // true if woken by a timeout
  bool isr;     // If task is woken from Interrupt context
  bool HoldingMutex;
  bool mutexs[SEMA_MAX]; // List of Semaphores the task is currently holding.
};
Task tasks[TASK_MAX]; // tasks[0] models a NULL dereference
#define BAD_ID TASK_MAX   // this ID and higher are considered invalid

// Signals task has finished step of execution
chan taskSignal = [1] of {byte};

// Signal task to execute
chan sched[(TASK_MAX)] = [1] of {byte};

// Clock signals new loop of system
chan clk = [2] of {byte};

// Signal for Semaphore Release
chan sema_signal[SEMA_MAX] = [TASK_MAX] of {byte};

chan sema_wait[SEMA_MAX] = [TASK_MAX] of {byte};

chan sema_ready = [SEMA_MAX] of {byte};

byte taskQueue[TASK_MAX];
 /*
 *  Task State Changes
 *
 *  Here we provide generic model code for starting and stopping task.
 *  This captures some of the behaviour of the scheduler.
 *  Features include:
 *     waitUntilReady
 *     stopclock
 */

/*
 * waitUntilReady(id) logs that task[id] is waiting,
 * and then attempts to execute a statement that blocks,
 * until some other process changes task[id]'s state to Ready.
 * It relies on the fact that if a statement blocks inside an atomic block,
 * the block loses its atomic behaviour and yields to other Promela processes
 *
 * It is used to model a task that has been suspended for any reason.
 */
inline waitUntilReady(id){
  atomic{
    printf("@@@ %d LOG Task %d waiting, state = ",_pid,id);
    printm(tasks[id].state); nl()
  }
  tasks[id].state == Ready; // breaks out of atomics if false
  printf("@@@ %d STATE %d Ready\n",_pid,id)
}

inline nl() { printf("\n") } // Useful shorthand

bool stopclock = false; // used by System to stop the Clock

mtype scenario; // used in models to identify top-level senario

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

  byte maxCount = 0; // DEBUG

  printf("@@@ %d LOG System running...\n",_pid);

  loop:
  taskid = 1;
  liveSeen = false;

  clk!1; 
  clk?0; // Wait for Clock to Tick

  //printf("@@@ %d LOG Loop through tasks...\n",_pid);

  do   // while taskid < TASK_MAX ....
  ::  taskid == TASK_MAX -> break;
  ::  else ->
      //atomic {
        //printf("@@@ %d LOG Task %d state is ",_pid,taskid);
        //printm(tasks[taskid].state); nl()
      //}
      if
      :: tasks[taskid].state == Zombie -> taskid++
      :: else ->
         if
         ::  tasks[taskid].state == OtherWait
             -> tasks[taskid].state = Ready
                //printf("@@@ %d STATE %d Ready\n",_pid,taskid)
         ::  else -> skip
         fi
         liveSeen = true;
         taskid++
      fi
  od

  //printf("@@@ %d LOG ...all visited, live:%d\n",_pid,liveSeen);

  // Semaphore Check sub-process: 
  byte sema_id = 0;
  byte wait_tid;
  do
  ::  sema_id < SEMA_MAX -> 
        if
        ::  sema_ready?sema_id -> 
              do
              ::  sema_wait[sema_id]?wait_tid ->
                    //printf("LOG : Task %d Ready now Sema is Free.\n", wait_tid);
                    tasks[wait_tid].state = Ready;
                    break;
              ::  timeout -> break;
              od
        ::  else
        fi
        sema_id=sema_id+1;
  ::  else -> break;
  od
  
  byte schedID = 0;
  do
  ::  tasks[taskQueue[schedID]].state == Ready ->
        // Choose Highest Priority Task that is in the state: Ready
        //printf("LOG : Scheduling Task %d to Run\n", taskQueue[schedID]);
        sched[taskQueue[schedID]]!0; // Signal Task to Run.
        taskSignal?0; // Wait for signal from running task.
        break;
  ::  else -> schedID = schedID+1; 
        if
        ::  schedID == TASK_MAX -> break;
        ::  else
        fi
  od

  if
  ::  liveSeen -> goto loop
  ::  else
  fi
  printf("@@@ %d LOG All are Zombies, game over.\n",_pid);
  stopclock = true;
  clk?0;           // Wait for Clock Tick
  clk!1;
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
      atomic {

        clk!0;
        clk?1;

        printf(" (tick) \n");
        tid = 1;
        do
        ::  tid == TASK_MAX -> break
        ::  else ->
            //atomic{printf("Clock: tid=%d, state=",tid); printm(tasks[tid].state); nl()};

              if
              ::  tasks[tid].state == TimeWait || tasks[tid].state == TimeBlocked ->
                  tix = tasks[tid].ticks - 1;
                  //printf("Clock: ticks=%d, tix=%d\n",tasks[tid].ticks,tix);
                  if
                  ::  tix <= 0
                      tasks[tid].tout = true
                      if 
                      ::  tasks[tid].state == TimeWait ->
                            tasks[tid].state = Ready;
                      ::  tasks[tid].state == TimeBlocked ->
                            tasks[tid].state = Blocked;
                      fi
                      //printf("@@@ %d STATE %d Ready\n",_pid,tid)
                  ::  else
                      tasks[tid].ticks = tix
                  fi
              ::  else // state != TimeWait
              fi
            tid = tid + 1
        od
      }
  od
stopped:
  printf("@@@ %d LOG Clock Stopped\n",_pid);
}



/*
 *  Simple Binary Semaphores for Test Synchronisation
 *
 *  need text here to explain usage
 */

 /*
 * Synchronisation Mechanisms
 *  TestSyncObtain(sem_id)   - call that waits to obtain semaphore `sem_id`
 *  TestSyncRelease(sem_id)  - call that releases semaphore `sem_id`
 *  TestSyncReleased(sem_id) - simulates ecosystem behaviour releases `sem_id`
 *
 * Binary semaphores:  True means available, False means in use.
 */

bool test_sync_sema[SEMA_MAX]; // Semaphore

inline TestSyncObtain(sem_id){
  atomic{
    printf("@@@ %d WAIT %d\n",_pid,sem_id);
    test_sync_sema[sem_id] ;        // wait until available
    test_sync_sema[sem_id] = false; // set as in use
    printf("@@@ %d LOG WAIT %d Over\n",_pid,sem_id);
  }
}

inline TestSyncRelease(sem_id){
  atomic{
    printf("@@@ %d SIGNAL %d\n",_pid,sem_id);
    test_sync_sema[sem_id] = true ; // release
  }
}

inline TestSyncReleased(sem_id)
{
  test_sync_sema[sem_id] = true ;
}

