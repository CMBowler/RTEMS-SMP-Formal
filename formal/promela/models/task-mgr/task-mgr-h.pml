
// We use two semaphores to synchronise the tasks
#define INVALID_ENTRY       (0)
#define SEMA_LOCK           (1)
#define SEMA_TASK0_FIN      (2)
#define SEMA_TASK1_FIN   	  (3)
#define SEMA_TASK2_FIN   	  (4)
#define SEMA_TASK3_FIN   	  (5)

/*
 * We need to output annotations for any #define we use.
 * It is simplest to keep them all together,
 * and use an inline to output them.
 */

#define MAX_PRIO        255
#define BAD_PRIO        MAX_PRIO
#define CURRENT_PRIO    0
#define LOW_PRIO        10
#define MED_PRIO        5
#define HIGH_PRIO       1
#define ISR_PRIO        11

#define INVALID_ID      0
#define RUNNER_ID       1
#define TASK0_ID        2
#define TASK1_ID        3
#define TASK2_ID        4
#define TASK3_ID        5

#define CLEAR_TASKS     255

#define PROC_YIELD      0

byte task_control = CLEAR_TASKS;

byte globalCounter = 0;

// Semaphore Queue & List of Queues

typedef semaQueue {
  byte id;
  bool free = true;
  byte Queue[TASK_MAX];
}

semaQueue semaList[SEMA_MAX];

// SMP

byte taskQueue[TASK_MAX];

typedef TaskPriorityQueue {
  byte sID;
  byte taskQueue[TASK_MAX];
}

TaskPriorityQueue schedList[NUM_PROC];

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

inline outputDeclarations () {
    printf("@@@ %d DECL byte createRC 0\n",_pid);
    printf("@@@ %d DECL byte startRC 0\n",_pid);
    printf("@@@ %d DECL byte deleteRC 0\n",_pid);
    printf("@@@ %d DECL byte suspendRC 0\n",_pid);
    printf("@@@ %d DECL byte isSuspendRC 0\n",_pid);
    printf("@@@ %d DECL byte resumeRC 0\n",_pid);
    printf("@@@ %d DECL byte setPriorityRC 0\n",_pid);
    printf("@@@ %d DECL byte wakeAfterRC 0\n", _pid);
    // Rather than refine an entire Task array, we refine array 'slices'
    //printf("@@@ %d DCLARRAY EvtSet pending TASK_MAX\n",_pid);
    //printf("@@@ %d DCLARRAY byte recout TASK_MAX\n",_pid);
    printf("@@@ %d DECL byte globalCounter 0\n", _pid);
    printf("@@@ %d DCLARRAY byte taskID TASK_MAX\n", _pid);
    printf("@@@ %d DCLARRAY Task tasks TASK_MAX\n",_pid);
    printf("@@@ %d DCLARRAY Semaphore semaphore SEMA_MAX\n",_pid);
}

typedef Mode {
    bool preempt;
    bool timeslice;
    bool ASR;
    int isr_lvl;
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
    // Allocate the lowest available task ID
    // to the newly created task.
    atomic {
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
        ::  raw_tid == 32 ->
                tid = 5;
    /*   
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
}

inline removeTask(taskID, rc) {
    byte raw_tid = 1 << taskID;
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

inline insertQueue(obj, size, taskID) {
  /*
    Insert a value into 
    a Queue.
  */
  byte index = 0;
  do
  ::  index == size -> 
    	  printf("Debug : Queue is Full!\n"); break;
  ::  else -> 
        if
        ::  obj.Queue[index] == 0 ->
              obj.Queue[index] = taskID;
              break;
        :: else -> index++
        fi
  od
}

inline popQueue(obj, size, taskID) {
  taskID = obj.Queue[0];
  /* 
    Move all entries in the
    queue up one position.
  */
  byte index = 0;
  do
  ::  index == (size-1) -> break;
  ::  else ->
        obj.Queue[index] = obj.Queue[index+1];
        index++
  od
}

inline isHoldingMutex(task) {
    /*
    If a given task is holding any bin semaphores
    which use a locking protocol: 
    return true, else false
    */
    atomic {
      task.HoldingMutex = false;
      byte mutID = 0;
      do
      ::  mutID < SEMA_MAX ->
            if
            ::  task.mutexs[mutID] == 1 ->
                  task.HoldingMutex = true;
                  break;
            ::  else -> mutID++
            fi
      ::  else -> break;
      od
    }
}

inline schedSync(taskId, schedId) {
    taskSignal[schedId]!0;
    schedSignal[taskId]?schedId;
}

inline UpdateCount() {
    atomic {
        printf("@@@ %d CALL updateCounter %d\n", _pid, globalCounter);
        globalCounter++
    }
}

inline ObtainSema(task, sid) {
  atomic {
    printf("@@@ %d WAIT %d\n",_pid,sid);
    if
    ::  semaList[sid].free == true ->
            semaList[sid].free = false;
    ::  else ->
            insertQueue(
              semaList[sid],
              TASK_MAX,
              task.tid
            )
            // Store preblocked state if required
            // and add SemaBlock state
            if
            ::  task.state != Blocked -> // Executing/Ready/Dormant
                  if
                  ::  task.state == Executing -> // Self suspend
                        task.preBlockState = Ready;
                  ::  else ->
                        task.preBlockState = task.state;
                  fi
                  task.state = Blocked;
            ::  else
            fi
            task.SemaBlock = true; 
    fi
  }
  schedSync(task.tid, task.homeSched);
  printf("@@@ %d LOG WAIT %d Over\n",_pid,sid);
}

inline ReleaseSema(task, sid) {
  atomic {
    printf("@@@ %d SIGNAL %d\n",_pid,sid);
    semaList[sid].free = true;
  }
  //schedSync(task.tid, task.homeSched);
}

inline ObtainMutex(task, sid) {
  atomic {
    ObtainSema(task, sid)
    task.mutexs[sid] = 1;
    task.HoldingMutex = true;
  }
}

inline ReleaseMutex(task, sid) { 
  bool rc; // TODO 
  atomic {
    if
    ::  task.mutexs[sid] == 1 ->
          task.mutexs[sid] = 0;
          isHoldingMutex(task);
          // If no Longer Holding a Mutex -> Allow Prio to Lower
          if
          ::  task.HoldingMutex == false && 
              task.inheritedPrio != 0 -> 
                  if
                  ::  task.preemptable ->
                        updateSchedQ(task, task.homeSched);
                  ::  else
                  fi
                  task.inheritedPrio = 0;
          :: else
          fi
          ReleaseSema(task, sid);
    ::  else -> rc = false
    fi
  }
  schedSync(task.tid, task.homeSched);
}

inline insertSchedQ(newTask, sid) {
  byte i=0;
  byte insertIndex;

  do
  ::  schedList[sid].taskQueue[i] == 0 || 
      tasks[schedList[sid].taskQueue[i]].prio > newTask.prio ->
        insertIndex = i;
        i = TASK_MAX-2;           
        do
        ::  i == insertIndex -> break;
        ::  else ->
              schedList[sid].taskQueue[i] = schedList[sid].taskQueue[i-1];
              i--;
        od
        schedList[sid].taskQueue[i] = newTask.tid;
        break;
  ::  else -> 
        i++; 
        if 
        ::  i == TASK_MAX -> break;
        ::  else -> skip;
        fi
  od

  /* Debug : print schedQ
  i = 0;
  printf(" LOG : Updated Task Queue %d: ", sid);
  do
  ::  i == TASK_MAX -> break;
  ::  else ->     
        printf("%d ", schedList[sid].taskQueue[i]);
        i=i+1;
  od
  nl();
  //*/
}

inline removeSchedQ(task, sid) {
  byte i=0;
  // Remove task from relevant Scheduler Queue
  do
  ::  schedList[sid].taskQueue[i] == task.tid ->
        do
        ::  i == TASK_MAX-2 -> break;
        ::  else ->
              schedList[sid].taskQueue[i] = schedList[sid].taskQueue[i+1];
              i++;
        od
  ::  else -> 
        i++;
        if 
        ::  i == TASK_MAX -> break;
        ::  else
        fi
  od

  /* Debug : print schedQ
  i = 0;
  printf(" LOG : Updated Task Queue %d: ", sid);
  do
  ::  i == TASK_MAX -> break;
  ::  else ->     
        printf("%d ", schedList[sid].taskQueue[i]);
        i=i+1;
  od
  nl();
  //*/
}

inline updateSchedQ(task, schedId) {
  removeSchedQ(task, schedId);
  insertSchedQ(task, schedId);
}

inline SuspendResume(myId, schedId, tid) {
    bool repeated = false;

    if
    ::  suspValId == true ->
            suspendId = tid;
    ::  else // Set to 0
    fi
    if
    ::  resumeValId == true ->
            resumeId = tid;
    ::  else ->
            resumeId = myId; // Should be Invalid
    fi

suspRepeat:
    // Suspend
    printf("@@@ %d CALL task_suspend %d suspendRC\n",
                _pid, suspendId, suspendRC);
    task_suspend(myId, schedId, tasks[suspendId], suspendRC);
    printf("@@@ %d SCALAR suspendRC %d\n",_pid,suspendRC);

    // Scenario: Already Suspended
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
    task_resume(myId, schedId, tasks[resumeId], resumeRC);
    printf("@@@ %d SCALAR resumeRC %d\n",_pid,resumeRC);

    if 
    ::  resumeValId == false ->
            // Resume Process properly so It can terminate
            printf("@@@ %d CALL task_resume %d resumeRC\n", 
                        _pid, tid, resumeRC);
            task_resume(myId, schedId, tasks[tid], resumeRC);
            printf("@@@ %d SCALAR resumeRC %d\n",_pid,resumeRC)
    ::  else
    fi
}

inline changePriority (callerId, schedId, taskid, prio, oldPrio, rc) {
    // Change the Priority of the given task
    // If prio = 0 -> returns current Priority with no update.
    printf("@@@ %d CALL task_setPriority %d %d %d setPriorityRC\n", 
                            _pid, taskid, prio, old_prio, rc);
    task_setPrio(callerId, schedId, tasks[taskid], prio, old_prio, rc);
    printf("@@@ %d SCALAR setPriorityRC %d\n",_pid,rc);
}

inline changeCheckPriority (callerId, schedId, taskid, prio, oldPrio, rc) {
    // Change the Priority of the given task
    // If prio = 0 -> returns current Priority with no update.
    printf("@@@ %d CALL task_setPriority %d %d %d setPriorityRC\n", 
                            _pid, taskid, prio, old_prio, rc);
    task_setPrio(callerId, schedId, tasks[taskid], prio, old_prio, rc);
    printf("@@@ %d CALL oldPrio %d\n",_pid, old_prio);
    printf("@@@ %d SCALAR setPriorityRC %d\n",_pid,rc);
}