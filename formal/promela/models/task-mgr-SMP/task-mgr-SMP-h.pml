// SMP Helper Functions

inline clearSuspends(myId, schedId) {
    byte taskID = 2;
    do
    ::  taskID == TASK_MAX -> break;
    ::  else -> 
          task_isSuspend(tasks[taskID], rc);
          if
          ::  rc == RC_AlrSuspd ->
                printf("@@@ %d CALL task_resume %d resumeRC\n", 
                        _pid, taskID);
                task_resume(myId, schedId, tasks[taskID], rc);
                printf("@@@ %d SCALAR resumeRC %d\n",_pid,rc);
          ::  else
          fi
          taskID++;
    od
}

inline selectId(tid) {
  tid = INVALID_ID;
  if
  ::  tid = TASK0_ID;
  ::  tid = TASK1_ID;
  ::  tid = TASK2_ID;
  ::  tid = TASK3_ID;
  fi
}

inline selectPrio(prio) {
  prio = MAX_PRIO;
  if
  ::  prio = LOW_PRIO;
  //::  prio = MED_PRIO;
  ::  prio = HIGH_PRIO;
  fi
}

inline selectTime(time) {
  time = 1;
  if
  ::  time = PROC_YIELD;
  ::  time = 10;
  fi
}

inline selectSched(sId) {
  sId = INVALID_SCHED;
  if
  ::  sId = 0;
  ::  sId = 1;
  ::  sId = 2;
  ::  sId = 3;
  fi
}

mtype {
  suspend, 
  resume, 
  setPrio, 
  wakeAfter, 
  setSched
}

inline selectOp(schedId, tid, prio, ticks, schId, rc) {
  mtype operation
  if
  //::  operation = suspend;
  //::  operation = resume;
  ::  operation = setPrio;
  ::  operation = wakeAfter;
  //::  operation = setSched;
  fi

  if
  ::  operation == suspend ->
        selectId(tid);
        printf("@@@ %d CALL task_suspend %d suspendRC\n", 
                _pid, tid);
        task_suspend(myId, schedId, tasks[tid], rc);
        printf("@@@ %d SCALAR suspendRC %d\n",_pid,rc)
  ::  operation == resume ->
        selectId(tid);
        printf("@@@ %d CALL task_resume %d resumeRC\n", 
                _pid, tid);
        task_resume(myId, schedId, tasks[tid], rc);
        printf("@@@ %d SCALAR resumeRC %d\n",_pid,rc)
  ::  operation == setPrio ->
        selectId(tid);
        selectPrio(prio);
        printf("@@@ %d CALL task_setPriority %d %d %d setPriorityRC\n", 
              _pid, tid, prio, old_prio);
        task_setPrio(myId, schedId, tasks[tid], prio, old_prio, rc);
        printf("@@@ %d CALL oldPrio %d\n",_pid, old_prio);
        printf("@@@ %d SCALAR setPriorityRC %d\n",_pid,rc)
  ::  operation == wakeAfter ->
        selectTime(ticks)
        printf("@@@ %d CALL task_wakeAfter %d %d wakeAfterRC\n", 
                _pid, myId, ticks);
        task_wakeAfter(schedId, tasks[myId], ticks, rc);
        printf("@@@ %d SCALAR wakeAfterRC %d\n",_pid, rc)
  ::  operation == setSched ->
        selectId(tid);
        selectSched(schId);
        selectPrio(prio);
        printf("@@@ %d CALL task_setScheduler %d %d %d setSchedRC\n", 
                _pid, tid, schId, prio);
        task_setScheduler(myId, schedId, tasks[tid], schId, prio, rc);
        printf("@@@ %d SCALAR setSchedRC %d\n",_pid,rc);
  fi
}
