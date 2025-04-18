/*
 SMP Helper Functions
*/

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
  ::  prio = MED_PRIO;
  ::  prio = HIGH_PRIO;
  fi
}

inline selectTime(time) {
  time = 1;
  if
  ::  time = PROC_YIELD;
  ::  time = 5;
  fi
}

inline selectSched(sId) {
  sId = INVALID_SCHED;
  if
  ::  sId = 0;
  ::  sId = 1;
  fi
}

mtype {
  suspRes, 
  setPrio, 
  wakeAfter, 
  setSched
}

inline selectOp(schedId, tid, prio, ticks, schId, rc) {
  mtype operation
  if
  ::  myId == 2 -> operation = suspRes;
  ::  myId == 3 -> operation = setPrio;
  ::  myId == 4 -> operation = wakeAfter;
  ::  myId == 5 -> operation = setSched;
  ::  else
  fi

  if
  ::  operation == suspRes ->
        // suspend
        selectId(tid);
        printf("@@@ %d CALL task_suspend %d suspendRC\n", 
                _pid, tid);
        task_suspend(myId, schedId, tasks[tid], rc);
        printf("@@@ %d SCALAR suspendRC %d\n",_pid,rc);
        // yeild
        printf("@@@ %d CALL task_wakeAfter %d %d wakeAfterRC\n", 
                _pid, myId, PROC_YIELD);
        // resume
        task_wakeAfter(schedId, tasks[myId], PROC_YIELD, rc);
        printf("@@@ %d CALL task_resume %d resumeRC\n", 
                _pid, tid);
        task_resume(myId, schedId, tasks[tid], rc);
        printf("@@@ %d SCALAR resumeRC %d\n",_pid,rc)
  ::  operation == setPrio ->
        selectId(tid);
        selectPrio(prio);
        byte old_prio = 1;
        printf("@@@ %d DECL byte priority 0\n",_pid);

        printf("@@@ %d CALL task_setPriority %d %d %d setPriorityRC\n", 
               _pid, tid, prio, old_prio);
        task_setPrio(myId, schedId, tasks[tid], prio, old_prio, rc);
        printf("@@@ %d CALL oldPrio %d\n",_pid, old_prio);
        printf("@@@ %d SCALAR setPriorityRC %d\n",_pid,rc);

        printf("@@@ %d CALL task_getPriority %d %d %d getPriorityRC\n", 
               _pid, tid, tasks[tid].homeSched, prio, old_prio);
        task_getPrio(tasks[tid], tasks[tid].homeSched, old_prio, rc);
        printf("@@@ %d SCALAR getPriorityRC %d\n",_pid,rc)
        printf("@@@ %d CALL oldPrio %d\n",_pid, old_prio);
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

        byte currScheduler=1;
        printf("@@@ %d DECL byte schedId 0\n",_pid);

        printf("@@@ %d CALL task_setScheduler %d %d %d setSchedulerRC\n", 
                _pid, tid, schId, prio);
        task_setScheduler(myId, schedId, tasks[tid], schId, prio, rc);
        printf("@@@ %d SCALAR setSchedulerRC %d\n",_pid,rc);

        printf("@@@ %d CALL task_getScheduler %d %d getSchedulerRC\n", 
                _pid, tid, currScheduler);
        task_getScheduler(tasks[tid], currScheduler, rc);
        printf("@@@ %d SCALAR getSchedulerRC %d\n",_pid,rc);
        printf("@@@ %d CALL schedId %d\n",_pid, currScheduler);

  fi
}
