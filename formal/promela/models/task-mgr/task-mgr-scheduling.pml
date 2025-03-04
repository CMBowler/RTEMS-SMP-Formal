#define TIMESLICE_MAX  2

// State a task should enter once chosen by a scheduler.
mtype { Executing }; 

// Signals task has finished step of execution
chan taskSignal[NUM_PROC] = [1] of {byte};

// Signal task to execute
chan schedSignal[TASK_MAX] = [NUM_PROC] of {byte};

proctype MultiSchedulerInit() {
  /* 
  Initialise all instances of the scheduler
  and its associated Task Priority Queue
  */
  byte schedId = 0;
  atomic {
    do
    ::  schedId == NUM_PROC -> break;
    ::  else -> 
          schedList[schedId].sID = schedId;
          run Scheduler(schedId);
          schedId++
    od
  }

}

/*
  Scheduler Model
*/
proctype Scheduler(byte schedID) {
    byte taskid, tix;
    byte prevRanTask, TimeSliceCounter;
    bool liveSeen;

    byte maxCount = 0; // DEBUG

    printf("@@@ %d LOG System running...\n",_pid);

    loop:

    liveSeen = false;
    prevRanTask = 0;
    TimeSliceCounter = 0;

    //printf("@@@ %d LOG Loop through tasks...\n",_pid);

    /* 
      Check for any Semaphores
      that have been released and
      have tasks waiting to obtain
    */

    byte semaId = 0;
    byte tid = 0;

    atomic {
      do
      ::  semaId == SEMA_MAX -> break;
      ::  else ->
            if 
            ::  semaList[semaId].free ->
                  if
                  ::  semaList[semaId].Queue[0] != 0 ->
                        semaList[semaId].free = false;
                        popQueue(
                          semaList[semaId],
                          TASK_MAX,
                          tid
                        );
                        tasks[tid].SemaBlock = false;
                        // Set task state to Ready if no other Block
                        if
                        ::  tasks[tid].TimeBlock == false && 
                            tasks[tid].SuspBlock == false -> 
                              tasks[tid].state = Ready;
                        :: else
                        fi
                  ::  else
                  fi
            ::  else
            fi
            semaId++
      od
    }

    /* Select Task to Run */

    byte queueID = 0;

    byte taskId;

    atomic {
      do
      ::  queueID == TASK_MAX -> break;
      ::  else -> 
            // Get new Task ID from Queue
            taskId = schedList[schedID].taskQueue[queueID];
            if
            ::  tasks[taskId].state == Ready ->
                  /* 
                    Choose Highest Priority Task that
                    is in the state: Ready 
                  */

                  //printf("LOG : Scheduling Task %d to Run\n", taskQueue[queueID]);

                  /* Time Slicing */

                  if
                  ::	taskId == prevRanTask &&
                      tasks[taskId].timeslicing ->
                        TimeSliceCounter = TimeSliceCounter + 1;
                        if
                        ::	TimeSliceCounter == TIMESLICE_MAX ->
                              /* 	
                                - Reset Timeslice Timer.
                                - Put Task at the back
                                  of its priority group.
                              */
                              TimeSliceCounter = 0;
                              updateSchedQ(
                                tasks[taskId], 
                                schedID
                              );
                        ::	else
                        fi
                  ::	else ->
                        TimeSliceCounter = 0;
                        prevRanTask = taskId;
                  fi
                  
                  // Set Chosen Task State to 'Executing'.
                  tasks[taskId].state = Executing;
                  // Signal Task to Run.
                  schedSignal[taskId]!schedID; 
                  // Wait for signal from running task.
                  taskSignal[schedID]?0; 
                  // Return Chosen Task State to 'Ready', if
                  // state hasnt been changed in execution.
                  if
                  ::  tasks[taskId].state == Executing ->
                        tasks[taskId].state = Ready;
                  ::  else
                  fi

                  break;
            ::  else -> queueID++
            fi
      od
    }

    /* Clock */

    taskId = 1;

    atomic {
      do
      ::  taskId == TASK_MAX -> break;
      ::  else ->
          //atomic {
              //printf("@@@ %d LOG Task %d state is ",_pid,taskid);
              //printm(tasks[taskid].state); nl()
          //}
          if
          ::  tasks[taskId].state == Zombie -> taskId++
          :: else ->
              if
              ::  tasks[taskId].state == OtherWait -> 
                      tasks[taskId].state = Ready
                      //printf("@@@ %d STATE %d Ready\n",_pid,taskid)
              ::  tasks[taskId].TimeBlock ->
                      tix = tasks[taskId].ticks - 1;
                      //printf("Clock: ticks=%d, tix=%d\n",tasks[tid].ticks,tix);
                      if
                      ::  tix <= 0
                          tasks[taskId].TimeBlock = false;
                          // If Task is not blocked by any other 
                          // mechanism, set the state to 'Ready'.
                          if 
                          ::  tasks[taskId].SemaBlock == false &&
                              tasks[taskId].SuspBlock == false -> 
                                tasks[taskId].state = Ready;
                          ::  else
                          fi
                          //printf("@@@ %d STATE %d Ready\n",_pid,tid)
                      ::  else
                          tasks[taskId].ticks = tix
                      fi
              ::  else -> skip
              fi
              liveSeen = true;
              taskId++
          fi
      od
    }

    printf(" (tick) \n");

    if
    ::  liveSeen && maxCount < 50 -> maxCount++; goto loop
    ::  else
    fi
    printf("@@@ %d LOG All are Zombies, game over.\n",_pid);
    printf("@@@ %d LOG Clock Stopped\n",_pid);
}
