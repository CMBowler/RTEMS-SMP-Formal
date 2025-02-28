#define TIMESLICE_MAX  2

// Signals task has finished step of execution
chan taskSignal = [1] of {byte};

// Signal task to execute
chan sched[(TASK_MAX)] = [1] of {byte};

// Signal for Semaphore Release
chan sema_signal[SEMA_MAX] = [TASK_MAX] of {byte};

chan sema_wait[SEMA_MAX] = [TASK_MAX] of {byte};

chan sema_ready = [SEMA_MAX] of {byte};

byte taskQueue[TASK_MAX];

/*
 * We need a process that periodically wakes up blocked processes.
 * This is modelling background behaviour of the system,
 * such as ISRs and scheduling.
 * We visit all tasks in round-robin order (to prevent starvation)
 * and make them ready if waiting on "other" things.
 * Tasks waiting for events or timeouts are not touched
 * This terminates when all tasks are zombies.
 */
proctype Scheduler () {
    byte taskid, schedID, tix;
    bool liveSeen;

    byte maxCount = 0; // DEBUG

    printf("@@@ %d LOG System running...\n",_pid);

    loop:
    taskid = 1;
    schedID = 0;
    liveSeen = false;
    prevRanTask = 0;
    TimeSliceCounter = 0;

    //printf("@@@ %d LOG Loop through tasks...\n",_pid);

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
    
    do
    ::  tasks[taskQueue[schedID]].state == Ready ->
            /* Choose Highest Priority Task that is in the state: Ready */
            //printf("LOG : Scheduling Task %d to Run\n", taskQueue[schedID]);

						/* Time Slicing */
						if
						::	taskQueue[schedID] == prevRanTask ->
									TimeSliceCounter = TimeSliceCounter + 1;
									if
									::	TimeSliceCounter == TIMESLICE_MAX ->
												/* 	
													- Reset Timeslice Timer.
													- Put Task at the back
														of its priority group.
												*/
												TimeSliceCounter = 0;
												updateSchedQ(taskQueue[schedID]);
									::	else
									fi
						::	else ->
									TimeSliceCounter = 0;
									prevRanTask = taskQueue[schedID];
						fi

            sched[taskQueue[schedID]]!0; // Signal Task to Run.
            taskSignal?0; // Wait for signal from running task.
            break;
    ::  else -> schedID = schedID+1; 
            if
            ::  schedID == TASK_MAX -> break;
            ::  else
            fi
    od

    do   // while taskid < TASK_MAX ....
    ::  taskid == TASK_MAX -> break;
    ::  else ->
        //atomic {
            //printf("@@@ %d LOG Task %d state is ",_pid,taskid);
            //printm(tasks[taskid].state); nl()
        //}
        if
        ::  tasks[taskid].state == Zombie -> taskid++
        :: else ->
            if
            ::  tasks[taskid].state == OtherWait -> 
                    tasks[taskid].state = Ready
                    //printf("@@@ %d STATE %d Ready\n",_pid,taskid)
            ::  tasks[taskid].state == TimeWait || tasks[taskid].state == TimeBlocked ->
                    tix = tasks[taskid].ticks - 1;
                    //printf("Clock: ticks=%d, tix=%d\n",tasks[tid].ticks,tix);
                    if
                    ::  tix <= 0
                        tasks[taskid].tout = true
                        if 
                        ::  tasks[taskid].state == TimeWait ->
                            tasks[taskid].state = Ready;
                        ::  tasks[taskid].state == TimeBlocked ->
                            tasks[taskid].state = Blocked;
                        fi
                        //printf("@@@ %d STATE %d Ready\n",_pid,tid)
                    ::  else
                        tasks[taskid].ticks = tix
                    fi
            ::  else -> skip
            fi
            liveSeen = true;
            taskid++
        fi
    od

    //printf("@@@ %d LOG ...all visited, live:%d\n",_pid,liveSeen);

    printf(" (tick) \n");

    if
    ::  liveSeen -> goto loop
    ::  else
    fi
    printf("@@@ %d LOG All are Zombies, game over.\n",_pid);
    printf("@@@ %d LOG Clock Stopped\n",_pid);
}
