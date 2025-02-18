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
#define SEMA_MAX 6
#define SCHED_MAX 1
#include "../common/model.pml"

//#include "debug.pml"
//Uncomment if no debug:
#include "task-mgr-h.pml"
#include "task-mgr-API.pml"
#include "task-mgr-scheduling.pml"

byte sendrc;            // Sender global variable
byte recrc;             // Receiver global variable
byte recout[TASK_MAX] ; // models receive 'out' location.

// Create global variables for scenarios

// Model return status
byte createRC;
byte startRC;
byte deleteRC;
byte suspendRC;
byte isSuspendRC;
byte resumeRC;
byte wakeAfterRC;

// Task Create
bool task_0_name;
byte tsk0_id;
byte createPrio;
bool createValId;

bool createTask;

// Task Start
byte taskEntry;
bool startValId;
bool startValEntry;
bool doubleStart;
bool failStart;

bool startTask0;
bool startTask1;

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
bool raiseWithMutex;

// Wake After

bool resumeSleep;
int sleepTime;

bool sleepTask;

// Task Mode
bool task_0_preempt;
bool task_1_preempt;

//bool preempt;

// Declare Scenario Types
mtype = {CreateDestroy, TaskStart, SuspResume, ChangePrio, TaskSleep, Debug}

inline chooseScenario() {

    // Defaults
    task_control = 28;	// 0001 1100 Task[1] reserved for runner.
    
    // Initialise scenario variables.

    // Task Create
    createTask = true;
    task_0_name = 1;
	createPrio = MED_PRIO;
	createValId = true;

    // Start Task
	startValId = true;
    startValEntry = true;
	doubleStart = false;
	taskEntry = SEMA_TASK_START_0;

    startTask0 = true;
    startTask1 = false; 

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
    raiseWithMutex = false;

    // Wake After
    resumeSleep = false;
    sleepTime = 10;

    // Task Mode 
    task_0_preempt = true;
    task_1_preempt = true;

    // Set runner task state to Ready
    // as this task is active from the start of all scenarios.
    printf("@@@ %d Initialising Runner\n",_pid);
    tasks[RUNNER_ID].tid = RUNNER_ID;
    tasks[RUNNER_ID].state = Ready;
    tasks[RUNNER_ID].prio = MED_PRIO;
    insertSchedQ(tasks[RUNNER_ID]);

    if
    ::  scenario = CreateDestroy;
    ::  scenario = TaskStart;
    ::  scenario = SuspResume;
    ::  scenario = ChangePrio;
    ::  scenario = TaskSleep;
    //::  scenario = Debug;
    fi

    atomic{printf("@@@ %d LOG scenario ",_pid); printm(scenario); nl()} ;

    // Create/Delete
    if
    ::  scenario == CreateDestroy ->
            startTask0 = false; 
            deleteTask = false;
            // Create/Delete
            if
            ::  task_0_name = 0;                        atomic{printf("@@@ %d LOG Create: Invalid Name ",_pid); nl()};
            ::  createPrio = 0;                         atomic{printf("@@@ %d LOG Create: Invalid Priority (0) ",_pid); nl()};
            ::  createPrio = MAX_PRIO;                  atomic{printf("@@@ %d LOG Create: Invalid Priority (MAX) ",_pid); nl()};
            ::  createValId = false;                    atomic{printf("@@@ %d LOG Create: Invalid Id ",_pid); nl()};
    //TODO  ::  scenario = TooMany;
            ::  createTask = false; deleteTask = true;  atomic{printf("@@@ %d LOG Delete: Invalid Id ",_pid); nl()};
            ::  deleteTask = true;                      atomic{printf("@@@ %d LOG Create: Success ",_pid); nl()};
            fi
    ::  scenario == TaskStart ->
            startTask0 = false;
            failStart = true;
            // Start
            if
            ::  startValId = false;                     atomic{printf("@@@ %d LOG Start: Invalid Id ",_pid); nl()};
            ::  startValEntry = false;                  atomic{printf("@@@ %d LOG Start: Invalid Entry ",_pid); nl()};
            ::  doubleStart = true; startTask0 = true;  atomic{printf("@@@ %d LOG Start: Task Already Started ",_pid); nl()};
            ::  startTask0 = true; failStart = false;   atomic{printf("@@@ %d LOG Start: Success ",_pid); nl()};
            fi
    ::  scenario == SuspResume ->
            suspendTask = true;
            // Suspend
            if
            ::  startValEntry = false; startTask0 = false;  atomic{printf("@@@ %d LOG Start: Invalid State for Suspend",_pid); nl()};
            ::  suspValId = false;                          atomic{printf("@@@ %d LOG Start: Invalid Suspend Id ",_pid); nl()};
            ::  resumeValId = false;                        atomic{printf("@@@ %d LOG Start: Invalid Resume Id ",_pid); nl()};
            ::  doubleSuspend = true;                       atomic{printf("@@@ %d LOG Start: Already Suspended ",_pid); nl()};
            ::  suspendSelf = true; suspendTask = false;    atomic{printf("@@@ %d LOG Start: Self Suspend ",_pid); nl()};
            ::  skip;                                       atomic{printf("@@@ %d LOG Start: Suspend/Resume ",_pid); nl()};
            fi
    ::  scenario == ChangePrio ->
            // Set Priority
            startTask1 = true;
            testPrio = true;
            if
            ::  suspendSelf = true;         atomic{printf("@@@ %d LOG Start: Lower Priority, SuspendSelf",_pid); nl()};
            ::  raiseWithMutex = true;      atomic{printf("@@@ %d LOG Start: Lower Priority while holding lock",_pid); nl()};
            ::  skip;                       atomic{printf("@@@ %d LOG Start: Lower Task0, Raise Task1",_pid); nl()};
            fi

            if
            ::  task_0_preempt = false;     atomic{printf("@@@ %d LOG Start: No Preemption: Task 0",_pid); nl()};
            ::  skip;
            fi
    ::  scenario == TaskSleep ->
            // Task Wake After
            sleepTask = true;
            if
            ::  resumeSleep = true; startTask1 = true;      atomic{printf("@@@ %d LOG Start: Attempt Resume during Sleep",_pid); nl()};
            ::  skip;                                       atomic{printf("@@@ %d LOG Start: Sleep Task",_pid); nl()};
            fi
    ::  else // Debug
    fi
}

proctype Runner(byte nid, myId) {

    tasks[RUNNER_ID].pmlid = _pid;

    sched[myId]?0;
    //assert(_priority == MED_PRIO)
    // Set Runner Task Priority to Medium in the C test code:
    byte old_prio = 1;
    byte setPriorityRC;
    printf("@@@ %d DECL byte priority 0\n",_pid);
    printf("@@@ %d CALL taskSelf_setPriority %d %d setPriorityRC\n", 
                            _pid, MED_PRIO, old_prio, setPriorityRC);

    /*
    if
    :: multicore ->
        // printf("@@@ %d CALL RunnerScheduler %d\n", _pid, rcvCore);
        printf("@@@ %d CALL SetProcessor %d\n", _pid, rcvCore);
    :: else
    fi
    */

	// Task 0 Create Params
	byte name = task_0_name;
    byte prio = createPrio;
    byte preempt = task_0_preempt;
	byte mode = 0;
	byte attr = 0;
	bool setRC;
	
	// Task 0 Start Params 
	byte entry = taskEntry;
	bool doubleDone = false;
	byte startId;
	//byte args = 0;

    // Procedure for Creating Task0
    if 
    ::  createTask == true ->
        
            if
            ::	createValId == true ->
                    setTask(tsk0_id, setRC);
                    if 
                    ::	setRC == false ->
                            printf("@@@ %d CALL TooMany\n", _pid);
                    :: 	else
                    fi
            ::	else ->
                    tsk0_id = 0;
                    setRC = true;
            fi

		printf("@@@ %d CALL task_create %d %d %d %d %d createRC\n", 
				_pid, name, prio, preempt, attr, tsk0_id);

        task_create(tasks[tsk0_id], tsk0_id, name, prio, preempt, setRC, createRC);
		
		printf("@@@ %d SCALAR createRC %d\n", _pid, createRC);
    ::  else
    fi

    if 
    ::  startTask0 || failStart -> 
            // Procedure for Starting Task0
            if
            ::	startValId == true ->
                    startId = tsk0_id;
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
            printf("@@@ %d CALL task_start %d %d startRC\n", 
                    _pid, startId, entry);
            task_start(myId, tasks[startId], entry, startRC);
            printf("@@@ %d CALL startRC %d\n", _pid, startRC);

            if
            :: 	doubleStart == true ->
                // Scenario: Already Started
                    if 
                    ::	doubleDone == false ->
                        doubleDone = true;
                        goto repeat_start;
                    :: else
                    fi
            :: else
            fi
    :: else 
    fi


    // Procedure for Creating and Starting Task1
    if
    ::  startTask1 == true ->
            // Create and Start New Task (1)
            setTask(tsk1_ID, setRC);
            printf("@@@ %d CALL task_create %d %d %d %d %d createRC\n", 
                    _pid, task_1_name, prio, mode, attr, tsk1_ID);
            task_create(tasks[tsk1_ID], tsk1_ID, task_1_name, prio, task_1_preempt,
                	    setRC, createRC);
            printf("@@@ %d SCALAR createRC %d\n", _pid, createRC);

            //
            task_start(myId, tasks[tsk1_ID], task_1_Entry, startRC);
            printf("@@@ %d CALL task_start %d %d startRC\n", 
                    _pid, tsk1_ID, task_1_Entry);
            printf("@@@ %d CALL startRC %d\n", _pid, startRC);
    ::  else -> skip
    fi

    UpdateCount();

    // At this point yield the processor over to any Ready Tasks
    printf("@@@ %d CALL task_wakeAfter %d %d wakeAfterRC\n", 
                                    _pid, tsk0_id, 0);
    task_wakeAfter(tasks[myId], PROC_YIELD, wakeAfterRC);
    printf("@@@ %d SCALAR wakeAfterRC %d\n",_pid, wakeAfterRC);

    // Procedure for Resuming Task0 once it suspends itself
    if
    ::  suspendSelf == true ->
            //Resume
            // Wait for Task 0 to self Suspend
            printf("@@@ %d CALL WaitForSuspend %d resumeRC\n", 
                        _pid, tsk0_id, resumeRC);
            do
            ::  isSuspendRC == RC_AlrSuspd -> break;
            ::  else -> 
                    task_isSuspend(tasks[tsk0_id], isSuspendRC);
            od

            printf("@@@ %d CALL task_resume %d resumeRC\n", 
                        _pid, tsk0_id, resumeRC);
            task_resume(myId, tasks[tsk0_id], resumeRC);
            printf("@@@ %d SCALAR resumeRC %d\n",_pid,resumeRC);

    ::  else
    fi

    // Procedure for Suspending and Resuming Worker Task 1
    if
    ::  suspendTask == true ->
            SuspendResume(myId, tsk0_id);
    ::  else
    fi

    // Obtain Semaphores, indicating both Worker Tasks have completed.
    // TODO: Possibly replace with an event receive.
    if 
    ::	startTask0 == true ->
            ObtainSema(myId, SEMA_TASK0_FIN);
    ::	else
    fi
    if
    ::  startTask1 == true ->
            ObtainSema(myId, SEMA_TASK1_FIN);
    ::	else
    fi

    if
    ::  createTask == true ->
            deleteId = tsk0_id;
    ::  else
    fi

    // Check that Priorities of Tasks has changed
    // Scenario: ChangePrio
    if
    ::  testPrio == true ->
            // Check Priority of Two tasks before deletion:
            // TSK0
            changeCheckPriority(myId, tsk0_id, CURRENT_PRIO, old_prio, setPriorityRC);
            // TSK1
            changeCheckPriority(myId, tsk1_ID, CURRENT_PRIO, old_prio, setPriorityRC);
    ::  else
    fi

    // Delete Worker Tasks before deleting Runner
    if
    ::  deleteTask == true -> 
			printf( "@@@ %d CALL task_delete %d deleteRC\n", _pid, deleteId);
			
            task_delete(tasks[deleteId], deleteId, deleteRC);

            printf("@@@ %d SCALAR delRC %d\n", _pid, deleteRC);

            schedSignal(myId);

            if
            ::  startTask1 == true ->
                    printf( "@@@ %d CALL task_delete %d deleteRC\n", _pid, tsk1_ID);
			
                    task_delete(tasks[tsk1_ID], tsk1_ID, deleteRC);

                    printf("@@@ %d SCALAR delRC %d\n", _pid, deleteRC);

                    schedSignal(myId);

            ::  else
            fi
    ::  else 
    fi

    // Delete Self (Runner) in Promela
    task_delete(tasks[myId], myId, deleteRC);
    // Signal to Sched Task is over.
    taskSignal!0;

}

proctype Task0(byte myId) {
    //assert(_priority == MED_PRIO);

    assert(myId < TASK_MAX);

    tasks[myId].pmlid = _pid;

    /*
    if
    :: multicore ->
        // printf("@@@ %d CALL RunnerScheduler %d\n", _pid, rcvCore);
        printf("@@@ %d CALL SetProcessor %d\n", _pid, rcvCore);
    :: else
    fi
    */

    if
    ::  startTask0 == true ->

            sched[myId]?0;

            tasks[myId].pmlid = _pid;
            //set_priority(_pid, tasks[myId].prio)

            //Do Stuff

            // Self Suspend:
            if
            ::  suspendSelf == true ->
                    // Suspend
                    printf("@@@ %d CALL task_suspend %d suspendRC\n", 
                                    _pid, tsk0_id, suspendRC);
                    task_suspend(myId, tasks[tsk0_id], suspendRC);
                    printf("@@@ %d SCALAR suspendRC %d\n",_pid,suspendRC);
            ::  suspendTask == true ->
                    // At this point yield the processor over to any Ready Tasks
                    printf("@@@ %d CALL task_wakeAfter %d %d wakeAfterRC\n", 
                                                    _pid, tsk0_id, 0);
                    task_wakeAfter(tasks[myId], PROC_YIELD, wakeAfterRC);
                    printf("@@@ %d SCALAR wakeAfterRC %d\n",_pid, wakeAfterRC);
            ::  else
            fi

            if
            ::  sleepTask == true ->
                   printf("@@@ %d CALL StartTimer\n", _pid);
                   printf("@@@ %d CALL task_wakeAfter %d %d wakeAfterRC\n", 
                                    _pid, tsk0_id, sleepTime);
                   task_wakeAfter(tasks[myId], sleepTime, wakeAfterRC);

                   printf("@@@ %d SCALAR wakeAfterRC %d\n",_pid, wakeAfterRC);
                   printf("@@@ %d CALL StopTimer\n", _pid);
                   printf("@@@ %d CALL AssessTimer %d\n", _pid, sleepTime);
                   
            ::  else 
            fi
            
            if
            ::  testPrio == true ->
                    byte setPriorityRC;
                    byte old_prio = 1;
                    
                    printf("@@@ %d DECL byte priority 0\n",_pid);

                    // Priority Changing 
                    if 
                    ::  raiseWithMutex == true ->
                            // Obtain Mutex:
                            ObtainMutex(myId, SEMA_LOCK);

                            // At this point yield the processor over to any Ready Tasks
                            printf("@@@ %d CALL task_wakeAfter %d %d wakeAfterRC\n", 
                                                            _pid, tsk0_id, 0);
                            task_wakeAfter(tasks[myId], PROC_YIELD, wakeAfterRC);
                            printf("@@@ %d SCALAR wakeAfterRC %d\n",_pid, wakeAfterRC);
/*
                            // Suspend Self
                            printf("@@@ %d CALL task_suspend %d suspendRC\n", 
                                            _pid, tsk0_id, suspendRC);
                            task_suspend(tasks[tsk0_id], suspendRC);
                            printf("@@@ %d SCALAR suspendRC %d\n",_pid,suspendRC);
*/
                    ::  else
                    fi

                    // Check Priority
                    //changePriority(taskId, CURRENT_PRIO, old_prio, setPriorityRC);

                    // Chage Priority to Low
                    changePriority(myId, myId, LOW_PRIO, old_prio, setPriorityRC);

                    // Check Priority
                    changeCheckPriority(myId, myId, CURRENT_PRIO, old_prio, setPriorityRC);
            
                    if 
                    ::  raiseWithMutex == true ->
                            // Release Mutex:
                            ReleaseMutex(myId, SEMA_LOCK);
                            // Check Priority
                            changeCheckPriority(myId, myId, CURRENT_PRIO, old_prio, setPriorityRC);
                    ::  else -> UpdateCount();
                    fi       
            ::  else -> skip
            fi
            // Release Semaphores
            ReleaseSema(myId, SEMA_TASK0_FIN);

            // Signal to Sched Task is over.
            taskSignal!0;

            // Quick Fix -> Set state to dormant if ProcType Ends before Task is deleted. 
            tasks[myId].state = Dormant;
    ::  else -> skip
    fi
    
}

proctype Task1(byte myId) {
    //assert(_priority == MED_PRIO);

    assert(myId < TASK_MAX);

    if
    ::  startTask1 == true ->

            sched[myId]?0;

            tasks[myId].pmlid = _pid;
            //set_priority(_pid, tasks[myId].prio)

            // Priority Changing 
            /*
            if 
            ::  raiseWithMutex == true ->
                    //Resume
                    // Wait for Task 0 to self Suspend
                    printf("@@@ %d CALL WaitForSuspend %d resumeRC\n", 
                                _pid, tsk0_id, resumeRC);
                    do
                    ::  isSuspendRC == RC_AlrSuspd -> break;
                    ::  else -> 
                            task_isSuspend(tasks[tsk0_id], isSuspendRC);
                    od

                    printf("@@@ %d CALL task_resume %d resumeRC\n", 
                                _pid, tsk0_id, resumeRC);
                    task_resume(tasks[tsk0_id], resumeRC);
                    printf("@@@ %d SCALAR resumeRC %d\n",_pid,resumeRC);
            ::  else
            fi
            */
            //printf("@@@ %d DECL byte priority 0\n",_pid);

            // Check Priority
            //changePriority(taskId, CURRENT_PRIO, old_prio, setPriorityRC);

            // Chage Priority to High
            //changePriority(taskId, HIGH_PRIO, old_prio, setPriorityRC);

            UpdateCount();

            if 
            ::  testPrio == true ->
                    byte setPriorityRC;
                    byte old_prio = 1;
                    // Obtain Mutex:
                    ObtainMutex(myId, SEMA_LOCK);
                    schedSignal(myId);

                    // Check Priority
                    //(taskId, CURRENT_PRIO, old_prio, setPriorityRC);

                    // Release Mutex:
                    ReleaseMutex(myId, SEMA_LOCK);
            ::  resumeSleep == true -> 
                    // Call resume on Task 0: 
                    printf("@@@ %d CALL task_resume %d resumeRC\n", 
                                _pid, tsk0_id, resumeRC);
                    task_resume(myId, tasks[tsk0_id], resumeRC);
                    printf("@@@ %d SCALAR resumeRC %d\n",_pid,resumeRC);
            ::  else
            fi

            UpdateCount();

            ReleaseSema(myId, SEMA_TASK1_FIN);

            // Signal to Sched Task is over.
            taskSignal!0;

            // Quick Fix -> Set state to dormant if ProcType Ends before Task is deleted. 
            tasks[myId].state = Dormant;
    ::  else
    fi
}

/*
proctype Task2 (byte taskid) {

}
*/

proctype PrioInheritance() {
    //printf("@@@ %d prio Inheritance Start \n",_pid);
    /* RTEMS Case:
    If the task is currently holding any binary semaphores which use a locking protocol, 
    then the task’s priority cannot be lowered immediately. If the task’s priority were 
    lowered immediately, then this could violate properties of the locking protocol and 
    may result in priority inversion. The requested lowering of the task’s priority will
    occur when the task has released all binary semaphores which make the task more important. 
    */
    //assert(_priority == ISR_PRIO);
    byte taskId, prio;
    do
    ::  interrupt_channel ? taskId, prio ->
            assert(taskId < TASK_MAX);
            if
            ::  taskId == 0 -> break;
            ::  else;
            fi
            tasks[taskId].HoldingMutex == false -> atomic {
                printf("@@@ %d prio Inheritance Enabled \n",_pid);
                tasks[taskId].prio = prio;
                updateSchedQ(tasks[taskId]);

                //schedSignal(taskId);
                //set_priority(tasks[taskId].pmlid, prio)
            }
    od
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

    //set_priority(_pid, MED_PRIO);


    if 
    ::  startTask0 == true ->
            printf("@@@ %d DEF TASK_0 %d\n",_pid,startTask0);
    ::  else
    fi
    if
    ::  startTask1 == true ->
            printf("@@@ %d DEF TASK_1 %d\n",_pid,startTask1);
    ::  else
    fi

    if
    ::  scenario == Debug ->
            printf("@@@ %d DEF TASK_1 %d\n",_pid,true);
            printf("@@@ %d DEF TASK_2 %d\n",_pid,true);
            printf("@@@ %d DEF CONFIGURE_APPLICATION_NEEDS_CLOCK_DRIVER %d\n", _pid, true);
            printf("@@@ %d DEF CONFIGURE_APPLICATION_NEEDS_CONSOLE_DRIVER %d\n", _pid, true);
    ::  else
    fi

    TestSyncRelease(SEMA_LOCK);

    atomic {
        run Scheduler();   
        run Runner(0, RUNNER_ID); 
        run Task0(TASK0_ID); 
        run Task1(TASK1_ID);
    }

    _nr_pr == 1;

    #ifdef TEST_GEN
    assert(false);
    #endif

    printf("Task Manager Model finished !\n")
}
