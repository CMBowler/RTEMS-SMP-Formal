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

#include "task-mgr-h.pml"
#include "task-mgr-API.pml"

byte sendrc;            // Sender global variable
byte recrc;             // Receiver global variable
byte recout[TASK_MAX] ; // models receive 'out' location.

byte createRC;
byte startRC;
byte deleteRC;
byte suspendRC;
byte isSuspendRC;
byte resumeRC;

byte task_id[TASK_MAX];

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
    task_suspend(tasks[suspId], suspendRC);
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
    task_resume(tasks[resumeId], resumeRC);
    printf("@@@ %d SCALAR resumeRC %d\n",_pid,resumeRC);

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

        task_create(tasks[insertId], insertId, name, prio, preempt, setRC, createRC);
		
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
            task_start(tasks[startId], entry, startRC);
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
            task_create(tasks[tsk1_ID], tsk1_ID, task_1_name, prio, preempt, setRC, createRC);
            printf("@@@ %d SCALAR createRC %d\n", _pid, createRC);
            //
            task_start(tasks[tsk1_ID], task_1_Entry, startRC);
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
                    task_isSuspend(tasks[insertId], isSuspendRC);
            od

            printf("@@@ %d CALL task_resume %d resumeRC\n", 
                        _pid, insertId, resumeRC);
            task_resume(tasks[insertId], resumeRC);
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
			
            task_delete(tasks[deleteId], deleteId, deleteRC);

            printf("@@@ %d SCALAR delRC %d\n", _pid, deleteRC);

            if
            ::  testPrio == true ->
                    printf( "@@@ %d CALL task_delete %d deleteRC\n", _pid, tsk1_ID);
			
                    task_delete(tasks[tsk1_ID], tsk1_ID, deleteRC);

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
                    task_suspend(tasks[insertId], suspendRC);
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
                    task_setPrio(tasks[taskid], CURRENT_PRIO, old_prio, setPriorityRC);
                    printf("@@@ %d SCALAR setPriorityRC %d\n",_pid,setPriorityRC);

                    // Chage Priority to High
                    printf("@@@ %d CALL task_setPriority %d LOW_PRIO %d setPriorityRC\n", 
                                            _pid, taskid, LOW_PRIO, old_prio, setPriorityRC);
                    task_setPrio(tasks[taskid], LOW_PRIO, old_prio, setPriorityRC);
                    printf("@@@ %d SCALAR setPriorityRC %d\n",_pid,setPriorityRC);

                    // Check Priority
                    printf("@@@ %d CALL task_setPriority %d %d %d setPriorityRC\n", 
                                            _pid, taskid, CURRENT_PRIO, old_prio, setPriorityRC);
                    task_setPrio(tasks[taskid], CURRENT_PRIO, old_prio, setPriorityRC);
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
            task_setPrio(tasks[taskid], CURRENT_PRIO, old_prio, setPriorityRC);
            printf("@@@ %d SCALAR setPriorityRC %d\n",_pid,setPriorityRC);

            // Chage Priority to High
            printf("@@@ %d CALL task_setPriority %d HIGH_PRIO %d setPriorityRC\n", 
                                    _pid, taskid, HIGH_PRIO, old_prio, setPriorityRC);
            task_setPrio(tasks[taskid], HIGH_PRIO, old_prio, setPriorityRC);
            printf("@@@ %d SCALAR setPriorityRC %d\n",_pid,setPriorityRC);

            // Check Priority
            printf("@@@ %d CALL task_setPriority %d %d %d setPriorityRC\n", 
                                    _pid, taskid, CURRENT_PRIO, old_prio, setPriorityRC);
            task_setPrio(tasks[taskid], CURRENT_PRIO, old_prio, setPriorityRC);
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
