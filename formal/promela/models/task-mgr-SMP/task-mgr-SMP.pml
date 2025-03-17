#define NUM_PROC 4
#define INVALID_SCHED NUM_PROC

#include "../common/rtems.pml"
#define TASK_MAX 6
#define SEMA_MAX 8
#include "../common/model.pml"

#include "../task-mgr/task-mgr-h.pml"
#include "../task-mgr/task-mgr-API.pml"
#include "../task-mgr/task-mgr-scheduling.pml"
#include "task-mgr-SMP-h.pml"



proctype Runner(byte myId) {

  tasks[myId].pmlid = _pid;

  byte schedId;
  schedSignal[myId]?schedId;

  byte newSched=0;

  byte old_prio = 0;
  byte setRC, rc;

  byte prio = MED_PRIO;
  bool preempt = true;
  byte name = 1;
  byte stackSize = 1;
  byte attr = 0;

  byte tsk0_id, tsk1_id, tsk2_id, tsk3_id;

  printf("@@@ %d DECL byte priority 0\n",_pid);
  printf("@@@ %d CALL taskSelf_setPriority %d %d setPriorityRC\n", 
                          _pid, MED_PRIO, old_prio);

  // ----------------------------------------------

  // Create Tasks

  // Create Task0
  // Add to Sched0
  setTask(tsk0_id, setRC);
  printf("@@@ %d CALL task_create %d %d %d %d %d %d createRC\n", 
          _pid, name, MED_PRIO, stackSize, preempt, attr, tsk0_id);
  task_create(
    tasks[myId].homeSched, 
    tasks[tsk0_id], 
    tsk0_id, 
    name, 
    prio, 
    preempt, 
    setRC, 
    rc
  );
  printf("@@@ %d SCALAR createRC %d\n", _pid, rc);
  
  // Create Task1

  name++;
  setTask(tsk1_id, setRC);
  printf("@@@ %d CALL task_create %d %d %d %d %d %d createRC\n", 
          _pid, name, prio, stackSize, preempt, attr, tsk1_id);
  task_create(
    tasks[myId].homeSched, 
    tasks[tsk1_id], 
    tsk1_id, 
    name, 
    prio, 
    preempt, 
    setRC, 
    rc
  );
  printf("@@@ %d SCALAR createRC %d\n", _pid, rc);

  // Add to Sched1
  newSched++;

  task_setScheduler(myId, schedId, tasks[tsk1_id], newSched, prio, rc);

  // Create Task2

  name++;
  setTask(tsk2_id, setRC);
  printf("@@@ %d CALL task_create %d %d %d %d %d %d createRC\n", 
          _pid, name, prio, stackSize, preempt, attr, tsk2_id);
  task_create(
    tasks[myId].homeSched, 
    tasks[tsk2_id], 
    tsk2_id, 
    name, 
    prio, 
    preempt, 
    setRC, 
    rc
  );
  printf("@@@ %d SCALAR createRC %d\n", _pid, rc);

  // Add to Sched1
  newSched++;

  task_setScheduler(myId, schedId, tasks[tsk2_id], newSched, prio, rc);
  
  // Create Task3
  // Add to Sched3

  name++;
  setTask(tsk3_id, setRC);
  printf("@@@ %d CALL task_create %d %d %d %d %d %d createRC\n", 
          _pid, name, prio, stackSize, preempt, attr, tsk3_id);
  task_create(
    tasks[myId].homeSched, 
    tasks[tsk3_id], 
    tsk3_id, 
    name, 
    prio, 
    preempt, 
    setRC, 
    rc
  );
  printf("@@@ %d SCALAR createRC %d\n", _pid, rc);

  // Add to Sched1
  newSched++;

  task_setScheduler(myId, schedId, tasks[tsk3_id], newSched, prio, rc);

  // ----------------------------------------------

  // Start Tasks together..

  byte Entry = 1;

  // Task 0
  task_start(
    myId, 
    tasks[myId].homeSched, 
    tasks[tsk0_id], 
    Entry, 
    rc
  );
  printf("@@@ %d CALL task_start %d %d startRC\n", 
          _pid, tsk0_id, Entry);
  printf("@@@ %d CALL startRC %d\n", _pid, rc);

  // Task 1
  task_start(
    myId, 
    tasks[myId].homeSched, 
    tasks[tsk1_id], 
    Entry, 
    rc
  );
  printf("@@@ %d CALL task_start %d %d startRC\n", 
          _pid, tsk1_id, Entry);
  printf("@@@ %d CALL startRC %d\n", _pid, rc);

  // Task 2
  task_start(
    myId, 
    tasks[myId].homeSched, 
    tasks[tsk2_id], 
    Entry, 
    rc
  );
  printf("@@@ %d CALL task_start %d %d startRC\n", 
          _pid, tsk2_id, Entry);
  printf("@@@ %d CALL startRC %d\n", _pid, rc);

  // Task 3
  task_start(
    myId, 
    tasks[myId].homeSched, 
    tasks[tsk3_id], 
    Entry, 
    rc
  );
  printf("@@@ %d CALL task_start %d %d startRC\n", 
          _pid, tsk3_id, Entry);
  printf("@@@ %d CALL startRC %d\n", _pid, rc);

  // ----------------------------------------------

  // Allow Tasks to run

  byte opsPerTask = 1;
  byte opCount=0;
  do
  ::  opCount == opsPerTask -> break;
  ::  else ->
        printf("@@@ %d CALL task_wakeAfter %d %d wakeAfterRC\n", 
                _pid, myId, 10);
        task_wakeAfter(schedId, tasks[myId], 10, rc);
        printf("@@@ %d SCALAR wakeAfterRC %d\n",_pid, rc);

        // For each task, if it is stuck in suspension, resume:
        clearSuspends(myId, schedId);

        opCount++;
  od

  // ----------------------------------------------

  // Wait for All tasks to finish 
  /* Debug
  atomic {
    printf("Status of Sem %d: %d\n", SEMA_TASK0_FIN, semaList[SEMA_TASK0_FIN].free);
    printf("Status of Sem %d: %d\n", SEMA_TASK1_FIN, semaList[SEMA_TASK1_FIN].free);
    printf("Status of Sem %d: %d\n", SEMA_TASK2_FIN, semaList[SEMA_TASK2_FIN].free);
    printf("Status of Sem %d: %d\n", SEMA_TASK3_FIN, semaList[SEMA_TASK3_FIN].free);
  }
  */

  printf("@@@ %d CALL task_wakeAfter %d %d wakeAfterRC\n", 
        _pid, myId, PROC_YIELD);
  task_wakeAfter(schedId, tasks[myId], PROC_YIELD, rc);
  printf("@@@ %d SCALAR wakeAfterRC %d\n",_pid, rc);

  clearSuspends(myId, schedId);

  ObtainSema(tasks[myId], SEMA_TASK0_FIN);
  ObtainSema(tasks[myId], SEMA_TASK1_FIN);
  ObtainSema(tasks[myId], SEMA_TASK2_FIN);
  ObtainSema(tasks[myId], SEMA_TASK3_FIN);

  // ----------------------------------------------

  // Delete All remaining Tasks:

  byte taskID = 2;
  do
  ::  taskID == TASK_MAX -> break;
  ::  else -> 
      printf( "@@@ %d CALL task_delete %d deleteRC\n", _pid, taskID);
      task_delete(myId, schedId, tasks[taskID], rc);
      printf("@@@ %d SCALAR delRC %d\n", _pid, rc);
      taskID++;
  od

  // ----------------------------------------------

  // Delete Self (Runner) in Promela
  task_exit(tasks[myId]);
  // Signal to Sched Task is over.
  taskSignal[schedId]!0;
}

proctype TaskN(byte myId, semaId) {

  tasks[myId].pmlid = _pid;

  byte schedId;
  schedSignal[myId]?schedId;

  ObtainSema(tasks[myId], semaId);

  byte tid, prio, ticks, sid, schId, rc;
  byte old_prio = 1;
  printf("@@@ %d DECL byte priority 0\n",_pid);

  atomic{selectOp(schedId, tid, prio, ticks, schId, rc)};

  atomic{selectOp(schedId, tid, prio, ticks, schId, rc)};

  //atomic{selectOp(schedId, tid, prio, ticks, schId, rc)};

  // Quick Fix -> Set state to dormant if ProcType Ends before Task is deleted. 
  tasks[myId].state = Dormant;
  ReleaseSema(tasks[myId], semaId);
  // Signal to Sched Task is over.
  taskSignal[schedId]!0
}

init {
    pid nr;

    printf("Task Manager Model running.\n");
    printf("Setup...\n");

    printf("@@@ %d NAME Task_Manager_TestGen\n",_pid)

    outputDefines();
    outputDeclarations();

    printf("@@@ %d INIT\n",_pid);

    printf("Run...\n");

    // Set runner task state to Ready
    // as this task is active from the start of all scenarios.
    printf("@@@ %d Initialising Runner\n",_pid);
    atomic {
      tasks[RUNNER_ID].tid = RUNNER_ID;
      tasks[RUNNER_ID].state = Ready;
      tasks[RUNNER_ID].prio = MED_PRIO;
      tasks[RUNNER_ID].homeSched = 0;
      tasks[RUNNER_ID].preemptable = 1;
      insertSchedQ(
        tasks[RUNNER_ID], 
        tasks[RUNNER_ID].homeSched
      );
    }

    task_control = 60;	// 0011 1100 Task[1] reserved for runner.

    run Runner(RUNNER_ID); 
    run TaskN(TASK0_ID, SEMA_TASK0_FIN); 
    run TaskN(TASK1_ID, SEMA_TASK1_FIN);
    run TaskN(TASK2_ID, SEMA_TASK2_FIN);
    run TaskN(TASK3_ID, SEMA_TASK3_FIN);

    MultiSchedulerInit();

    _nr_pr == 1;

    #ifdef TEST_GEN
    assert(false);
    #endif

    printf("Task Manager Model finished !\n")
}
