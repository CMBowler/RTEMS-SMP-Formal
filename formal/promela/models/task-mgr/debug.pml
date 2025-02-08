#include "task-mgr-h.pml"

bool end_task = 0;

proctype DebugRunner(byte tid) {
    printf("@@@ %d CALL DebugRunner\n", _pid);

    run DebugTask0() priority MED_PRIO;
    run DebugTask1() priority MED_PRIO;
    run DebugTask2() priority MED_PRIO;

    end_task = 1;

    // Stop the System & Clock Process
    tasks[tid].state = Zombie;
}

proctype DebugTask0() {
    printf("@@@ %d CALL DebugTask0 %d\n", _pid, SEMA_LOCK);
    end_task == 1;
}

proctype DebugTask1() {
    printf("@@@ %d CALL DebugTask1 %d\n", _pid, SEMA_LOCK);
    end_task == 1;
}

proctype DebugTask2() {
    printf("@@@ %d CALL DebugTask2 %d\n", _pid, SEMA_LOCK);
    end_task == 1;
}