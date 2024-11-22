inline task_create(task, tid, name, prio, preempt, tidRC, rc) {
    atomic {
        if
		::	name == 0 ->
				rc = RC_InvName;
        ::  prio == 0 ->
                rc = RC_InvPrio;
        ::  prio >= BAD_PRIO ->
                rc = RC_InvPrio;
		::  tidRC == false ->
                rc = RC_TooMany;
		::	tid == 0 ->
				rc = RC_InvAddr;
        ::  else ->
				task.pmlid = _pid;
				task.prio = prio;
				task.preemptable = preempt;
				task.state = Dormant;
        fi
    }
}
//*/

///*
inline task_start(task, entry, rc) {
    atomic {
        if
        ::  task.state == Zombie ->
                printf("@@@ %d LOG Start NULL out.\n",_pid);
                rc = RC_InvId;
		:: 	else ->
				if
				::  task.state != Dormant ->
						rc = RC_IncState;
				:: 	else ->
						if 
						::  entry == 0 -> rc = RC_InvAddr;
						::  else ->
							task.state = Ready;
							task.start = entry;
							// Start Task Model
							TestSyncRelease(entry);
							rc = RC_OK;
						fi
				fi
        fi
    }
}
//*/


inline task_suspend(task, rc) {
    atomic {
        if
        ::  task.state == Zombie ->
                rc = RC_InvId;
        ::  task.state == Blocked ->
                rc = RC_AlrSuspd;
        ::  else ->
                task.state = Blocked;
                rc = RC_OK;
        fi
    }
}

inline task_isSuspend(task, rc) {
    atomic {
        if
        ::  task.state == Zombie ->
                rc = RC_InvId;
        ::  task.state == Blocked ->
                rc = RC_AlrSuspd;
        ::  else ->
                rc = RC_OK;
        fi
    }
}

inline task_resume(task, rc) {
    atomic {
        if
        ::  task.state == Zombie ->
            rc = RC_InvId;
        ::  else ->
                if
                :: task.state != Blocked ->
                    rc = RC_IncState;
                :: else ->
                    task.state = Ready ->
                    rc = RC_OK;
                fi
        fi
    }
}

inline task_delete(task, tid, rc) {
    atomic {
        if
        ::  task.state == Zombie ->
                rc = RC_InvId;
        ::  else ->
                if
                ::  task.isr == true ->
                        rc = RC_FrmIsr;
                ::  else ->
                        bool isremoved;
                        removeTask(tid, isremoved);
                        if
                        ::  isremoved == false ->
                                rc = RC_InvId;
                        ::  else ->
                                task.state = Zombie;
                                task.start = 0;
                                rc = RC_OK;
                        fi
                fi
        fi
    }
}
//*/


inline task_setPrio(task, new, old, rc) {
    atomic {
        if
        ::  task.state == Zombie ->
                rc = RC_InvId;
        ::  old == INVALID_ID ->
                rc = RC_InvAddr;
        ::  else ->
                if
                ::  new > MAX_PRIO ->
                        rc = RC_InvPrio;
                ::  new == CURRENT_PRIO ->
                        old = task.prio;
                        rc = RC_OK;
                ::  else ->
                        old = task.prio;
                        if
                        ::  new <= old -> skip
                        ::  else ->
                        // If the task is currently holding any binary semaphores 
                        // which use a locking protocol, then the task’s priority cannot be lowered immediately
                                
                        fi
                        task.prio = new;
                        set_priority(task.pmlid, new); //TODO
                        rc = RC_OK;
                fi
        fi
    }
}