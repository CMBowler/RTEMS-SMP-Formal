/*
 * task_create(task, tid, name, prio, preempt, tidRC, rc)
 *
 * Simulates a call to rtems_task_create
 *   task : struct to store task information
 *   tid : variable storing new task ID
 *   name : name given to new task
 *   prio : task priority
 *   preempt : boolean field in task mode
 *   tidRC : return code for if a new task ID could be allocated
 *   rc : updated with the return code when task_create completes
 *
 * Corresponding RTEMS call:
 *   rc = rtems_task_create(name, prio, stack, mode, tid);
 *     `name` models `rtems_name name`
 *     `prio` models `rtems_task_priority initial_priority`
 *     `stack` models `size_t stack_size` set to `RTEMS_MINIMUM_STACK_SIZE`
 *     `mode` models `rtems_mode initial_modes`, set to `RTEMS_DEFAULT_MODES`
 *     `tid` models `rtems_id           *id`
 *
 */
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

/*
 * task_start(task, entry, rc)
 *
 * Simulates a call to rtems_task_start
 *  task : struct storing the relevant task information
 *          task = tasks[tid]
 *  tid : id of the relevant task
 *  entry : semaphore corresponding to a process, 
            upon calling task_start the semaphore releases a 
            waiting process, modelling the starting of a task.
 *  rc : updated with the return code when task_start completes
 *
 * Corresponding RTEMS call:
 *   rc = rtems_task_start(tid, entry, arg);
 *     `tid` models `rtems_id id`
 *     `entry` models `rtems_task_entry entry_point`
 *     `arg` models `rtems_task_argument argument` and
 *                  is not utilised in the model. 
 *
 */
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

/*
 * task_suspend(task, rc)
 *
 * Simulates a call to rtems_task_start
 *   task : struct storing the relevant task information
 *          task = tasks[tid]
 *   tid : id of the relevant task
 *   rc : updated with the return code when task_start completes
 *
 * Corresponding RTEMS call:
 *   rc = rtems_task_suspend(tid);
 *     `tid` models `rtems_id id`
 *
 */
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

/*
 * task_isSuspend(task, rc)
 *
 * Simulates a call to rtems_task_start
 *   task : struct storing the relevant task information
 *          task = tasks[tid]
 *   tid : id of the relevant task
 *   rc : updated with the return code when task_start completes
 *
 * Corresponding RTEMS call:
 *   rc = rtems_task_is_suspended(tid);
 *     `tid` models `rtems_id id`
 *
 */
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

/*
 * task_resume(task, rc)
 *
 * Simulates a call to rtems_task_start
 *   task : struct storing the relevant task information
 *          task = tasks[tid]
 *   tid : id of the relevant task
 *   rc : updated with the return code when task_start completes
 *
 * Corresponding RTEMS call:
 *   rc = rtems_task_resume(tid);
 *     `tid` models `rtems_id id`
 *
 */
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

/*
 * task_resume(task, tid, rc)
 *
 * Simulates a call to rtems_task_start
 *   task : struct storing the relevant task information
 *          task = tasks[tid]
 *   tid : id of the relevant task
 *   rc : updated with the return code when task_start completes
 *
 * Corresponding RTEMS call:
 *   rc = rtems_task_resume(tid);
 *     `tid` models `rtems_id id`
 *
 */
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

/*
 * task_setPrio(tid, new, old, rc)
 *
 * Simulates a call to rtems_task_start
 *   task : struct storing the relevant task information
 *          task = tasks[tid]
 *   tid : id of the relevant task
 *   new : new priority that the relevant task will be set to
 *   old : priority of the relevant task before setting it to the
           value of new
 *   rc : updated with the return code when task_start completes
 *
 * Corresponding RTEMS call:
 *   rc = rtems_task_set_priority(tid, new, old);
 *      `tid` models `rtems_id id`
 *      `new` models `rtems_task_priority new_priority`
 *      `old` models `rtems_task_priority old_priority`
 *
 */
inline task_setPrio(tid, new, old, rc) {
    atomic {
        if
        ::  tasks[tid].state == Zombie ->
                rc = RC_InvId;
        ::  old == INVALID_ID ->
                rc = RC_InvAddr;
        ::  else ->
                if
                ::  new > MAX_PRIO ->
                        rc = RC_InvPrio;
                ::  new == CURRENT_PRIO ->
                        old = tasks[tid].prio;
                        rc = RC_OK;
                ::  else ->
                        old = tasks[tid].prio;
                        if
                        ::  new > old -> 
                                tasks[tid].prio = new;
                                set_priority(tasks[tid].pmlid, new); //TODO
                        ::  else ->
                                /*
                                If the task is currently holding any 
                                binary semaphores which use a locking protocol, 
                                then the task’s priority cannot be lowered immediately
                                */
                                interrupt_channel ! tid, new;
                        fi
                        rc = RC_OK;
                fi
        fi
    }
}

/*
inline task_setPrio(task, sched, prio, rc) {
    if
    ::  prio == 0 ->
            rc = RC_InvAddr
    ::  else ->
            if
            ::  task.state == Zombie ->
                    rc = RC_InvId
            ::  else ->
                    if
                    ::  sched.state == Zombie ->
                            rc = RC_InvId
                    ::  else ->

}

inline rtems_task_wake_after(ticks) {

    // ticks == 0: RTEMS_YIELD_PROCESSOR
    int count = 0;
    do
    ::  
}
*/