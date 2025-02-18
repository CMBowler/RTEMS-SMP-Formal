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
inline task_create(task, id, name, prio, preempt, tidRC, rc) {
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
		::	id == 0 ->
				rc = RC_InvAddr;
        ::  else ->
                task.tid = id;
				task.prio = prio;
				task.preemptable = preempt;
				task.state = Dormant;
                insertSchedQ(task);
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
inline task_start(callerId, task, entry, rc) {
    atomic {
        if
        ::  task.tid == INVALID_ID ->
                //printf("@@@ %d LOG Start NULL out.\n",_pid);
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
							//TestSyncRelease(entry);
							rc = RC_OK;
						fi
				fi
        fi
    }
    if 
    ::  tasks[callerId].preemptable -> schedSignal(callerId);
    ::  else
    fi
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
inline task_suspend(callerId, task, rc) {
    atomic {
        if
        ::  task.state == Zombie ->
                rc = RC_InvId;
        ::  task.state == Blocked || task.state == TimeBlocked ->
                rc = RC_AlrSuspd;
        ::  task.state == TimeWait ->
                task.state = TimeBlocked;
                rc = RC_OK;
        ::  else ->
                task.state = Blocked;
                rc = RC_OK;
        fi
    }
    schedSignal(callerId);
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
        ::  task.state == Blocked || task.state == TimeBlocked ->
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
inline task_resume(callerId, task, rc) {
    atomic {
        if
        ::  task.state == Zombie ->
                rc = RC_InvId;
        ::  task.state == TimeBlocked ->
                task.state = TimeWait;
                rc = RC_OK;
        ::  task.state == Blocked ->
                task.state = Ready;
                rc = RC_OK;
        ::  else -> // Task State == Ready/Dormant
                rc = RC_IncState;
        fi
    }
    if 
    ::  tasks[callerId].preemptable -> schedSignal(callerId);
    ::  else
    fi
}

/*
 * task_delete(task, tid, rc)
 *
 * Simulates a call to rtems_task_start
 *   task : struct storing the relevant task information
 *          task = tasks[tid]
 *   tid : id of the relevant task
 *   rc : updated with the return code when task_start completes
 *
 * Corresponding RTEMS call:
 *   rc = rtems_task_delete(tid);
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
                                removeSchedQ(task);
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
inline task_setPrio(callerId, task, new, old, rc) {
    atomic {
        if
        ::  task.state == Zombie ->
                rc = RC_InvId;
        ::  old == INVALID_ID ->
                rc = RC_InvAddr;
        ::  else ->
                if  
                ::  task.inheritedPrio != 0 ->
                        old = task.inheritedPrio;
                ::  else -> 
                        old = task.prio;
                fi

                if
                ::  new > MAX_PRIO ->
                        rc = RC_InvPrio;
                ::  new == CURRENT_PRIO ->
                        rc = RC_OK;
                ::  else ->
                        task.prio = new;
                        if
                        ::  new <= old || task.HoldingMutex == false-> 
                                updateSchedQ(task);
                        ::  else
                                /*
                                If the task is currently holding any 
                                binary semaphores which use a locking protocol, 
                                then the task’s priority cannot be lowered immediately
                                */
                                task.inheritedPrio = old;
                        fi
                        rc = RC_OK;
                fi
        fi
    }
    if 
    ::  tasks[callerId].preemptable -> schedSignal(callerId);
    ::  else
    fi
}

/*
inline task_getPrio(task, sched, prio, rc) {
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
*/

/*
 * task_wakeAfter(ticks, rc)
 *
 * Simulates a call to rtems_task_start
 *   ticks : ticks that should pass before the task is awakened
 *   rc : updated with the return code when task_start completes
 *
 * Corresponding RTEMS call:
 *   rc = rtems_task_wake_after(ticks);
 *      `ticks` models `rtems_interval ticks`
 *
 */
inline task_wakeAfter(task, time, rc) {

    // API can only be used in 
    // a self-referential way:
    // A task cannot sleep another task
    // Using this API
    assert(task.pmlid == _pid);
    assert(task.state == Ready);

    byte id = task.tid;

    if
    ::  time == PROC_YIELD ->
            /*  
                Keep state of task as Ready
                but send Task to the the end
                of its priority group.
            */
            updateSchedQ(task);
            schedSignal(id);
    ::  else -> 
            atomic {
                task.state = TimeWait;
                task.ticks = time
            }
            // Wait out Timer
            do
            ::  task.state == Ready -> break;
            ::  else -> schedSignal(id);
            od
    fi

    rc = RC_OK;
}
