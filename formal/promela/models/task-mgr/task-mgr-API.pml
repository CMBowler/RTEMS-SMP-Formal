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
inline task_create(schedId, task, id, name, prio, preempt, tidRC, rc) {
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
        insertSchedQ(task, schedId);
        task.homeSched = schedId;
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
inline task_start(callerId, schedId, task, entry, rc) {
  atomic {
    if
    ::  task.tid == INVALID_ID ->
	        //printf("@@@ %d LOG Start NULL out.\n",_pid);
          rc = RC_InvId;
		:: 	else ->
          if 
          ::  entry == 0 -> 
                rc = RC_InvAddr;
          ::  else ->
                if
                ::  task.state == Dormant ->
                      task.state = Ready;
                      task.start = entry;
                      rc = RC_OK;
                ::  task.state == Blocked -> 
                      /*
                        In the case a task has been suspended 
                        before it is started, the state cannot
                        be set to ready, as this over-writes 
                        the blocked state, instead we can set
                        the tasks 'preBlockState' to ready.
                      */
                      task.preBlockState = Ready;
                      task.start = entry;
                      rc = RC_OK;
                :: 	else ->
                      rc = RC_IncState;
                fi
          fi
    fi
  }

  if 
  ::  tasks[callerId].preemptable -> schedSync(callerId, schedId);
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
inline task_suspend(callerId, schedId, task, rc) {
  atomic {
    if
    ::  task.state == Zombie ->
  	      rc = RC_InvId;
  	::  task.state == Blocked && task.SuspBlock ->
          rc = RC_AlrSuspd;
    ::  else ->
          // Store preblocked state if required
          // and add SuspBlock state
          if
          ::  task.state != Blocked -> // Executing/Ready/Dormant
                if
                ::  task.state == Executing -> // Self suspend
                      task.preBlockState = Ready;
                ::  else ->
                      task.preBlockState = task.state;
                fi
                task.state = Blocked;
          ::  else
          fi
          task.SuspBlock = true; 
          rc = RC_OK;
    fi
	}

  schedSync(callerId, schedId);
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
    ::  task.state == Blocked && task.SuspBlock == true->
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
inline task_resume(callerId, schedId, task, rc) {
  atomic {
    if
    ::  task.state == Zombie ->
          rc = RC_InvId;
    ::  task.state == Blocked && task.SuspBlock ->
          task.SuspBlock = false;
          if
          ::  task.TimeBlock == false && 
              task.SemaBlock == false -> 
                task.state = task.preBlockState;
          ::  else
          fi
          rc = RC_OK;
    ::  else -> // Task State == Ready/Dormant
          rc = RC_IncState;
    fi
  }

  if 
  ::  tasks[callerId].preemptable -> schedSync(callerId, schedId);
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
inline task_delete(callerId, schedId, task, rc) {
  byte taskId = task.tid;
  byte taskSched = task.homeSched;
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
                removeTask(task.tid, isremoved);
                if
                ::  isremoved == false ->
                      rc = RC_InvId;
                ::  else ->
                      // Reset elements of TCB
                      task.state = Zombie;
                      task.start = 0;
                      // Remove from all Scheduler Task Queues
                      byte sID = 0;
                      do
                      ::  sID == NUM_PROC -> break;
                      ::  else -> 
                            removeSchedQ(task, sID);
                            sID++;
                      od
                      task.tid = 0;
                      task.preemptable = 0;
                      task.TimeBlock = 0;
                      task.SemaBlock = 0;
                      task.SuspBlock = 0;
                      task.pmlid = 0;
                      task.prio = 0;
                      rc = RC_OK;
                fi
          fi
    fi
  }
  //schedSignal[taskId]!taskSched; 
  schedSync(callerId, schedId);
}

inline task_exit(task) {
  assert(task.pmlid == _pid);
  byte taskId = task.tid;
  byte taskSched = task.homeSched;
  atomic {
    if
    ::  task.state == Zombie ->
          skip;
    ::  else ->
          if
          ::  task.isr == true ->
                skip;
          ::  else ->
                bool isremoved;
                removeTask(task.tid, isremoved);
                if
                ::  isremoved == false ->
                      skip;
                ::  else ->
                      // Reset elements of TCB
                      task.state = Zombie;
                      task.start = 0;
                      // Remove from all Scheduler Task Queues
                      byte sID = 0;
                      do
                      ::  sID == NUM_PROC -> break;
                      ::  else -> 
                            removeSchedQ(task, sID);
                            sID++;
                      od
                      task.tid = 0;
                      task.preemptable = 0;
                      task.TimeBlock = 0;
                      task.SemaBlock = 0;
                      task.SuspBlock = 0;
                      task.pmlid = 0;
                      task.prio = 0;
                      skip;
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
inline task_setPrio(callerId, schedId, task, new, old, rc) {
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
                      updateSchedQ(task, task.homeSched);
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
  ::  tasks[callerId].preemptable -> schedSync(callerId, schedId);
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
inline task_wakeAfter(schedId, task, time, rc) {

	// API can only be used in 
	// a self-referential way:
	// A task cannot sleep another task
	// Using this API
	assert(task.pmlid == _pid);

	byte id = task.tid;

  atomic {
    if
    ::  time == PROC_YIELD ->
          /*  
              Keep state of task as Ready
              but send Task to the the end
              of its priority group.
          */
          updateSchedQ(task, task.homeSched);
    ::  else -> 
          // Store preblocked state if required
          // and add TimeBlock state
          if
          ::  task.state != Blocked -> // Executing/Ready/Dormant
                if
                ::  task.state == Executing -> // Self suspend
                      task.preBlockState = Ready;
                ::  else ->
                      task.preBlockState = task.state;
                fi
                task.state = Blocked;
          ::  else 
          fi
          task.TimeBlock = true
          task.ticks = time
    fi
  }
  // Wait out Blocked State
  schedSync(id, task.homeSched);

	rc = RC_OK;
}

inline task_getScheduler(task, scheduler, rc) {
  // return the home scheduler of the task
  atomic {
    if
    ::  scheduler == 0 ->
          rc = RC_InvAddr;
    ::  else -> 
          if
          ::  task.state = Zombie ->
                rc = RC_InvId;
          ::  else -> 
                scheduler = task.homeSched;
                rc = RC_OK;
          fi
    fi
  }
}

inline task_setScheduler(callerId, schedulerId, task, sched, prio, rc) {
  // set the home scheduler of the task
  atomic  {
    if
    ::  task.homeSched == sched ->
          rc = RC_OK;
    ::  task.state == Zombie ->
          rc = RC_InvId;
    ::  task.tid == 0 ->
          rc = RC_InvId;
    ::  sched >= INVALID_SCHED ->
          rc = RC_InvId;
    ::  else ->
          if
          ::  prio > MAX_PRIO || prio == 0 ->
                rc = RC_InvPrio;
          ::  else ->
                if
                ::  task.state == Blocked || task.inheritedPrio != 0 ->
                      rc = RC_RsrcInUse;
                ::  else -> 
                      removeSchedQ(task, task.homeSched);
                      task.homeSched = sched;
                      // And add it to its new home scheduler.
                      insertSchedQ(task, task.homeSched);
                      rc = RC_OK;
                fi
          fi
    fi
  }
  
  schedSync(callerId, schedulerId);
}
