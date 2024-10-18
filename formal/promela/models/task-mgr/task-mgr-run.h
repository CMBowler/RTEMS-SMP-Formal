/* SPDX-License-Identifier: BSD-2-Clause */

static void Worker{0}( rtems_task_argument arg )
{{
  Context *ctx;
  rtems_event_set events;

  ctx = (Context *) arg;

  T_log( T_NORMAL, "Worker Running" );
  TestSegment2( ctx );
  T_log( T_NORMAL, "Worker finished" );

  // (void) rtems_task_suspend( RTEMS_SELF );
  // Ensure we hold no semaphores
  ReleaseTestSyncSema( ctx->worker_wakeup );
  ReleaseTestSyncSema( ctx->runner_wakeup );
  // Wait for events so we don't terminate
  rtems_event_receive( RTEMS_ALL_EVENTS, RTEMS_DEFAULT_OPTIONS, 0, &events );

}}

/*
RTEMS_ALIGNED( RTEMS_TASK_STORAGE_ALIGNMENT ) static char WorkerStorage{0}[
  RTEMS_TASK_STORAGE_SIZE(
    MAX_TLS_SIZE + TEST_MINIMUM_STACK_SIZE,
    WORKER_ATTRIBUTES
  )
];
*/

static void RtemsModelTaskMgr_Setup{0}(
  RtemsModelTaskMgr_Context *ctx
)
{{

  T_log( T_NORMAL, "Runner Setup" );

  memset( ctx, 0, sizeof( *ctx ) );
  ctx->runner_thread = _Thread_Get_executing();
  ctx->runner_id = ctx->runner_thread->Object.id;

  T_log( T_NORMAL, "Creating Worker TestSync Semaphore" );
  ctx->worker_wakeup = CreateTestSyncSema( "WRKR" );
  T_log( T_NORMAL, "Creating Runner TestSync Semaphore" );
  ctx->runner_wakeup = CreateTestSyncSema( "RUNR" );

  // Add worker to the taskId array:
  tasks[1] = Worker{0};

  
}}

static void RtemsModelTaskMgr_Setup_Wrap{0}( void *arg )
{{
  RtemsModelTaskMgr_Context *ctx;

  ctx = arg;
  RtemsModelTaskMgr_Setup{0}( ctx );
}}

static RtemsModelTaskMgr_Context RtemsModelTaskMgr_Instance{0};

static T_fixture RtemsModelTaskMgr_Fixture{0} = {{
  .setup = RtemsModelTaskMgr_Setup_Wrap{0},
  .stop = NULL,
  .teardown = RtemsModelTaskMgr_Teardown_Wrap,
  .scope = RtemsModelTaskMgr_Scope,
  .initial_context = &RtemsModelTaskMgr_Instance{0}
}};

static T_fixture_node RtemsModelTaskMgr_Node{0};

void RtemsModelTaskMgr_Run{0}(
  rtems_status_code ( *t_create )(
                        rtems_name, 
                        rtems_task_priority, 
                        size_t, 
                        rtems_mode,
                        rtems_attribute, 
                        rtems_id *
                    ),
  rtems_status_code ( *t_start )( 
                        rtems_id,
                        rtems_task_entry,
                        rtems_task_argument
                    ),
  rtems_status_code ( *t_delete )(
                        rtems_id
                    ),
  unsigned int         wait_class,
  int                  waiting_for_event
)
{{
  RtemsModelTaskMgr_Context *ctx;

  T_set_verbosity( T_NORMAL );

  T_log( T_NORMAL, "Runner Invoked" );
  T_log( T_NORMAL, "Runner Wait Class: %d", wait_class );
  T_log( T_NORMAL, "Runner WaitForEvent: %d", waiting_for_event );

  T_log( T_NORMAL, "Pushing Test Fixture..." );


  ctx = T_push_fixture(
    &RtemsModelTaskMgr_Node{0},
    &RtemsModelTaskMgr_Fixture{0}
  );
  // This runs RtemsModelEventsMgr_Fixture

  T_log( T_NORMAL, "Test Fixture Pushed" );


  //ctx->send = send;
  //ctx->receive = receive;
  //ctx->get_pending_events = get_pending_events;
  ctx->t_create = t_create;
  ctx->t_start = t_start;
  ctx->t_delete = t_delete;

  ctx->wait_class = wait_class;
  ctx->waiting_for_event = waiting_for_event;

  ctx->this_test_number = {0};

  // RtemsModelEventsMgr_Prepare( ctx );
  ctx->events_to_send = 0;
  ctx->send_status = RTEMS_INCORRECT_STATE;
  ctx->received_events = 0xffffffff;
  ctx->receive_option_set = 0;
  ctx->receive_timeout = RTEMS_NO_TIMEOUT;
  ctx->unsatisfied_pending = 0xffffffff;
  memset( &ctx->thread_switch_log, 0, sizeof( ctx->thread_switch_log ) );
  //T_eq_u32( GetPending( ctx ), 0 );
  _Thread_Wait_flags_set( ctx->runner_thread, THREAD_WAIT_CLASS_PERIOD );

  TestSegment0( ctx );

  Runner( ctx );

  RtemsModelTaskMgr_Cleanup( ctx );

  T_log( T_NORMAL, "Run Pop Fixture" );
  ShowWorkerSemaId( ctx->worker_id, ctx->worker_wakeup );
  T_pop_fixture();
  
}}

/** @}} */