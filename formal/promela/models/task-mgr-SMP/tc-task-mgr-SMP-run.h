/**
 * @fn void T_case_body_RtemsEventValSendReceive( void )
 */
T_TEST_CASE( RtemsModelTaskMgrSMP{0} )
{{
  RtemsModelTaskMgrSMP_Run{0}(
    TaskCreate,
    TaskStart,
    TaskDelete,
    TaskSuspend,
    IsTaskSuspended,
    TaskResume,
    TaskSetPriority,
    TaskWakeAfter,
    TaskSetScheduler,
    THREAD_WAIT_CLASS_EVENT,
    STATES_WAITING_FOR_EVENT
  );
}}