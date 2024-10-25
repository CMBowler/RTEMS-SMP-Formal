/**
 * @fn void T_case_body_RtemsEventValSendReceive( void )
 */
T_TEST_CASE( RtemsModelTaskMgr{0} )
{{
  RtemsModelTaskMgr_Run{0}(
    TaskCreate,
    TaskStart,
    TaskDelete,
    TaskSuspend,
    TaskResume,
    THREAD_WAIT_CLASS_EVENT,
    STATES_WAITING_FOR_EVENT
  );
}}