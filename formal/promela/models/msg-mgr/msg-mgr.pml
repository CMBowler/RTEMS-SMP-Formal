/* SPDX-License-Identifier: BSD-2-Clause */

/*
 * msg-mgr.pml
 *
 * Copyright (C) 2022-2024 Trinity College Dublin (www.tcd.ie)
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

#include "../common/rtems.pml"
#define TASK_MAX 4 //three rtems tasks
#define SEMA_MAX 3
#include "../common/model.pml"

// Message queue attributes

#define NULL 0





#define MAX_MESSAGE_QUEUES 3
#define MAX_PENDING_MESSAGES 4
#define MAX_MESSAGE_SIZE 1
#define QUEUE_NAME 1

inline outputDefines() {
    printf("@@@ %d DEF TASK_MAX %d\n",_pid,TASK_MAX);
    printf("@@@ %d DEF BAD_ID %d\n",_pid,BAD_ID);
    printf("@@@ %d DEF SEMA_MAX %d\n",_pid,SEMA_MAX);
    printf("@@@ %d DEF MAX_MESSAGE_SIZE %d\n",_pid, MAX_MESSAGE_SIZE);
    printf("@@@ %d DEF MAX_MESSAGE_QUEUES %d\n",_pid, MAX_MESSAGE_QUEUES);
    printf("@@@ %d DEF MAX_PENDING_MESSAGES %d\n",_pid, MAX_PENDING_MESSAGES);
}

mtype{ MsgWait } ;// need to know when Blocked waiting for message

typedef MsgState{
  int rcvInterval; //how many ticks to wait
  int rcvMsg; //hold value of message received, modelling receive buffer
  int sndMsg; //hold value of message to send, modelling send buffer
  int targetQueue; //queue id for task to interact with
  int numSends; //number of message send calls to make
  int msgSize; //size of message to send
  // Scenario related?
  bool doCreate; // whether to create a queue
  bool doSend; //whether task should send
  bool doReceive; //whether task should receive
  bool doWait; //whether task should wait message
};

MsgState msgstate[TASK_MAX]; // msgstate[0] models a NULL dereference

byte sendrc;            // Sender global variable
byte recrc;             // Receiver global variable
byte qrc              // creation variable
byte recout[TASK_MAX] ; // models receive 'out' location.


typedef Config {
    int name; //An integer is used to represent valid RTEMS_NAME
    int count; //Max messages for a queue
    int maxSize; //Max message size
    mtype attrSet; // RTEMS_ATTRIBUTE_SET, FIFO||priority
};

typedef MessageQueue {
  Config config;
  int messages [MAX_PENDING_MESSAGES] //message circular buffer
  int head; //top of message queue
  int tail; //end of message queue
  bool queueFull; //used to determine full or empty state
  int waitingTasks [TASK_MAX]; //task circular buffer
  int nextTask; //top of task queue
  int lastTask; //end of task queue
  bool taskFull;
};

MessageQueue queueList[MAX_MESSAGE_QUEUES]; //queueList[0] is null

/*
* Helper functions for task
* and message queue operations
*/

inline enqueueTask(id, qid) {
  atomic{
    queueList[qid].waitingTasks[queueList[qid].lastTask] = id;
    if 
    :: queueList[qid].lastTask == TASK_MAX-1 -> queueList[qid].lastTask = 0;
    :: else -> queueList[qid].lastTask++;
    fi
    if
    :: queueList[qid].lastTask == queueList[qid].nextTask -> queueList[qid].taskFull = true;
    :: else -> skip;
    fi
  }
}

inline dequeueTask(id,qid) {
  atomic{
    id = queueList[qid].waitingTasks[queueList[qid].nextTask];
    if 
    :: queueList[qid].nextTask == TASK_MAX-1 -> queueList[qid].nextTask = 0;
    :: else -> queueList[qid].nextTask++;
    fi
    if
    :: queueList[qid].lastTask == queueList[qid].nextTask -> queueList[qid].taskFull = false;
    :: else -> skip;
    fi
  }
}



inline enqueueMessage(id,msg) {
  atomic{
    queueList[id].messages[queueList[id].head] = msg;
   //printf("enqueue message %d", msg);
    if 
    :: queueList[id].head == MAX_PENDING_MESSAGES-1 -> queueList[id].head = 0;
    :: else -> queueList[id].head++;
    fi
    if
    :: queueList[id].head == queueList[id].tail -> queueList[id].queueFull = true;
    :: else -> skip;
    fi
  }
}

inline dequeueMessage(id,msg) {
  atomic{
    msg = queueList[id].messages[queueList[id].tail];
    //printf("dequeue message %d", msg);
    if 
    :: msg == 0 -> skip;
    :: queueList[id].tail == MAX_PENDING_MESSAGES-1 -> queueList[id].tail = 0;
    :: else -> queueList[id].tail++;
    fi
    if
    :: queueList[id].head == queueList[id].tail -> queueList[id].queueFull = false;
    :: else -> skip;
    fi
  }
}


inline sizeOfQueue(id, qsize) {
  atomic{
  if 
  :: queueList[id].head == queueList[id].tail ->
      if
      ::  -> qsize = MAX_PENDING_MESSAGES;
      :: else -> qsize = 0;
      fi
  :: queueList[id].head > queueList[id].tail -> qsize = queueList[id].head - queueList[id].tail;
  :: queueList[id].head < queueList[id].tail -> qsize = MAX_PENDING_MESSAGES + queueList[id].head - queueList[id].tail;
  fi
  return qsize;
  }
}

//Declare needed arrays, variables
inline outputDeclarations () {
  printf("@@@ %d DECL byte sendrc 0\n",_pid);
  printf("@@@ %d DECL byte recrc 0\n",_pid);
  printf("@@@ %d DECL byte qrc 0\n",_pid);
  printf("@@@ %d DECL uint8_t send_counter 0\n",_pid);
  printf("@@@ %d DCLARRAY uint8_t receive_buffer MAX_MESSAGE_SIZE\n",_pid);
  printf("@@@ %d DCLARRAY uint8_t send_buffer MAX_MESSAGE_SIZE\n",_pid);
  printf("@@@ %d DCLARRAY RTEMS_MESSAGE_QUEUE_BUFFER queue_buffer MAX_PENDING_MESSAGES\n",_pid);
  // Rather than refine an entire Task array, we refine array 'slices'
  printf("@@@ %d DCLARRAY byte recout TASK_MAX\n",_pid);
  printf("@@@ %d DCLARRAY Semaphore test_sync_sema SEMA_MAX\n",_pid);
}



/* message_queue_create()
* creates a message queue object from passed parameters
* queue_name -rtems object name
* msg_count - max messages in queue
* max_size - max message size
* rc - return flag
*/

inline message_queue_create(queue_name, msg_count, max_size, rc) {
    atomic{
      //only one queue created
      int qid = 1;
      if
      ::  queue_name == 0 -> rc = RC_InvName;
      ::  max_size == 0 -> rc = RC_InvSize;
      ::  msg_count == 0 -> rc = RC_InvNum;
      ::  else -> 
            queueList[qid].config.count = msg_count;
            queueList[qid].config.maxSize = max_size;
            queueList[qid].queueFull = false;
            queueList[qid].config.name = queue_name;
            rc = RC_OK;
      fi
      ;
  }
}


/*
* message_queue_send
*    self: id of calling task
*    qid: id of queue
*    msg : message
*    size : size of the message
*    rc: return code
*
* This directive will send a message to the to the specficied
* message queue.
*  If there is a task waiting it will copy the message to that tasks
*  buffer and unblock it
*  If there is no task waiting it will ad the message to the message queue
*/

inline message_queue_send(self,qid,msg,size,rc) {
    atomic{
      int queuedTask = queueList[qid].waitingTasks[queueList[qid].nextTask];
      if
      ::  qid == 0 -> rc = RC_InvId;
      ::  else ->
          if
          ::  msg == NULL -> rc = RC_InvAddr;
          ::  size > queueList[qid].config.maxSize -> rc = RC_InvSize;
          ::  queueList[qid].queueFull -> rc = RC_TooMany;
          ::  else ->
              if 
              ::  queuedTask == 0 -> //no task waiting, add to buffer
                  enqueueMessage(qid,msg);
                  printf("@@@ %d LOG Send queueing message\n",_pid)
                  rc = RC_OK;
              ::  else -> //task waiting
                  dequeueTask(queuedTask,qid);
                  enqueueMessage(qid,msg);
                  printf("@@@ %d LOG Send to task %d\n",_pid, queuedTask)
                  //msgstate[queuedTask].rcvMsg = msg;
                  //printf("%d rcv msg %d",_pid,msgstate[queuedTask].rcvMsg)
                  tasks[queuedTask].state = Ready
                  printf("@@@ %d STATE %d Ready\n",_pid, queuedTask)
                  rc = RC_OK;
              fi
          fi
      fi 
    }
}

inline message_queue_receive(self,qid,msg,rc) { 
  int rcvmsg;
  atomic{
    if
    :: qid == 0 -> rc = RC_InvId;
    //:: msg == 0 -> rc = RC_InvAddr
    //:: size >= config.maxSize -> RC_InvSize
    :: else -> 
      dequeueMessage(qid,msg);
      if
      :: msg == 0 && !msgstate[self].doWait -> 
        rc = RC_Unsat; printf("@@@ %d LOG Receive Not Satisfied (no wait)\n",_pid)
      :: msg == 0 && msgstate[self].doWait ->
        printf("@@@ %d LOG Receive Not Satisfied (timeout %d)\n",
                _pid,
                msgstate[self].rcvInterval);
        tasks[self].ticks = msgstate[self].rcvInterval;
        tasks[self].tout = false;
        printf("@@@ %d STATE %d TimeWait %d\n",
                _pid,
                self,
                msgstate[self].rcvInterval);
        tasks[self].state = TimeWait;
        enqueueTask(self,qid);
        waitUntilReady(self);
        
        if
        ::  tasks[self].tout  ->  dequeueTask(self,qid); rc = RC_Timeout; 
        ::  else              -> dequeueMessage(qid,msg);
        fi

      :: else -> rc = RC_OK;
      fi
    fi   
  }
}


/*
 * Model Processes
 * We shall use four processes in this model.
 *  One will represent the RTEMS send task 
 *  Two will represent the RTEMS receive tasks
 *  One will model a timer
 */

// These are not output to test generation
#define SEND_ID 1
#define RCV1_ID 2
#define RCV2_ID 3

/*
 * Sender Scenario
 */
byte sendTarget;
byte msize;
bool sendAgain
int totalSendCount
int currSendCount
/*
 * Receiver Scenario
 */

/*
 * Semaphore Setup
 */
int sendSema;
int rcvSema1;
int startSema;
int rcvSema2;

/*
* Queue setup
*
*/
bool queueCreated;
int queueId;




mtype = {Send,Receive,SndRcv, RcvSnd};

inline chooseScenario() {

  sendAgain = false;
  test_sync_sema[0] = false;
  test_sync_sema[1] = false;
  test_sync_sema[2] = false;
  sendSema = 0;
  rcvSema1 = 1;
  rcvSema2 = 2;
  startSema = sendSema;
  msgstate[SEND_ID].doCreate = true;
  tasks[SEND_ID].state = Ready;
  tasks[RCV1_ID].state = Ready;
  tasks[RCV2_ID].state = Ready;

  //Queue parameters
  queueCreated = false;
  queueId = 1;

  msize = MAX_MESSAGE_SIZE;
  //set up defaults
  msgstate[SEND_ID].numSends = 1;
  msgstate[SEND_ID].sndMsg = 1;
  msgstate[SEND_ID].targetQueue = queueId;
  msgstate[RCV1_ID].targetQueue = queueId;
  msgstate[RCV2_ID].targetQueue = queueId;
  msgstate[SEND_ID].sndMsg = 1;
  msgstate[SEND_ID].msgSize = MAX_MESSAGE_SIZE;


  //select scenario
  if
  ::  scenario = Send;
  ::  scenario = Receive;
  ::  scenario = SndRcv;
  ::  scenario = RcvSnd;
  fi

  atomic{printf("@@@ %d LOG scenario ",_pid); 
  printm(scenario); 
  nl()};


  if
  :: scenario == Send ->
        msgstate[RCV1_ID].doReceive = false;
        msgstate[RCV2_ID].doReceive = false;
        msgstate[SEND_ID].doSend = true;
        if
        ::  msgstate[SEND_ID].targetQueue = 0;
            printf("@@@ %d LOG sub-scenario Send Bad ID\n", _pid)
        ::  msgstate[SEND_ID].targetQueue = queueId;
            printf("@@@ %d LOG sub-scenario Send Success\n", _pid)
        ::  msgstate[SEND_ID].msgSize = MAX_MESSAGE_SIZE + 1;
            printf("@@@ %d LOG sub-scenario Send Size Error\n", _pid)
        ::  msgstate[SEND_ID].sndMsg = 0;
            printf("@@@ %d LOG sub-scenario Buffer Address Error\n", _pid)
        ::  msgstate[SEND_ID].numSends = MAX_PENDING_MESSAGES + 1;
            printf("@@@ %d LOG sub-scenario Too Many messages Error\n", _pid)         
        fi

  :: scenario == Receive ->
        msgstate[SEND_ID].doSend = false;
        msgstate[RCV1_ID].doReceive = true;
        msgstate[RCV2_ID].doReceive = false;
        startSema = rcvSema1;
        
        if
        ::  msgstate[RCV1_ID].doWait = false;
            if
            ::  msgstate[RCV1_ID].targetQueue = 0;
                printf("@@@ %d LOG sub-scenario Rcv Bad ID No Wait\n", _pid)
            ::  msgstate[SEND_ID].targetQueue = queueId;
                printf("@@@ %d LOG sub-scenario Rcv Success No Wait\n", _pid, msgstate[RCV1_ID].doWait, msgstate[RCV1_ID].rcvInterval)
            fi 
        ::  msgstate[RCV1_ID].doWait = true; msgstate[RCV1_ID].rcvInterval = 5;
            printf("@@@ %d LOG sub-scenario Rcv Success wait:%d interval:%d\n", _pid, msgstate[RCV1_ID].doWait, msgstate[RCV1_ID].rcvInterval)
        fi
        
        /*
        if
        ::  msgstate[RCV2_ID].doWait = false;  
        ::  msgstate[RCV2_ID].doWait = true; msgstate[RCV2_ID].rcvInterval = 5;
        fi
        printf("@@@ %d LOG sub-scenario Receive2 wait:%d interval:%d\n", _pid, msgstate[RCV2_ID].doWait, msgstate[RCV2_ID].rcvInterval)
        */

  :: scenario == SndRcv ->

        if
        ::  msgstate[SEND_ID].numSends = 2;     
        ::  msgstate[SEND_ID].numSends = 1;
        fi
        printf("@@@ %d LOG sub-scenario SndRcv numSends:%d\n", 
                _pid, 
                msgstate[SEND_ID].numSends
                )
        /* 
        if
        ::  msgstate[RCV1_ID].doWait = false;      
        ::  msgstate[RCV1_ID].doWait = true; msgstate[RCV1_ID].rcvInterval = 5;
        fi
        printf("@@@ %d LOG sub-scenario Receive1 wait:%d interval:%d\n", _pid, msgstate[RCV1_ID].doWait, msgstate[RCV1_ID].rcvInterval)
        if
        ::  msgstate[RCV2_ID].doWait = false;      
        ::  msgstate[RCV2_ID].doWait = true; msgstate[RCV2_ID].rcvInterval = 5;
        fi
        printf("@@@ %d LOG sub-scenario Receive2 wait:%d interval:%d\n", _pid, msgstate[RCV2_ID].doWait, msgstate[RCV2_ID].rcvInterval)
        */
        
        msgstate[SEND_ID].doSend = true;
        msgstate[RCV1_ID].doReceive = true;
        msgstate[RCV2_ID].doReceive = true;

  :: scenario == RcvSnd ->
        startSema = rcvSema1;
        msgstate[SEND_ID].doSend = true;
        msgstate[RCV1_ID].doReceive = true;
        msgstate[RCV1_ID].doWait = true;
        msgstate[RCV1_ID].rcvInterval = 5;
        msgstate[RCV2_ID].doReceive = false;
        //msgstate[SEND_ID].numSends = 2
        /*
        if
        :: msgstate[RCV1_ID].doWait = false; msgstate[RCV2_ID].doWait = false;
        :: msgstate[RCV1_ID].doWait = true;  msgstate[RCV2_ID].doWait = true; msgstate[RCV1_ID].rcvInterval = 10; msgstate[RCV2_ID].rcvInterval = 10;
        fi
        printf("@@@ %d LOG sub-scenario RcvSnd wait:%d interval:%d\n", _pid, msgstate[RCV1_ID].doWait, msgstate[RCV1_ID].rcvInterval)
        */

  fi
}


proctype Sender (byte taskid) {

  tasks[taskid].pmlid = _pid;
  tasks[taskid].state = Ready;
  printf("@@@ %d TASK Runner\n",_pid,taskid);
  
  if 
  ::  (msgstate[taskid].doCreate && !queueCreated) ->
      printf("@@@ %d CALL message_queue_construct %d %d %d %d %d qrc\n", _pid, 
              taskid, 
              QUEUE_NAME,
              MAX_PENDING_MESSAGES, 
              MAX_MESSAGE_SIZE, 
              queueId);
      message_queue_create(QUEUE_NAME, 
                            MAX_PENDING_MESSAGES, 
                            MAX_MESSAGE_SIZE, 
                            qrc);
      printf("@@@ %d SCALAR qrc %d\n",_pid,qrc);
      queueCreated = true;
      TestSyncRelease(startSema);
  fi
  
  if
  :: msgstate[taskid].doSend -> 
      TestSyncObtain(sendSema);
      repeat:
      atomic{
      printf("@@@ %d CALL message_queue_send %d %d %d %d sendrc\n",
              _pid,
              taskid, 
              msgstate[taskid].targetQueue, 
              msgstate[taskid].sndMsg, 
              msgstate[taskid].msgSize);
      message_queue_send(taskid,
                          msgstate[taskid].targetQueue,
                          msgstate[taskid].sndMsg,
                          msgstate[taskid].msgSize,
                          sendrc);
      printf("@@@ %d SCALAR sendrc %d\n",_pid,sendrc);
      msgstate[taskid].numSends-- ;
      if
      :: msgstate[taskid].numSends != 0 -> msgstate[SEND_ID].sndMsg++; goto repeat; 
      :: scenario == RcvSnd -> skip;
      :: else -> TestSyncRelease(rcvSema1);
      fi
      }
  :: else -> skip;
  fi


  //adjust semaphore behaviour for RcvSnd as Receive1 starts
  if 
  :: scenario == RcvSnd -> 
        TestSyncObtain(rcvSema1);
        TestSyncObtain(rcvSema2);
  :: else ->         
        TestSyncObtain(sendSema);
        TestSyncObtain(rcvSema2);
        TestSyncObtain(rcvSema1);
  fi
  
  printf("@@@ %d LOG Sender %d finished\n",_pid,taskid);
  tasks[taskid].state = Zombie;
  printf("@@@ %d STATE %d Zombie\n",_pid,taskid);
}

proctype Receiver1 (byte taskid) {

  tasks[taskid].pmlid = _pid;
  tasks[taskid].state = Ready;
  printf("@@@ %d TASK Worker1\n",_pid);

  
  TestSyncObtain(rcvSema1);

  if
  :: msgstate[taskid].doReceive && scenario != RcvSnd->
      atomic{
      printf("@@@ %d CALL message_queue_receive %d %d %d %d recrc\n",
              _pid,taskid,
              msgstate[taskid].targetQueue,
              msgstate[taskid].doWait,
              msgstate[taskid].rcvInterval);
      message_queue_receive(taskid,
                              msgstate[taskid].targetQueue,
                              msgstate[taskid].rcvMsg,
                              recrc);
      printf("@@@ %d LOG received %d\n", _pid,msgstate[taskid].rcvMsg);
      printf("@@@ %d SCALAR recrc %d\n",_pid,recrc);
      TestSyncRelease(rcvSema2);
      }   
  :: msgstate[taskid].doReceive && scenario == RcvSnd->
      atomic{
      TestSyncRelease(sendSema);
      printf("@@@ %d CALL message_queue_receive %d %d %d %d recrc\n",
                _pid,
                taskid,
                msgstate[taskid].targetQueue,
                msgstate[taskid].doWait,
                msgstate[taskid].rcvInterval);
      message_queue_receive(taskid,
                              msgstate[taskid].targetQueue,
                              msgstate[taskid].rcvMsg,
                              recrc);
      printf("@@@ %d LOG received %d\n", _pid,msgstate[taskid].rcvMsg);
      printf("@@@ %d SCALAR recrc %d\n",_pid,recrc);
      }
  :: else -> TestSyncRelease(rcvSema2); 
  fi

 

  atomic{
  TestSyncRelease(rcvSema1);
  printf("@@@ %d LOG Receiver1 %d finished\n",_pid,taskid);
  tasks[taskid].state = Zombie;
  printf("@@@ %d STATE %d Zombie\n",_pid,taskid)
  }
}

proctype Receiver2 (byte taskid) {

  tasks[taskid].pmlid = _pid;
  tasks[taskid].state = Ready;
  printf("@@@ %d TASK Worker2\n",_pid);
  
  if
  :: scenario == RcvSnd ->
      goto rcvSkip;
  :: else -> TestSyncObtain(rcvSema2);
  fi
  
  
  if
  :: msgstate[taskid].doReceive && scenario != RcvSnd-> 
      atomic{
      printf("@@@ %d CALL message_queue_receive %d %d %d %d recrc\n",
              _pid,
              taskid,
              msgstate[taskid].targetQueue,
              msgstate[taskid].doWait,
              msgstate[taskid].rcvInterval);
      message_queue_receive(taskid,msgstate[taskid].targetQueue,msgstate[taskid].rcvMsg,recrc);
      printf("@@@ %d LOG received %d\n", _pid,msgstate[taskid].rcvMsg);
      printf("@@@ %d SCALAR recrc %d\n",_pid,recrc);
      TestSyncRelease(sendSema);
      }
  :: msgstate[taskid].doReceive && scenario == RcvSnd->
      atomic{
      printf("@@@ %d CALL message_queue_receive %d %d %d %d recrc\n",
              _pid,
              taskid,msgstate[taskid].targetQueue,
              msgstate[taskid].doWait,
              msgstate[taskid].rcvInterval);
      TestSyncRelease(sendSema);
      message_queue_receive(taskid,msgstate[taskid].targetQueue,msgstate[taskid].rcvMsg,recrc);
      printf("@@@ %d LOG received %d\n", _pid,msgstate[taskid].rcvMsg);
      printf("@@@ %d SCALAR recrc %d\n",_pid,recrc);
      }
  :: else -> TestSyncRelease(sendSema);
  fi

  rcvSkip:
  atomic{
  TestSyncRelease(rcvSema2);
  printf("@@@ %d LOG Receiver2 %d finished\n",_pid,taskid);
  tasks[taskid].state = Zombie;
  printf("@@@ %d STATE %d Zombie\n",_pid,taskid)
  }
}

init {
  pid nr;

  printf("Message Manager Model running.\n");
  printf("Setup...\n");
  
  printf("@@@ %d NAME Message_Manager_TestGen\n",_pid)
  //#define required in test file
  outputDefines();
  //Structures and data types required in test file
  outputDeclarations();

  printf("@@@ %d INIT\n",_pid);
  chooseScenario();

  printf("Run...\n");
  //start nececssary processes
  run System();
  run Clock();
  
  run Sender(SEND_ID);
  run Receiver1(RCV1_ID);
  run Receiver2(RCV2_ID);
  
  _nr_pr == 1;

#ifdef TEST_GEN
  assert(false);
#endif


printf("Message Manager Model finished !\n")
}