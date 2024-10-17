/* SPDX-License-Identifier: BSD-2-Clause */

static void Runner( RtemsModelTaskMgr_Context *ctx )
{
  T_log( T_NORMAL, "Runner running" );
  TestSegment1( ctx );
  TestSegment2( ctx );
  T_log( T_NORMAL, "Runner finished" );
}
