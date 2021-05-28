/**
  @file

  @ingroup cudd

  @brief Functions for %BDD and %ADD reduction by linear
  transformations.

  @author Fabio Somenzi

  @copyright@parblock
  Copyright (c) 1995-2015, Regents of the University of Colorado

  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions
  are met:

  Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

  Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

  Neither the name of the University of Colorado nor the names of its
  contributors may be used to endorse or promote products derived from
  this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
  COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
  LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
  LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
  ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
  POSSIBILITY OF SUCH DAMAGE.
  @endparblock

*/

#include "util.h"
#include "cuddInt.h"

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

#define CUDD_SWAP_MOVE 0
#define CUDD_LINEAR_TRANSFORM_MOVE 1
#define CUDD_INVERSE_TRANSFORM_MOVE 2
#if SIZEOF_VOID_P == 8
#define BPL 64
#define LOGBPL 6
#else
#define BPL 32
#define LOGBPL 5
#endif

/*---------------------------------------------------------------------------*/
/* Stucture declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/** \cond */

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static int ddLinearUniqueCompare (void const *ptrX, void const *ptrY);
static int ddLinearAndSiftingAux (DdManager *table, int x, int xLow, int xHigh);
static Move * ddLinearAndSiftingUp (DdManager *table, int y, int xLow, Move *prevMoves);
static Move * ddLinearAndSiftingDown (DdManager *table, int x, int xHigh, Move *prevMoves);
static int ddLinearAndSiftingBackward (DdManager *table, int size, Move *moves);
static Move* ddUndoMoves (DdManager *table, Move *moves);
static void cuddXorLinear (DdManager *table, int x, int y);

/** \endcond */


/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/


/**
  @brief Prints the linear transform matrix.

  @return 1 in case of success; 0 otherwise.

  @sideeffect none

*/
int
Cudd_PrintLinear(
  DdManager * table)
{
    int i,j,k;
    int retval;
    int nvars = table->linearSize;
    int wordsPerRow = ((nvars - 1) >> LOGBPL) + 1;
    ptruint word;

    for (i = 0; i < nvars; i++) {
	for (j = 0; j < wordsPerRow; j++) {
	    word = table->linear[i*wordsPerRow + j];
	    for (k = 0; k < BPL; k++) {
              retval = fprintf(table->out,"%" PRIuPTR,word & (ptruint) 1);
		if (retval == 0) return(0);
		word >>= 1;
	    }
	}
	retval = fprintf(table->out,"\n");
	if (retval == 0) return(0);
    }
    return(1);

} /* end of Cudd_PrintLinear */


/**
  @brief Reads an entry of the linear transform matrix.

  @sideeffect none

*/
int
Cudd_ReadLinear(
  DdManager * table /**< CUDD manager */,
  int  x /**< row index */,
  int  y /**< column index */)
{
    int nvars = table->size;
    ptruint wordsPerRow = ((ptruint)(nvars - 1) >> LOGBPL) + 1;
    ptruint word;
    int bit;
    int result;

    assert(table->size == table->linearSize);

    word = wordsPerRow * (ptruint) x + ((ptruint) y >> LOGBPL);
    bit  = y & (BPL-1);
    result = (int) ((table->linear[word] >> bit) & (ptruint) 1);
    return(result);

} /* end of Cudd_ReadLinear */


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/


/**
  @brief %BDD reduction based on combination of sifting and linear
  transformations.

  @details Assumes that no dead nodes are present.
    <ol>
    <li> Order all the variables according to the number of entries
    in each unique table.
    <li> Sift the variable up and down, remembering each time the
    total size of the %DD heap. At each position, linear transformation
    of the two adjacent variables is tried and is accepted if it reduces
    the size of the %DD.
    <li> Select the best permutation.
    <li> Repeat 3 and 4 for all variables.
    </ol>

  @return 1 if successful; 0 otherwise.

  @sideeffect None

*/
int
cuddLinearAndSifting(
  DdManager * table,
  int  lower,
  int  upper)
{
    int		i;
    IndexKey	*var;
    int		size;
    int		x;
    int		result;
#ifdef DD_STATS
    int		previousSize;
#endif

#ifdef DD_STATS
    table->totalNumberLinearTr = 0;
#endif

    size = table->size; //变量数

    var = NULL;
    if (table->linear == NULL) { //在这里就是判断变换矩阵创建了没有
	result = cuddInitLinear(table); //没有就初始化一个
	if (result == 0) goto cuddLinearAndSiftingOutOfMem;
#if 0
	(void) fprintf(table->out,"\n");
	result = Cudd_PrintLinear(table);
	if (result == 0) goto cuddLinearAndSiftingOutOfMem;
#endif
    } else if (table->size != table->linearSize) { //判断子表(变量)的数目和变换矩阵的行列数是否一致
	result = cuddResizeLinear(table); //不一致就resize变换矩阵
	if (result == 0) goto cuddLinearAndSiftingOutOfMem;
#if 0
	(void) fprintf(table->out,"\n");
	result = Cudd_PrintLinear(table);
	if (result == 0) goto cuddLinearAndSiftingOutOfMem;
#endif
    }

    /* Find order in which to sift variables. */
    var = ALLOC(IndexKey,size); //新建一条用于排序的变量链
    if (var == NULL) {
	table->errorCode = CUDD_MEMORY_OUT;
	goto cuddLinearAndSiftingOutOfMem;
    }

    for (i = 0; i < size; i++) { //给变量链赋值
	x = table->perm[i]; //取出在排列中第i个变量(相当于BDD的第i层的变量是什么)
	var[i].index = i; //给要排序的变量附上index
	var[i].keys = table->subtables[x].keys; //给每个要排序的变量附上对应的keys(这个变量拥有的结点数量)
    }

    util_qsort(var,size,sizeof(IndexKey),ddLinearUniqueCompare); //对变量进行快排,排序标准:结点数相近的变量放一起

    /* Now sift. */
    for (i = 0; i < ddMin(table->siftMaxVar,size); i++) { //确定参与sift的变量个数
	x = table->perm[var[i].index]; //把在var的变量一个个拿出来
	if (x < lower || x > upper) continue; //检测没有超过边界
#ifdef DD_STATS
	previousSize = (int) (table->keys - table->isolated);
#endif
	result = ddLinearAndSiftingAux(table,x,lower,upper); //传进当前选中的变量,在边界范围内上下swap
	if (!result) goto cuddLinearAndSiftingOutOfMem;
#ifdef DD_STATS
	if (table->keys < (unsigned) previousSize + table->isolated) {
	    (void) fprintf(table->out,"-");
	} else if (table->keys > (unsigned) previousSize + table->isolated) {
	    (void) fprintf(table->out,"+");	/* should never happen */
	    (void) fprintf(table->out,"\nSize increased from %d to %u while sifting variable %d\n", previousSize, table->keys - table->isolated, var[i].index);
	} else {
	    (void) fprintf(table->out,"=");
	}
	fflush(table->out);
#endif
#ifdef DD_DEBUG
	(void) Cudd_DebugCheck(table);
#endif
    }

    FREE(var);

#ifdef DD_STATS
    (void) fprintf(table->out,"\n#:L_LINSIFT %8d: linear trans.",
		   table->totalNumberLinearTr);
#endif

    return(1);

cuddLinearAndSiftingOutOfMem:

    if (var != NULL) FREE(var);

    return(0);

} /* end of cuddLinearAndSifting */


/**
  @brief Linearly combines two adjacent variables.

  @details Specifically, replaces the top variable with the exclusive
  nor of the two variables.  It assumes that no dead nodes are present
  on entry to this procedure.  The procedure then guarantees that no
  dead nodes will be present when it terminates.  cuddLinearInPlace
  assumes that x &lt; y.

  @return the number of keys in the table if successful; 0 otherwise.

  @sideeffect The two subtables corrresponding to variables x and y are
  modified. The global counters of the unique table are also affected.

  @see cuddSwapInPlace

*/
int
cuddLinearInPlace(
  DdManager * table,
  int  x,
  int  y)
{
    DdNodePtr *xlist, *ylist;
    int    xindex, yindex;
    int    xslots, yslots;
    int    xshift, yshift;
#if defined(DD_COUNT) || defined(DD_DEBUG)
    int    oldxkeys;
#endif
    int oldykeys;
    int    newxkeys, newykeys;
    int    comple, newcomplement;
    int    i;
    int    posn;
    int    isolated;
    DdNode *f,*f0,*f1,*f01,*f00,*f11,*f10,*newf1,*newf0;
    DdNode *g,*next,*last=NULL;
    DdNodePtr *previousP;
    DdNode *tmp;
    DdNode *sentinel = &(table->sentinel);
#ifdef DD_DEBUG
    int    count, idcheck;
#endif

#ifdef DD_DEBUG
    assert(x < y);
    assert(cuddNextHigh(table,x) == y);
    assert(table->subtables[x].keys != 0);
    assert(table->subtables[y].keys != 0);
    assert(table->subtables[x].dead == 0);
    assert(table->subtables[y].dead == 0);
#endif

    xindex = table->invperm[x]; //取出要处理变量的index
    yindex = table->invperm[y];

    if (cuddTestInteract(table,xindex,yindex)) { //只对interact的变量进行LT(显然)
#ifdef DD_STATS
	table->totalNumberLinearTr++;
#endif
	/* Get parameters of x subtable. */
	xlist = table->subtables[x].nodelist; //把x结点链取出
#if defined(DD_COUNT) || defined(DD_DEBUG)
	oldxkeys = table->subtables[x].keys;
#endif
	xslots = table->subtables[x].slots; //x子表的槽数
	xshift = table->subtables[x].shift; //x的哈希辅助

	/* Get parameters of y subtable. */
	ylist = table->subtables[y].nodelist;
	oldykeys = table->subtables[y].keys;
	yslots = table->subtables[y].slots;
	yshift = table->subtables[y].shift;

	newxkeys = 0; //因为x子表是要重建的
	newykeys = oldykeys; //y子表不用变化

	/* Check whether the two projection functions involved in this
	** swap are isolated. At the end, we'll be able to tell how many
	** isolated projection functions are there by checking only these
	** two functions again. This is done to eliminate the isolated
	** projection functions from the node count.
	*/
	isolated = - ((table->vars[xindex]->ref == 1) +
		     (table->vars[yindex]->ref == 1)); //暂时对孤立结点处理

	/* The nodes in the x layer are put in a chain.
	** The chain is handled as a FIFO; g points to the beginning and
	** last points to the end.
	*/
	g = NULL; //g链存放x结点,先进先出链,g指针保持在链头,last指针保持在链尾
#ifdef DD_DEBUG
	last = NULL;
#endif
	for (i = 0; i < xslots; i++) { //遍历x子表的各个槽
	    f = xlist[i];
	    if (f == sentinel) continue;
	    xlist[i] = sentinel; //因为x子表要重建,所以各个冲突链都要摘掉
	    if (g == NULL) { //把摘出来的x结点放在g链
		g = f;
	    } else {
		last->next = f; //插在g链的尾部
	    }
	    while ((next = f->next) != sentinel) { //每条冲突链只拿第一个结点
		f = next;
	    } /* while there are elements in the collision chain */
	    last = f;
	} /* for each slot of the x subtable */
	//到这里就把x子表的每个槽的第一个结点拿出来,并且x子表只留下槽位,内容清零了.x子表每条冲突链的第一个结点都放在g链上
#ifdef DD_DEBUG
	/* last is always assigned in the for loop because there is at
	** least one key */
	assert(last != NULL);
#endif
	last->next = NULL; //最后一个结点的下一个指针指向null

#ifdef DD_COUNT
	table->swapSteps += oldxkeys;
#endif
	/* Take care of the x nodes that must be re-expressed.
	** They form a linked list pointed by g.
	*/
	f = g; //开始对g链处理
	while (f != NULL) { //把g链的结点逐个拿出来
	    next = f->next;
	    /* Find f1, f0, f11, f10, f01, f00. */
	    f1 = cuddT(f); //拿出x结点的f1孩子
#ifdef DD_DEBUG
	    assert(!(Cudd_IsComplement(f1)));
#endif
	    if ((int) f1->index == yindex) { //如果x结点的f1孩子y结点
		f11 = cuddT(f1); f10 = cuddE(f1);
	    } else {
		f11 = f10 = f1;
	    }
#ifdef DD_DEBUG
	    assert(!(Cudd_IsComplement(f11)));
#endif
	    f0 = cuddE(f); //x结点的0孩子
	    comple = Cudd_IsComplement(f0);
	    f0 = Cudd_Regular(f0);
	    if ((int) f0->index == yindex) {
		f01 = cuddT(f0); f00 = cuddE(f0);
	    } else {
		f01 = f00 = f0;
	    }
	    if (comple) {
		f01 = Cudd_Not(f01);
		f00 = Cudd_Not(f00);
	    }
	    /* Decrease ref count of f1. */
	    cuddSatDec(f1->ref); //断开x结点的1边
	    /* Create the new T child. */
	    if (f11 == f00) { //如果f11和f00相等的话，说明f1可以约减
		newf1 = f11;
		cuddSatInc(newf1->ref); //增加引用计数
	    } else {
		/* Check ylist for triple (yindex,f11,f00). */
		posn = ddHash(f11, f00, yshift); //找有没有现存的y结点可以做f1结点
		/* For each element newf1 in collision list ylist[posn]. */
		previousP = &(ylist[posn]);
		newf1 = *previousP;
		while (f11 < cuddT(newf1)) {
		    previousP = &(newf1->next);
		    newf1 = *previousP;
		}
		while (f11 == cuddT(newf1) && f00 < cuddE(newf1)) {
		    previousP = &(newf1->next);
		    newf1 = *previousP;
		}
		if (cuddT(newf1) == f11 && cuddE(newf1) == f00) { //这里是找到现存的y结点可以做f1
		    cuddSatInc(newf1->ref);
		} else { /* no match */ //找不到的话,创建一颗新的y结点做f1结点
		    newf1 = cuddDynamicAllocNode(table);
		    if (newf1 == NULL)
			goto cuddLinearOutOfMem;
		    newf1->index = yindex; newf1->ref = 1;
		    cuddT(newf1) = f11;
		    cuddE(newf1) = f00;
		    /* Insert newf1 in the collision list ylist[posn];
		    ** increase the ref counts of f11 and f00.
		    */
		    newykeys++; //结点数加1
		    newf1->next = *previousP; //把这颗新的y结点插入到冲突链的链尾
		    *previousP = newf1; //更新队尾指针位置
		    cuddSatInc(f11->ref); //f1的两个孩子引用要加1
		    tmp = Cudd_Regular(f00);
		    cuddSatInc(tmp->ref);
		}
	    } //到这里f结点(g链上的一颗结点(x结点))的f1孩子就处理完成了
	    cuddT(f) = newf1; //把处理好的f1结点作为f的1孩子
#ifdef DD_DEBUG
	    assert(!(Cudd_IsComplement(newf1)));
#endif
		//下面就是同样的过程处理f0结点
	    /* Do the same for f0, keeping complement dots into account. */
	    /* decrease ref count of f0 */
	    tmp = Cudd_Regular(f0);
	    cuddSatDec(tmp->ref);
	    /* create the new E child */
	    if (f01 == f10) {
		newf0 = f01;
		tmp = Cudd_Regular(newf0);
		cuddSatInc(tmp->ref);
	    } else {
		/* make sure f01 is regular */
		newcomplement = Cudd_IsComplement(f01);
		if (newcomplement) {
		    f01 = Cudd_Not(f01);
		    f10 = Cudd_Not(f10);
		}
		/* Check ylist for triple (yindex,f01,f10). */
		posn = ddHash(f01, f10, yshift);
		/* For each element newf0 in collision list ylist[posn]. */
		previousP = &(ylist[posn]);
		newf0 = *previousP;
		while (f01 < cuddT(newf0)) {
		    previousP = &(newf0->next);
		    newf0 = *previousP;
		}
		while (f01 == cuddT(newf0) && f10 < cuddE(newf0)) {
		    previousP = &(newf0->next);
		    newf0 = *previousP;
		}
		if (cuddT(newf0) == f01 && cuddE(newf0) == f10) {
		    cuddSatInc(newf0->ref);
		} else { /* no match */
		    newf0 = cuddDynamicAllocNode(table);
		    if (newf0 == NULL)
			goto cuddLinearOutOfMem;
		    newf0->index = yindex; newf0->ref = 1;
		    cuddT(newf0) = f01;
		    cuddE(newf0) = f10;
		    /* Insert newf0 in the collision list ylist[posn];
		    ** increase the ref counts of f01 and f10.
		    */
		    newykeys++;
		    newf0->next = *previousP;
		    *previousP = newf0;
		    cuddSatInc(f01->ref);
		    tmp = Cudd_Regular(f10);
		    cuddSatInc(tmp->ref);
		}
		if (newcomplement) {
		    newf0 = Cudd_Not(newf0);
		}
	    }
	    cuddE(f) = newf0; //把处理好的f0结点作为f的0孩子

	    /* Re-insert the modified f in xlist.
	    ** The modified f does not already exists in xlist.
	    ** (Because of the uniqueness of the cofactors.)
	    */
	    //把这颗处理完(包括结点的孩子)的f结点(x结点),放入到之前已经清空内容只保留槽位的x子表上
	    posn = ddHash(newf1, newf0, xshift);
	    newxkeys++;
	    previousP = &(xlist[posn]);
	    tmp = *previousP;
	    while (newf1 < cuddT(tmp)) { //寻找合适位置
		previousP = &(tmp->next);
		tmp = *previousP;
	    }
	    while (newf1 == cuddT(tmp) && newf0 < cuddE(tmp)) { //寻找合适位置
		previousP = &(tmp->next);
		tmp = *previousP;
	    }
	    f->next = *previousP; //把结点插入到子表的冲突链中
	    *previousP = f; //调整队尾指针位置
	    f = next; //接着处理下一个结点
	} /* while f != NULL */
	//到这里,放在g链中的x结点已经重新处理并放回x子表上

	/* GC the y layer. */

	/* For each node f in ylist. */
	//这里把y子表中引用为0的y结点给释放掉
	for (i = 0; i < yslots; i++) {
	    previousP = &(ylist[i]);
	    f = *previousP;
	    while (f != sentinel) {
		next = f->next;
		if (f->ref == 0) { //释放y结点的操作,包括对它孩子结点的引用计数减1
		    tmp = cuddT(f);
		    cuddSatDec(tmp->ref);
		    tmp = Cudd_Regular(cuddE(f));
		    cuddSatDec(tmp->ref);
		    cuddDeallocNode(table,f);
		    newykeys--;
		} else {
		    *previousP = f;
		    previousP = &(f->next);
		}
		f = next;
	    } /* while f */
	    *previousP = sentinel;
	} /* for every collision list */

#ifdef DD_DEBUG
#if 0
	(void) fprintf(table->out,"Linearly combining %d and %d\n",x,y);
#endif
	count = 0;
	idcheck = 0;
	for (i = 0; i < yslots; i++) {
	    f = ylist[i];
	    while (f != sentinel) {
		count++;
		if (f->index != (DdHalfWord) yindex)
		    idcheck++;
		f = f->next;
	    }
	}
	if (count != newykeys) {
	    fprintf(table->err,"Error in finding newykeys\toldykeys = %d\tnewykeys = %d\tactual = %d\n",oldykeys,newykeys,count);
	}
	if (idcheck != 0)
	    fprintf(table->err,"Error in id's of ylist\twrong id's = %d\n",idcheck);
	count = 0;
	idcheck = 0;
	for (i = 0; i < xslots; i++) {
	    f = xlist[i];
	    while (f != sentinel) {
		count++;
		if (f->index != (DdHalfWord) xindex)
		    idcheck++;
		f = f->next;
	    }
	}
	if (count != newxkeys || newxkeys != oldxkeys) {
	    fprintf(table->err,"Error in finding newxkeys\toldxkeys = %d \tnewxkeys = %d \tactual = %d\n",oldxkeys,newxkeys,count);
	}
	if (idcheck != 0)
	    fprintf(table->err,"Error in id's of xlist\twrong id's = %d\n",idcheck);
#endif

	isolated += (table->vars[xindex]->ref == 1) +
		    (table->vars[yindex]->ref == 1); //计算本次操作产生的孤立结点个数
	table->isolated += (unsigned int) isolated; //更新唯一表(总表)中的孤立结点数目

	/* Set the appropriate fields in table. */
	table->subtables[y].keys = newykeys; //更新y子表的结点个数

	/* Here we should update the linear combination table
	** to record that x <- x EXNOR y. This is done by complementing
	** the (x,y) entry of the table.
	*/

	table->keys += newykeys - oldykeys; //更新总表(唯一表)的总结点个数

	cuddXorLinear(table,xindex,yindex); //更新线性矩阵
    }

#ifdef DD_DEBUG
    if (table->enableExtraDebug) {
	(void) Cudd_DebugCheck(table);
    }
#endif

    return((int) (table->keys - table->isolated));

cuddLinearOutOfMem:
    (void) fprintf(table->err,"Error: cuddLinearInPlace out of memory\n");

    return (0);

} /* end of cuddLinearInPlace */


/**
  @brief Updates the interaction matrix.

  @sideeffect none

*/
void
cuddUpdateInteractionMatrix(
  DdManager * table,
  int  xindex,
  int  yindex)
{
    int i;
    for (i = 0; i < yindex; i++) {
	if (i != xindex && cuddTestInteract(table,i,yindex)) {
	    if (i < xindex) {
		cuddSetInteract(table,i,xindex);
	    } else {
		cuddSetInteract(table,xindex,i);
	    }
	}
    }
    for (i = yindex+1; i < table->size; i++) {
	if (i != xindex && cuddTestInteract(table,yindex,i)) {
	    if (i < xindex) {
		cuddSetInteract(table,i,xindex);
	    } else {
		cuddSetInteract(table,xindex,i);
	    }
	}
    }

} /* end of cuddUpdateInteractionMatrix */


/**
  @brief Initializes the linear transform matrix.

  @return 1 if successful; 0 otherwise.

  @sideeffect none

*/
int
cuddInitLinear(
  DdManager * table)
{
    int words; //words*64(32)就是矩阵的单元数,其实是用bit表示单元,一个字有64(32)个bit
    int wordsPerRow; //矩阵每行的变量数
    int nvars; //子表的数量，那就是变量的个数
    int word; 
    int bit;
    int i;
    ptruint *linear;

    nvars = table->size; //子表的数量,变量的数量
    wordsPerRow = ((nvars - 1) >> LOGBPL) + 1; //算出每一行要多少个字,因为每个bit是代表一个变量
    words = wordsPerRow * nvars; //列*行,算出总共要多少个字
    table->linear = linear = ALLOC(ptruint,words); //用一维空间来表示矩阵,分配空间
    if (linear == NULL) {
    table->errorCode = CUDD_MEMORY_OUT;
    return(0);
    }
    table->memused += words * sizeof(ptruint); //这个是更新ddmanger的内存占用
    table->linearSize = nvars; //更新ddm的矩阵的行数(列数是多少个bit表示)
    for (i = 0; i < words; i++) linear[i] = 0; //把矩阵所有单元都置0
    for (i = 0; i < nvars; i++) { //对矩阵每行进行处理
	word = wordsPerRow * i + (i >> LOGBPL); //这是算它对第几个字进行赋值
	bit  = i & (BPL-1); //这是算它在字里面的哪一个位赋值
	linear[word] = (ptruint) 1 << bit; //对矩阵进行赋值
    }
    return(1); //初始化成功后的矩阵应该是对角线为一的规范矩阵

} /* end of cuddInitLinear */


/**
  @brief Resizes the linear transform matrix.

  @return 1 if successful; 0 otherwise.

  @sideeffect none

*/
int
cuddResizeLinear(
  DdManager * table)
{
    int words,oldWords;
    int wordsPerRow,oldWordsPerRow;
    int nvars,oldNvars;
    int word,oldWord;
    int bit;
    int i,j;
    ptruint *linear,*oldLinear;

    oldNvars = table->linearSize;
    oldWordsPerRow = ((oldNvars - 1) >> LOGBPL) + 1;
    oldWords = oldWordsPerRow * oldNvars;
    oldLinear = table->linear;

    nvars = table->size;
    wordsPerRow = ((nvars - 1) >> LOGBPL) + 1;
    words = wordsPerRow * nvars;
    table->linear = linear = ALLOC(ptruint,words);
    if (linear == NULL) {
	table->errorCode = CUDD_MEMORY_OUT;
	return(0);
    }
    table->memused += (words - oldWords) * sizeof(ptruint);
    for (i = 0; i < words; i++) linear[i] = 0;

    /* Copy old matrix. */
    for (i = 0; i < oldNvars; i++) {
	for (j = 0; j < oldWordsPerRow; j++) {
	    oldWord = oldWordsPerRow * i + j;
	    word = wordsPerRow * i + j;
	    linear[word] = oldLinear[oldWord];
	}
    }
    FREE(oldLinear);

    /* Add elements to the diagonal. */
    for (i = oldNvars; i < nvars; i++) {
	word = wordsPerRow * i + (i >> LOGBPL);
	bit  = i & (BPL-1);
	linear[word] = (ptruint) 1 << bit;
    }
    table->linearSize = nvars;

    return(1);

} /* end of cuddResizeLinear */


/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/


/**
  @brief Comparison function used by qsort.

  @details Comparison function used by qsort to order the
  variables according to the number of keys in the subtables.

  @return the difference in number of keys between the two variables
  being compared.

  @sideeffect None

*/
static int
ddLinearUniqueCompare(
  void const * ptrX,
  void const * ptrY)
{
    IndexKey const * pX = (IndexKey const *) ptrX;
    IndexKey const * pY = (IndexKey const *) ptrY;
#if 0
    if (pY->keys == pX->keys) {
	return(pX->index - pY->index);
    }
#endif
    return(pY->keys - pX->keys);

} /* end of ddLinearUniqueCompare */


/**
  @brief Given xLow <= x <= xHigh moves x up and down between the
  boundaries.

  @details At each step a linear transformation is tried, and, if it
  decreases the size of the %DD, it is accepted. Finds the best position
  and does the required changes.

  @return 1 if successful; 0 otherwise.

  @sideeffect None

*/
static int
ddLinearAndSiftingAux(
  DdManager * table,
  int  x,
  int  xLow,
  int  xHigh)
{

    Move	*move;
    Move	*moveUp;		/* list of up moves */
    Move	*moveDown;		/* list of down moves */
    int		initialSize;
    int		result;

    initialSize = (int) (table->keys - table->isolated); //整个表的结点数-整个表的孤立结点数

    moveDown = NULL;
    moveUp = NULL;

    if (x == xLow) { //选中的变量就是低边界变量
	moveDown = ddLinearAndSiftingDown(table,x,xHigh,NULL); //选中变量往高边界走
	/* At this point x --> xHigh unless bounding occurred. */
	if (moveDown == (Move *) CUDD_OUT_OF_MEM) goto ddLinearAndSiftingAuxOutOfMem;
	/* Move backward and stop at best position. */
	result = ddLinearAndSiftingBackward(table,initialSize,moveDown); //回到记录到最好的位置
	if (!result) goto ddLinearAndSiftingAuxOutOfMem;

    } else if (x == xHigh) {
	moveUp = ddLinearAndSiftingUp(table,x,xLow,NULL); //选中变量往上线性筛选
	/* At this point x --> xLow unless bounding occurred. */
	if (moveUp == (Move *) CUDD_OUT_OF_MEM) goto ddLinearAndSiftingAuxOutOfMem;
	/* Move backward and stop at best position. */
	result = ddLinearAndSiftingBackward(table,initialSize,moveUp); //回到记录到的最好位置
	if (!result) goto ddLinearAndSiftingAuxOutOfMem;

    } else if ((x - xLow) > (xHigh - x)) { /* must go down first: shorter */ //x离下边界更近,先往下走
	moveDown = ddLinearAndSiftingDown(table,x,xHigh,NULL); //先往下走,记录下移动顺序和变换后的大小
	/* At this point x --> xHigh unless bounding occurred. */
	if (moveDown == (Move *) CUDD_OUT_OF_MEM) goto ddLinearAndSiftingAuxOutOfMem;
	moveUp = ddUndoMoves(table,moveDown); //还原x到原始位置,返回的是边界到原始位置的变换记录链表
#ifdef DD_DEBUG
	assert(moveUp == NULL || moveUp->x == (DdHalfWord) x);
#endif
	moveUp = ddLinearAndSiftingUp(table,x,xLow,moveUp); //接着向上移动,直到上边界
	if (moveUp == (Move *) CUDD_OUT_OF_MEM) goto ddLinearAndSiftingAuxOutOfMem;
	/* Move backward and stop at best position. */
	result = ddLinearAndSiftingBackward(table,initialSize,moveUp); //从整一条下边界到上边界的记录列表中,找到最好位置,回到最好位置
	if (!result) goto ddLinearAndSiftingAuxOutOfMem;

    } else { /* must go up first: shorter */ //优先向上移动,跟优先向下移动的情况一致
	moveUp = ddLinearAndSiftingUp(table,x,xLow,NULL);
	/* At this point x --> xLow unless bounding occurred. */
	if (moveUp == (Move *) CUDD_OUT_OF_MEM) goto ddLinearAndSiftingAuxOutOfMem;
	moveDown = ddUndoMoves(table,moveUp);
#ifdef DD_DEBUG
	assert(moveDown == NULL || moveDown->y == (DdHalfWord) x);
#endif
	moveDown = ddLinearAndSiftingDown(table,x,xHigh,moveDown);
	if (moveDown == (Move *) CUDD_OUT_OF_MEM) goto ddLinearAndSiftingAuxOutOfMem;
	/* Move backward and stop at best position. */
	result = ddLinearAndSiftingBackward(table,initialSize,moveDown);
	if (!result) goto ddLinearAndSiftingAuxOutOfMem;
    }

    while (moveDown != NULL) { //遍历记录链,释放这两条记录列表的作用
	move = moveDown->next;
	cuddDeallocMove(table, moveDown); //内存先不释放,链的结点先放在free链上,要用新结点的时候就不用新建空间了
	moveDown = move;
    }
    while (moveUp != NULL) { //同上
	move = moveUp->next;
	cuddDeallocMove(table, moveUp);
	moveUp = move;
    }

    return(1);

ddLinearAndSiftingAuxOutOfMem:
    while (moveDown != NULL) {
	move = moveDown->next;
	cuddDeallocMove(table, moveDown);
	moveDown = move;
    }
    while (moveUp != NULL) {
	move = moveUp->next;
	cuddDeallocMove(table, moveUp);
	moveUp = move;
    }

    return(0);

} /* end of ddLinearAndSiftingAux */


/**
  @brief Sifts a variable up and applies linear transformations.

  @details Moves y up until either it reaches the bound (xLow) or the
  size of the %DD heap increases too much.

  @return the set of moves in case of success; NULL if memory is full.

  @sideeffect None

*/ //跟ddLinearAndSiftingDown()一样
static Move *
ddLinearAndSiftingUp(
  DdManager * table,
  int  y,
  int  xLow,
  Move * prevMoves)
{
    Move	*moves;
    Move	*move;
    int		x;
    int		size, newsize;
    int		limitSize;
    int		xindex, yindex;
    int		isolated;
    int		L;	/* lower bound on DD size */
#ifdef DD_DEBUG
    int checkL;
    int z;
    int zindex;
#endif

    moves = prevMoves;
    yindex = table->invperm[y];

    /* Initialize the lower bound.
    ** The part of the DD below y will not change.
    ** The part of the DD above y that does not interact with y will not
    ** change. The rest may vanish in the best case, except for
    ** the nodes at level xLow, which will not vanish, regardless.
    */
    limitSize = L = (int) (table->keys - table->isolated);
    for (x = xLow + 1; x < y; x++) {
	xindex = table->invperm[x];
	if (cuddTestInteract(table,xindex,yindex)) {
	    isolated = table->vars[xindex]->ref == 1;
	    L -= (int) table->subtables[x].keys - isolated;
	}
    }
    isolated = table->vars[yindex]->ref == 1;
    L -= (int) table->subtables[y].keys - isolated;

    x = cuddNextLow(table,y);
    while (x >= xLow && L <= limitSize) {
	xindex = table->invperm[x];
#ifdef DD_DEBUG
	checkL = table->keys - table->isolated;
	for (z = xLow + 1; z < y; z++) {
	    zindex = table->invperm[z];
	    if (cuddTestInteract(table,zindex,yindex)) {
		isolated = table->vars[zindex]->ref == 1;
		checkL -= table->subtables[z].keys - isolated;
	    }
	}
	isolated = table->vars[yindex]->ref == 1;
	checkL -= table->subtables[y].keys - isolated;
	if (L != checkL) {
	    (void) fprintf(table->out, "checkL(%d) != L(%d)\n",checkL,L);
	}
#endif
	size = cuddSwapInPlace(table,x,y);
	if (size == 0) goto ddLinearAndSiftingUpOutOfMem;
	newsize = cuddLinearInPlace(table,x,y);
	if (newsize == 0) goto ddLinearAndSiftingUpOutOfMem;
	move = (Move *) cuddDynamicAllocNode(table);
	if (move == NULL) goto ddLinearAndSiftingUpOutOfMem;
	move->x = x;
	move->y = y;
	move->next = moves;
	moves = move;
	move->flags = CUDD_SWAP_MOVE;
	if (newsize >= size) {
	    /* Undo transformation. The transformation we apply is
	    ** its own inverse. Hence, we just apply the transformation
	    ** again.
	    */
	    newsize = cuddLinearInPlace(table,x,y);
	    if (newsize == 0) goto ddLinearAndSiftingUpOutOfMem;
#ifdef DD_DEBUG
	    if (newsize != size) {
		(void) fprintf(table->out,"Change in size after identity transformation! From %d to %d\n",size,newsize);
	    }
#endif
	} else if (cuddTestInteract(table,xindex,yindex)) {
	    size = newsize;
	    move->flags = CUDD_LINEAR_TRANSFORM_MOVE;
	    cuddUpdateInteractionMatrix(table,xindex,yindex);
	}
	move->size = size;
	/* Update the lower bound. */
	if (cuddTestInteract(table,xindex,yindex)) {
	    isolated = table->vars[xindex]->ref == 1;
	    L += (int) table->subtables[y].keys - isolated;
	}
	if ((double) size > (double) limitSize * table->maxGrowth) break;
	if (size < limitSize) limitSize = size;
	y = x;
	x = cuddNextLow(table,y);
    }
    return(moves);

ddLinearAndSiftingUpOutOfMem:
    while (moves != NULL) {
	move = moves->next;
	cuddDeallocMove(table, moves);
	moves = move;
    }
    return((Move *) CUDD_OUT_OF_MEM);

} /* end of ddLinearAndSiftingUp */


/**
  @brief Sifts a variable down and applies linear transformations.

  @details Moves x down until either it reaches the bound (xHigh) or
  the size of the %DD heap increases too much.

  @return the set of moves in case of success; NULL if memory is full.

  @sideeffect None

*/
static Move *
ddLinearAndSiftingDown(
  DdManager * table,
  int  x,
  int  xHigh,
  Move * prevMoves)
{
    Move	*moves;
    Move	*move; 
    int		y;
    int		size, newsize;
    int		R;	/* upper bound on node decrease */
    int		limitSize;
    int		xindex, yindex;
    int		isolated;
#ifdef DD_DEBUG
    int		checkR;
    int		z;
    int		zindex;
#endif

    moves = prevMoves; //维持以前的变换记录链,以后新的记录插到这个链
    /* Initialize R */
    xindex = table->invperm[x]; //在列表中取出变量X的index
    limitSize = size = table->keys - table->isolated; //记录一下当前的dd结点数
    R = 0;
    for (y = xHigh; y > x; y--) {
	yindex = table->invperm[y]; //取出变量y的index
	if (cuddTestInteract(table,xindex,yindex)) { //如果x和y是interact的话，说明可以LT，更新一下要处理结点数
	    isolated = table->vars[yindex]->ref == 1; //如果变量y的引用计数等于1的话，它就是isolated的
	    R += table->subtables[y].keys - isolated; //更新要处理的结点个数
	}
    }

    y = cuddNextHigh(table,x); //下一个子表(变量)（index+1）
    while (y <= xHigh && size - R < limitSize) { //y在边界内,且需要执行变换
#ifdef DD_DEBUG
	checkR = 0;
	for (z = xHigh; z > x; z--) {
	    zindex = table->invperm[z];
	    if (cuddTestInteract(table,xindex,zindex)) {
		isolated = table->vars[zindex]->ref == 1;
		checkR += (int) table->subtables[z].keys - isolated;
	    }
	}
	if (R != checkR) {
	    (void) fprintf(table->out, "checkR(%d) != R(%d)\n",checkR,R);
	}
#endif
	/* Update upper bound on node decrease. */
	yindex = table->invperm[y]; //取出y变量的index
	if (cuddTestInteract(table,xindex,yindex)) { //更新需要处理结点的个数,如果x和y是interact但是y是isolate的话,需要处理的结点数就减1
	    isolated = table->vars[yindex]->ref == 1;
	    R -= (int) table->subtables[y].keys - isolated;
	}
	size = cuddSwapInPlace(table,x,y); //交换x和y两个变量
	if (size == 0) goto ddLinearAndSiftingDownOutOfMem;
	newsize = cuddLinearInPlace(table,x,y); //线性变换两个变量
	if (newsize == 0) goto ddLinearAndSiftingDownOutOfMem;
	move = (Move *) cuddDynamicAllocNode(table); //生成一个新的变换记录,后面会插入到变换记录列表
	if (move == NULL) goto ddLinearAndSiftingDownOutOfMem;
	move->x = x;
	move->y = y;
	move->next = moves; //把这个记录加入到swap/LT记录列表
	moves = move; //更新变换记录列表的指针,moves保持指向最新一次变换记录上
	move->flags = CUDD_SWAP_MOVE; //更新变换的类型
	if (newsize >= size) { //如果LT比swap产生的结点数,就再次执行LT以抵消LT
	    /* Undo transformation. The transformation we apply is
	    ** its own inverse. Hence, we just apply the transformation
	    ** again.
	    */
	    newsize = cuddLinearInPlace(table,x,y);
	    if (newsize == 0) goto ddLinearAndSiftingDownOutOfMem;
	    if (newsize != size) {
		(void) fprintf(table->out,"Change in size after identity transformation! From %d to %d\n",size,newsize);
	    }
	} else if (cuddTestInteract(table,xindex,yindex)) { //如果LT效果更好,并且执行LT的两个变量是interact的话,要更新一下interact矩阵
	    size = newsize; //采用LT的size
	    move->flags = CUDD_LINEAR_TRANSFORM_MOVE; //变换记录也更新为LT
	    cuddUpdateInteractionMatrix(table,xindex,yindex); //更新一下interact矩阵
	}
	move->size = size; 
	if ((double) size > (double) limitSize * table->maxGrowth) break;
	if (size < limitSize) limitSize = size; //更新一下限制大小(用来保证下次变换不超过一个阀值)
	x = y; //轮到下两个变量
	y = cuddNextHigh(table,x);
    }
    return(moves); //成功是返回变换记录列表

ddLinearAndSiftingDownOutOfMem:
    while (moves != NULL) {
	move = moves->next;
	cuddDeallocMove(table, moves);
	moves = move;
    }
    return((Move *) CUDD_OUT_OF_MEM);

} /* end of ddLinearAndSiftingDown */


/**
  @brief Given a set of moves, returns the %DD heap to the order
  giving the minimum size.

  @details In case of ties, returns to the closest position giving the
  minimum size.

  @return 1 in case of success; 0 otherwise.

  @sideeffect None

*/
static int
ddLinearAndSiftingBackward(
  DdManager * table,
  int  size,
  Move * moves)
{
    Move *move;
    int	res;

    for (move = moves; move != NULL; move = move->next) { //遍历变换记录列表
	if (move->size < size) {
	    size = move->size; //拿到变换记录列表中最好的size记录(size最小)
	}
    }

    for (move = moves; move != NULL; move = move->next) { //遍历变换记录列表
	if (move->size == size) return(1); //当前处理的变换记录跟最好记录一样,直接返回1
	if (move->flags == CUDD_LINEAR_TRANSFORM_MOVE) { //如果记录是LT记录
	    res = cuddLinearInPlace(table,(int)move->x,(int)move->y); //再次执行LT,就抵消LT
	    if (!res) return(0);
	}
	res = cuddSwapInPlace(table,(int)move->x,(int)move->y); //在做LinearAndSifting的时候一定会执行swap(LT有可能没有),所以还原的时候要再次swap
	if (!res) return(0);
	if (move->flags == CUDD_INVERSE_TRANSFORM_MOVE) { //这是对IT的还原
	    res = cuddLinearInPlace(table,(int)move->x,(int)move->y);
	    if (!res) return(0);
	}
    }

    return(1);

} /* end of ddLinearAndSiftingBackward */


/**
  @brief Given a set of moves, returns the %DD heap to the order
  in effect before the moves.

  @return 1 in case of success; 0 otherwise.

  @sideeffect None

*/
static Move*
ddUndoMoves(
  DdManager * table,
  Move * moves)
{
    Move *invmoves = NULL;
    Move *move;
    Move *invmove;
    int	size;

    for (move = moves; move != NULL; move = move->next) { //对所有变换记录遍历,以抵消所以变换
	invmove = (Move *) cuddDynamicAllocNode(table); //创建一个反向移动的记录
	if (invmove == NULL) goto ddUndoMovesOutOfMem;
	invmove->x = move->x;
	invmove->y = move->y;
	invmove->next = invmoves; //新的记录插入到链
	invmoves = invmove; //invmoves指针保持在最新记录上
	if (move->flags == CUDD_SWAP_MOVE) { //变换类型是swap的情况
	    invmove->flags = CUDD_SWAP_MOVE; //更新变换类型
	    size = cuddSwapInPlace(table,(int)move->x,(int)move->y); //还原变换
	    if (!size) goto ddUndoMovesOutOfMem;
	} else if (move->flags == CUDD_LINEAR_TRANSFORM_MOVE) { //变换类型是LT的情况
	    invmove->flags = CUDD_INVERSE_TRANSFORM_MOVE; //更新变换类型
	    size = cuddLinearInPlace(table,(int)move->x,(int)move->y); //还原LT产生的效果
	    if (!size) goto ddUndoMovesOutOfMem;
	    size = cuddSwapInPlace(table,(int)move->x,(int)move->y); //还原swap效果
	    if (!size) goto ddUndoMovesOutOfMem;
	} else { /* must be CUDD_INVERSE_TRANSFORM_MOVE */ //InvT的情况(IT就是先LT再swap,一般是先swap再LT)
#ifdef DD_DEBUG
	    (void) fprintf(table->err,"Unforseen event in ddUndoMoves!\n");
#endif
	    invmove->flags = CUDD_LINEAR_TRANSFORM_MOVE;
	    size = cuddSwapInPlace(table,(int)move->x,(int)move->y);
	    if (!size) goto ddUndoMovesOutOfMem;
	    size = cuddLinearInPlace(table,(int)move->x,(int)move->y);
	    if (!size) goto ddUndoMovesOutOfMem;
	}
	invmove->size = size; //更新还原记录的大小
    }

    return(invmoves); //根据变换记录列表完成了变换的抵消,并返回抵消记录列表

ddUndoMovesOutOfMem:
    while (invmoves != NULL) {
	move = invmoves->next;
	cuddDeallocMove(table, invmoves);
	invmoves = move;
    }
    return((Move *) CUDD_OUT_OF_MEM);

} /* end of ddUndoMoves */


/**
  @brief XORs two rows of the linear transform matrix.

  @details Replaces the first row with the result.

  @sideeffect none

*/
static void
cuddXorLinear(
  DdManager * table,
  int  x,
  int  y)
{
    int i;
    int nvars = table->size;
    int wordsPerRow = ((nvars - 1) >> LOGBPL) + 1; //用一个bit表示一个变量,算出矩阵每行需要几个word(64bit/32bit)
    int xstart = wordsPerRow * x; //定位到x行
    int ystart = wordsPerRow * y; //定位到y行
    ptruint *linear = table->linear; //取出线性矩阵

    for (i = 0; i < wordsPerRow; i++) { //把x变量所在的行(x行)的每个字拿出来处理
	linear[xstart+i] ^= linear[ystart+i]; //x->x XOR y
    }

} /* end of cuddXorLinear */
