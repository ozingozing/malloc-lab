/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};
/* 단일 워드(4) 또는 더블 워드(8) 정렬 */
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* ALIGMENT의 가장 가까운 배수로 올림 */
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// ADD
#define WSIZE 4             // word사이즈 header/footer (byte)사이즈
#define DSIZE 8             // Double word size(byte)
#define CHUNKSIZE (1 << 12) // heap 총 크기

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

// Explicit free list
#define PRED(bp) ((char *)(bp))         // 이전 블록의 bp에 들어있는 주소값을 리턴
#define SUCC(bp) ((char *)(bp + WSIZE)) // 이후 블록의 bp
//

// 0 == FirstFit(묵시적 가용 리스트)
// 1 == NextFit (묵시적 가용 리스트)
// 2 == BestFit (묵시적 가용 리스트)
// 3 == FindFit (명시적 가용 리스트)
#define Fit 3

static char *heap_listp = NULL;
static char *lastPtr = NULL;
// Explicit free list
static char *free_listp; // free list의 맨 첫 블록을 가리키는 포인터
static char *find_ptr = NULL;
//
// ADD
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *first_fit(size_t asize);
static void *next_fit(size_t asize);
static void *best_fit(size_t asize);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
//
/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    find_ptr = heap_listp; // find_ptr 은 heap_listp의 주소값을 복사한다.
    heap_listp += (DSIZE);
    lastPtr = heap_listp;
    if ((extend_heap(CHUNKSIZE / WSIZE)) == NULL)
        return -1;

    return 0;
}

static void *extend_heap(size_t words)
{

    char *bp = NULL;
    size_t size = 0;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(PRED(bp), 0);
    PUT(SUCC(bp), 0);
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    {
        add_free(bp);
        return bp;
    }
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        fix_link(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        fix_link(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP((PREV_BLKP(bp))), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        fix_link(PREV_BLKP(bp)); // 전블록
        fix_link(NEXT_BLKP(bp)); // 다음블록
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    lastPtr = bp;
    add_free(bp);
    return bp;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 * mm_malloc - brk 포인터를 증가시켜 블록을 할당합니다.
 *     항상 정렬된 배수의 크기의 블록을 할당합니다.
 */
void *mm_malloc(size_t size)
{
    size_t asize = 0;
    size_t extendsize = 0;
    char *bp = NULL;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = ALIGN(size + DSIZE);
#if (Fit == 0)
    bp = first_fit(asize);
#elif (Fit == 1)
    bp = next_fit(asize);
#elif (Fit == 2)
    bp = best_fit(asize);
#elif (Fit == 3)
    bp = find_fit(asize);
#endif
    if (bp != NULL)
    {
        place(bp, asize);
        lastPtr = bp;
        return bp;
    }

    bp = extend_heap(MAX(asize, CHUNKSIZE) / WSIZE);
    if (bp == NULL)
        return NULL;
    place(bp, asize);
    lastPtr = bp;
    return bp;
}

static void *first_fit(size_t asize)
{
    void *bp = NULL;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    }
    return NULL;
}

static void *next_fit(size_t asize)
{
    do
    {
        if (!GET_ALLOC(HDRP(lastPtr)) && asize <= GET_SIZE(HDRP(lastPtr)))
            return lastPtr;

        lastPtr = NEXT_BLKP(lastPtr);

        if (GET_SIZE(HDRP(lastPtr)) == 0)
            lastPtr = heap_listp;
    } while (heap_listp != lastPtr);

    return NULL;
}

static void *best_fit(size_t asize)
{
    void *bp;
    void *bestp = NULL;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            bestp = bp;
        }
    }

    return bestp;
}

static void *find_fit(size_t asize)
{
    char *get_address = GET(find_ptr);

    while (get_address != NULL)
    {
        if (GET_SIZE(HDRP(get_address)) >= asize)
        {
            return get_address;
        }
        get_address = GET(SUCC(get_address));
    }
    return NULL; // not fit any
}

static void place(void *bp, size_t asize)
{
    size_t currentSize = GET_SIZE(HDRP(bp));
    fix_link(bp);
    if ((currentSize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK((currentSize - asize), 0));
        PUT(FTRP(bp), PACK((currentSize - asize), 0));
        PUT(SUCC(bp), 0);
        PUT(PRED(bp), 0);
        coalesce(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(currentSize, 1));
        PUT(FTRP(bp), PACK(currentSize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    if (bp == 0)
        return;
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(SUCC(bp), 0);
    PUT(PRED(bp), 0);
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * mm_realloc - 간단히 mm_malloc과 mm_free의 측면에서 구현됩니다.
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) // 입력 포인터가 NULL이면, 입력 사이즈만큼 새롭게 할당 (예외처리)
    {
        return mm_malloc(size);
    }

    if (size == 0) // 입력 사이즈가 0이면, 입력 포인터의 블록을 해제 (예외처리)
    {
        add_free(ptr);
        mm_free(ptr);
        return NULL;
    }

    void *oldptr = ptr;
    void *temp = ptr;
    size_t copySize = GET_SIZE(HDRP(oldptr)); // 재할당하려는 블록의 사이즈
    if (size <= DSIZE)
        size = 2 * DSIZE;
    else
        size = ALIGN(size + DSIZE);
    if (size + DSIZE <= copySize) // (재할당 하려는 블록 사이즈 + 8 bytes(Header + Footer)) <= 현재 블록 사이즈
    {
        return oldptr; // 현재 블록에 재할당해도 문제 없기 때문에, 포인터만 반환
    }
    else // (재할당 하려는 블록 사이즈 + 8 bytes) > 현재 블록 사이즈
         // 경우에 따라서 인접 Free block을 활용하는 방안과, 새롭게 할당하는 방안을 이용해야 함
    {
        size_t next_size = copySize + GET_SIZE(HDRP(NEXT_BLKP(oldptr))); // 현재 블록 사이즈 + 다음 블록 사이즈 = next_size
        size_t prev_size = copySize + GET_SIZE(HDRP(PREV_BLKP(oldptr))); // 이전 블록 사이즈
        fix_link((oldptr));
        if (!GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) && (size <= next_size))
        // 다음 블록이 Free block이고, (재할당 하려는 블록의 사이즈 + 8 bytes) <= (현재 블록 사이즈 + 다음 블록 사이즈)
        // 현재 블록과 다음 블록을 하나의 블록으로 취급해도 크기의 문제가 발생하지 않음
        // malloc을 하지 않아도 됨 -> 메모리 공간 및 시간적 이득을 얻을 수 있음
        {

            PUT(HDRP(oldptr), PACK(next_size, 1)); // 현재 블록의 Header Block에, (현재 블록 사이즈 + 다음 블록 사이즈) 크기와 Allocated 상태 기입
            PUT(FTRP(oldptr), PACK(next_size, 1)); // 현재 블록의 Footer Block에, (현재 블록 사이즈 + 다음 블록 사이즈) 크기와 Allocated 상태 기입
            lastPtr = oldptr;                      // next_fit 사용을 위한 포인터 동기화
            // fix_link(NEXT_BLKP(oldptr));
            return oldptr;
        }
        else if (!GET_ALLOC(HDRP(PREV_BLKP(oldptr))) && (size + DSIZE <= prev_size))
        // 이전 블록이 Free block이고, (재할당 하려는 블록의 사이즈 + 8 bytes) <= (이전 블록 사이즈 + 현재 블록 사이즈)
        // 이전 블록과 현재 블록을 하나의 블록으로 취급해도 크기의 문제가 발생하지 않음
        // malloc을 하지 않아도 됨 -> 메모리 공간 및 시간적 이득을 얻을 수 있음
        {

            void *prev_ptr = PREV_BLKP(oldptr);      // 이전 블록의 bp
            memmove(prev_ptr, oldptr, copySize);     // 이전 블록의 bp로 현재 block의 메모리 영역을 옮긴다
            PUT(HDRP(prev_ptr), PACK(prev_size, 1)); // 이전 블록의 Header Block에, (이전 블록 사이즈 + 현재 블록 사이즈) 크기와 Allocated 상태 기입
            PUT(FTRP(prev_ptr), PACK(prev_size, 1)); // 이전 블록의 Footer Block에, (이전 블록 사이즈 + 현재 블록 사이즈) 크기와 Allocated 상태 기입
            lastPtr = prev_ptr;                      // next_fit 사용을 위한 포인터 동기화
            fix_link(((prev_ptr)));
            return prev_ptr;
        }
        else if (!GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) && !GET_ALLOC(HDRP(PREV_BLKP(oldptr))) && (size + DSIZE <= next_size + copySize + prev_size))
        // 이전 블록과 다음 블록이 모두 Free block, (재할당 하려는 블록의 사이즈 + 8 bytes) <= (이전 블록 사이즈 + 현재 블록 사이즈 + 다음 블록 사이즈)
        // 이전 블록과 현재 블록과 다음 블록을 하나의 블록으로 취급해도 크기의 문제가 발생하지 않음
        // malloc을 하지 않아도 됨 -> 메모리 공간 및 시간적 이득을 어등ㄹ 수 있음
        {
            void *prev_ptr = PREV_BLKP(oldptr);                             // 이전 블록의 bp
            memmove(prev_ptr, oldptr, copySize);                            // 이전 블록의 bp로 현재 block의 메모리 영역을 옮긴다
            PUT(HDRP(prev_ptr), PACK(prev_size + copySize + next_size, 1)); // 이전 블록의 Header Block에, (이전 블록 사이즈 + 현재 블록 사이즈 + 다음 블록 사이즈) 크기와 Allocated 상태 기입
            PUT(FTRP(prev_ptr), PACK(prev_size + copySize + next_size, 1)); // 이전 블록의 Footer Block에, (이전 블록 사이즈 + 현재 블록 사이즈 + 다음 블록 사이즈) 크기와 Allocated 상태 기입
            lastPtr = prev_ptr;                                             // next_fit 사용을 위한 포인터 동기화
            fix_link(((prev_ptr)));
            fix_link(NEXT_BLKP(NEXT_BLKP(prev_ptr)));
            return prev_ptr;
        }
        else // 위 케이스에 모두 해당되지 않아, 결국 malloc을 해야 하는 경우
        {
            void *newptr = mm_malloc(size + DSIZE); // (할당하려는 크기 + 8 bytes)만큼 새롭게 할당
            if (newptr == NULL)             // 새로 할당한 주소가 NULL일 경우 (예외처리)
            {
                return NULL;
            }
            memmove(newptr, oldptr, size + DSIZE); // payload 복사
            lastPtr = newptr;              // next_fit 사용을 위한 포인터 동기화
            fix_link(newptr);
            mm_free(oldptr); // 기존의 블록은 Free block으로 바꾼다
            return newptr;   // 새롭게 할당된 주소의 포인터를 반환
        }
    }
    // Defualt
    //  if (ptr == NULL) {
    //      return mm_malloc(size);
    //  }

    // if (size <= 0) {
    //     mm_free(ptr);
    //     return 0;
    // }

    // void *newptr = mm_malloc(size);
    // if (newptr == NULL) {
    //   return NULL;
    // }

    // size_t copySize = GET_SIZE(HDRP(ptr)) - DSIZE;  //payload만큼 복사
    // if (size < copySize) {
    //   copySize = size;
    // }

    // memmove(newptr, ptr, copySize);   // 새 블록으로 데이터 복사
    // mm_free(ptr);
    // return newptr;
}

void add_free(char *ptr)
{
    char *succ; // char* succ = *(unsigned int*)(find_ptr); \\         ---------------succ = **find_ptr;
    succ = GET(find_ptr);
    if (succ != 0)
    {                   // 루트에 연결 되어있는게 있을 때. // 루트가 가리키는 주소가 널이 아닐떄
        PUT(succ, ptr); // 첫 노드의 이전 항목에 지금 갱신되는 것을 넣어주고.
    }
    PUT(SUCC(ptr), succ); // ptr의 다음 노드를 첫번째 노드로 연결 시켜준다.
    PUT(find_ptr, ptr);   // 루트가 가리키는 애를 새로들어온 애로 바꾼다.
}
void fix_link(char *ptr)
{ // fix과정은 무조건 연결을 끊어줌
    if (GET(PRED(ptr)) == NULL)
    { // 첫노드
        if (GET(SUCC(ptr)) != NULL)
        {                                 // 다음 노드가 연결되어있으면,
            PUT(PRED(GET(SUCC(ptr))), 0); // 다음 노드의 주소의 이전 노드의 주소를 지운다.
        }
        PUT(find_ptr, GET(SUCC(ptr))); // 루트 노드가 첫 노드가 가리키던 다음 노드를 가리키게 한다.
    }
    else
    { // 루트노드 이외에 다른 노드일 때
        if (GET(SUCC(ptr)) != NULL)
        {                                              // 전, 후 모두 노드가 연결되어있으면
            PUT(PRED(GET(SUCC(ptr))), GET(PRED(ptr))); // 다음노드의 주소의 이전노드값을 지금 노드의 이전값과 연결시킨다.
        }
        PUT(SUCC(GET(PRED(ptr))), GET(SUCC(ptr))); // 이전 노드에 입력되어있던 다음 노드 주소에 지금 노드의 다음노드 주소를 넣어준다.
    }
    PUT(SUCC(ptr), 0); // 현재 노드의 SUCC, PRED 초기화
    PUT(PRED(ptr), 0);
}