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
#include <sys/mman.h>
#include <errno.h>

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
    ""
};

// 주소를 single word(4)로 정렬할지, double word(8)로 정렬할지 결정한다.
#define ALIGNMENT 8

// 받은 주소가 ALIGNMENT의 가장 가까운 배수가 되도록 만든다
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 기본 상수 및 매크로
#define WSIZE 4 // word의 크기
#define DSIZE 8 // double word의 크기
#define CHUNKSIZE (1<<12) // heap 영역을 한 번 늘릴 때 마다 늘려줄 크기

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 더 큰 값을 반환

// 크기와 할당 여부를 하나의 word에 저장하기 위해 사용
#define PACK(size, alloc) ((size) | (alloc))

// p(블록)에 있는 값을 읽고 쓸 때 사용
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// 주소 p(블록)에서 크기와 할당 여부를 가져옴
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// 블록 포인터 bp를 받으면 그 블록의 header와 footer 주소를 반환
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 블록 포인터 bp를 받으면 그 다음 블록의 header와 이전 블록의 footer 주소를 반환
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// 이전과 다음 가용리스트의 bp
#define PREC_FREEP(bp) (*(void**)(bp))
#define SUCC_FREEP(bp) (*(void**)(bp + WSIZE))

static char *heap_listp;
static char *free_listp;

static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void insertBlock(void *bp);
static void removeBlock(void *bp);

// malloc 패키지를 초기화(빈 heap을 만들기 위한 함수)
int mm_init(void)
{
    // 초기 heap영역 할당
    // heap의 최대 크기 이상을 요청한다면 -1(fail)을 반환
    if((heap_listp = mem_sbrk(6 * WSIZE)) == (void *) - 1) return -1;
    PUT(heap_listp, 0);                         // epilogue 블록과 짝을 맞춰주기 위한 padding 블록
    PUT(heap_listp + (1 * WSIZE), PACK(2 * WSIZE, 1)); // prologue header
    PUT(heap_listp + (2 * WSIZE), PACK(2 * WSIZE, 1)); // prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));  // epilogue header
    free_listp = heap_listp + (2 * WSIZE);                     // 초기 heap pointer를 prologue header 뒤로 옮긴다.
    // pointer가 header로 부터 다른 블록의 값을 가지고 오거나 이동을 용이하게 하기 위함

    if(extend_heap(4) == NULL) return -1;

    // heap에 블록을 할당하기 위해 가용 블록의 사이즈를 한 번 늘린다
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1;

    return 0;
}

// 가용 블록이 생길 경우 이전, 다음 블록의 가용 여부를 확인하고 연결해주는 함수
static void *coalesce(void *bp)
{
    // 다음 블록의 footer, 이전 블록의 header를 통해 가용 여부를 확인
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // case 1: 이전 블록과 다음 블록이 모두 할당되어 있다면 해당 블록만 free_list에 넣어줌

    // case 2: 이전 블록이 가용 블록이고, 다음 블록이 할당되어 있는 경우
    if(!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        removeBlock(bp); //free 상태였던 다음 블록을 free_list에서 제거
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // case 3: 이전 블록이 할당되어 있고, 다음 블록이 가용 블록인 경우
    else if(prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        removeBlock(NEXT_BLKP(bp)); //free 상태였던 이전 블록을 free_list에서 제거
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // case 4: 이전 블록과 다음 블록이 모두 가용상태인 경우
    else if(!prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp))); // 연결할 가용 블록의 전체 사이즈 계산
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        bp = PREV_BLKP(bp); // bp를 연결할 가용 블록들의 맨 앞으로 보냄
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // 연결된 새 가용 블록을 free_list에 추가
    insertBlock(bp);

    return bp;
}

// free_list의 첫번째에 새로 만들어진 가용 블록을 추가하는 함수 
void insertBlock(void *bp)
{
    SUCC_FREEP(bp) = free_listp;
    PREC_FREEP(bp) = NULL;
    PREC_FREEP(free_listp) = bp;
    free_listp = bp;
}

// 할당되거나 연결되는 가용 블록을 free_list에서 제거하는 함수
void removeBlock(void *bp)
{
    // free_list의 첫번쩨 블록을 제거하는 경우
    if( bp == free_listp)
    {
        PREC_FREEP(SUCC_FREEP(bp)) = NULL;
        free_listp = SUCC_FREEP(bp);
    }
    // free_list의 첫번째 블록을 제외한 나머지 블록 중에서 제거하는 경우
    else
    {
        SUCC_FREEP(PREC_FREEP(bp)) = SUCC_FREEP(bp);
        PREC_FREEP(SUCC_FREEP(bp)) = PREC_FREEP(bp);
    }
}

//  heap이 초기화(init) 되거나 적당한 가용 블록을 찾지 못했을 때 heap 영역을 확장하기 위한 함수.
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; //byte를 8의 배수로 맞추기 위해 홀수일 때 +1
    if((long)(bp = mem_sbrk(size)) == -1) return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size == 0) return NULL;

    if(size < DSIZE) asize = 2 * DSIZE;
    else asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL) return NULL;
    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize)
{
    // first-fit 방식으로 구현
    void *bp;
    // free_list의 첫번째 블록부터 할당된 블록이 나올 때 까지 블록을 하나씩 옮기며 반복
    // 여기서 할당된 블록은 prolog 블록을 의미
    for(bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp))
    {
        if(asize <= GET_SIZE(HDRP(bp))) return bp; // 현재 가용 블록의 사이즈가 찾고자 하는 사이즈와 같거나 크다면 반환
    }
    return NULL; // 찾지 못했으면 NULL 반환
}

// 할당할 수 있는 free 블록을 free_list에서 삭제
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if((csize - asize) < (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        removeBlock(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        removeBlock(bp);

        csize -= asize;
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize, 0));
        PUT(FTRP(bp), PACK(csize, 0));
        coalesce(bp);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (size <= 0)
    {
        mm_free(ptr);
        return 0;
    }
    if (ptr == NULL)
    {
        return mm_malloc(size);
    }
    
    void *newp = mm_malloc(size);
    
    if (newp == NULL)
    {
        return 0;
    }
    
    size_t oldsize = GET_SIZE(HDRP(ptr));
    if (size < oldsize)
    {
        oldsize = size;
    }
    
    memcpy(newp, ptr, oldsize);
    mm_free(ptr);
    
    return newp;
}