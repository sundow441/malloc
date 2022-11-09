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
#define LISTLIMIT 20 // free_list의 개수 제한

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
static char *last_bp;
static char *segregation_list[LISTLIMIT]; //free_list의 리스트

static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void insertBlock(void *bp, size_t size);
static void removeBlock(void *bp);
static void *next_fit(size_t adjusted_size);

// malloc 패키지를 초기화(빈 heap을 만들기 위한 함수)
int mm_init(void)
{
    int list;
    for(list = 0; list < LISTLIMIT; list++)
    {
        segregation_list[list] = NULL;
    }

    // 초기 heap영역 할당
    // heap의 최대 크기 이상을 요청한다면 -1(fail)을 반환
    if((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) - 1) return -1;
    PUT(heap_listp, 0);                         // epilogue 블록과 짝을 맞춰주기 위한 padding 블록
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // prologue header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));  // epilogue header
    heap_listp += (2 * WSIZE);                     // 초기 heap pointer를 prologue header 뒤로 옮긴다.
    // pointer가 header로 부터 다른 블록의 값을 가지고 오거나 이동을 용이하게 하기 위함

    if(extend_heap(4) == NULL) return -1;

    // heap에 regular block을 할당하기 위해 가용 블록의 사이즈를 한 번 늘린다
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1;
    // last_bp = (char *)heap_listp;

    return 0;
}

// bp를 증가시켜 블록을 할당하는 함수
void *mm_malloc(size_t size)
{
    int asize = ALIGN(size + SIZE_T_SIZE);
    //size_t asize;
    size_t extendsize;
    char *bp;

    if(size == 0) return NULL;

    if((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        // last_bp = bp;
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL) return NULL;
    place(bp, asize);
    // last_bp = bp;
    return bp;
}

//  heap이 초기화(init) 되거나 적당한 가용 블록을 찾지 못했을 때 heap 영역을 확장하기 위한 함수.
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; //byte를 8의 배수로 맞추기 위해 홀수일 때 +1
    if((long)(bp = mem_sbrk(size)) == -1) return NULL; // size 만큼 heap 공간 요청

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

// 
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

// 가용 블록이 생길 경우 이전, 다음 블록의 가용 여부를 확인하고 연결해주는 함수
static void *coalesce(void *bp)
{
    // 다음 블록의 footer, 이전 블록의 header를 통해 가용 여부를 확인
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // case 1: 이전 블록과 다음 블록이 모두 할당되어 있다면 해당 블록만 free_list에 넣어줌
    if(prev_alloc && next_alloc)
    {
        insertBlock(bp, size);
        // last_bp = bp;
        return bp;
    }
    // case 2: 이전 블록이 가용 블록이고, 다음 블록이 할당되어 있는 경우
    else if(!prev_alloc && next_alloc)
    {
        removeBlock(PREV_BLKP(bp)); //free 상태였던 다음 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // case 3: 이전 블록이 할당되어 있고, 다음 블록이 가용 블록인 경우
    else if(prev_alloc && !next_alloc)
    {
        removeBlock(NEXT_BLKP(bp)); //free 상태였던 이전 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // case 4: 이전 블록과 다음 블록이 모두 가용상태인 경우
    else if(!prev_alloc && !next_alloc)
    {        
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 연결할 가용 블록의 전체 사이즈 계산
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp); // bp를 연결할 가용 블록들의 맨 앞으로 보냄
    }
    // 연결된 새 가용 블록을 free_list에 추가
    insertBlock(bp, size);

    // last_bp = bp;
    return bp;
}

// segregation_list에 새로 만들어진 가용 블록을 추가하는 함수 
void insertBlock(void *bp, size_t size)
{
    int list = 0; // 리스트의 인덱스
    void *search_ptr;
    void *insert_ptr = NULL; // search_ptr의 값을 저장해놓는 용도(seach_ptr 이전 블록)

    // segregation_list의 인덱스를 찾는 과정
    while((list < LISTLIMIT - 1) && (size > 1))
    {
        size >>= 1;
        list++;
    }

    search_ptr = segregation_list[list];
    // 오름차순으로 저장하기 위해 나보다 작으면 넘기고 나보다 크면 멈춤
    while((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr))))
    {
        insert_ptr = search_ptr;
        search_ptr = SUCC_FREEP(search_ptr);
    }

    if(search_ptr !=NULL)
    {
        if(insert_ptr != NULL) // 이전 블록이 존재하는 경우(리스트의 중간에 블록을 삽입하는 경우)
        {
            SUCC_FREEP(bp) = search_ptr;
            PREC_FREEP(bp) = insert_ptr;
            PREC_FREEP(search_ptr) = bp;
            SUCC_FREEP(insert_ptr) = bp;
        }
        else // 이전 블록이 존재하지 않아(리스트에서 가장 작아) 리스트의 첫번째에 삽입하는 경우
        {
            SUCC_FREEP(bp) = search_ptr;
            PREC_FREEP(bp) = NULL;
            PREC_FREEP(search_ptr) = bp;
            segregation_list[list] = bp; // segregation_list 최신화
        }
    }
    else // search_ptr이 NULL일 때
    {
        if(insert_ptr != NULL) // 리스트에서 가장 커 리스트의 마지막에 삽입하는 경우
        {
            SUCC_FREEP(bp) = NULL;
            PREC_FREEP(bp) = insert_ptr;
            SUCC_FREEP(insert_ptr) = bp;
        }
        else // 리스트가 비어있어 처음으로 삽입하는 경우
        {
            SUCC_FREEP(bp) = NULL;
            PREC_FREEP(bp) = NULL;
            segregation_list[list] = bp; // segregation_list 최신화
        }
    }

    return;
}

// 할당되거나 연결되는 가용 블록을 free_list에서 제거하는 함수
void removeBlock(void *bp)
{
    int list = 0; // 리스트의 인덱스
    size_t size = GET_SIZE(HDRP(bp));

    // segregation_list의 인덱스를 찾는 과정
    while((list < LISTLIMIT - 1) && (size > 1))
    {
        size >>= 1;
        list++;
    }

    if(SUCC_FREEP(bp) != NULL) // 다음 블록이 연결되어 있는 경우
    {
        if(PREC_FREEP(bp) != NULL) // 이전 블록이 연결되어 있는 경우(리스트 중간의 블록을 지우는 경우)
        {
            PREC_FREEP(SUCC_FREEP(bp)) = PREC_FREEP(bp);
            SUCC_FREEP(PREC_FREEP(bp)) = SUCC_FREEP(bp);
        }
        else // 이전 블록이 연결되어 있지 않은 경우(리스트 첫 번째 블록을 지우는 경우)
        {
            PREC_FREEP(SUCC_FREEP(bp)) = NULL;
            segregation_list[list] = SUCC_FREEP(bp); // segregation_list 포인터를 다음 블록으로 변경
        }
    }
    else // 다음 블록이 연결되지 않은 경우(NULL)
    {
        if(PREC_FREEP(bp) != NULL) // 이전 블록이 연결되어 있는 경우(리스트 마지막 블록을 지우는 경우)
        {
            SUCC_FREEP(PREC_FREEP(bp)) = NULL;
        }
        else // 애초에 리스트에 블록이 하나만 존재할 경우
        {
            segregation_list[list] = NULL; // segregation_list 포인터를 NULL로 변경
        }
    }

    return;
}

static void *find_fit(size_t asize)
{
    // first-fit 방식으로 구현
    void *bp;

    int list = 0;
    size_t searchsize = asize;
    // free_list의 첫번째 블록부터 할당된 블록이 나올 때 까지 블록을 하나씩 옮기며 반복
    // 여기서 할당된 블록은 prolog 블록을 의미
    while(list < LISTLIMIT)
    {
        if((list == LISTLIMIT - 1) || (searchsize <= 1) && (segregation_list[list] != NULL))
        {
            bp = segregation_list[list];
            while((bp != NULL) && (asize > GET_SIZE(HDRP(bp)))) bp = SUCC_FREEP(bp);
            if(bp != NULL) return bp;
        }
        searchsize >>=1;
        list++;
    }
    return NULL; // 찾지 못했으면 NULL 반환
}

static void *next_fit(size_t adjusted_size) {
    char *bp = last_bp;

    for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= adjusted_size) {
            last_bp = bp;
            return bp;
        }
    }

    bp = heap_listp;
    while (bp < last_bp) {
        bp = NEXT_BLKP(bp);
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= adjusted_size) {
            last_bp = bp;
            return bp;
        }
    }

    return NULL;
}

// 할당할 수 있는 free 블록을 free_list에서 삭제
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    removeBlock(bp);

    if((csize - asize) < (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    else
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        coalesce(bp);
    }
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
        return NULL;
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