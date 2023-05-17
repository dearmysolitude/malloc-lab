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
    "Team 08",
    /* First member's full name */
    "Jooyoung Park",
    /* First member's email address */
    "optimisticnihilism2007@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8 //더블 워드의 크기로 설정

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 포인터 조작을 위한 매크로들

#define WSIZE       4       // word와 header, footer사이즈(bytes)
#define DSIZE       8       // 더블 워드의 사이즈(bytes)
#define CHUNKSIZE (1<<12)   // 힙 확장 크기(bytes), 2^12 = 4096, 1을 12자리 옮기는 비트연산이다 
//**4kb는 한 page의 크기이다**

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/*크기 및 할당 비트를 통합하여 헤더, 풋터에 저장할 값을 반환*/
#define PACK(size, alloc)   ((size) | (alloc)) //비트연산자, OR 연산

/*포인터 p의 참조 인자를 읽기/쓰기*/
#define GET(p)      (*(unsigned int *)(p)) //할당 여부
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 
 * 사이즈의 최소 단위가 16바이트(헤더: 4byte, 풋터: 4byte, payload: 추가되므로 최소 사이즈는 16byte이다.)임을 알 수 있다.
 * 이진수로 바꿔보면 맨 처음 세자리는 사용하지 않게 되는데, 여기에 할당 여부를 비트연산으로 추가하여 헤더로 사용한다.
 */
#define GET_SIZE(p)     (GET(p) & ~0x7)// 블록에서 사이즈만 가져온다
#define GET_ALLOC(p)    (GET(p) & 0x1) // 가용 여부

//얘네는 그림 그려보면 쉽게 알 수 있을 것
/*블록 포인터로 헤더, 풋터의 포인터 반환, bp는 그 블록의 payload가 시작하는 첫번째 위치, 즉 헤더 다음*/
#define HDRP(bp)        ((char *) (bp) - WSIZE) //헤더 찾기
#define FTRP(bp)        ((char *) (bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 풋터 찾기

/*이전 블록의 포인터를 반환*/
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* 
 * char과 int: 정숫값 저장변수
 * char: 1바이트 -> 문자 저장에 용이, 어떤 ASCII든 저장 가능.
 * char에 문자만 저장해야 하는 것은 아님, 작은 크기 정숫값 사용에 쓰이기도 한다
 * 메모리 블록 크기는 바이트 단위로 표기되어 메모리 블록 나타내는 데 적합함
 * int: 4바이트. 할당 여부를 나타내는데 적합
 * unsigned: 양수만, 보통 signed이므로 양수와 음수 모두 포함
 * 이 코드에서는 블록 포인터를 char로, 블록 헤더와 풋터를 unsigned int로(1 워드 = 4 바이트) 저장한다.
 */

/* 
 * mm_init - initialize the malloc package.
 */
static char *heap_listp;
static char *anchor; //next fit에서 사용하는 닻 역할
/* anchor가 바뀌는 경우는 다음과 같다
 * 1) mem_init에서 anchor = heap_listp
 * 2) place로 블록을 나누어 줄 때
 * 3) coalesce로 블록 합칠 때
 */

/* static 변수: 컴파일 시에 할당, 프로그램 종료까지 유지됨, 함수 내부에서 사용하면
 * 해당 함수 내에서만 사용할 수 있음. 지역/전역 변수 특성 모두 가짐.지역 변수처럼 함수 내에서 사용할 수 있지만,
 * 전역 변수처럼 프로그램 종료 시까지 메모리에 유지. 파일이 고유 핸들이나 소켓을 갖도록 할 수 있다.
 */

static void *extend_heap(size_t);
static void *coalesce(void *);
static void *find_fit(size_t);
static void place(void *, size_t);


// [implicit free list] + [next-fit]

int mm_init(void)
{
    /*빈 힙을 생성한다*/
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) {
        return -1;
    }
    
    PUT(heap_listp, 0); //alignment padding
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); //prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); //prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); //epiligue header
    heap_listp += (2*WSIZE); //힙을 추가할 위치로 이동

    /*비어있는 힙을 CHUNKSIZE 바이트의 크기인 free block으로 확대한다(최초 가용 블록)*/
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }

    anchor = heap_listp;
    //처음 시작: anchor는 heap_listp를 가르키는 것으로 시작한다.

    return 0;
}

/* extend heap함수는 1) 힙이 초기화 될 때 2) mm_malloc 이 적당한 맞춤fit을 찾지 못했을 때 호출됨
 * 정렬 유지를 위해 요청 크기를 인접 2워드의 배수(8바이트)로 반올림하고,
 * 그 후 메모리 시스템으로부터 추가 힙 공간을 요청한다.
 */

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /*추가 힙 공간 요청*/
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; //결과는 블록의 크기를 의미
    // 2 워드로 반올림, words%2가 0이 아니면 첫번재 조건으로 간다
    if ((long)(bp = mem_sbrk(size)) == -1) { 
        return NULL;
    }
    // mem_sbrk가 size바이트의 메모리 할당 못하면, NULL을 반환.(성공하면 할당 메모리의 시작 주소를 반환한다)
    // -1이라면, 힙이 가득 찼거나, 시스템에서 메모리 할당을 허용하지 않거나 기타 시스템 오류를 의미함
    // -1이 아니라면 bp에는 mem_sbrk()의해 할당된 메모리 시작주소가 저장된다. if 들어가지 않고 다음 코드로 넘어감.

    /*새로운 블록을 초기화(header, footer)후 epilogue header를 새로 설정한다*/
    PUT(HDRP(bp), PACK(size, 0)); /*가용 블록 헤더*/
    PUT(FTRP(bp), PACK(size, 0)); /*가용 블록 풋터*/
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /*새로운 epilogue 헤더*/

    /*이전 블록이 가용하다면 합친다*/
    return coalesce(bp);
}

// static void *find_fit(size_t asize) /*first fit*/
// {
//     /*first-fit search*/
//     void *bp;

//     for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
//             //만약 할당이 되어있지 안고, 넣으려는 사이즈가 해당 블록보다 작은 경우
//             return bp; //여기에 할당해
//         }
//     }
//     return NULL; /*맞는 곳이 없다면*/
// }

static void *find_fit(size_t asize) { /*next-fit*/
    void *bp;
    for (bp = anchor; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    for (bp = heap_listp; bp!=anchor; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize) /*초과 부분을 분할하는 함수*/
{
    size_t csize = GET_SIZE(HDRP(bp)); //분할할 블록의 사이즈
    if((csize - asize) >= (2*DSIZE)) { //분할할 곳의 사이즈와 할당할 크기가 헤더풋터제외후 크기보다 크거나 같다면
        PUT(HDRP(bp), PACK(asize, 1)); //나누어 지는 곳 중 채울 곳은 채우고
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        anchor = bp; //next-fit 
        PUT(HDRP(bp), PACK(csize - asize, 0)); //나머지는 비우고
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; /*만들 블록 사이즈*/
    size_t extendsize;/*맞는 블록을 가져갈 수 없으면 늘릴 양*/
    char *bp;
    /*가짜 요청 무시*/
    if(size == 0) {
        return NULL;
    }
    /*정렬 요청과 오버헤드를 포함하기 위해 블록 사이즈 조정*/
    if (size <= DSIZE) { //넣어야 할 데이터의 크기가 DSIZE보다 작다면.
        asize = 2 * DSIZE; /*최소 바이트 사이즈: 16바이트: 헤더4, 풋터4, + 알파*/
    }
    else {
        asize = DSIZE * ((size  + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }////오버헤드 바이트 추가 후 인접 8배수로 반올림

    /*가용 블록을 찾는다*/
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /*가용 공간을 찾을 수 없는 경우 힙 공간을 추가로 가져온다*/
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); //bp가 위치한 블록의 헤더에서 블록 크기를 가져온다.
    PUT(HDRP(bp), PACK(size, 0)); //헤더로 가서 헤더에 사이즈와 0(할당되지 않음)을 넣는다
    PUT(FTRP(bp), PACK(size, 0)); //풋터로 가서 풋터에 사이즈와 0(할당되지 않음)을 넣는다
    coalesce(bp);// 앞이나 뒤가 free라면 합쳐버린다 
}

void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); //이전 블록의 가용 여부(이전 블록의 풋터에서)
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 가용 여부(다음 블록의 헤더에서)
    size_t size = GET_SIZE(HDRP(bp)); //지금 블록의 사이즈

    if (prev_alloc && next_alloc) { // CASE1: 앞이나 뒤가 모두 할당되어 있다면
        return bp;
    }
    else if (prev_alloc && !next_alloc) { // CASE2: 뒷 부분이 할당되어 있지 않으면
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 사이즈는 뒷 블록 사이즈를 가져와 합쳐버린다 
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0)); // FTRP는 HDRP를 기반으로 풋터 위치를 구하므로 굳이 다른 조작할 필요 없음
    }
    else if (!prev_alloc && next_alloc) { // CASE3: 앞 부분이 할당되어 있지 않으면
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); //앞부분의 헤더에 지금 쓸 정보를 덮어쓴다
        bp = PREV_BLKP(bp);
    }
    else { //CASE4: 앞뒤 모두 할당되어있지 않을 때
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    anchor = bp;
    return bp;
}












