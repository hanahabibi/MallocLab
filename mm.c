/*
 *
 *  DESCRIPTION:
 *
 *  Our allocator uses two lists to store blocks. The global variable heap_listp points to the beginning of the heap.
 *  The global variable free_listp points to the beginning of the freelist which is used to store all the free blocks of the heap.
 *  We initialize both lists by calling mm_init. This method creates a prologue block which consists of header and footer and an epilogue block
 *  which consists of only a header. The free_lisp is set to NULL since there aren't any free blocks yet.
 *
 *  When mm_malloc is called the allocator searches for a fitting block in the freelist using the first-fit algorithm (find_fit). If a fitting block
 *  is found the bytes are placed (place) into the block. If the found block can store more than the requested number of bytes and there are still enough
 *  bytes left to store another block of minimum 16 bytes, the found block gets split into two and the free one is added back to the freelist.
 *
 *  In case that a fitting block doesn't exist the heap needs to be extended (extend_heap). extend_heap calculates the number of bytes that are needed
 *  and makes sure to align them.
 *
 *  The mm_free method frees a block and calls coalesce to check if the freed block is next to another free block(s). If so, the method coalesces them and
 *  modifies the heap and the freelist.
 *
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
        "Hana Habibi",
        /* First member's email address */
        "hana.habibi@stud.uni-due.de",
        /* Second member's full name (leave blank if none) */
        "Noemi Kallweit",
        /* Second member's email address (leave blank if none) */
        "noemi.kallweit@stud.uni-due.de"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)

/* Minimum size a block can have */
#define MINIMUM 16

/* Returns the maximum of two sizes */
#define MAX(x, y) ((x)>(y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* read size and allocation bit */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Used for valid heap checking */
#define GET_ALIGN(p) (GET(p) & 0x7)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given block ptr bp of free block, compute address of next and previous free blocks */
#define NEXT_FREE(bp) (GET(bp + WSIZE))
#define PREV_FREE(bp) (GET(bp))

/* Global variables */
static char *heap_listp;  /* Pointer to first block of heap */
char *free_listp;         /* Pointer to first block of freelist */

/* Pointer to epilogue block */
char *epilogue = 0;

/* Declarations */
static void *find_fit(size_t asize);
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void add_freeblock(void *bp);
static void remove_freeblock(void *bp);
static int mm_check();

/*
 * initializes the allocator
 */
int mm_init(void)
{

    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)                         // create the initial empty heap
        return -1;
    PUT(heap_listp, 0);                                                         // alignment padding
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));                                // set the prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));                                // set the prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));                                    // set the epilogue header
    epilogue = (heap_listp + (3*WSIZE));                                        // needed for heap checker
    heap_listp += (2*WSIZE);
    free_listp = NULL;                                                          // initialize the freelist to be empty

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)                                   // extend the empty heap with a free block of CHUNKSIZE bytes
        return -1;
    return 0;
}

/*
 * allocates a block on the heap
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)                                                              // if the block's size is 0 do nothing
        return NULL;

    if (size <= DSIZE)                                                          // if the size is less than the minimum block size,
        asize = MINIMUM;                                                        // set it to minimum
    else                                                                        // align the size to be a multiple of 8
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1))/ DSIZE);

    if ((bp = find_fit(asize)) != NULL){                                        // search for a fit and places the block if one is found
        place(bp, asize);
        return bp;
    }
    extendsize = MAX(asize, CHUNKSIZE);                                         // set the number of bytes to extend the heap to the maximum of asize and CHUNKSIZE
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)                           // if no fit was found the heap needs to be extended
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * remove the block from the malloc list and free the place
 */
void mm_free(void *ptr)
{
    if(ptr == NULL || heap_listp == NULL)                                      // if freeing nothing or if heap isn't initialized yet, return
        return;

    size_t size = GET_SIZE(HDRP(ptr));                                         // get size of the block
    PUT(HDRP(ptr), PACK(size, 0));                                             // set size of the block in header must be 0
    PUT(FTRP(ptr), PACK(size, 0));                                             // set size of the block in footer must be 0
    coalesce(ptr);                                                             // coalesce the block, if needed
}


/*
 * Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size){
    /*
     * ATTENTION: You do not need to implement realloc for this assignment
     */
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

/*
 * finds a fitting block for asize bytes using first fit search
 */
static void *find_fit(size_t asize){
    void *bp = free_listp;                                                      // point to the beginning of the freelist
    for(; bp != NULL; bp = (char *) NEXT_FREE(bp)) {                            // iterate through freelist until it finds a block that fits a size
        if(asize <= GET_SIZE(HDRP(bp)))
            return bp;
    }
    return NULL;                                                                // if there is no fit it return NULL
}

/*
* extends the heap by adding a free block to the end of size bytes
*/
static void *extend_heap(size_t words){
    char *bp;
    size_t size;                                                                // make sure the block will be aligned
    size = (words % 2) ? (words+1) * WSIZE: words * WSIZE;                      // calculate the number of bytes that have to be added to the heap
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));                                               // initialize the header and footer of the new block
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));                                        // set the block after the new block the be the epilogue block

    return coalesce(bp);                                                        // try coalescing
}

/*
 * places asize bytes in a block and splits the block if it can still store at least 16 bytes
 */
static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));                                          // size of block where asize bytes are placed
    if ((csize-asize) >= MINIMUM) {                                             // if the current block's size can still at least store MIMIMUM bytes the block is split
        remove_freeblock(bp);                                                   // remove the block from freelist
        PUT(HDRP(bp), PACK(asize, 1));                                          // set size in block's header to asize and allocation bit to 1
        PUT(FTRP(bp), PACK(asize, 1));                                          // set size in block's footer to asize and allocation bit to 1
        bp = NEXT_BLKP(bp);                                                     // set pointer to next block
        PUT(HDRP(bp), PACK(csize - asize, 0));                                  // set size in next block's header to the remaining bits and allocation bit to 0
        PUT(FTRP(bp), PACK(csize - asize, 0));                                  // set size in next block's footer to the remaining bits and allocation bit to 0
        add_freeblock(bp);                                                      // add the free block to the freelist
    }
    else{                                                                       // if the block isn't large enough to be split use the whole block
        PUT(HDRP(bp), PACK(csize,1));                                           // set size in block's header to csize and allocation bit to 1
        PUT(FTRP(bp), PACK(csize,1));                                           // set size in block's header to csize and allocation bit to 1
        remove_freeblock(bp);                                                   // remove the block from free list
    }
}

/*
 * checks if the adjacent blocks are also free and coalesces them
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));                         // store allocation bit of previous block
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));                         // store allocation bit of next block
    size_t size = GET_SIZE(HDRP(bp));                                           // store size of current block

    if (prev_alloc && next_alloc) {                                             // if the next and previous block are allocated, no coalescing possible
        add_freeblock(bp);                                                      // add block to freelist
        return bp;
    }

    else if (prev_alloc && !next_alloc) {                                       // if the next block is free and previous is allocated coalesce current and next block
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));                                  // set size of new block to size of next + size of current block
        remove_freeblock(NEXT_BLKP(bp));                                        // remove next block from freelist, since it won't exist anymore
        PUT(HDRP(bp), PACK(size, 0));                                           // set new size in block's header
        PUT(FTRP(bp), PACK(size,0));                                            // set new size in block's footer
        add_freeblock(bp);                                                      // add new block to the freelist
    }

    else if (!prev_alloc && next_alloc) {                                       // if previous block is free and next is allocated
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));                                  // set size of new block to size of previous + size of current block
        remove_freeblock(PREV_BLKP(bp));                                        // remove previous block from freelist, since it won't exist anymore
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));                                // set new size in previous block's header
        PUT(FTRP(bp), PACK(size, 0));                                           // set new size in footer
        bp = PREV_BLKP(bp);                                                     // set the block pointer to the previous block since this is the new beginning of the block
        add_freeblock(bp);                                                      // add new block to the freelist
    }

    else {                                                                      // if both adjacent blocks are free
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));  // set size of new block to size of previous + size of current + size of next block
        remove_freeblock(PREV_BLKP(bp));                                        // remove previous block from freelist
        remove_freeblock(NEXT_BLKP(bp));                                        // remove next block from freelist
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));                                // set new size in previous block's header
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));                                // set new size in next block's header
        bp = PREV_BLKP(bp);                                                     // set the block pointer to the previous block since this is the new beginning of the block
        add_freeblock(bp);                                                      // add new block to the freelist
    }

    //mm_check();

    return bp;
}

/*
 * adds a new free block to the beginning of the freelist
 */
static void add_freeblock(void *bp){

    if (free_listp == NULL){                                                    // if the list is empty,
        free_listp = bp;                                                        // set bp to be the first element of the list
        PUT(bp, 0);                                                             // set previous of block to 0
        PUT(bp+WSIZE, 0);                                                       // set next of block to 0
    }
    else {
        PUT(((char *) free_listp), (int) bp);                                   // set the current head of the list's previous to bp
        PUT(bp, 0);                                                             // set bp's previous to 0
        PUT(bp + WSIZE, (int) free_listp);                                      // set bp's next to the head of the list
        free_listp = bp;                                                        // set the head of the list to bp
    }
}

/*
 * removes free block from the freelist by adjusting the pointers to the previous and next blocks of the removed one
 */
static void remove_freeblock(void *bp){

    if ((PREV_FREE(bp) == 0) && (NEXT_FREE(bp) == 0)){                          // if the block doesn't have a previous or next block it means that it is the only one in the freelist
        free_listp = 0;
    }
    else if (PREV_FREE(bp) == 0 && NEXT_FREE(bp) != 0){                         // if the block has a next but not a previous block it means that it is the first one in the list
        free_listp = (char *)NEXT_FREE(bp);                                     // set beginning of the list to next block
        PUT((char *) NEXT_FREE(bp), 0);                                         // set next block's previous to 0
    }
    else if (PREV_FREE(bp) != 0 && NEXT_FREE(bp) == 0){                         // if the block has a previous but not a next block it means that it is the last one in the list
        PUT(((char *)PREV_FREE(bp) + WSIZE), 0);                                // set the previous block's next to 0
    }
    else{                                                                       // if the block is in middle of the list
        PUT(((char *)PREV_FREE(bp) + WSIZE), NEXT_FREE(bp));                    // set previous block's next to point to bp's next
        PUT(((char *)NEXT_FREE(bp)), PREV_FREE(bp));                            // set next blocks's previous to previous block
    }
}

/*
 * checks if the blocks in the free list are not allocated
 */
static int correct_free_marked(void){
    void *bp = free_listp;
    for (bp = free_listp; bp != NULL; ) {                                       // iterate through the free list
        if (GET_ALLOC(HDRP(bp))) {                                              // if any block is allocated
            printf("Error: block in free list but marked allocated\n");         // print an error message
            return 0;                                                           // return error
        }
        bp = (char *)NEXT_FREE(bp);                                             // go to the next free block
    }
    return 1;
}

/*
 * checks that no blocks escaped coalescing
 */
static int check_coalescing(){
    char* bp = heap_listp;                                                       // pointer to the heap list
    if(GET_ALLOC(bp) == 0){                                                      // if block not allocated
        if (NEXT_BLKP(bp) != NULL && !GET_ALLOC(HDRP(NEXT_BLKP(bp)))){           // and the next one is also not allocated
            printf("Error: next block not coalesced\n");                         // then the blocks are not coalesced, print error message
            return 0;                                                            // return error
        }
    }
    return 1;
}

/*
 * checks that every free block of the heap is on the freelist.
 */
static int check_freelist(void){
    void *bp = heap_listp;				                           // pointer to the heap list
    while (bp != NULL && GET_SIZE(HDRP(bp)) != 0){                               // iterate through the heap list
        if (GET_ALLOC(HDRP(bp)) == 0){ 		                           // if it finds a free block
            void *cmp = free_listp;   		                           // get the beginning of the free blocks list
            while (bp != cmp){  			                           // iterate through the free blocks list
                if (GET_SIZE(HDRP(cmp)) == 0){                                   // if we reach the end of the list before finding the free block on the free list
                    printf("Error: Free block not found in freelist\n");         // return an error message
                    return 0;                                                    // return an error
                }
                cmp = (char *)NEXT_FREE(cmp);                                            // get the next block in the freelist
            }
        }
        bp = NEXT_BLKP(bp);                                                      // get the next block in the heap list
    }
    return 1;
}


/*
 * check whether any of the allocated blocks overlap each other
 */
static int check_overlap(void){
    void *bp = heap_listp;                                                       // pointer to the heap list
    while(bp != NULL && GET_SIZE(HDRP(bp))!=0){                                  // iterate through the heap list
        if(GET_ALLOC(HDRP(bp))){                                                 // if pointed block is allocated
            if (bp + GET_SIZE(HDRP(bp)) - WSIZE >= (void*)NEXT_BLKP(bp)) {       // if current pointer + size is greater than address of next, there is an overlap
                printf("Error: Overlapping occured\n");                          // if overlap occurs return error message
                return 0;                                                        // return error
            }
        }
        bp = NEXT_BLKP(bp);                                                      // else go to the next block
    }
    return 1;
}

/*
 * check to see if pointers in heap block point to a valid heap address
 *  - pointer has to be smaller than the next block pointers
 *  - pointer has to be aligned to 8
 */
static int check_valid_heap(void){
    char *bp;
    for(bp = NEXT_BLKP(heap_listp); bp < epilogue; bp = NEXT_BLKP(bp)) {                      // iterate through the heap list
        if((HDRP(bp) < HDRP(NEXT_BLKP(heap_listp))) || (GET_ALIGN(HDRP(bp)) != 8)) {          // if any of the conditions is true
            printf("Error: current block does not point to a valid heap address: %p\n", bp);  // print an error message
            return 0;                                                                         // return an error
        }
    }
    return 1;
}

/*
 * checks if both header and footer of the blocks in the free list are not allocated
 */
static int check_consistency(void){
    char* free = free_listp;                                                                  // we use the free blocks list
    for (; free != NULL; free = (char *) NEXT_FREE(free)){                                    // iterate through it
        if (GET_ALLOC(HDRP(free)) || GET_ALLOC(FTRP(free))){                                  // if the header or the footer would be allocated
            printf("Error: header and footer are inconsistent in free list \n");              // print an error message
            return 0;                                                                         // return an error
        }
    }
    return 1;
}

/*
 * heapchecker checks:
 *   -  Is every block in the free list marked as free?                       -> correct_free_marked()
 *   -  Are there any contiguous free blocks that somehow escaped coalescing? -> check_coalescing()
 *   -  Is every free block actually in the free list?                        -> check_freelist()
 *   -  Do the pointers in the free list point to valid free blocks?          -> check_consistency(), check_freelist()
 *   -  Do any allocated blocks overlap                                       -> check_overlap()
 *   -  Do the pointers in a heap block point to valid heap addresses?        -> check_valid_heap()
 */
int mm_check(void)
{
    if(correct_free_marked() == 0)
        return 0;
    if (check_coalescing() == 0)
        return 0;
    if (check_freelist() == 0)
        return 0;
    if (check_overlap() == 0)
        return 0;
    if (check_valid_heap() == 0)
        return 0;
    if(check_consistency() == 0)
        return 0;

    return 1;
}
