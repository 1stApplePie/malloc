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
    "3team",
    /* First member's full name */
    "admin",
    /* First member's email address */
    "a@a",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

// Basic constants and macros
#define WSIZE       4       // Word and header / footer size (bytes)
#define DSIZE       8       // Double word size (bytes)
#define CHUNKSIZE   1 << 12 // Extemd heap by this amount (bytes)

#define MAX(x, y) ((x) > (y)) ? (x) : (y)

// Pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

// Read and write a word at address p
#define GET(p) (*(unsigned int *) (p))
#define PUT(p, val) (*(unsigned int *) (p) = (val))

// Read the size and allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~0x7) // get 0xXXXXXXX_
#define GET_ALLOC(p) (GET(p) & 0x1) // 0 is free, 1 is allocated

// Given block ptr block_pt, compute address of its header and footer
#define HDRP(block_pt) ((char *)(block_pt) - WSIZE) // header pointer = block_pt - header size(wsize)
#define FTRP(block_pt) ((char *)(block_pt) + GET_SIZE(HDRP(block_pt)) - DSIZE)    // footer pointer = block_pt + block_pt size - dsize

// Given block ptr block_pt, compute address of next and previous blocks
#define NEXT_BLKP(block_pt) ((char *)(block_pt) + GET_SIZE((char *)(block_pt) - WSIZE))   // next block pointer = block_pt + size of block_pt - wsize
#define PREV_BLKP(block_pt) ((char *)(block_pt) - GET_SIZE((char *)(block_pt) - DSIZE))   // previous block pointer = (block_pt - wsize) - previous block size(information in footer) + wsize 

/* Private local function Declaration */
static void *coalesce(void *);
static void *extend_heap(size_t);
static void *find_fit(size_t);
static void place(void *, size_t);

/* Private local variable Declaration*/
static char *heap_pt;
static char *last_block_pt;

/* Function Definition */
/* 
 * coalesce - Free block coalescing for efficient memory management.
 */
static void *coalesce(void *block_pt) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(block_pt)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(block_pt)));
    size_t size = GET_SIZE(HDRP(block_pt));

    if (prev_alloc && next_alloc) {         // case 1
        return block_pt;
    }

    else if (prev_alloc && !next_alloc) {   // case 2
        size += GET_SIZE(HDRP(NEXT_BLKP(block_pt)));
        PUT(HDRP(block_pt), PACK(size, 0));
        PUT(FTRP(block_pt), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {   // case 3
        size += GET_SIZE(HDRP(PREV_BLKP(block_pt)));
        PUT(FTRP(block_pt), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(block_pt)), PACK(size, 0));
        block_pt = PREV_BLKP(block_pt);
    }

    else {                                  // case 4
        size += GET_SIZE(HDRP(PREV_BLKP(block_pt))) +
        GET_SIZE(FTRP(NEXT_BLKP(block_pt)));
        PUT(HDRP(PREV_BLKP(block_pt)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(block_pt)), PACK(size, 0));
        block_pt = PREV_BLKP(block_pt);
    }
    
    return block_pt;
}

/* 
 * extend_heap - Extend the heap by allocating a new free block.
 */
static void *extend_heap(size_t words) {
    char *block_pt;
    size_t size;

    // Allocate an even number of words to maintain alignment
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(block_pt = mem_sbrk(size)) == -1)
        return NULL;

    // Initialize free block header/footer and the epilogue header
    PUT(HDRP(block_pt), PACK(size, 0));           // Free block header
    PUT(FTRP(block_pt), PACK(size, 0));           // Free block footer
    PUT(HDRP(NEXT_BLKP(block_pt)), PACK(0, 1));   // New epilogue header

    // Coalesce if the previous block was free
    return coalesce(block_pt);
}

/* 
 * find_fit - Function to search for a memory block to be used for memory allocation
 */
static void *find_fit(size_t asize) {
    char *block_pt;
    // First-fit search
    // Search for blocks after heap_pt
    for (block_pt = heap_pt; GET_SIZE(HDRP(block_pt)) > 0; block_pt = NEXT_BLKP(block_pt)) {
        if (!GET_ALLOC(HDRP(block_pt)) && (asize <= GET_SIZE(HDRP(block_pt)))) {
            return block_pt;
        }
    }

    return NULL;    // No fit
}

/* 
 * place - Place the allocated block within a free block, splitting it if necessary.
 */
static void place(void * block_pt, size_t asize) {
    size_t csize = GET_SIZE(HDRP(block_pt));

    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(block_pt), PACK(asize, 1));
        PUT(FTRP(block_pt), PACK(asize, 1));
        block_pt = NEXT_BLKP(block_pt);
        PUT(HDRP(block_pt), PACK(csize-asize, 0));
        PUT(FTRP(block_pt), PACK(csize-asize, 0));
    }
    else {
        PUT(HDRP(block_pt), PACK(csize, 1));
        PUT(FTRP(block_pt), PACK(csize, 1));
    }
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // Create the initial emtpy heap
    if ((heap_pt = mem_sbrk(4*WSIZE)) == (void *) - 1) 
        return -1;
    
    PUT(heap_pt, 0);                            // Alignment padding
    PUT(heap_pt + (1*WSIZE), PACK(DSIZE, 1));   // Prologue header
    PUT(heap_pt + (2*WSIZE), PACK(DSIZE, 1));   // Prologue footer
    PUT(heap_pt + (3*WSIZE), PACK(0, 1));       // Epilogue header
    
    heap_pt += (2*WSIZE);

    // Extend the empty heap with a free block of CHUNKSIZE bytes
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;         // Adjusted block size
    size_t extendsize;      // Amount to extend heap if no fit
    char *block_pt;

    // Ignore spurious requests
    if (size == 0) 
        return NULL;

    // Adjust block size to include overhead and alignment reqs
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    // Search the free list for a fit
    if ((block_pt = find_fit(asize)) != NULL) {
        place(block_pt, asize);

        return block_pt;
    }

    // No fit found. Get more memory and place the block
    extendsize = MAX(asize, CHUNKSIZE);
    if ((block_pt = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(block_pt, asize);

    return block_pt;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *old_ptr = ptr;
    void *new_ptr;
    size_t old_size = GET_SIZE(HDRP(old_ptr));
    size_t new_size = size + (2*WSIZE);    // Add header, footer byte
      
    if (new_size <= old_size) {
        return old_ptr;
    }

    else {
        new_ptr = mm_malloc(new_size);
        if (new_ptr == NULL) 
            return NULL;
        place(new_ptr, new_size);
    }

    memcpy(new_ptr, old_ptr, new_size);
    mm_free(ptr);
    return new_ptr;
}