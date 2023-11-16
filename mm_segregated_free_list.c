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
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE        sizeof(void *) // Word and header / footer size (bytes)
#define DSIZE        (2 * WSIZE)    // Double word size (bytes)
#define CHUNKSIZE    (1 << 12)      /* Extend heap by this amount (bytes) */
#define SEG_LIST_LEN 20

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)        // get 0xXXXXX___
#define GET_ALLOC(p) (GET(p) & 0x1)         // 0 is free, 1 is allocated

/* Given block bp bp, compute address of its header and footer */
// header pointer = block_pt - header size(wsize)
#define HDRP(bp) ((unsigned char *)(bp)-WSIZE)
// footer pointer = block_pt + block_pt size - dsize
#define FTRP(bp) ((unsigned char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)   

/* Given block bp bp, compute address of next and previous blocks */
// next block pointer = block_pt + size of block_pt
#define NEXT_BLKP(bp) \
    ((unsigned char *)(bp) + GET_SIZE(((unsigned char *)(bp)-WSIZE)))
// previous block pointer = block_pt - previous block size(information in footer)
#define PREV_BLKP(bp) \
    ((unsigned char *)(bp)-GET_SIZE(((unsigned char *)(bp)-DSIZE)))

#define PRED(bp) (*(unsigned char **)(bp))
#define SUCC(bp) (*(unsigned char **)((bp) + WSIZE))

typedef enum { ZERO_BLK = 0, FREE_BLK = 0, ALLOC_BLK = 1 } block_status_t;

/* Declarations */
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *extend_heap(size_t);
static void *coalesce(void *);
static void *attach_free_list(void *bp, size_t asize);
static void *detach_free_list(void *bp);
static size_t asize_to_index(size_t asize);

/* Heap list */
static void *heap_listp = NULL;
static void *free_listp[SEG_LIST_LEN] = {NULL};

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
    // Create the initial emtpy heap
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) {
        return -1;
    }

    PUT(heap_listp, 0);                                     // Alignment padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, ALLOC_BLK));  // Prologue header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, ALLOC_BLK));  // Prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, ALLOC_BLK));      // Epilogue header

    // increments the pointer `heap_listp` to skip over the prologue block
    heap_listp = heap_listp + (2 * WSIZE);

    for (size_t i = 0; i < SEG_LIST_LEN; i++) {
        free_listp[i] = NULL;
    }

    // Extend the empty heap with a free block of CHUNKSIZE bytes
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    size_t asize;
    size_t extend_size;
    unsigned char *bp;

    if (size == 0) {
        return NULL;
    }

    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = DSIZE * ((size + DSIZE + DSIZE - 1) / DSIZE);
    }

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extend_size = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extend_size / WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, FREE_BLK));
    PUT(FTRP(bp), PACK(size, FREE_BLK));
    coalesce(bp);
}

/*
 * coalesce - Combine adjacent free blocks (bp) in the heap to reduce
 * fragmentation.
 */
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // If the previous block and the next block are allocated, it is the default
    // Case 1: Previous block is allocated, next block is free
    if (prev_alloc && !next_alloc) {
        detach_free_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, FREE_BLK));
        PUT(FTRP(bp), PACK(size, FREE_BLK));
    }

    // Case 2: Previous block is free, next block is allocated
    else if (!prev_alloc && next_alloc) {
        detach_free_list(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, FREE_BLK));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, FREE_BLK));
        bp = PREV_BLKP(bp);
    }

    // Case 3: Previous block and next block are both free
    else if (!prev_alloc && !next_alloc) {
        detach_free_list(PREV_BLKP(bp));
        detach_free_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, FREE_BLK));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, FREE_BLK));
        bp = PREV_BLKP(bp);
    }

    attach_free_list(bp, size);
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size) {
    void *old_ptr = bp;
    void *new_ptr;
    size_t old_size = GET_SIZE(HDRP(old_ptr));
    size_t new_size = ALIGN(size + DSIZE);  // Add header, footer byte

    // Case 1: Requested size is equal to the current size
    if (new_size == old_size) {
        return old_ptr;
    }

    // Case 2: Requested size is smaller than the current size
    else if (new_size < old_size) {
        if ((old_size - new_size) >= (2 * DSIZE)) {
            PUT(HDRP(old_ptr), PACK(new_size, ALLOC_BLK));
            PUT(FTRP(old_ptr), PACK(new_size, ALLOC_BLK));
            PUT(HDRP(NEXT_BLKP(old_ptr)), PACK(old_size - new_size, FREE_BLK));
            PUT(FTRP(NEXT_BLKP(old_ptr)), PACK(old_size - new_size, FREE_BLK));
            attach_free_list(NEXT_BLKP(old_ptr), old_size - new_size);
        }
        return old_ptr;
    }

    // Case 3: Combine with the next free block
    else if (!GET_ALLOC(HDRP(NEXT_BLKP(old_ptr))) &&
             (old_size + GET_SIZE(HDRP(NEXT_BLKP(old_ptr)))) >= new_size) {
        detach_free_list(NEXT_BLKP(old_ptr));

        size_t extended_size = old_size + GET_SIZE(HDRP(NEXT_BLKP(old_ptr)));

        if ((extended_size - new_size) >= (2 * DSIZE)) {
            PUT(HDRP(old_ptr), PACK(new_size, ALLOC_BLK));
            PUT(FTRP(old_ptr), PACK(new_size, ALLOC_BLK));
            PUT(HDRP(NEXT_BLKP(old_ptr)),
                PACK(extended_size - new_size, FREE_BLK));
            PUT(FTRP(NEXT_BLKP(old_ptr)),
                PACK(extended_size - new_size, FREE_BLK));
            attach_free_list(NEXT_BLKP(old_ptr), extended_size - new_size);
        } else {
            PUT(HDRP(old_ptr), PACK(extended_size, ALLOC_BLK));
            PUT(FTRP(old_ptr), PACK(extended_size, ALLOC_BLK));
        }
        return old_ptr;
    }

    // Case 4: Combine with the previous free block
    else if (!GET_ALLOC(HDRP(PREV_BLKP(old_ptr))) &&
             (old_size + GET_SIZE(HDRP(PREV_BLKP(old_ptr)))) >= new_size) {
        detach_free_list(PREV_BLKP(old_ptr));

        size_t extended_size = old_size + GET_SIZE(HDRP(PREV_BLKP(old_ptr)));
        old_ptr = PREV_BLKP(old_ptr);

        if ((extended_size - new_size) >= (2 * DSIZE)) {
            memmove(old_ptr, NEXT_BLKP(old_ptr),
                    GET_SIZE(HDRP(NEXT_BLKP(old_ptr))) - (DSIZE));
            PUT(HDRP(old_ptr), PACK(new_size, ALLOC_BLK));
            PUT(FTRP(old_ptr), PACK(new_size, ALLOC_BLK));
            PUT(HDRP(NEXT_BLKP(old_ptr)),
                PACK(extended_size - new_size, FREE_BLK));
            PUT(FTRP(NEXT_BLKP(old_ptr)),
                PACK(extended_size - new_size, FREE_BLK));
            attach_free_list(NEXT_BLKP(old_ptr), extended_size - new_size);
        } else {
            memmove(old_ptr, NEXT_BLKP(old_ptr),
                    GET_SIZE(HDRP(NEXT_BLKP(old_ptr))) - (DSIZE));
            PUT(HDRP(old_ptr), PACK(extended_size, ALLOC_BLK));
            PUT(FTRP(old_ptr), PACK(extended_size, ALLOC_BLK));
        }
        return old_ptr;
    }

    // Case 5: Allocate a new block and free the old block
    else {
        new_ptr = mm_malloc(new_size);
        if (new_ptr == NULL) return NULL;
        memcpy(new_ptr, old_ptr, old_size);
        mm_free(bp);
        return new_ptr;
    }
}
/*
 * extend_heap - Extend the heap by allocating a new free block.
 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    // Allocate an even number of words to maintain alignment
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }

    // Initialize free block header/footer and the epilogue header
    PUT(HDRP(bp), PACK(size, FREE_BLK));           // Free block header
    PUT(FTRP(bp), PACK(size, FREE_BLK));           // Free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, ALLOC_BLK));  // New epilogue header

    // Coalesce if the previous block was free
    return coalesce(bp);
}

/*
 * find_fit - Find a free block in the segregated free list that can accommodate
 * the requested block size (asize).
 */
static void *find_fit(size_t asize) {
    size_t start_index = asize_to_index(asize);

    // Iterate through the segregated free list starting from the determined
    // index
    for (size_t i = start_index; i < SEG_LIST_LEN; i++) {
        if (free_listp[i] == NULL) {
            continue;
        }

        // Iterate through the blocks in the current free list
        for (void *bp = free_listp[i]; bp != NULL; bp = SUCC(bp)) {
            if (GET_SIZE(HDRP(bp)) >= asize) {
                return bp;
            }
        }
    }

    return NULL;
}

/*
 * place - Place a block of the specified size at the beginning of the free
 * block(bp).
 */
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    detach_free_list(bp);

    // Check if splitting the block is necessary
    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, ALLOC_BLK));
        PUT(FTRP(bp), PACK(asize, ALLOC_BLK));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, FREE_BLK));
        PUT(FTRP(bp), PACK(csize - asize, FREE_BLK));
        coalesce(bp);
    }
    // Allocate the entire block without splitting
    else {
        PUT(HDRP(bp), PACK(csize, ALLOC_BLK));
        PUT(FTRP(bp), PACK(csize, ALLOC_BLK));
    }
}

/*
 * attach_free_list - Attach a free block (bp) to the appropriate position in
 * the free list.
 */
static void *attach_free_list(void *bp, size_t asize) {
    void *next_bp;
    void *prev_bp = NULL;

    size_t index = asize_to_index(asize);

    next_bp = free_listp[index];

    // Find the appropriate position in the free list based on block size
    while ((next_bp != NULL) && (asize > GET_SIZE(HDRP(next_bp)))) {
        prev_bp = next_bp;
        next_bp = SUCC(next_bp);
    }

    // Update pointers to insert the block into the free list
    if (next_bp != NULL) {
        // Insert the block between prev_bp and next_bp
        if (prev_bp != NULL) {
            SUCC(bp) = next_bp;
            PRED(bp) = prev_bp;
            PRED(next_bp) = bp;
            SUCC(prev_bp) = bp;
        }
        // Insert the block at the beginning of the free list
        else {
            SUCC(bp) = next_bp;
            PRED(bp) = NULL;
            PRED(next_bp) = bp;
            free_listp[index] = bp;
        }
    } else {
        // Insert the block at the end of the free list
        if (prev_bp != NULL) {
            SUCC(bp) = NULL;
            PRED(bp) = prev_bp;
            SUCC(prev_bp) = bp;
        }
        // The free list is empty, insert the block as the only element
        else {
            SUCC(bp) = NULL;
            PRED(bp) = NULL;
            free_listp[index] = bp;
        }
    }

    return bp;
}

/*
 * detach_free_list - Detach a free block (bp) from the segregated free list.
 */
static void *detach_free_list(void *bp) {
    size_t asize = GET_SIZE(HDRP(bp));
    size_t index = asize_to_index(asize);

    // Check if the block is at the beginning of the free list
    if (bp == free_listp[index]) {
        free_listp[index] = SUCC(bp);
    }

    // Check if the block is at the end of the free list
    else if (SUCC(bp) == NULL) {
        SUCC(PRED(bp)) = NULL;
    }

    // The block is in the middle of the free list
    else if (SUCC(bp) != NULL) {
        SUCC(PRED(bp)) = SUCC(bp);
        PRED(SUCC(bp)) = PRED(bp);
    }

    return bp;
}

/*
 * asize_to_index - Convert block size (asize) to the corresponding index in the
 * segregated free list.
 */
static size_t asize_to_index(size_t asize) {
    size_t power = 1;
    size_t index = 0;

    // Handle the special case when asize is 0
    if (asize == 0) {
        return 0;
    }

    // Calculate the index based on powers of 2
    while (power <= asize) {
        power <<= 1;
        index += 1;
    }

    // Ensure that the index does not exceed the maximum index in the segregated
    // free list
    if (index >= SEG_LIST_LEN) {
        index = SEG_LIST_LEN - 1;
    }
    return index;
}