/*
 * mm.c
 *
 * Arun Marsten
 * amarsten
 * 15213
 *
 * I implemented my malloc using an explicit list structure, which used
 * the system of adding predecessor and successor nodes to the free list.
 * The allocated blocks had only an identical header and footer, while the 
 * free blocks contained two 4byte offsets (which could be used thanks to 
 * the fact that the heap was only 2^32 bytes) which pointed to the free 
 * blocks that were before and after it in the list.
 *
 * The explicit list used a LIFO structure which meant that every new
 * free block got added to the beginning of the free list. 
 *
 * When the free blocks got coalesced I simply switched around the 
 * next and prev pointers to remove the nodes that got coalesced from 
 * the free list.
 *
 * In find fit I used a mixture of first fit and best fit. I would loop 
 * through the free list to find a node of appropriate size. After that 
 * I would check the next few nodes to see if there were any after it
 * that were more suitable.
 *
 * For ease of calculation I used heap_listp as the front and back of my free list.
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...)    printf(__VA_ARGS__)
#define CHECKHEAP(verbose)  mm_checkheap(verbose);
#define ENTER   printf("Entering %s\n", __func__);
#define EXIT   printf("Exiting %s\n", __func__);
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/*
 * Initialize: return -1 on error, 0 on success.
 */
/*
 *  * If NEXT_FIT defined use next fit search, else use first fit search 
 *   */
#define NEXT_FITx

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ //line:vm:mm:beginconst
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<9)  /* Extend heap by this amount (bytes) */  //line:vm:mm:endconst 
#define MINBLKSIZE  (2*DSIZE)

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            //line:vm:mm:get
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    //line:vm:mm:put

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)                    //line:vm:mm:getalloc

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      //line:vm:mm:hdrp
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //line:vm:mm:ftrp

/* Given lock ptr bp, compute and/or set pred and succ */
#define GET_PRED(bp)    (COMP_ADDRESS(*((unsigned int *)(bp))))
#define GET_SUCC(bp)    (COMP_ADDRESS(*((unsigned int *)(bp + WSIZE))))
#define SET_PRED(bp, val)   (*(unsigned int *)bp = (unsigned int)COMP_OFFSET(val))
#define SET_SUCC(bp, val)   (*(unsigned int *)(bp + WSIZE) = (unsigned int)COMP_OFFSET(val)) 


/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //line:vm:mm:nextblkp
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //line:vm:mm:prevblkp
/* $end mallocmacros */

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */  
static char *first_free;
#ifdef NEXT_FIT
static char *rover;           /* Next fit rover */
#endif

#define COMP_OFFSET(address)    (unsigned long int)(address) - (unsigned long int)(heap_listp)    
#define COMP_ADDRESS(offset)    (unsigned long int)(heap_listp) + (unsigned long int)(offset)

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);
void mm_checkheap(int verbose);
static int in_freelist(void *bp);
static void freelist_add(void *bp);

/* 
 *  * mm_init - Initialize the memory manager 
 *   */
int mm_init(void) 
{
    ;
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) //line:vm:mm:begininit
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);                     //line:vm:mm:endinit  
    first_free = heap_listp;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    ;
    return 0;
}

/* 
 *  * malloc - Allocate a block with at least size bytes of payload 
 *   */
void *malloc(size_t size) 
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      

    if (heap_listp == 0){
        mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= MINBLKSIZE)                        
        asize = 3*DSIZE;                                        
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); 

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  
        place(bp, asize);                  
        ;
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);                 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;                                  
    place(bp, asize);                                 
    
    return bp;
} 



/* 
 *  * free - Free a block 
 *   */
void free(void *bp)
{
    if(bp == 0) 
        return;

    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0){
        mm_init();
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    freelist_add(bp);
    coalesce(bp);
    ;
}

/*
 * are_adjacent - Handles the case of the two blocks being coalesced
 * being next to each other in the list
 */ 
static void are_adjacent(void *bp, int case3)
{
    if(case3){
        void *next = (void *)GET_SUCC(bp);
        SET_PRED(next, heap_listp);
        first_free = next;
    }
    else{
        void *new_succ = (void *)GET_SUCC(GET_SUCC(bp));
        SET_SUCC(bp, new_succ);
        if (new_succ != heap_listp)
            SET_PRED(new_succ, bp);
    }
}

/*
 * not_adjacent - Handles the case of the two blocks being coalesced
 * not being next to each other in the list
 */ 
static void not_adjacent(void *bp, int case3)
{
    if(case3){
        void* prev = PREV_BLKP(bp);
        
        SET_SUCC((void *)GET_PRED(prev), GET_SUCC(prev));
        if ((char *)GET_SUCC(prev) != heap_listp)
            SET_PRED((void *)GET_SUCC(prev), GET_PRED(prev));
        SET_PRED(prev, heap_listp);
        SET_SUCC(prev, GET_SUCC(bp));
        first_free = prev;
        SET_PRED((void *)GET_SUCC(bp), first_free);
    }
    else{
        void *next = NEXT_BLKP(bp);
        void *pred = (void *)GET_PRED(next);
        void *succ = (void *)GET_SUCC(next);

        SET_SUCC(pred, succ);
        if (succ != heap_listp)
            SET_PRED(succ, pred);
    }
}

/*
 *  * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 *   */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        if ((void *)GET_SUCC(bp) == NEXT_BLKP(bp))
            are_adjacent(bp, 0);
        else 
            not_adjacent(bp, 0);
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        if ((void *)GET_SUCC(bp) == PREV_BLKP(bp))
            are_adjacent(bp, 1);
        else 
            not_adjacent(bp, 1);
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {                                     /* Case 4 */
        if ((void *)GET_SUCC(bp) == NEXT_BLKP(bp))
            are_adjacent(bp, 0);
        else 
            not_adjacent(bp, 0);
        if ((void *)GET_SUCC(bp) == PREV_BLKP(bp))
            are_adjacent(bp, 1);
        else 
            not_adjacent(bp, 1);
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 *  * realloc - Naive implementation of realloc
 *   */
void *realloc(void *ptr, size_t size)
{
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return malloc(size);
    }

    newptr = malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    free(ptr);

    return newptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc (size_t nmemb, size_t size)
{
  size_t bytes = nmemb * size;
  void *newptr;

  newptr = malloc(bytes);
  memset(newptr, 0, bytes);

  return newptr;
}

/* 
 *  * The remaining routines are internal helper routines 
 *   */

/* 
 *  * extend_heap - Extend heap with free block and return its block pointer
 *   */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1)  
        return NULL;                                        

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */  
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 
    

    /* Add extension of heap to the free list */
    freelist_add(bp);

    /* Coalesce if the previous block was free */
    return coalesce(bp);                                          
}

/* 
 *  * place - Place block of asize bytes at start of free block bp 
 *   *         and split if remainder would be at least minimum block size
 *    */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); 
    void *pred = (void *)GET_PRED(bp);
    void *succ = (void *)GET_SUCC(bp);

        if((csize - asize) >= (3*DSIZE)) {
            PUT(HDRP(bp), PACK(asize, 1));
            PUT(FTRP(bp), PACK(asize, 1));
            void *new_bp = NEXT_BLKP(bp);
            PUT(HDRP(new_bp), PACK(csize-asize, 0));
            PUT(FTRP(new_bp), PACK(csize-asize, 0));
            SET_PRED(new_bp, pred);
            SET_SUCC(new_bp, succ);
            if(pred != heap_listp)
                SET_SUCC(pred, new_bp);
            if(succ != heap_listp)
                SET_PRED(succ, new_bp);
            if(bp == first_free)
                first_free = new_bp;
        }

        else { 
            PUT(HDRP(bp), PACK(csize, 1));
            PUT(FTRP(bp), PACK(csize, 1));
            if (pred == heap_listp){
                first_free = (char *)succ;
                if (succ != heap_listp){
                    SET_PRED(first_free, heap_listp);
                }
            }
            else if (succ != heap_listp){
                SET_SUCC(pred, succ);
                SET_PRED(succ, pred);
            }
            else{
                SET_SUCC(pred, succ);
            }
        }
}

/* 
 *  * find_fit - Find a fit for a block with asize bytes 
 *   */
static void *find_fit(size_t asize)
{
    /* First fit search */
    void *bp;

    for (bp = first_free; bp != heap_listp; bp = (void *)(GET_SUCC(bp))) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }

    return NULL;
}
/*
 * freelist_add - Adds bp to the front of the free list
 * for LIFO structure
 */
static void freelist_add(void *bp)
{ 

    SET_PRED(bp, heap_listp);
    SET_SUCC(bp, first_free);
    if (first_free != heap_listp)
        SET_PRED(first_free, bp);
    first_free = bp;
}


static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%c:%c]\n", bp, 
         (unsigned int)hsize, (halloc ? 'a' : 'f'), 
         (unsigned int)fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8){
        printf("Error: %p is not doubleword aligned\n", bp);
        exit(0);
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp))){
        printf("Error: header does not match footer\n"); 
        exit(0);
    }
    if (!GET_ALLOC(HDRP(bp))){
        if (!(in_freelist(bp))){
            printf("Error: free block not in free list\n");
            exit(0);
        }
        if((void *)GET_SUCC(bp) == bp){
            printf("Cycle\n");
            exit(0);
        }

    }
}

/* Checks if a block is in the free list */
int in_freelist(void *bp)
{
    char *list_ptr;
    for (list_ptr = first_free; list_ptr != heap_listp; list_ptr = (void *)(GET_SUCC(list_ptr))){
        if (list_ptr == bp){            
            return 1;
        }
    }
    return 0;
}

/* 
 *  * checkheap - Minimal check of the heap for consistency 
 *   */
void mm_checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose)
        printf("Heap (%p):\n", heap_listp);


    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))){
        printf("Bad prologue header\n");
        exit(0);
    }

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) 
            printblock(bp);
        checkblock(bp);
    }

    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))){
        printf("Bad epilogue header\n");
        exit(0);
    }

}
