/*
 * mm.c -  Simple allocator based on segregated free list implementation.
 * There are several free lists (28) that a free block can be placed in or removed from.
 * All of these lists are initialized to NULL and blocks are added as they are found as free.
 * Each list contains block of the same size, and the allocator searches through the list
 * to place a free block. Can either split block or if no eligible block, try next list. 
 * My implementation also uses first fit search of the whole list.
 *
 * Each block has header and footer of the form:
 *
 *            4           4
 *      --------------------------------
 *     |   unused   | block_size | a/f |
 *      --------------------------------
 * 
 * Furthermore, each free block is at min 32 bytes.
 *
 * a/f is 1 iff the block is allocated. The list has the following form:
 *
 * begin                                       end
 * heap                                       heap
 *  ----------------------------------------------
 * | hdr(8:a) | zero or more free blks | hdr(0:a) |
 *  ----------------------------------------------
 * | prologue |                       | epilogue |
 * | block    |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */
#include "memlib.h"
#include "mm.h"
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* Your info */
team_t team = {
  /* First and last name */
  "Elizabeth Kim",
  /* UID */
  "005736849",
  /* Custom message (16 chars) */
  "slayful",
};

typedef struct {
  uint32_t allocated : 1;
  uint32_t block_size : 31;
  uint32_t _;
} header_t;

typedef header_t footer_t;

typedef struct block_t {
  uint32_t allocated : 1;
  uint32_t block_size : 31;
  uint32_t _;
  union {
      struct {
        struct block_t* next;
        struct block_t* prev;
      };
      int payload[0];
  } body;
} block_t;

/* This enum can be used to set the allocated bit in the block */
enum block_state  { FREE,
                    ALLOC };

#define CHUNKSIZE (1 << 16) /* initial heap size (bytes) */ 
#define OVERHEAD (sizeof(header_t) + sizeof(footer_t)) /* overhead of the header and footer of an allocated block */
#define MIN_BLOCK_SIZE (32) /* the minimum block size needed to keep in a freelist (header + footer + next pointer + prev pointer) */

/* Global variables */
static block_t *prologue; /* pointer to first block */
static block_t **freelist; /* pointers to pointer to beginning of list */

/* function prototypes for internal helper routines */
static block_t *extend_heap(size_t words, bool coalesced);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);
static footer_t *get_footer(block_t *block);
static void printblock(block_t *block);
static void checkblock(block_t *block);
static int chooseList(int list);
static void insertBlock(block_t *block, int list);
static void removeBlock(block_t *block, int list);

static int numLists = 28; // how many lists in total set of segregated free lists
static int smallSize = 96; // size

/*
 * mm_init - Initialize the memory manager
 */
/* $begin mminit */
int mm_init(void) {
  /* initialize different segregated free lists */
  freelist = mem_sbrk(8 * numLists);
  int i = 0;
  while (i < numLists) {
    freelist[i] = NULL;
    i++;
  }

  /* create the initial empty heap */
  if ((prologue = mem_sbrk(CHUNKSIZE)) == (void*)-1)
    return -1;
  /* initialize the prologue */
  prologue->allocated = ALLOC;
  prologue->block_size = sizeof(header_t);
  /* initialize the first free block */
  block_t *init_block = (void *)prologue + sizeof(header_t);
  init_block->allocated = FREE;
  init_block->block_size = CHUNKSIZE - OVERHEAD;
  footer_t *init_footer = get_footer(init_block);
  init_footer->allocated = FREE;
  init_footer->block_size = init_block->block_size;

  // one big block
  freelist[numLists - 1] = init_block;
  // prev and next null, circular
  init_block->body.prev = NULL;
  init_block->body.next = NULL;

  /* initialize the epilogue - block size 0 will be used as a terminating condition */
  block_t *epilogue = (void *)init_block + init_block->block_size;
  epilogue->allocated = ALLOC;
  epilogue->block_size = 0;
  return 0;
}
/* $end mminit */

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) {
  uint32_t asize;        /* adjusted block size */
  uint32_t extendsize;   /* amount to extend heap if no fit */
  uint32_t extendwords;  /* number of words to extend heap if no fit */
  block_t *block;

  /* Ignore spurious requests */
  if (size == 0)
    return NULL;

  /* Adjust block size to include overhead and alignment reqs. */
  size += OVERHEAD;

  asize = ((size + 7) >> 3) << 3; /* align to multiple of 8 */

  if (asize < MIN_BLOCK_SIZE) {
    asize = MIN_BLOCK_SIZE;
  }

  // account for small blocks bc can just extend by that size
  if (asize <= smallSize) {
    extendsize = asize;
    extendwords = extendsize >> 3;
    if ((block = extend_heap(extendwords, false)) != NULL) {
      place(block, asize);
      return block->body.payload;
    }
  }

  /* Search the free list for a fit */
  if ((block = find_fit(asize)) != NULL) {
    place(block, asize);
    return block->body.payload;
  }

  /* No fit found. Get more memory and place the block */
  extendsize = (asize > CHUNKSIZE) // extend by the larger of the two
                  ? asize
                  : CHUNKSIZE;
  extendwords = extendsize >> 3; // extendsize/8
  if ((block = extend_heap(extendwords, true)) != NULL) {
    place(block, asize);
    return block->body.payload;
  }
  /* no more memory :( */
  return NULL;
}
/* $end mmmalloc */

/*
 * mm_free - Free a block
 */
/* $begin mmfree */
void mm_free(void * ptr) {
  block_t *block = ptr - sizeof(header_t);
  block->allocated = FREE;
  footer_t *footer = get_footer(block);
  footer->allocated = FREE;

  insertBlock(block, chooseList(block->block_size));

  coalesce(block);

} /* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 * NO NEED TO CHANGE THIS CODE!
 */
void * mm_realloc(void * ptr, size_t size) {
  void *newp;
  size_t copySize;

  if ((newp = mm_malloc(size)) == NULL) {
      printf("ERROR: mm_malloc failed in mm_realloc\n");
      exit(1);
  }
  block_t* block = ptr - sizeof(header_t);
  copySize = block->block_size;
  if (size < copySize)
    copySize = size;
  memcpy(newp, ptr, copySize);
  mm_free(ptr);
  return newp;
}

/*
 * mm_checkheap - Check the heap for consistency
 */
void mm_checkheap(int verbose) {
  block_t *block = prologue;

  if (verbose)
    printf("Heap (%p):\n", prologue);

  if (block -> block_size != sizeof(header_t) || !block -> allocated)
    printf("Bad prologue header\n");
  checkblock(prologue);

  /* iterate through the heap (both free and allocated blocks will be present) */
  for (block = (void * ) prologue + prologue -> block_size; block -> block_size > 0; block = (void * ) block + block -> block_size) {
    if (verbose)
      printblock(block);
    checkblock(block);
  }

  if (verbose)
    printblock(block);
  if (block -> block_size != 0 || !block -> allocated)
    printf("Bad epilogue header\n");
}
/* $end mmcheckheap */

/* The remaining routines are internal helper routines */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static block_t *extend_heap(size_t words, bool coalesced) {
  block_t *block;
  uint32_t size;
  size = words << 3; // words*8
  if (size == 0 || (block = mem_sbrk(size)) == (void *)-1)
    return NULL;
  /* The newly acquired region will start directly after the epilogue block */
  /* Initialize free block header/footer and the new epilogue header */
  /* use old epilogue as new free block header */
  block = (void *)block - sizeof(header_t);
  block->allocated = FREE;
  block->block_size = size;
  /* free block footer */
  footer_t *block_footer = get_footer(block);
  block_footer->allocated = FREE;
  block_footer->block_size = block->block_size;
  /* new epilogue header */
  header_t *new_epilogue = (void *)block_footer + sizeof(header_t);
  new_epilogue->allocated = ALLOC;
  new_epilogue->block_size = 0;

  // add new block to list
  insertBlock(block, chooseList(block->block_size));

  /* Coalesce if the previous block was free */
  if (coalesced == true) {
    return coalesce(block);
  } else {
    return block;
  }

}
/* $end mmextendheap */

/*
 * place - Place block of asize bytes at start of free block block
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
static void place(block_t *block, size_t asize) {
  size_t split_size = block->block_size - asize;
  if (split_size >= MIN_BLOCK_SIZE) {
    // remove block from list
    removeBlock(block, chooseList(block->block_size));

    /* split the block by updating the header and marking it allocated*/
    block->block_size = asize;
    block->allocated = ALLOC;
    /* set footer of allocated block*/
    footer_t *footer = get_footer(block);
    footer->block_size = asize;
    footer->allocated = ALLOC;
    /* update the header of the new free block */
    block_t *new_block = (void *)block + block->block_size;
    new_block->block_size = split_size;
    new_block->allocated = FREE;
    /* update the footer of the new free block */
    footer_t *new_footer = get_footer(new_block);
    new_footer->block_size = split_size;
    new_footer->allocated = FREE;

    // add new block to list
    insertBlock(new_block, chooseList(new_block->block_size));

  } else {
    // take block out of list
    removeBlock(block, chooseList(block->block_size));

    /* splitting the block will cause a splinter so we just include it in the allocated block */
    block->allocated = ALLOC;
    footer_t *footer = get_footer(block);
    footer->allocated = ALLOC;
  }
}
/* $end mmplace */

/*
 * find_fit - Find a fit for a block with asize bytes
 */ 

static block_t *find_fit(size_t asize) {
  block_t *b;

  for (int list = chooseList(asize); list < numLists; list++) {
    b = freelist[list];
    for (b; b != NULL; b = b->body.next) {
      /* block must be free and the size must be large enough to hold the request */
      if (!b->allocated && asize <= b->block_size) {
        return b;
      }
    }
  }
  return NULL; // no fit 
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static block_t *coalesce(block_t *block) {
  footer_t *prev_footer = (void *)block - sizeof(header_t);
  header_t *next_header = (void *)block + block->block_size;
  bool prev_alloc = prev_footer->allocated;
  bool next_alloc = next_header->allocated;
  block_t *prev_block = (void *)prev_footer - (prev_footer->block_size) + sizeof(header_t);
  block_t *next_block = (void *)next_header;

  if (prev_alloc && next_alloc) { /* Case 1 */
    /* no coalesceing */
    return block;
  } 
  
  else if (prev_alloc && !next_alloc) { /* Case 2 */

    // remove current and next blocks from list
    removeBlock(block, chooseList(block -> block_size));
    removeBlock(next_block, chooseList(next_block -> block_size));

    /* Update header of current block to include next block's size */
    // block_t *prev_block = (void *)prev_footer - prev_footer->block_size + sizeof(header_t);
    block->block_size += next_header->block_size;
    /* Update footer of next block to reflect new size */
    footer_t *next_footer = get_footer(block);
    next_footer->block_size = block->block_size;

    // add block to list
    insertBlock(block, chooseList(block->block_size));

  } else if (!prev_alloc && next_alloc) { /* Case 3 */

    // remove current and prev blocks from list
    removeBlock(block, chooseList(block->block_size));
    removeBlock(prev_block, chooseList(prev_block->block_size));

    /* Update header of prev block to include current block's size */
    // block_t *prev_block = (void *)prev_footer - prev_footer->block_size + sizeof(header_t);
    prev_block->block_size += block->block_size;
    /* Update footer of current block to reflect new size */
    footer_t *footer = get_footer(prev_block);
    footer->block_size = prev_block->block_size;
    block = prev_block;

    // add prev block to list
    insertBlock(prev_block, chooseList(prev_block->block_size));
  } 
  
  else { /* Case 4 */

    // remove all blocks: current, prev, next
    removeBlock(block, chooseList(block->block_size));
    removeBlock(prev_block, chooseList(prev_block->block_size));
    removeBlock(next_block, chooseList(next_block->block_size));

    /* Update header of prev block to include current and next block's size */
    block_t *prev_block = (void *)prev_footer - prev_footer->block_size + sizeof(header_t);
    prev_block->block_size += block->block_size + next_header->block_size;
    /* Update footer of next block to reflect new size */
    footer_t *next_footer = get_footer(prev_block);
    next_footer->block_size = prev_block -> block_size;
    block = prev_block;

    // add prev block to list
    insertBlock(prev_block, chooseList(prev_block->block_size));

  }

  return block;
}

static footer_t* get_footer(block_t * block) {
  return (void *)block + block->block_size - sizeof(footer_t);
}

static void printblock(block_t *block) {
    uint32_t hsize, halloc, fsize, falloc;

    hsize = block->block_size;
    halloc = block->allocated;
    footer_t *footer = get_footer(block);
    fsize = footer->block_size;
    falloc = footer->allocated;

    if (hsize == 0) {
        printf("%p: EOL\n", block);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", block, hsize,
           (halloc ? 'a' : 'f'), fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(block_t *block) {
  if ((uint64_t) block -> body.payload % 8) {
    printf("Error: payload for block at %p is not aligned\n", block);
  }
  footer_t * footer = get_footer(block);
  if (block -> block_size != footer -> block_size) {
    printf("Error: header does not match footer\n");
  }
}

static int chooseList(int list) { // calculate which free list to add/remove from
  int whichList = 31 - __builtin_clz(list);
  whichList = whichList - (16 - numLists);
  return (whichList < (numLists - 1) ? whichList : (numLists - 1));
}

static void insertBlock(block_t *block, int list) { // add block to free list
  if (freelist[list] == NULL) {
    block->body.prev = NULL;
    block->body.next = NULL;
    freelist[list] = block;
  } else {
    block->body.prev = NULL;
    block->body.next = freelist[list];
    freelist[list]->body.prev = block;
    freelist[list] = block;
  }
}

static void removeBlock(block_t *block, int list) { // remove block from free list
  if (freelist[list]->body.prev == NULL && freelist[list]->body.next == NULL) {
    freelist[list] = NULL;
  } else if (block->body.next == NULL) {
      block->body.prev->body.next = NULL;
  } else if (block == freelist[list]) {
      block->body.next->body.prev = NULL;
      freelist[list] = block->body.next;
  } else {
      block->body.prev->body.next = block->body.next;
      block->body.next->body.prev = block->body.prev;  
  }
}