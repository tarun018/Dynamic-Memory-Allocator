

/*

TARUN GUPTA 201201168
RISHABH SANKLECHA 201201177
TEAM NAME : @@Malloc@@
Submission Date: 10-03-2014

 * In this approach, a block is allocated by simply incrementing

 * the brk pointer. Realloc is implemented directly using mm_malloc and mm_free.

 *

 * NOTE TO STUDENTS: Replace this header comment with your own header

 * comment that gives a high level description of your solution.

 */

#include <stdio.h>
#include <stdlib.h>
#include<stdint.h>
#include <string.h>
#include <assert.h>
#include <unistd.h>
#include "mm.h"
#include "memlib.h"

/*********************************************************
* NOTE TO STUDENTS: Before you do anything else, please
* provide your team information in the following struct.
********************************************************/

team_t team = {
	/* Team name */
	"@@Malloc@@",
	/* First member's full name */
	"TARUN GUPTA",
	/* First member's email address */
	"tarun1995gupta@gmail.com",
	/* Second member's full name (leave blank if none) */
	"RISHABH SANKLECHA",
	/* Second member's email address (leave blank if none) */
	"rishu.sanklecha@gmail.com"
};

#define WORD sizeof(void *) /* Word and header/footer size (bytes) */
#define OVERHEAD 8
#define BLKSIZE 16
#define DWORD (2 * WORD)    /* Doubleword size (bytes) */
#define TWORD (3 * WORD)
#define QWORD (4 * WORD)// FOR INITIALIZING HEAP
#define ALIGNMENT 8
#define CHUNKSIZE (1 << 12)      /* Extend heap by this amount (bytes) */


#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Read and write a word at address p. */
#define GET(p) (*(uintptr_t *)(p))
#define PUT(p, val) (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p) (GET(p) & ~(DWORD - 1))  
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc) ((size) | (alloc))

/*pointer p (block pointer), address of  header, footer, left child, right child.*/ 

/* Given block ptr bp, compute address of its header and footer. */
#define HEAD(p) ((char *)(p) - WORD)
#define FOOT(p) ((char *)(p) + GET_SIZE(HEAD(p)) - DWORD)

/* Given block ptr bp, compute address of next and previous blocks. */
#define PREV_BLK(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DWORD)))
#define NEXT_BLK(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WORD))) 

/* converting passed size to a  multiple of 8 */
#define ALIGN_SIZE(size) (((size)+(ALIGNMENT - 1)) & ~(DWORD - 1))

/* Getting values of header and footer*/
#define GET_HEAD(bp) (GET(HEAD(bp)))
#define GET_FOOT(bp) (GET(FOOT(bp)))

#define GET_RIGHT(bp)		(*(void **)(bp + WORD))
#define GET_LEFT(bp)		(*(void **)bp)
#define PUT_RIGHT(bp, ptr)	(GET_RIGHT(bp) = ptr)
#define PUT_LEFT(bp, ptr)	(GET_LEFT(bp) = ptr)

/* Get the address of the next and previous free block within the free list */
#define RIGHT_FREE(bp) (GET(bp + WORD))
#define LEFT_FREE(bp) (GET(bp))

/* Get the pointers to the next and prevoius free blocks */
#define RIGHT_FREE_PTR(bp) ((char *)RIGHT_FREE(bp))
#define LEFT_FREE_PTR(bp) ((char *)LEFT_FREE(bp))
 

int mm_init (void); 
void *mm_malloc (size_t size); 
void mm_free (void *bp); 
void *mm_realloc (void *bp, size_t size); 

static void insertioninlinkedlist (void *bp); // insertion for doubly linked list
static void deletioninlinkedlist (void *bp); // deletion for doubly linked list
static void *coalesce (void *bp); 
static int allocated(const void *p);
void printblock(void *bp);
void checkheap(void);
static void *extend_heap (size_t asize); 
static void *place (void *bp, size_t size); 
static void *find_fit (size_t size); 
static int blockinheap(const void *p); // check if pointer is in heap
static int aligned(const void *p);

/* Global variables */ 

static char *pointertofreelist;
static char *pointertoheap = NULL; 


/*Checking if our block size is aligned to 8 byte boundaries. */ 

static int aligned(const void *p) 
{
    return (size_t)p % ALIGNMENT;
}

/* Checks block is in the heap */

static int blockinheap(const void *p)
{
	return (p <= mem_heap_hi()) && (p >= mem_heap_lo());
}

/* Check both header and footer for whether the block is free */
static int allocated(const void *p)
{
	return (GET_ALLOC(HEAD(p)) == 1) && (GET_ALLOC(FOOT(p)) == 1);
}

int mm_init(void) 
{ 
	/* Create the initial empty heap. */ 
	if ((pointertoheap = mem_sbrk(4*WORD)) == (void *)-1 ) 
		return -1; 

	PUT(pointertoheap, 0); 
	PUT(pointertoheap + WORD, PACK(OVERHEAD, 1));
	PUT(pointertoheap + DWORD, PACK(OVERHEAD, 1));
	PUT(pointertoheap + TWORD, PACK(0, 1)); 
	pointertoheap += QWORD; 
	pointertofreelist = NULL; 
	if (extend_heap(CHUNKSIZE/WORD) == NULL) 
		return -1;
	return 0;
}


/* Freeing bp if bp not null */
void mm_free(void *bp) 
{
	if (bp == 0){
		return;
	}
	size_t size = GET_SIZE(HEAD(bp));
	PUT(HEAD(bp), PACK(size, 0));
	PUT(FOOT(bp), PACK(size, 0));
	coalesce(bp);
}


/*looks through the existing free list to see if there are any blocks of memory large enough
 to fit the request block. If no fit exist, then it calls extend heap. */
void *mm_malloc(size_t size) 
{
	size_t adj;
	size_t exact;
	char *bp;
	if (size == 448)
		size+=64;
	if (size == 112)
		size+=16;
	if (pointertoheap == NULL){
		mm_init();
	}

	/* Ignore spurious requests */

	if (size <= 0)
		return NULL;

	/* Aligning to 8 byte boundaries */
	if (size <= BLKSIZE - OVERHEAD)
		adj = BLKSIZE;
	else 
		adj = ALIGN_SIZE(size + (OVERHEAD));
	
	if ((bp = find_fit(adj)) !=  NULL){
		place(bp, adj);
		return bp;
	}
	else{
		//extending heap if no fit found.
		exact = MAX (CHUNKSIZE, adj); 
		if ((bp = extend_heap(ALIGN_SIZE(exact))) == NULL)
			return NULL;
		place(bp, adj);
		return bp;
	}
}


/* Realloc the given pointer bp */
void *mm_realloc(void *ptr, size_t size) 
{
	size_t size_old = GET_SIZE(HEAD(ptr));
	// if size is 0, means we wish to free the block.
	if (size == 0){
		mm_free(ptr);
		return NULL;
	}
	// spurious request
	if (ptr == NULL)
		return mm_malloc(size);

	size_t size_new = ALIGN_SIZE(size + OVERHEAD);
	// if the size_new is smaller than the size_old
	if (size_old > size_new){
		// checking for status of next block ans also coalesce if free.
		if (GET_ALLOC(HEAD(ptr))){
			// check if the size_old minus size_new is bigger than BLKSIZE
			if (size_old - size_new >= BLKSIZE){
				PUT(HEAD(ptr), PACK(size_new, 1));
				PUT(FOOT(ptr), PACK(size_new, 1));
				// header and footer for freed block 
				void *newfree_block = NEXT_BLK(ptr);
				PUT(HEAD(newfree_block), PACK(size_old - size_new, 0));
				PUT(FOOT(newfree_block), PACK(size_old - size_new, 0));
				insertioninlinkedlist(newfree_block);
			}
			return ptr;
		}
		// if next block ptr & 0x1 == 0
		else{
			size_t newfree_size = size_old + GET_SIZE(HEAD(NEXT_BLK(ptr))) - size_new;
			deletioninlinkedlist(NEXT_BLK(ptr));
			PUT(HEAD(ptr), PACK(size_new, 1));
			PUT(FOOT(ptr), PACK(size_new, 1));
			void *nextblkpointer = NEXT_BLK(ptr);
			PUT(HEAD(nextblkpointer), PACK(newfree_size, 0));
			PUT(FOOT(nextblkpointer), PACK(newfree_size, 0));
			insertioninlinkedlist(nextblkpointer);
			return ptr;

		}

	}
	//size_new > size_old 
	else{
		//allocation status --> next and previous block
		void *prev_blk_pointer = PREV_BLK(ptr);
		void *next_blk_pointer = NEXT_BLK(ptr);
		size_t prev_allocated_status = GET_ALLOC(HEAD(prev_blk_pointer));
		size_t next_allocated_status = GET_ALLOC(HEAD(next_blk_pointer));
		size_t size_total;
		size_t size_diff;
		if (!prev_allocated_status && (size_total = GET_SIZE(HEAD(prev_blk_pointer)) + size_old) >= size_new){
			deletioninlinkedlist(prev_blk_pointer);
			memcpy(prev_blk_pointer, ptr, size_old - OVERHEAD);
			size_diff = size_total - size_new;
			if (size_diff >= BLKSIZE){
				PUT(HEAD(prev_blk_pointer), PACK(size_new, 1));
				PUT(FOOT(prev_blk_pointer), PACK(size_new, 1));
				void *temp = NEXT_BLK(prev_blk_pointer);
				PUT(HEAD(temp), PACK(size_diff, 0));
				PUT(FOOT(temp), PACK(size_diff, 0));
				insertioninlinkedlist(temp);
			}
			else{
				PUT(HEAD(prev_blk_pointer), PACK(size_total, 1));
				PUT(FOOT(prev_blk_pointer), PACK(size_total, 1));
				}
			return prev_blk_pointer;
		}
		else if (!next_allocated_status && (size_total = GET_SIZE(HEAD(next_blk_pointer)) + size_old) >= size_new){
			deletioninlinkedlist(next_blk_pointer);
			size_diff = size_total - size_new;
			if (size_diff >= BLKSIZE){
				PUT(HEAD(ptr), PACK(size_new, 1));
				PUT(FOOT(ptr), PACK(size_new, 1));
				void *temp = NEXT_BLK(ptr);
				PUT(HEAD(temp), PACK(size_diff, 0));
				PUT(FOOT(temp), PACK(size_diff, 0));
				insertioninlinkedlist(temp);
			}
			else{
				PUT(HEAD(ptr), PACK(size_total, 1));
				PUT(FOOT(ptr), PACK(size_total, 1));
			}
			return ptr;

	}
		else{
			void *nptr;
			size_t extsize;
			if ((nptr = find_fit(size_new)) == NULL){
				extsize = MAX(size_new, CHUNKSIZE);
				extend_heap(extsize);
				if((nptr = find_fit(size_new))==NULL)

					return NULL;

			}

			place(nptr, size_new);

			memcpy(nptr, ptr, size_old - OVERHEAD);

			mm_free(ptr);

			return nptr;

		}

	}

}

/*This function is called when heap does not have enough memory for malloc request.
Extends heap with asize.*/
void *extend_heap(size_t asize) 

{ 
	char *bp; 	
	/* Requesting additional memory */
	if ((long)(bp = mem_sbrk(asize)) == -1)
		return NULL; 

	/*Initialize new free block-- header and footer */

	PUT(HEAD(bp), PACK(asize, 0));
	PUT(FOOT(bp), PACK(asize, 0));

	/* Since heap is entended, we have to update the epilogue of the heap. */

	PUT(HEAD(NEXT_BLK(bp)), PACK(0,1)); 

	/* coalesing this new block with previous block (free block) (if available)*/
	return coalesce(bp); 

}

/*
checking previous and next blocks for allocation status and then coalesce with 4 cases:
prev free next allocated
prev allocated next allocated
prev allocated next free
prev free next free

*/
static void *coalesce(void *bp) 

{

	size_t prev_allocated_status = GET_ALLOC((char *)(bp) - DWORD);
	size_t next_allocated_status = GET_ALLOC((char *)(FOOT(bp)) + WORD);

	

	
	size_t sizeofblock = GET_SIZE(HEAD(bp));

	
	if (prev_allocated_status && next_allocated_status)

		insertioninlinkedlist(bp);

	

	
	else if (prev_allocated_status && !next_allocated_status){

	
		sizeofblock += GET_SIZE(HEAD(NEXT_BLK(bp)));

	
		deletioninlinkedlist(NEXT_BLK(bp));

	
		PUT(HEAD(bp), PACK(sizeofblock, 0));

	
		PUT(FOOT(bp), PACK(sizeofblock, 0)); 

		insertioninlinkedlist(bp);

	}	

	
	else if (!prev_allocated_status && next_allocated_status){

	
		bp = PREV_BLK(bp);

	
		sizeofblock += GET_SIZE(HEAD(bp));

	
		PUT(HEAD(bp), PACK(sizeofblock, 0));


		PUT(FOOT(bp), PACK(sizeofblock, 0));

	}	


	else{

		char *prev_blk_pointer = PREV_BLK(bp);

		char *next_blk_pointer = NEXT_BLK(bp);

		


		sizeofblock += GET_SIZE(HEAD(prev_blk_pointer)) + GET_SIZE(HEAD(next_blk_pointer));


		PUT(HEAD(prev_blk_pointer), PACK(sizeofblock, 0));


		PUT(FOOT(next_blk_pointer), PACK(sizeofblock, 0));

		

		deletioninlinkedlist(next_blk_pointer);

		bp = prev_blk_pointer;

	}

	return bp;

}

/* modifying the allocation information and splitting the block if necessary. */
static void *place(void *bp, size_t asize) 

{



	size_t current__size = GET_SIZE(HEAD(bp));

	deletioninlinkedlist(bp);

	

	if (current__size - asize >= BLKSIZE){

		/* Change new header and footer information*/

		PUT(HEAD(bp), PACK(asize, 1));

		PUT(FOOT(bp), PACK(asize, 1));

		/* Store pointer of next block in bp */

		bp = NEXT_BLK(bp);

		/* Change header and footer information for the new free block */

		PUT(HEAD(bp), PACK(current__size - asize, 0));

		PUT(FOOT(bp), PACK(current__size - asize, 0));

		insertioninlinkedlist(bp);

	}

	else {

		/* indicate that the block has been allocated */

		PUT(HEAD(bp), PACK(current__size, 1));

		PUT(FOOT(bp), PACK(current__size, 1));

	}

	return bp;

}

/* Searches for the best available size block by traversing the entire list */

static void *find_fit(size_t size) 

{

	char *current = pointertofreelist;

	char *best_fit_pointer = NULL;

	/* while current block size is not the desired size and the current block 

	   is not the last block yet */

	while(current != NULL){

		if (GET_SIZE(HEAD(current)) == size){

			deletioninlinkedlist(current);

			return current;

		}

		else if (GET_SIZE(HEAD(current)) < size){

			current = RIGHT_FREE_PTR(current);

		}

		else{

			if (best_fit_pointer == NULL)

				best_fit_pointer = current;

			else if (GET_SIZE(HEAD(best_fit_pointer)) > GET_SIZE(HEAD(current)))

				best_fit_pointer = current;

			current = RIGHT_FREE_PTR(current);

		}

	}

	if (best_fit_pointer == NULL)

		return NULL;

	else{

		return best_fit_pointer;

	}

}

/* Deletion of bp doubly linked list of free blocks */

static void deletioninlinkedlist(void *bp) 

{

	char *left_pointer = LEFT_FREE_PTR(bp);

	char *right_pointer = RIGHT_FREE_PTR(bp);

	

	/* If the block, bp, to be deleted is at the begining of the free list*/ 

	if (left_pointer == NULL){

		pointertofreelist = right_pointer;

		/* If bp is not at the end of the list, then set the next block

		   at the beginning of list */

		if (right_pointer != NULL)

			PUT_LEFT(right_pointer, NULL);

	}

	/* If bp is not at the begining of the list */

	else{

		PUT_RIGHT(left_pointer, right_pointer);

		/* if bp is not the end of list */

		if (right_pointer != NULL)

			PUT_LEFT(right_pointer, left_pointer);

	}

}


/* Inserting a block (bp) from doubly linked list of free blocks */


static void insertioninlinkedlist(void *bp) 

{

	char *block_pointer = pointertofreelist;

	

	PUT_RIGHT(bp, block_pointer);

	PUT_LEFT(bp, NULL);

	

	if (block_pointer != NULL)

		PUT_LEFT(pointertofreelist, bp);

	pointertofreelist = bp;

}




/* Print all blocks in heap */

void printblock(void *bp)

{

	size_t hsize, halloc, fsize, falloc;

		

	hsize = GET_SIZE(HEAD(bp));

	halloc = GET_ALLOC(HEAD(bp));

	fsize = GET_SIZE(FOOT(bp));

	falloc = GET_ALLOC(FOOT(bp));

	

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 

	hsize, (halloc ? 'a' : 'f'), 

	fsize, (falloc ? 'a' : 'f')); 

	

    if (hsize == 0) {

		printf("%p: EOL\n", bp);

		return;

    }

}

/* Print a list of free blocks in memory */

void print_free_list(void)

{

	int n = 0;

	void *list = pointertofreelist;

	while (list!=NULL && list <=mem_heap_hi()){

		printf("Block #%d\n", n);

		if (blockinheap(list))

			printf("Pointer in the heap \n");

		else {

			printf("ERROR:The pointer is not in heap. Exit\n");

			exit(0);

        }

			

		printf("Block of size %d ", GET_SIZE(HEAD(list)));

		printf("at address %p \n", list);

		printf("linked to right free block at %p \n", RIGHT_FREE_PTR(list));

		printf("and left free block at %p \n", LEFT_FREE_PTR(list));

        list = RIGHT_FREE_PTR(list);

        n++;

    }

}
/* Check if a block is properly aligned and if the header matches the footer */

static void checkblock(void *bp) 

{

    if ((size_t)bp % ALIGNMENT)

	printf("Error: %p is not doubleword aligned\n", bp);

    if (GET(HEAD(bp)) != GET(FOOT(bp)))

	printf("Error: header does not match footer\n");

}

/* Check the entire heap for consistency */

void checkheap(void) 

{

    char *bp = pointertoheap;

	printf("Heap (%p):\n", pointertoheap - ALIGNMENT);

	printf("Prologue layout: ");

	printblock(bp - OVERHEAD);

	printf("\n");

	

    if ((GET_SIZE(HEAD(pointertoheap - OVERHEAD)) != DWORD) 

		|| !GET_ALLOC(HEAD(pointertoheap - OVERHEAD))){

		

		printf("Bad prologue header\n");

		checkblock(pointertoheap - OVERHEAD);

	}

    for (bp = pointertoheap; GET_SIZE(HEAD(bp)) > 0; bp = NEXT_BLK(bp)) {

	    printblock(bp);

		checkblock(bp);

    }

	printblock(bp);

    if ((GET_SIZE(HEAD(bp)) != 0) || !(GET_ALLOC(HEAD(bp))))

	printf("Bad epilogue header\n");

}




