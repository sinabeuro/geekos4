/*
 * Paging-based user mode implementation
 * Copyright (c) 2003,2004 David H. Hovemeyer <daveho@cs.umd.edu>
 * $Revision: 1.50 $
 * 
 * This is free software.  You are permitted to use,
 * redistribute, and modify it as specified in the file "COPYING".
 */

#include <geekos/int.h>
#include <geekos/mem.h>
#include <geekos/paging.h>
#include <geekos/malloc.h>
#include <geekos/string.h>
#include <geekos/argblock.h>
#include <geekos/kthread.h>
#include <geekos/range.h>
#include <geekos/vfs.h>
#include <geekos/user.h>


#define DEFAULT_USER_STACK_SIZE 8192
#define USER_BASE_ADRR 0x80000000

/* ----------------------------------------------------------------------
 * Private functions
 * ---------------------------------------------------------------------- */

// TODO: Add private functions
/* ----------------------------------------------------------------------
 * Public functions
 * ---------------------------------------------------------------------- */

/*
 * Destroy a User_Context object, including all memory
 * and other resources allocated within it.
 */
void Destroy_User_Context(struct User_Context* context)
{
    /*
     * Hints:
     * - Free all pages, page tables, and page directory for
     *   the process (interrupts must be disabled while you do this,
     *   otherwise those pages could be stolen by other processes)
     * - Free semaphores, files, and other resources used
     *   by the process
     */
    TODO("Destroy User_Context data structure after process exits");
}

/*
 * Load a user executable into memory by creating a User_Context
 * data structure.
 * Params:
 * exeFileData - a buffer containing the executable to load
 * exeFileLength - number of bytes in exeFileData
 * exeFormat - parsed ELF segment information describing how to
 *   load the executable's text and data segments, and the
 *   code entry point address
 * command - string containing the complete command to be executed:
 *   this should be used to create the argument block for the
 *   process
 * pUserContext - reference to the pointer where the User_Context
 *   should be stored
 *
 * Returns:
 *   0 if successful, or an error code (< 0) if unsuccessful
 */
int Load_User_Program(char *exeFileData, ulong_t exeFileLength,
    struct Exe_Format *exeFormat, const char *command,
    struct User_Context **pUserContext)
{
    /*
     * Hints:
     * - This will be similar to the same function in userseg.c
     * - Determine space requirements for code, data, argument block,
     *   and stack
     * - Allocate pages for above, map them into user address
     *   space (allocating page directory and page tables as needed)
     * - Fill in initial stack pointer, argument block address,
     *   and code entry point fields in User_Context
     */
	struct Segment_Descriptor* desc;
	static void * virtSpace;
	unsigned long virtSize;
	unsigned short LDTSelector;
	unsigned short codeSelector, dataSelector;
	int i, j;
	ulong_t maxva = 0;
	unsigned numArgs;
	ulong_t argBlockSize;
	unsigned long stackPointerAddr;
	ulong_t vaddr = 0;
	void* paddr = 0;

	Get_Argument_Block_Size(command, &numArgs, &argBlockSize);

	/* Find maximum virtual address */
	for (i = 0; i < exeFormat->numSegments; ++i) {
	  struct Exe_Segment *segment = &exeFormat->segmentList[i];
	  ulong_t topva = segment->startAddress + segment->sizeInMemory; 
	  
	  if (topva > maxva)
		maxva = topva;
	}
	
	/* setup some memory space for the program */
	virtSize = Round_Up_To_Page(maxva);
	stackPointerAddr = 0xFFFFFFFF;
	//+ DEFAULT_USER_STACK_SIZE;	

    extern struct Page* g_pageList;
    				
	pde_t* pde = 0;
	pte_t* pte = 0;

	// copy all of the mappings from the kernel mode page directory 
	pde = (pde_t*)Alloc_Page();
	memcpy(pde, Get_PDBR(), PAGE_SIZE);
	
	// alloc user page table(start from 0x80000000) 
	pde = &pde[PAGE_DIRECTORY_INDEX(USER_BASE_ADRR)];
    for (i=0; i<PAGE_DIRECTORY_INDEX(virtSize); i++) {
		pte = (pte_t*)Alloc_Page();
		memset(pte,0,PAGE_SIZE);
		pde[i].pageTableBaseAddr = (uint_t)PAGE_ALLIGNED_ADDR(pte);
		pde[i].present = 1;
		pde[i].flags = VM_USER;

		for(j=0; j < NUM_PAGE_TABLE_ENTRIES; j++){
			vaddr = USER_BASE_ADRR + ((i*NUM_PAGE_TABLE_ENTRIES+j)<<PAGE_POWER);
			paddr = Alloc_Pageable_Page(&pte[j], vaddr);
			pte[j].pageBaseAddr = PAGE_ALLIGNED_ADDR(paddr); 
			//memcpy(paddr, exeFileData + segment->offsetInFile, PAGE_SIZE);
			pte[j].present = 1;
			pte[j].flags = VM_USER;
		}
	}

	Format_Argument_Block(stackPointerAddr, numArgs, stackPointerAddr, command);
	
	*pUserContext = (struct User_Context*)Malloc(sizeof(struct User_Context));
	(*pUserContext)->memory = (char*)virtSpace;
	(*pUserContext)->size = virtSize;
	(*pUserContext)->entryAddr = exeFormat->entryAddr;
	(*pUserContext)->stackPointerAddr = stackPointerAddr;
	(*pUserContext)->argBlockAddr = stackPointerAddr;
	(*pUserContext)->refCount = 0; // important

	// setup LDT
	// alloc LDT seg desc in GDT
	desc = Allocate_Segment_Descriptor();
	Init_LDT_Descriptor(
					 desc,
					 ((*pUserContext)->ldt), // base address
					 2  // num pages
					 );
	LDTSelector = Selector(KERNEL_PRIVILEGE, true, Get_Descriptor_Index( desc )); //
	(*pUserContext)->ldtDescriptor = desc;
	(*pUserContext)->ldtSelector = LDTSelector;

	desc = &((*pUserContext)->ldt)[0];
	Init_Code_Segment_Descriptor(
					 desc,
					 (unsigned long)virtSpace, // base address
					 (virtSize/PAGE_SIZE)+10,  // num pages
					 USER_PRIVILEGE		   // privilege level (0 == kernel)
					 );
	codeSelector = Selector(USER_PRIVILEGE, false, 0);
	(*pUserContext)->csSelector = codeSelector;

	desc = &((*pUserContext)->ldt)[1];
	Init_Data_Segment_Descriptor(
					 desc,
					 (unsigned long)virtSpace, // base address
					 (virtSize/PAGE_SIZE)+10,  // num pages
					 USER_PRIVILEGE		   // privilege level (0 == kernel)
					 );
	dataSelector = Selector(USER_PRIVILEGE, false, 1);
	(*pUserContext)->dsSelector = dataSelector;	
	
	Print("virtSize : %d\n", PAGE_DIRECTORY_INDEX(USER_BASE_ADRR+(virtSize<<12)));
     
    TODO("Load user program into address space");
}

/*
 * Copy data from user buffer into kernel buffer.
 * Returns true if successful, false otherwise.
 */
bool Copy_From_User(void* destInKernel, ulong_t srcInUser, ulong_t numBytes)
{
    /*
     * Hints:
     * - Make sure that user page is part of a valid region
     *   of memory
     * - Remember that you need to add 0x80000000 to user addresses
     *   to convert them to kernel addresses, because of how the
     *   user code and data segments are defined
     * - User pages may need to be paged in from disk before being accessed.
     * - Before you touch (read or write) any data in a user
     *   page, **disable the PAGE_PAGEABLE bit**.
     *
     * Be very careful with race conditions in reading a page from disk.
     * Kernel code must always assume that if the struct Page for
     * a page of memory has the PAGE_PAGEABLE bit set,
     * IT CAN BE STOLEN AT ANY TIME.  The only exception is if
     * interrupts are disabled; because no other process can run,
     * the page is guaranteed not to be stolen.
     */
    TODO("Copy user data to kernel buffer");
}

/*
 * Copy data from kernel buffer into user buffer.
 * Returns true if successful, false otherwise.
 */
bool Copy_To_User(ulong_t destInUser, void* srcInKernel, ulong_t numBytes)
{
    /*
     * Hints:
     * - Same as for Copy_From_User()
     * - Also, make sure the memory is mapped into the user
     *   address space with write permission enabled
     */
    TODO("Copy kernel data to user buffer");
}

/*
 * Switch to user address space.
 */
void Switch_To_Address_Space(struct User_Context *userContext)
{
    /*
     * - If you are still using an LDT to define your user code and data
     *   segments, switch to the process's LDT
     * - 
     */

    TODO("Switch_To_Address_Space() using paging");
}


