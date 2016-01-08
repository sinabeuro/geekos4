/*
 * Segmentation-based user mode implementation
 * Copyright (c) 2001,2003 David H. Hovemeyer <daveho@cs.umd.edu>
 * $Revision: 1.23 $
 * 
 * This is free software.  You are permitted to use,
 * redistribute, and modify it as specified in the file "COPYING".
 */

#include <geekos/ktypes.h>
#include <geekos/kassert.h>
#include <geekos/defs.h>
#include <geekos/mem.h>
#include <geekos/string.h>
#include <geekos/malloc.h>
#include <geekos/int.h>
#include <geekos/gdt.h>
#include <geekos/segment.h>
#include <geekos/tss.h>
#include <geekos/kthread.h>
#include <geekos/argblock.h>
#include <geekos/user.h>



extern void Load_LDTR(ushort_t LDTselector);

/* ----------------------------------------------------------------------
 * Variables
 * ---------------------------------------------------------------------- */

#define DEFAULT_USER_STACK_SIZE 8192


/* ----------------------------------------------------------------------
 * Private functions
 * ---------------------------------------------------------------------- */


/*
 * Create a new user context of given size
 */

/* TODO: Implement
static struct User_Context* Create_User_Context(ulong_t size)
*/


static bool Validate_User_Memory(struct User_Context* userContext,
    ulong_t userAddr, ulong_t bufSize)
{
    ulong_t avail;

    if (userAddr >= userContext->size)
        return false;

    avail = userContext->size - userAddr;
    if (bufSize > avail)
        return false;

    return true;
}

/* ----------------------------------------------------------------------
 * Public functions
 * ---------------------------------------------------------------------- */

/*
 * Destroy a User_Context object, including all memory
 * and other resources allocated within it.
 */
void Destroy_User_Context(struct User_Context* userContext)
{
    /*
     * Hints:
     * - you need to free the memory allocated for the user process
     * - don't forget to free the segment descriptor allocated
     *   for the process's LDT
     */

    Free_Segment_Descriptor(userContext->ldtDescriptor);
    Free(userContext->memory);
    Free(userContext);
	return 0;
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
     * - Determine where in memory each executable segment will be placed
     * - Determine size of argument block and where it memory it will
     *   be placed
     * - Copy each executable segment into memory
     * - Format argument block in memory
     * - In the created User_Context object, set code entry point
     *   address, argument block address, and initial kernel stack pointer
     *   address
     */
	struct Segment_Descriptor* desc;
	static void * virtSpace;
	unsigned long virtSize;
	unsigned short LDTSelector;
	unsigned short codeSelector, dataSelector;
	int i;
	ulong_t maxva = 0;
	unsigned numArgs;
	ulong_t argBlockSize;
	unsigned long stackPointerAddr;

	Get_Argument_Block_Size(command, &numArgs, &argBlockSize);
	
	/* Find maximum virtual address */
	for (i = 0; i < exeFormat->numSegments; ++i) {
	  struct Exe_Segment *segment = &exeFormat->segmentList[i];
	  ulong_t topva = segment->startAddress + segment->sizeInMemory; 
	  
	  if (topva > maxva)
		maxva = topva;
	}
	
	/* setup some memory space for the program */
	virtSize = Round_Up_To_Page(maxva) 
	+ DEFAULT_USER_STACK_SIZE;
	stackPointerAddr = virtSize;
	virtSize += argBlockSize;/* leave some slack for stack */
	virtSpace = Malloc(virtSize);
	memset((char *) virtSpace, '\0', virtSize);
	
	/* Load segment data into memory */
	for (i = 0; i < exeFormat->numSegments; ++i) {
	  struct Exe_Segment *segment = &exeFormat->segmentList[i];
	
	memcpy(virtSpace + segment->startAddress,
		 exeFileData + segment->offsetInFile,
		 segment->lengthInFile);
	}

	Format_Argument_Block(virtSpace + stackPointerAddr, numArgs, stackPointerAddr, command);
	
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

	// process argument...
	return 0;
}

/*
 * Copy data from user memory into a kernel buffer.
 * Params:
 * destInKernel - address of kernel buffer
 * srcInUser - address of user buffer
 * bufSize - number of bytes to copy
 *
 * Returns:
 *   true if successful, false if user buffer is invalid (i.e.,
 *   doesn't correspond to memory the process has a right to
 *   access)
 */
bool Copy_From_User(void* destInKernel, ulong_t srcInUser, ulong_t bufSize)
{
	/*
		* Hints:
		* - the User_Context of the current process can be found
		*	from g_currentThread->userContext
		* - the user address is an index relative to the chunk
		*	of memory you allocated for it
		* - make sure the user buffer lies entirely in memory belonging
		*	to the process
		*/
	   struct User_Context* userContext = g_currentThread->userContext;
	   
	   memcpy(destInKernel, (void*)(userContext->memory + srcInUser), bufSize);
	
	   return true;
	   //Validate_User_Memory(NULL,0,0); /* delete this; keeps gcc happy */

}

/*
 * Copy data from kernel memory into a user buffer.
 * Params:
 * destInUser - address of user buffer
 * srcInKernel - address of kernel buffer
 * bufSize - number of bytes to copy
 *
 * Returns:
 *   true if successful, false if user buffer is invalid (i.e.,
 *   doesn't correspond to memory the process has a right to
 *   access)
 */
bool Copy_To_User(ulong_t destInUser, void* srcInKernel, ulong_t bufSize)
{
    /*
     * Hints: same as for Copy_From_User()
     */
     
    struct User_Context* userContext = g_currentThread->userContext;
    
    memcpy((void*)(userContext->memory + destInUser), srcInKernel, bufSize);

	return true;

}

/*
 * Switch to user address space belonging to given
 * User_Context object.
 * Params:
 * userContext - the User_Context
 */
void Switch_To_Address_Space(struct User_Context *userContext)
{
    /*
     * Hint: you will need to use the lldt assembly language instruction
     * to load the process's LDT by specifying its LDT selector.
     */    
	Load_LDTR((userContext->ldtSelector));
    
}

