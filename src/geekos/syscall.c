/*
 * System call handlers
 * Copyright (c) 2003, Jeffrey K. Hollingsworth <hollings@cs.umd.edu>
 * Copyright (c) 2003,2004 David Hovemeyer <daveho@cs.umd.edu>
 * $Revision: 1.59 $
 * 
 * This is free software.  You are permitted to use,
 * redistribute, and modify it as specified in the file "COPYING".
 */

#include <geekos/syscall.h>
#include <geekos/errno.h>
#include <geekos/kthread.h>
#include <geekos/int.h>
#include <geekos/elf.h>
#include <geekos/malloc.h>
#include <geekos/screen.h>
#include <geekos/keyboard.h>
#include <geekos/string.h>
#include <geekos/user.h>
#include <geekos/timer.h>
#include <geekos/vfs.h>
#include <geekos/synch.h>

/*
 * Null system call.
 * Does nothing except immediately return control back
 * to the interrupted user program.
 * Params:
 *  state - processor registers from user mode
 *
 * Returns:
 *   always returns the value 0 (zero)
 */
static int Sys_Null(struct Interrupt_State* state)
{
	return 0;
}

/*
 * Exit system call.
 * The interrupted user process is terminated.
 * Params:
 *	 state->ebx - process exit code
 * Returns:
 *	 Never returns to user mode!
 */
static int Sys_Exit(struct Interrupt_State* state)
{
	Exit(state->ebx);
}

/*
 * Print a string to the console.
 * Params:
 *	 state->ebx - user pointer of string to be printed
 *	 state->ecx - number of characters to print
 * Returns: 0 if successful, -1 if not
 */
static int Sys_PrintString(struct Interrupt_State* state)
{	
	char string[100];
	int len = state->ecx;	
	int i;
	
	Copy_From_User(string, state->ebx, len);

	for(i = 0; i < len; i++)
		Put_Char(*(string+i));
	return 0;
}

/*
 * Get a single key press from the console.
 * Suspends the user process until a key press is available.
 * Params:
 *	 state - processor registers from user mode
 * Returns: the key code
 */
static int Sys_GetKey(struct Interrupt_State* state)
{
	return Wait_For_Key();
}

/*
 * Set the current text attributes.
 * Params:
 *	 state->ebx - character attributes to use
 * Returns: always returns 0
 */
static int Sys_SetAttr(struct Interrupt_State* state)
{
	Set_Current_Attr(state->ebx);
	return 0;
}

/*
 * Get the current cursor position.
 * Params:
 *	 state->ebx - pointer to user int where row value should be stored
 *	 state->ecx - pointer to user int where column value should be stored
 * Returns: 0 if successful, -1 otherwise
 */
static int Sys_GetCursor(struct Interrupt_State* state)
{
	int row, col;
	Get_Cursor(&row, &col);
	Copy_To_User(state->ebx, &row, sizeof(int*));
	Copy_To_User(state->ecx, &col, sizeof(int*));
	return 0;
}

/*
 * Set the current cursor position.
 * Params:
 *	 state->ebx - new row value
 *	 state->ecx - new column value
 * Returns: 0 if successful, -1 otherwise
 */
static int Sys_PutCursor(struct Interrupt_State* state)
{
	TODO("PutCursor system call");
}

/*
 * Create a new user process.
 * Params:
 *	 state->ebx - user address of name of executable
 *	 state->ecx - length of executable name
 *	 state->edx - user address of command string
 *	 state->esi - length of command string
 * Returns: pid of process if successful, error code (< 0) otherwise
 */
static int Sys_Spawn(struct Interrupt_State* state)
{
	char program[256] = {'\0',}; 
	char command[256] = {'\0',};
	int pid;
	struct Kernel_Thread **pThread;
	Copy_From_User(program, state->ebx, state->ecx);
	Copy_From_User(command, state->edx, state->esi);
	
	Print("%s\n", program);
	Enable_Interrupts();
	pid = Spawn(program, command, pThread);
	Disable_Interrupts();

	return pid; 
}

/*
 * Wait for a process to exit.
 * Params:
 *	 state->ebx - pid of process to wait for
 * Returns: the exit code of the process,
 *	 or error code (< 0) on error
 */
static int Sys_Wait(struct Interrupt_State* state)
{	
	int exitcode;
	Enable_Interrupts();
	exitcode = Join(Lookup_Thread(state->ebx));
	Disable_Interrupts();
	return exitcode;
}

/*
 * Get pid (process id) of current thread.
 * Params:
 *	 state - processor registers from user mode
 * Returns: the pid of the current thread
 */
static int Sys_GetPID(struct Interrupt_State* state)
{
	return g_currentThread->pid;
}

/*
 * Set the scheduling policy.
 * Params:
 *   state->ebx - policy,
 *   state->ecx - number of ticks in quantum
 * Returns: 0 if successful, -1 otherwise
 */
static int Sys_SetSchedulingPolicy(struct Interrupt_State* state)
{	
	g_Quantum = state->ecx;

	// MLF -> RR
	if(state->ebx == 0)
	{
    	Switch_To_RR();
    	return 0;
	}
   	// RR -> MLF
    else if(state->ebx == 1)
    {
		Switch_To_MLF();
		return 0;
	}
    else 
    	return -1;
}

/*
 * Get the time of day.
 * Params:
 *   state - processor registers from user mode
 *
 * Returns: value of the g_numTicks global variable
 */
static int Sys_GetTimeOfDay(struct Interrupt_State* state)
{
    return g_numTicks;
}

/*
 * Create a semaphore.
 * Params:
 *   state->ebx - user address of name of semaphore
 *   state->ecx - length of semaphore name
 *   state->edx - initial semaphore count
 * Returns: the global semaphore id
 */
static int Sys_CreateSemaphore(struct Interrupt_State* state)
{
	char name[25];
	Copy_From_User(name, state->ebx, state->ecx);
	return Create_Semaphore(name, state->edx);   	
}

/*
 * Acquire a semaphore.
 * Assume that the process has permission to access the semaphore,
 * the call will block until the semaphore count is >= 0.
 * Params:
 *   state->ebx - the semaphore id
 *
 * Returns: 0 if successful, error code (< 0) if unsuccessful
 */
static int Sys_P(struct Interrupt_State* state)
{
	return P(state->ebx);
}

/*
 * Release a semaphore.
 * Params:
 *   state->ebx - the semaphore id
 *
 * Returns: 0 if successful, error code (< 0) if unsuccessful
 */
static int Sys_V(struct Interrupt_State* state)
{
    return V(state->ebx);
}

/*
 * Destroy a semaphore.
 * Params:
 *   state->ebx - the semaphore id
 *
 * Returns: 0 if successful, error code (< 0) if unsuccessful
 */
static int Sys_DestroySemaphore(struct Interrupt_State* state)
{
	return Destroy_Semaphore(state->ebx);
}


/*
 * Global table of system call handler functions.
 */
const Syscall g_syscallTable[] = {
    Sys_Null,
    Sys_Exit,
    Sys_PrintString,
    Sys_GetKey,
    Sys_SetAttr,
    Sys_GetCursor,
    Sys_PutCursor,
    Sys_Spawn,
    Sys_Wait,
    Sys_GetPID,
    /* Scheduling and semaphore system calls. */
    Sys_SetSchedulingPolicy,
    Sys_GetTimeOfDay,
    Sys_CreateSemaphore,
    Sys_P,
    Sys_V,
    Sys_DestroySemaphore,
};

/*
 * Number of system calls implemented.
 */
const int g_numSyscalls = sizeof(g_syscallTable) / sizeof(Syscall);
