# 1 "ldv/68_1/drivers/staging/lirc/lirc_imon.ko/unsafe.cil.out.i"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "ldv/68_1/drivers/staging/lirc/lirc_imon.ko/unsafe.cil.out.i"
# 145 "include/linux/init.h"
typedef void (*ctor_fn_t)(void);
# 19 "include/asm-generic/int-ll64.h"
typedef signed char __s8;
# 20 "include/asm-generic/int-ll64.h"
typedef unsigned char __u8;
# 22 "include/asm-generic/int-ll64.h"
typedef short __s16;
# 23 "include/asm-generic/int-ll64.h"
typedef unsigned short __u16;
# 25 "include/asm-generic/int-ll64.h"
typedef int __s32;
# 26 "include/asm-generic/int-ll64.h"
typedef unsigned int __u32;
# 29 "include/asm-generic/int-ll64.h"
typedef long long __s64;
# 30 "include/asm-generic/int-ll64.h"
typedef unsigned long long __u64;
# 43 "include/asm-generic/int-ll64.h"
typedef unsigned char u8;
# 46 "include/asm-generic/int-ll64.h"
typedef unsigned short u16;
# 49 "include/asm-generic/int-ll64.h"
typedef unsigned int u32;
# 51 "include/asm-generic/int-ll64.h"
typedef long long s64;
# 52 "include/asm-generic/int-ll64.h"
typedef unsigned long long u64;
# 11 "include/asm-generic/types.h"
typedef unsigned short umode_t;
# 11 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/posix_types_64.h"
typedef unsigned int __kernel_mode_t;
# 14 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/posix_types_64.h"
typedef int __kernel_pid_t;
# 16 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/posix_types_64.h"
typedef unsigned int __kernel_uid_t;
# 17 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/posix_types_64.h"
typedef unsigned int __kernel_gid_t;
# 18 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/posix_types_64.h"
typedef unsigned long __kernel_size_t;
# 19 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/posix_types_64.h"
typedef long __kernel_ssize_t;
# 21 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/posix_types_64.h"
typedef long __kernel_time_t;
# 23 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/posix_types_64.h"
typedef long __kernel_clock_t;
# 24 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/posix_types_64.h"
typedef int __kernel_timer_t;
# 25 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/posix_types_64.h"
typedef int __kernel_clockid_t;
# 32 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/posix_types_64.h"
typedef long long __kernel_loff_t;
# 41 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/posix_types_64.h"
typedef __kernel_uid_t __kernel_uid32_t;
# 42 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/posix_types_64.h"
typedef __kernel_gid_t __kernel_gid32_t;
# 21 "include/linux/types.h"
typedef __u32 __kernel_dev_t;
# 24 "include/linux/types.h"
typedef __kernel_dev_t dev_t;
# 26 "include/linux/types.h"
typedef __kernel_mode_t mode_t;
# 29 "include/linux/types.h"
typedef __kernel_pid_t pid_t;
# 34 "include/linux/types.h"
typedef __kernel_clockid_t clockid_t;
# 37 "include/linux/types.h"
typedef _Bool bool;
# 39 "include/linux/types.h"
typedef __kernel_uid32_t uid_t;
# 40 "include/linux/types.h"
typedef __kernel_gid32_t gid_t;
# 53 "include/linux/types.h"
typedef __kernel_loff_t loff_t;
# 62 "include/linux/types.h"
typedef __kernel_size_t size_t;
# 67 "include/linux/types.h"
typedef __kernel_ssize_t ssize_t;
# 77 "include/linux/types.h"
typedef __kernel_time_t time_t;
# 110 "include/linux/types.h"
typedef __s32 int32_t;
# 116 "include/linux/types.h"
typedef __u32 uint32_t;
# 141 "include/linux/types.h"
typedef unsigned long sector_t;
# 142 "include/linux/types.h"
typedef unsigned long blkcnt_t;
# 154 "include/linux/types.h"
typedef u64 dma_addr_t;
# 177 "include/linux/types.h"
typedef __u16 __le16;
# 201 "include/linux/types.h"
typedef unsigned int gfp_t;
# 202 "include/linux/types.h"
typedef unsigned int fmode_t;
# 212 "include/linux/types.h"
struct __anonstruct_atomic_t_7 {
   int counter ;
};
# 212 "include/linux/types.h"
typedef struct __anonstruct_atomic_t_7 atomic_t;
# 217 "include/linux/types.h"
struct __anonstruct_atomic64_t_8 {
   long counter ;
};
# 217 "include/linux/types.h"
typedef struct __anonstruct_atomic64_t_8 atomic64_t;
# 222 "include/linux/types.h"
struct list_head {
   struct list_head *next ;
   struct list_head *prev ;
};
# 226 "include/linux/types.h"
struct hlist_node;
# 226 "include/linux/types.h"
struct hlist_node;
# 226 "include/linux/types.h"
struct hlist_head {
   struct hlist_node *first ;
};
# 230 "include/linux/types.h"
struct hlist_node {
   struct hlist_node *next ;
   struct hlist_node **pprev ;
};
# 59 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/alternative.h"
struct module;
# 59 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/alternative.h"
struct module;
# 59 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/alternative.h"
struct module;
# 16 "include/linux/dynamic_debug.h"
struct _ddebug {
   char const *modname ;
   char const *function ;
   char const *filename ;
   char const *format ;
   unsigned int lineno : 24 ;
   unsigned int flags : 8 ;
   char enabled ;
} __attribute__((__aligned__(8))) ;
# 10 "include/asm-generic/bug.h"
struct bug_entry {
   int bug_addr_disp ;
   int file_disp ;
   unsigned short line ;
   unsigned short flags ;
};
# 113 "include/linux/kernel.h"
struct completion;
# 113 "include/linux/kernel.h"
struct completion;
# 113 "include/linux/kernel.h"
struct completion;
# 114 "include/linux/kernel.h"
struct pt_regs;
# 114 "include/linux/kernel.h"
struct pt_regs;
# 114 "include/linux/kernel.h"
struct pt_regs;
# 322 "include/linux/kernel.h"
struct pid;
# 322 "include/linux/kernel.h"
struct pid;
# 322 "include/linux/kernel.h"
struct pid;
# 12 "include/linux/thread_info.h"
struct timespec;
# 12 "include/linux/thread_info.h"
struct timespec;
# 12 "include/linux/thread_info.h"
struct timespec;
# 18 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/page.h"
struct page;
# 18 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/page.h"
struct page;
# 18 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/page.h"
struct page;
# 20 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/thread_info.h"
struct task_struct;
# 20 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/thread_info.h"
struct task_struct;
# 20 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/thread_info.h"
struct task_struct;
# 7 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
struct task_struct;
# 8 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
struct mm_struct;
# 8 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
struct mm_struct;
# 8 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
struct mm_struct;
# 99 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/ptrace.h"
struct pt_regs {
   unsigned long r15 ;
   unsigned long r14 ;
   unsigned long r13 ;
   unsigned long r12 ;
   unsigned long bp ;
   unsigned long bx ;
   unsigned long r11 ;
   unsigned long r10 ;
   unsigned long r9 ;
   unsigned long r8 ;
   unsigned long ax ;
   unsigned long cx ;
   unsigned long dx ;
   unsigned long si ;
   unsigned long di ;
   unsigned long orig_ax ;
   unsigned long ip ;
   unsigned long cs ;
   unsigned long flags ;
   unsigned long sp ;
   unsigned long ss ;
};
# 136 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/ptrace.h"
struct task_struct;
# 141 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/vm86.h"
struct kernel_vm86_regs {
   struct pt_regs pt ;
   unsigned short es ;
   unsigned short __esh ;
   unsigned short ds ;
   unsigned short __dsh ;
   unsigned short fs ;
   unsigned short __fsh ;
   unsigned short gs ;
   unsigned short __gsh ;
};
# 11 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/math_emu.h"
union __anonunion____missing_field_name_14 {
   struct pt_regs *regs ;
   struct kernel_vm86_regs *vm86 ;
};
# 11 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/math_emu.h"
struct math_emu_info {
   long ___orig_eip ;
   union __anonunion____missing_field_name_14 __annonCompField5 ;
};
# 8 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/current.h"
struct task_struct;
# 13 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/pgtable_64_types.h"
typedef unsigned long pgdval_t;
# 14 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/pgtable_64_types.h"
typedef unsigned long pgprotval_t;
# 190 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/pgtable_types.h"
struct pgprot {
   pgprotval_t pgprot ;
};
# 190 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/pgtable_types.h"
typedef struct pgprot pgprot_t;
# 192 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/pgtable_types.h"
struct __anonstruct_pgd_t_17 {
   pgdval_t pgd ;
};
# 192 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/pgtable_types.h"
typedef struct __anonstruct_pgd_t_17 pgd_t;
# 280 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/pgtable_types.h"
typedef struct page *pgtable_t;
# 293 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/pgtable_types.h"
struct file;
# 293 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/pgtable_types.h"
struct file;
# 293 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/pgtable_types.h"
struct file;
# 311 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/pgtable_types.h"
struct seq_file;
# 311 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/pgtable_types.h"
struct seq_file;
# 311 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/pgtable_types.h"
struct seq_file;
# 22 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/desc_defs.h"
struct __anonstruct____missing_field_name_22 {
   unsigned int a ;
   unsigned int b ;
};
# 22 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/desc_defs.h"
struct __anonstruct____missing_field_name_23 {
   u16 limit0 ;
   u16 base0 ;
   unsigned int base1 : 8 ;
   unsigned int type : 4 ;
   unsigned int s : 1 ;
   unsigned int dpl : 2 ;
   unsigned int p : 1 ;
   unsigned int limit : 4 ;
   unsigned int avl : 1 ;
   unsigned int l : 1 ;
   unsigned int d : 1 ;
   unsigned int g : 1 ;
   unsigned int base2 : 8 ;
};
# 22 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/desc_defs.h"
union __anonunion____missing_field_name_21 {
   struct __anonstruct____missing_field_name_22 __annonCompField7 ;
   struct __anonstruct____missing_field_name_23 __annonCompField8 ;
};
# 22 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/desc_defs.h"
struct desc_struct {
   union __anonunion____missing_field_name_21 __annonCompField9 ;
} __attribute__((__packed__)) ;
# 45 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/paravirt_types.h"
struct page;
# 46 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/paravirt_types.h"
struct thread_struct;
# 46 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/paravirt_types.h"
struct thread_struct;
# 46 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/paravirt_types.h"
struct thread_struct;
# 49 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/paravirt_types.h"
struct mm_struct;
# 50 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/paravirt_types.h"
struct desc_struct;
# 51 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/paravirt_types.h"
struct task_struct;
# 52 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/paravirt_types.h"
struct cpumask;
# 52 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/paravirt_types.h"
struct cpumask;
# 52 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/paravirt_types.h"
struct cpumask;
# 322 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/paravirt_types.h"
struct arch_spinlock;
# 322 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/paravirt_types.h"
struct arch_spinlock;
# 322 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/paravirt_types.h"
struct arch_spinlock;
# 13 "include/linux/cpumask.h"
struct cpumask {
   unsigned long bits[((4096UL + 8UL * sizeof(long )) - 1UL) / (8UL * sizeof(long ))] ;
};
# 13 "include/linux/cpumask.h"
typedef struct cpumask cpumask_t;
# 622 "include/linux/cpumask.h"
typedef struct cpumask *cpumask_var_t;
# 20 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/system.h"
struct task_struct;
# 11 "include/linux/personality.h"
struct pt_regs;
# 280 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
struct i387_fsave_struct {
   u32 cwd ;
   u32 swd ;
   u32 twd ;
   u32 fip ;
   u32 fcs ;
   u32 foo ;
   u32 fos ;
   u32 st_space[20] ;
   u32 status ;
};
# 296 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
struct __anonstruct____missing_field_name_31 {
   u64 rip ;
   u64 rdp ;
};
# 296 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
struct __anonstruct____missing_field_name_32 {
   u32 fip ;
   u32 fcs ;
   u32 foo ;
   u32 fos ;
};
# 296 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
union __anonunion____missing_field_name_30 {
   struct __anonstruct____missing_field_name_31 __annonCompField12 ;
   struct __anonstruct____missing_field_name_32 __annonCompField13 ;
};
# 296 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
union __anonunion____missing_field_name_33 {
   u32 padding1[12] ;
   u32 sw_reserved[12] ;
};
# 296 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
struct i387_fxsave_struct {
   u16 cwd ;
   u16 swd ;
   u16 twd ;
   u16 fop ;
   union __anonunion____missing_field_name_30 __annonCompField14 ;
   u32 mxcsr ;
   u32 mxcsr_mask ;
   u32 st_space[32] ;
   u32 xmm_space[64] ;
   u32 padding[12] ;
   union __anonunion____missing_field_name_33 __annonCompField15 ;
} __attribute__((__aligned__(16))) ;
# 331 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
struct i387_soft_struct {
   u32 cwd ;
   u32 swd ;
   u32 twd ;
   u32 fip ;
   u32 fcs ;
   u32 foo ;
   u32 fos ;
   u32 st_space[20] ;
   u8 ftop ;
   u8 changed ;
   u8 lookahead ;
   u8 no_update ;
   u8 rm ;
   u8 alimit ;
   struct math_emu_info *info ;
   u32 entry_eip ;
};
# 351 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
struct ymmh_struct {
   u32 ymmh_space[64] ;
};
# 356 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
struct xsave_hdr_struct {
   u64 xstate_bv ;
   u64 reserved1[2] ;
   u64 reserved2[5] ;
} __attribute__((__packed__)) ;
# 362 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
struct xsave_struct {
   struct i387_fxsave_struct i387 ;
   struct xsave_hdr_struct xsave_hdr ;
   struct ymmh_struct ymmh ;
} __attribute__((__packed__, __aligned__(64))) ;
# 369 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
union thread_xstate {
   struct i387_fsave_struct fsave ;
   struct i387_fxsave_struct fxsave ;
   struct i387_soft_struct soft ;
   struct xsave_struct xsave ;
};
# 376 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
struct fpu {
   union thread_xstate *state ;
};
# 421 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
struct kmem_cache;
# 421 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
struct kmem_cache;
# 423 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
struct perf_event;
# 423 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
struct perf_event;
# 423 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
struct perf_event;
# 425 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/processor.h"
struct thread_struct {
   struct desc_struct tls_array[3] ;
   unsigned long sp0 ;
   unsigned long sp ;
   unsigned long usersp ;
   unsigned short es ;
   unsigned short ds ;
   unsigned short fsindex ;
   unsigned short gsindex ;
   unsigned long fs ;
   unsigned long gs ;
   struct perf_event *ptrace_bps[4] ;
   unsigned long debugreg6 ;
   unsigned long ptrace_dr7 ;
   unsigned long cr2 ;
   unsigned long trap_no ;
   unsigned long error_code ;
   struct fpu fpu ;
   unsigned long *io_bitmap_ptr ;
   unsigned long iopl ;
   unsigned int io_bitmap_max ;
};
# 23 "include/asm-generic/atomic-long.h"
typedef atomic64_t atomic_long_t;
# 8 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/spinlock_types.h"
struct arch_spinlock {
   unsigned int slock ;
};
# 8 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/spinlock_types.h"
typedef struct arch_spinlock arch_spinlock_t;
# 14 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/spinlock_types.h"
struct __anonstruct_arch_rwlock_t_36 {
   unsigned int lock ;
};
# 14 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/spinlock_types.h"
typedef struct __anonstruct_arch_rwlock_t_36 arch_rwlock_t;
# 12 "include/linux/lockdep.h"
struct task_struct;
# 13 "include/linux/lockdep.h"
struct lockdep_map;
# 13 "include/linux/lockdep.h"
struct lockdep_map;
# 13 "include/linux/lockdep.h"
struct lockdep_map;
# 8 "include/linux/debug_locks.h"
struct task_struct;
# 48 "include/linux/debug_locks.h"
struct task_struct;
# 4 "include/linux/stacktrace.h"
struct task_struct;
# 5 "include/linux/stacktrace.h"
struct pt_regs;
# 8 "include/linux/stacktrace.h"
struct task_struct;
# 10 "include/linux/stacktrace.h"
struct stack_trace {
   unsigned int nr_entries ;
   unsigned int max_entries ;
   unsigned long *entries ;
   int skip ;
};
# 50 "include/linux/lockdep.h"
struct lockdep_subclass_key {
   char __one_byte ;
} __attribute__((__packed__)) ;
# 54 "include/linux/lockdep.h"
struct lock_class_key {
   struct lockdep_subclass_key subkeys[8UL] ;
};
# 65 "include/linux/lockdep.h"
struct lock_class {
   struct list_head hash_entry ;
   struct list_head lock_entry ;
   struct lockdep_subclass_key *key ;
   unsigned int subclass ;
   unsigned int dep_gen_id ;
   unsigned long usage_mask ;
   struct stack_trace usage_traces[13] ;
   struct list_head locks_after ;
   struct list_head locks_before ;
   unsigned int version ;
   unsigned long ops ;
   char const *name ;
   int name_version ;
   unsigned long contention_point[4] ;
   unsigned long contending_point[4] ;
};
# 150 "include/linux/lockdep.h"
struct lockdep_map {
   struct lock_class_key *key ;
   struct lock_class *class_cache[2] ;
   char const *name ;
   int cpu ;
   unsigned long ip ;
};
# 196 "include/linux/lockdep.h"
struct held_lock {
   u64 prev_chain_key ;
   unsigned long acquire_ip ;
   struct lockdep_map *instance ;
   struct lockdep_map *nest_lock ;
   u64 waittime_stamp ;
   u64 holdtime_stamp ;
   unsigned int class_idx : 13 ;
   unsigned int irq_context : 2 ;
   unsigned int trylock : 1 ;
   unsigned int read : 2 ;
   unsigned int check : 2 ;
   unsigned int hardirqs_off : 1 ;
   unsigned int references : 11 ;
};
# 20 "include/linux/spinlock_types.h"
struct raw_spinlock {
   arch_spinlock_t raw_lock ;
   unsigned int magic ;
   unsigned int owner_cpu ;
   void *owner ;
   struct lockdep_map dep_map ;
};
# 20 "include/linux/spinlock_types.h"
typedef struct raw_spinlock raw_spinlock_t;
# 64 "include/linux/spinlock_types.h"
struct __anonstruct____missing_field_name_38 {
   u8 __padding[(unsigned int )(& ((struct raw_spinlock *)0)->dep_map)] ;
   struct lockdep_map dep_map ;
};
# 64 "include/linux/spinlock_types.h"
union __anonunion____missing_field_name_37 {
   struct raw_spinlock rlock ;
   struct __anonstruct____missing_field_name_38 __annonCompField17 ;
};
# 64 "include/linux/spinlock_types.h"
struct spinlock {
   union __anonunion____missing_field_name_37 __annonCompField18 ;
};
# 64 "include/linux/spinlock_types.h"
typedef struct spinlock spinlock_t;
# 11 "include/linux/rwlock_types.h"
struct __anonstruct_rwlock_t_39 {
   arch_rwlock_t raw_lock ;
   unsigned int magic ;
   unsigned int owner_cpu ;
   void *owner ;
   struct lockdep_map dep_map ;
};
# 11 "include/linux/rwlock_types.h"
typedef struct __anonstruct_rwlock_t_39 rwlock_t;
# 119 "include/linux/seqlock.h"
struct seqcount {
   unsigned int sequence ;
};
# 119 "include/linux/seqlock.h"
typedef struct seqcount seqcount_t;
# 14 "include/linux/time.h"
struct timespec {
   __kernel_time_t tv_sec ;
   long tv_nsec ;
};
# 62 "include/linux/stat.h"
struct kstat {
   u64 ino ;
   dev_t dev ;
   umode_t mode ;
   unsigned int nlink ;
   uid_t uid ;
   gid_t gid ;
   dev_t rdev ;
   loff_t size ;
   struct timespec atime ;
   struct timespec mtime ;
   struct timespec ctime ;
   unsigned long blksize ;
   unsigned long long blocks ;
};
# 50 "include/linux/wait.h"
struct __wait_queue_head {
   spinlock_t lock ;
   struct list_head task_list ;
};
# 54 "include/linux/wait.h"
typedef struct __wait_queue_head wait_queue_head_t;
# 56 "include/linux/wait.h"
struct task_struct;
# 96 "include/linux/nodemask.h"
struct __anonstruct_nodemask_t_41 {
   unsigned long bits[(((unsigned long )(1 << 10) + 8UL * sizeof(long )) - 1UL) / (8UL * sizeof(long ))] ;
};
# 96 "include/linux/nodemask.h"
typedef struct __anonstruct_nodemask_t_41 nodemask_t;
# 60 "include/linux/pageblock-flags.h"
struct page;
# 48 "include/linux/mutex.h"
struct mutex {
   atomic_t count ;
   spinlock_t wait_lock ;
   struct list_head wait_list ;
   struct task_struct *owner ;
   char const *name ;
   void *magic ;
   struct lockdep_map dep_map ;
};
# 69 "include/linux/mutex.h"
struct mutex_waiter {
   struct list_head list ;
   struct task_struct *task ;
   void *magic ;
};
# 20 "include/linux/rwsem.h"
struct rw_semaphore;
# 20 "include/linux/rwsem.h"
struct rw_semaphore;
# 20 "include/linux/rwsem.h"
struct rw_semaphore;
# 26 "include/linux/rwsem.h"
struct rw_semaphore {
   long count ;
   spinlock_t wait_lock ;
   struct list_head wait_list ;
   struct lockdep_map dep_map ;
};
# 8 "include/linux/memory_hotplug.h"
struct page;
# 177 "include/linux/ioport.h"
struct device;
# 177 "include/linux/ioport.h"
struct device;
# 177 "include/linux/ioport.h"
struct device;
# 103 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/mpspec.h"
struct device;
# 46 "include/linux/ktime.h"
union ktime {
   s64 tv64 ;
};
# 59 "include/linux/ktime.h"
typedef union ktime ktime_t;
# 10 "include/linux/timer.h"
struct tvec_base;
# 10 "include/linux/timer.h"
struct tvec_base;
# 10 "include/linux/timer.h"
struct tvec_base;
# 12 "include/linux/timer.h"
struct timer_list {
   struct list_head entry ;
   unsigned long expires ;
   struct tvec_base *base ;
   void (*function)(unsigned long ) ;
   unsigned long data ;
   int slack ;
   int start_pid ;
   void *start_site ;
   char start_comm[16] ;
   struct lockdep_map lockdep_map ;
};
# 289 "include/linux/timer.h"
struct hrtimer;
# 289 "include/linux/timer.h"
struct hrtimer;
# 289 "include/linux/timer.h"
struct hrtimer;
# 290 "include/linux/timer.h"
enum hrtimer_restart;
# 290 "include/linux/timer.h"
enum hrtimer_restart;
# 17 "include/linux/workqueue.h"
struct work_struct;
# 17 "include/linux/workqueue.h"
struct work_struct;
# 17 "include/linux/workqueue.h"
struct work_struct;
# 79 "include/linux/workqueue.h"
struct work_struct {
   atomic_long_t data ;
   struct list_head entry ;
   void (*func)(struct work_struct *work ) ;
   struct lockdep_map lockdep_map ;
};
# 92 "include/linux/workqueue.h"
struct delayed_work {
   struct work_struct work ;
   struct timer_list timer ;
};
# 25 "include/linux/completion.h"
struct completion {
   unsigned int done ;
   wait_queue_head_t wait ;
};
# 42 "include/linux/pm.h"
struct device;
# 50 "include/linux/pm.h"
struct pm_message {
   int event ;
};
# 50 "include/linux/pm.h"
typedef struct pm_message pm_message_t;
# 204 "include/linux/pm.h"
struct dev_pm_ops {
   int (*prepare)(struct device *dev ) ;
   void (*complete)(struct device *dev ) ;
   int (*suspend)(struct device *dev ) ;
   int (*resume)(struct device *dev ) ;
   int (*freeze)(struct device *dev ) ;
   int (*thaw)(struct device *dev ) ;
   int (*poweroff)(struct device *dev ) ;
   int (*restore)(struct device *dev ) ;
   int (*suspend_noirq)(struct device *dev ) ;
   int (*resume_noirq)(struct device *dev ) ;
   int (*freeze_noirq)(struct device *dev ) ;
   int (*thaw_noirq)(struct device *dev ) ;
   int (*poweroff_noirq)(struct device *dev ) ;
   int (*restore_noirq)(struct device *dev ) ;
   int (*runtime_suspend)(struct device *dev ) ;
   int (*runtime_resume)(struct device *dev ) ;
   int (*runtime_idle)(struct device *dev ) ;
};
# 392 "include/linux/pm.h"
enum rpm_status {
    RPM_ACTIVE = 0,
    RPM_RESUMING = 1,
    RPM_SUSPENDED = 2,
    RPM_SUSPENDING = 3
} ;
# 414 "include/linux/pm.h"
enum rpm_request {
    RPM_REQ_NONE = 0,
    RPM_REQ_IDLE = 1,
    RPM_REQ_SUSPEND = 2,
    RPM_REQ_AUTOSUSPEND = 3,
    RPM_REQ_RESUME = 4
} ;
# 422 "include/linux/pm.h"
struct wakeup_source;
# 422 "include/linux/pm.h"
struct wakeup_source;
# 422 "include/linux/pm.h"
struct wakeup_source;
# 424 "include/linux/pm.h"
struct dev_pm_info {
   pm_message_t power_state ;
   unsigned int can_wakeup : 1 ;
   unsigned int async_suspend : 1 ;
   bool is_prepared : 1 ;
   bool is_suspended : 1 ;
   spinlock_t lock ;
   struct list_head entry ;
   struct completion completion ;
   struct wakeup_source *wakeup ;
   struct timer_list suspend_timer ;
   unsigned long timer_expires ;
   struct work_struct work ;
   wait_queue_head_t wait_queue ;
   atomic_t usage_count ;
   atomic_t child_count ;
   unsigned int disable_depth : 3 ;
   unsigned int ignore_children : 1 ;
   unsigned int idle_notification : 1 ;
   unsigned int request_pending : 1 ;
   unsigned int deferred_resume : 1 ;
   unsigned int run_wake : 1 ;
   unsigned int runtime_auto : 1 ;
   unsigned int no_callbacks : 1 ;
   unsigned int irq_safe : 1 ;
   unsigned int use_autosuspend : 1 ;
   unsigned int timer_autosuspends : 1 ;
   enum rpm_request request ;
   enum rpm_status runtime_status ;
   int runtime_error ;
   int autosuspend_delay ;
   unsigned long last_busy ;
   unsigned long active_jiffies ;
   unsigned long suspended_jiffies ;
   unsigned long accounting_timestamp ;
   void *subsys_data ;
};
# 475 "include/linux/pm.h"
struct dev_power_domain {
   struct dev_pm_ops ops ;
};
# 11 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/mmu.h"
struct __anonstruct_mm_context_t_111 {
   void *ldt ;
   int size ;
   unsigned short ia32_compat ;
   struct mutex lock ;
   void *vdso ;
};
# 11 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/mmu.h"
typedef struct __anonstruct_mm_context_t_111 mm_context_t;
# 8 "include/linux/vmalloc.h"
struct vm_area_struct;
# 8 "include/linux/vmalloc.h"
struct vm_area_struct;
# 8 "include/linux/vmalloc.h"
struct vm_area_struct;
# 964 "include/linux/mmzone.h"
struct page;
# 10 "include/linux/gfp.h"
struct vm_area_struct;
# 29 "include/linux/sysctl.h"
struct completion;
# 72 "include/linux/rcupdate.h"
struct rcu_head {
   struct rcu_head *next ;
   void (*func)(struct rcu_head *head ) ;
};
# 937 "include/linux/sysctl.h"
struct nsproxy;
# 937 "include/linux/sysctl.h"
struct nsproxy;
# 937 "include/linux/sysctl.h"
struct nsproxy;
# 48 "include/linux/kmod.h"
struct cred;
# 48 "include/linux/kmod.h"
struct cred;
# 48 "include/linux/kmod.h"
struct cred;
# 49 "include/linux/kmod.h"
struct file;
# 264 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/elf.h"
struct task_struct;
# 10 "include/linux/elf.h"
struct file;
# 27 "include/linux/elf.h"
typedef __u64 Elf64_Addr;
# 28 "include/linux/elf.h"
typedef __u16 Elf64_Half;
# 32 "include/linux/elf.h"
typedef __u32 Elf64_Word;
# 33 "include/linux/elf.h"
typedef __u64 Elf64_Xword;
# 203 "include/linux/elf.h"
struct elf64_sym {
   Elf64_Word st_name ;
   unsigned char st_info ;
   unsigned char st_other ;
   Elf64_Half st_shndx ;
   Elf64_Addr st_value ;
   Elf64_Xword st_size ;
};
# 203 "include/linux/elf.h"
typedef struct elf64_sym Elf64_Sym;
# 20 "include/linux/kobject_ns.h"
struct sock;
# 20 "include/linux/kobject_ns.h"
struct sock;
# 20 "include/linux/kobject_ns.h"
struct sock;
# 21 "include/linux/kobject_ns.h"
struct kobject;
# 21 "include/linux/kobject_ns.h"
struct kobject;
# 21 "include/linux/kobject_ns.h"
struct kobject;
# 27 "include/linux/kobject_ns.h"
enum kobj_ns_type {
    KOBJ_NS_TYPE_NONE = 0,
    KOBJ_NS_TYPE_NET = 1,
    KOBJ_NS_TYPES = 2
} ;
# 40 "include/linux/kobject_ns.h"
struct kobj_ns_type_operations {
   enum kobj_ns_type type ;
   void *(*grab_current_ns)(void) ;
   void const *(*netlink_ns)(struct sock *sk ) ;
   void const *(*initial_ns)(void) ;
   void (*drop_ns)(void * ) ;
};
# 22 "include/linux/sysfs.h"
struct kobject;
# 23 "include/linux/sysfs.h"
struct module;
# 24 "include/linux/sysfs.h"
enum kobj_ns_type;
# 26 "include/linux/sysfs.h"
struct attribute {
   char const *name ;
   mode_t mode ;
   struct lock_class_key *key ;
   struct lock_class_key skey ;
};
# 56 "include/linux/sysfs.h"
struct attribute_group {
   char const *name ;
   mode_t (*is_visible)(struct kobject * , struct attribute * , int ) ;
   struct attribute **attrs ;
};
# 85 "include/linux/sysfs.h"
struct file;
# 86 "include/linux/sysfs.h"
struct vm_area_struct;
# 88 "include/linux/sysfs.h"
struct bin_attribute {
   struct attribute attr ;
   size_t size ;
   void *private ;
   ssize_t (*read)(struct file * , struct kobject * , struct bin_attribute * , char * ,
                   loff_t , size_t ) ;
   ssize_t (*write)(struct file * , struct kobject * , struct bin_attribute * , char * ,
                    loff_t , size_t ) ;
   int (*mmap)(struct file * , struct kobject * , struct bin_attribute *attr , struct vm_area_struct *vma ) ;
};
# 112 "include/linux/sysfs.h"
struct sysfs_ops {
   ssize_t (*show)(struct kobject * , struct attribute * , char * ) ;
   ssize_t (*store)(struct kobject * , struct attribute * , char const * , size_t ) ;
};
# 117 "include/linux/sysfs.h"
struct sysfs_dirent;
# 117 "include/linux/sysfs.h"
struct sysfs_dirent;
# 117 "include/linux/sysfs.h"
struct sysfs_dirent;
# 20 "include/linux/kref.h"
struct kref {
   atomic_t refcount ;
};
# 60 "include/linux/kobject.h"
struct kset;
# 60 "include/linux/kobject.h"
struct kset;
# 60 "include/linux/kobject.h"
struct kobj_type;
# 60 "include/linux/kobject.h"
struct kobj_type;
# 60 "include/linux/kobject.h"
struct kobject {
   char const *name ;
   struct list_head entry ;
   struct kobject *parent ;
   struct kset *kset ;
   struct kobj_type *ktype ;
   struct sysfs_dirent *sd ;
   struct kref kref ;
   unsigned int state_initialized : 1 ;
   unsigned int state_in_sysfs : 1 ;
   unsigned int state_add_uevent_sent : 1 ;
   unsigned int state_remove_uevent_sent : 1 ;
   unsigned int uevent_suppress : 1 ;
};
# 110 "include/linux/kobject.h"
struct kobj_type {
   void (*release)(struct kobject *kobj ) ;
   struct sysfs_ops const *sysfs_ops ;
   struct attribute **default_attrs ;
   struct kobj_ns_type_operations const *(*child_ns_type)(struct kobject *kobj ) ;
   void const *(*namespace)(struct kobject *kobj ) ;
};
# 118 "include/linux/kobject.h"
struct kobj_uevent_env {
   char *envp[32] ;
   int envp_idx ;
   char buf[2048] ;
   int buflen ;
};
# 125 "include/linux/kobject.h"
struct kset_uevent_ops {
   int (* const filter)(struct kset *kset , struct kobject *kobj ) ;
   char const *(* const name)(struct kset *kset , struct kobject *kobj ) ;
   int (* const uevent)(struct kset *kset , struct kobject *kobj , struct kobj_uevent_env *env ) ;
};
# 142 "include/linux/kobject.h"
struct sock;
# 161 "include/linux/kobject.h"
struct kset {
   struct list_head list ;
   spinlock_t list_lock ;
   struct kobject kobj ;
   struct kset_uevent_ops const *uevent_ops ;
};
# 34 "include/linux/moduleparam.h"
struct kernel_param;
# 34 "include/linux/moduleparam.h"
struct kernel_param;
# 34 "include/linux/moduleparam.h"
struct kernel_param;
# 36 "include/linux/moduleparam.h"
struct kernel_param_ops {
   int (*set)(char const *val , struct kernel_param const *kp ) ;
   int (*get)(char *buffer , struct kernel_param const *kp ) ;
   void (*free)(void *arg ) ;
};
# 48 "include/linux/moduleparam.h"
struct kparam_string;
# 48 "include/linux/moduleparam.h"
struct kparam_string;
# 48 "include/linux/moduleparam.h"
struct kparam_array;
# 48 "include/linux/moduleparam.h"
struct kparam_array;
# 48 "include/linux/moduleparam.h"
union __anonunion____missing_field_name_195 {
   void *arg ;
   struct kparam_string const *str ;
   struct kparam_array const *arr ;
};
# 48 "include/linux/moduleparam.h"
struct kernel_param {
   char const *name ;
   struct kernel_param_ops const *ops ;
   u16 perm ;
   u16 flags ;
   union __anonunion____missing_field_name_195 __annonCompField31 ;
};
# 61 "include/linux/moduleparam.h"
struct kparam_string {
   unsigned int maxlen ;
   char *string ;
};
# 67 "include/linux/moduleparam.h"
struct kparam_array {
   unsigned int max ;
   unsigned int elemsize ;
   unsigned int *num ;
   struct kernel_param_ops const *ops ;
   void *elem ;
};
# 391 "include/linux/moduleparam.h"
struct module;
# 26 "include/linux/jump_label.h"
struct module;
# 61 "include/linux/jump_label.h"
struct jump_label_key {
   atomic_t enabled ;
};
# 22 "include/linux/tracepoint.h"
struct module;
# 23 "include/linux/tracepoint.h"
struct tracepoint;
# 23 "include/linux/tracepoint.h"
struct tracepoint;
# 23 "include/linux/tracepoint.h"
struct tracepoint;
# 25 "include/linux/tracepoint.h"
struct tracepoint_func {
   void *func ;
   void *data ;
};
# 30 "include/linux/tracepoint.h"
struct tracepoint {
   char const *name ;
   struct jump_label_key key ;
   void (*regfunc)(void) ;
   void (*unregfunc)(void) ;
   struct tracepoint_func *funcs ;
};
# 8 "include/asm-generic/module.h"
struct mod_arch_specific {

};
# 21 "include/trace/events/module.h"
struct module;
# 37 "include/linux/module.h"
struct kernel_symbol {
   unsigned long value ;
   char const *name ;
};
# 49 "include/linux/module.h"
struct module;
# 51 "include/linux/module.h"
struct module_attribute {
   struct attribute attr ;
   ssize_t (*show)(struct module_attribute * , struct module * , char * ) ;
   ssize_t (*store)(struct module_attribute * , struct module * , char const * ,
                    size_t count ) ;
   void (*setup)(struct module * , char const * ) ;
   int (*test)(struct module * ) ;
   void (*free)(struct module * ) ;
};
# 70 "include/linux/module.h"
struct module_param_attrs;
# 70 "include/linux/module.h"
struct module_param_attrs;
# 70 "include/linux/module.h"
struct module_kobject {
   struct kobject kobj ;
   struct module *mod ;
   struct kobject *drivers_dir ;
   struct module_param_attrs *mp ;
};
# 83 "include/linux/module.h"
struct exception_table_entry;
# 83 "include/linux/module.h"
struct exception_table_entry;
# 83 "include/linux/module.h"
struct exception_table_entry;
# 265 "include/linux/module.h"
enum module_state {
    MODULE_STATE_LIVE = 0,
    MODULE_STATE_COMING = 1,
    MODULE_STATE_GOING = 2
} ;
# 272 "include/linux/module.h"
struct module_sect_attrs;
# 272 "include/linux/module.h"
struct module_sect_attrs;
# 272 "include/linux/module.h"
struct module_notes_attrs;
# 272 "include/linux/module.h"
struct module_notes_attrs;
# 272 "include/linux/module.h"
struct ftrace_event_call;
# 272 "include/linux/module.h"
struct ftrace_event_call;
# 272 "include/linux/module.h"
struct module_ref {
   unsigned int incs ;
   unsigned int decs ;
};
# 272 "include/linux/module.h"
struct module {
   enum module_state state ;
   struct list_head list ;
   char name[64UL - sizeof(unsigned long )] ;
   struct module_kobject mkobj ;
   struct module_attribute *modinfo_attrs ;
   char const *version ;
   char const *srcversion ;
   struct kobject *holders_dir ;
   struct kernel_symbol const *syms ;
   unsigned long const *crcs ;
   unsigned int num_syms ;
   struct kernel_param *kp ;
   unsigned int num_kp ;
   unsigned int num_gpl_syms ;
   struct kernel_symbol const *gpl_syms ;
   unsigned long const *gpl_crcs ;
   struct kernel_symbol const *unused_syms ;
   unsigned long const *unused_crcs ;
   unsigned int num_unused_syms ;
   unsigned int num_unused_gpl_syms ;
   struct kernel_symbol const *unused_gpl_syms ;
   unsigned long const *unused_gpl_crcs ;
   struct kernel_symbol const *gpl_future_syms ;
   unsigned long const *gpl_future_crcs ;
   unsigned int num_gpl_future_syms ;
   unsigned int num_exentries ;
   struct exception_table_entry *extable ;
   int (*init)(void) ;
   void *module_init ;
   void *module_core ;
   unsigned int init_size ;
   unsigned int core_size ;
   unsigned int init_text_size ;
   unsigned int core_text_size ;
   unsigned int init_ro_size ;
   unsigned int core_ro_size ;
   struct mod_arch_specific arch ;
   unsigned int taints ;
   unsigned int num_bugs ;
   struct list_head bug_list ;
   struct bug_entry *bug_table ;
   Elf64_Sym *symtab ;
   Elf64_Sym *core_symtab ;
   unsigned int num_symtab ;
   unsigned int core_num_syms ;
   char *strtab ;
   char *core_strtab ;
   struct module_sect_attrs *sect_attrs ;
   struct module_notes_attrs *notes_attrs ;
   char *args ;
   void *percpu ;
   unsigned int percpu_size ;
   unsigned int num_tracepoints ;
   struct tracepoint * const *tracepoints_ptrs ;
   unsigned int num_trace_bprintk_fmt ;
   char const **trace_bprintk_fmt_start ;
   struct ftrace_event_call **trace_events ;
   unsigned int num_trace_events ;
   unsigned int num_ftrace_callsites ;
   unsigned long *ftrace_callsites ;
   struct list_head source_list ;
   struct list_head target_list ;
   struct task_struct *waiter ;
   void (*exit)(void) ;
   struct module_ref *refptr ;
   ctor_fn_t *ctors ;
   unsigned int num_ctors ;
};
# 38 "include/linux/slub_def.h"
struct kmem_cache_cpu {
   void **freelist ;
   unsigned long tid ;
   struct page *page ;
   int node ;
   unsigned int stat[19] ;
};
# 48 "include/linux/slub_def.h"
struct kmem_cache_node {
   spinlock_t list_lock ;
   unsigned long nr_partial ;
   struct list_head partial ;
   atomic_long_t nr_slabs ;
   atomic_long_t total_objects ;
   struct list_head full ;
};
# 64 "include/linux/slub_def.h"
struct kmem_cache_order_objects {
   unsigned long x ;
};
# 71 "include/linux/slub_def.h"
struct kmem_cache {
   struct kmem_cache_cpu *cpu_slab ;
   unsigned long flags ;
   unsigned long min_partial ;
   int size ;
   int objsize ;
   int offset ;
   struct kmem_cache_order_objects oo ;
   struct kmem_cache_order_objects max ;
   struct kmem_cache_order_objects min ;
   gfp_t allocflags ;
   int refcount ;
   void (*ctor)(void * ) ;
   int inuse ;
   int align ;
   int reserved ;
   char const *name ;
   struct list_head list ;
   struct kobject kobj ;
   int remote_node_defrag_ratio ;
   struct kmem_cache_node *node[1 << 10] ;
};
# 94 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/uaccess.h"
struct exception_table_entry {
   unsigned long insn ;
   unsigned long fixup ;
};
# 12 "include/linux/mod_devicetable.h"
typedef unsigned long kernel_ulong_t;
# 98 "include/linux/mod_devicetable.h"
struct usb_device_id {
   __u16 match_flags ;
   __u16 idVendor ;
   __u16 idProduct ;
   __u16 bcdDevice_lo ;
   __u16 bcdDevice_hi ;
   __u8 bDeviceClass ;
   __u8 bDeviceSubClass ;
   __u8 bDeviceProtocol ;
   __u8 bInterfaceClass ;
   __u8 bInterfaceSubClass ;
   __u8 bInterfaceProtocol ;
   kernel_ulong_t driver_info ;
};
# 219 "include/linux/mod_devicetable.h"
struct of_device_id {
   char name[32] ;
   char type[32] ;
   char compatible[128] ;
   void *data ;
};
# 244 "include/linux/usb/ch9.h"
struct usb_device_descriptor {
   __u8 bLength ;
   __u8 bDescriptorType ;
   __le16 bcdUSB ;
   __u8 bDeviceClass ;
   __u8 bDeviceSubClass ;
   __u8 bDeviceProtocol ;
   __u8 bMaxPacketSize0 ;
   __le16 idVendor ;
   __le16 idProduct ;
   __le16 bcdDevice ;
   __u8 iManufacturer ;
   __u8 iProduct ;
   __u8 iSerialNumber ;
   __u8 bNumConfigurations ;
} __attribute__((__packed__)) ;
# 300 "include/linux/usb/ch9.h"
struct usb_config_descriptor {
   __u8 bLength ;
   __u8 bDescriptorType ;
   __le16 wTotalLength ;
   __u8 bNumInterfaces ;
   __u8 bConfigurationValue ;
   __u8 iConfiguration ;
   __u8 bmAttributes ;
   __u8 bMaxPower ;
} __attribute__((__packed__)) ;
# 337 "include/linux/usb/ch9.h"
struct usb_interface_descriptor {
   __u8 bLength ;
   __u8 bDescriptorType ;
   __u8 bInterfaceNumber ;
   __u8 bAlternateSetting ;
   __u8 bNumEndpoints ;
   __u8 bInterfaceClass ;
   __u8 bInterfaceSubClass ;
   __u8 bInterfaceProtocol ;
   __u8 iInterface ;
} __attribute__((__packed__)) ;
# 355 "include/linux/usb/ch9.h"
struct usb_endpoint_descriptor {
   __u8 bLength ;
   __u8 bDescriptorType ;
   __u8 bEndpointAddress ;
   __u8 bmAttributes ;
   __le16 wMaxPacketSize ;
   __u8 bInterval ;
   __u8 bRefresh ;
   __u8 bSynchAddress ;
} __attribute__((__packed__)) ;
# 576 "include/linux/usb/ch9.h"
struct usb_ss_ep_comp_descriptor {
   __u8 bLength ;
   __u8 bDescriptorType ;
   __u8 bMaxBurst ;
   __u8 bmAttributes ;
   __le16 wBytesPerInterval ;
} __attribute__((__packed__)) ;
# 637 "include/linux/usb/ch9.h"
struct usb_interface_assoc_descriptor {
   __u8 bLength ;
   __u8 bDescriptorType ;
   __u8 bFirstInterface ;
   __u8 bInterfaceCount ;
   __u8 bFunctionClass ;
   __u8 bFunctionSubClass ;
   __u8 bFunctionProtocol ;
   __u8 iFunction ;
} __attribute__((__packed__)) ;
# 846 "include/linux/usb/ch9.h"
enum usb_device_speed {
    USB_SPEED_UNKNOWN = 0,
    USB_SPEED_LOW = 1,
    USB_SPEED_FULL = 2,
    USB_SPEED_HIGH = 3,
    USB_SPEED_WIRELESS = 4,
    USB_SPEED_SUPER = 5
} ;
# 854 "include/linux/usb/ch9.h"
enum usb_device_state {
    USB_STATE_NOTATTACHED = 0,
    USB_STATE_ATTACHED = 1,
    USB_STATE_POWERED = 2,
    USB_STATE_RECONNECTING = 3,
    USB_STATE_UNAUTHENTICATED = 4,
    USB_STATE_DEFAULT = 5,
    USB_STATE_ADDRESS = 6,
    USB_STATE_CONFIGURED = 7,
    USB_STATE_SUSPENDED = 8
} ;
# 10 "include/linux/irqreturn.h"
enum irqreturn {
    IRQ_NONE = 0,
    IRQ_HANDLED = 1,
    IRQ_WAKE_THREAD = 2
} ;
# 16 "include/linux/irqreturn.h"
typedef enum irqreturn irqreturn_t;
# 31 "include/linux/irq.h"
struct seq_file;
# 12 "include/linux/irqdesc.h"
struct proc_dir_entry;
# 12 "include/linux/irqdesc.h"
struct proc_dir_entry;
# 12 "include/linux/irqdesc.h"
struct proc_dir_entry;
# 39 "include/linux/irqdesc.h"
struct irqaction;
# 39 "include/linux/irqdesc.h"
struct irqaction;
# 16 "include/linux/profile.h"
struct proc_dir_entry;
# 17 "include/linux/profile.h"
struct pt_regs;
# 65 "include/linux/profile.h"
struct task_struct;
# 66 "include/linux/profile.h"
struct mm_struct;
# 88 "include/linux/profile.h"
struct pt_regs;
# 363 "include/linux/irq.h"
struct irqaction;
# 132 "include/linux/hardirq.h"
struct task_struct;
# 100 "include/linux/rbtree.h"
struct rb_node {
   unsigned long rb_parent_color ;
   struct rb_node *rb_right ;
   struct rb_node *rb_left ;
} __attribute__((__aligned__(sizeof(long )))) ;
# 110 "include/linux/rbtree.h"
struct rb_root {
   struct rb_node *rb_node ;
};
# 8 "include/linux/timerqueue.h"
struct timerqueue_node {
   struct rb_node node ;
   ktime_t expires ;
};
# 13 "include/linux/timerqueue.h"
struct timerqueue_head {
   struct rb_root head ;
   struct timerqueue_node *next ;
};
# 27 "include/linux/hrtimer.h"
struct hrtimer_clock_base;
# 27 "include/linux/hrtimer.h"
struct hrtimer_clock_base;
# 27 "include/linux/hrtimer.h"
struct hrtimer_clock_base;
# 28 "include/linux/hrtimer.h"
struct hrtimer_cpu_base;
# 28 "include/linux/hrtimer.h"
struct hrtimer_cpu_base;
# 28 "include/linux/hrtimer.h"
struct hrtimer_cpu_base;
# 44 "include/linux/hrtimer.h"
enum hrtimer_restart {
    HRTIMER_NORESTART = 0,
    HRTIMER_RESTART = 1
} ;
# 108 "include/linux/hrtimer.h"
struct hrtimer {
   struct timerqueue_node node ;
   ktime_t _softexpires ;
   enum hrtimer_restart (*function)(struct hrtimer * ) ;
   struct hrtimer_clock_base *base ;
   unsigned long state ;
   int start_pid ;
   void *start_site ;
   char start_comm[16] ;
};
# 145 "include/linux/hrtimer.h"
struct hrtimer_clock_base {
   struct hrtimer_cpu_base *cpu_base ;
   int index ;
   clockid_t clockid ;
   struct timerqueue_head active ;
   ktime_t resolution ;
   ktime_t (*get_time)(void) ;
   ktime_t softirq_time ;
   ktime_t offset ;
};
# 178 "include/linux/hrtimer.h"
struct hrtimer_cpu_base {
   raw_spinlock_t lock ;
   unsigned long active_bases ;
   ktime_t expires_next ;
   int hres_active ;
   int hang_detected ;
   unsigned long nr_events ;
   unsigned long nr_retries ;
   unsigned long nr_hangs ;
   ktime_t max_hang_time ;
   struct hrtimer_clock_base clock_base[3] ;
};
# 9 "include/trace/events/irq.h"
struct irqaction;
# 106 "include/linux/interrupt.h"
struct irqaction {
   irqreturn_t (*handler)(int , void * ) ;
   unsigned long flags ;
   void *dev_id ;
   struct irqaction *next ;
   int irq ;
   irqreturn_t (*thread_fn)(int , void * ) ;
   struct task_struct *thread ;
   unsigned long thread_flags ;
   unsigned long thread_mask ;
   char const *name ;
   struct proc_dir_entry *dir ;
} __attribute__((__aligned__((1) << (12) ))) ;
# 172 "include/linux/interrupt.h"
struct device;
# 682 "include/linux/interrupt.h"
struct seq_file;
# 19 "include/linux/klist.h"
struct klist_node;
# 19 "include/linux/klist.h"
struct klist_node;
# 19 "include/linux/klist.h"
struct klist_node;
# 39 "include/linux/klist.h"
struct klist_node {
   void *n_klist ;
   struct list_head n_node ;
   struct kref n_ref ;
};
# 4 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/device.h"
struct dma_map_ops;
# 4 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/device.h"
struct dma_map_ops;
# 4 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/device.h"
struct dev_archdata {
   void *acpi_handle ;
   struct dma_map_ops *dma_ops ;
   void *iommu ;
};
# 28 "include/linux/device.h"
struct device;
# 29 "include/linux/device.h"
struct device_private;
# 29 "include/linux/device.h"
struct device_private;
# 29 "include/linux/device.h"
struct device_private;
# 30 "include/linux/device.h"
struct device_driver;
# 30 "include/linux/device.h"
struct device_driver;
# 30 "include/linux/device.h"
struct device_driver;
# 31 "include/linux/device.h"
struct driver_private;
# 31 "include/linux/device.h"
struct driver_private;
# 31 "include/linux/device.h"
struct driver_private;
# 32 "include/linux/device.h"
struct class;
# 32 "include/linux/device.h"
struct class;
# 32 "include/linux/device.h"
struct class;
# 33 "include/linux/device.h"
struct subsys_private;
# 33 "include/linux/device.h"
struct subsys_private;
# 33 "include/linux/device.h"
struct subsys_private;
# 34 "include/linux/device.h"
struct bus_type;
# 34 "include/linux/device.h"
struct bus_type;
# 34 "include/linux/device.h"
struct bus_type;
# 35 "include/linux/device.h"
struct device_node;
# 35 "include/linux/device.h"
struct device_node;
# 35 "include/linux/device.h"
struct device_node;
# 37 "include/linux/device.h"
struct bus_attribute {
   struct attribute attr ;
   ssize_t (*show)(struct bus_type *bus , char *buf ) ;
   ssize_t (*store)(struct bus_type *bus , char const *buf , size_t count ) ;
};
# 82 "include/linux/device.h"
struct device_attribute;
# 82 "include/linux/device.h"
struct device_attribute;
# 82 "include/linux/device.h"
struct driver_attribute;
# 82 "include/linux/device.h"
struct driver_attribute;
# 82 "include/linux/device.h"
struct bus_type {
   char const *name ;
   struct bus_attribute *bus_attrs ;
   struct device_attribute *dev_attrs ;
   struct driver_attribute *drv_attrs ;
   int (*match)(struct device *dev , struct device_driver *drv ) ;
   int (*uevent)(struct device *dev , struct kobj_uevent_env *env ) ;
   int (*probe)(struct device *dev ) ;
   int (*remove)(struct device *dev ) ;
   void (*shutdown)(struct device *dev ) ;
   int (*suspend)(struct device *dev , pm_message_t state ) ;
   int (*resume)(struct device *dev ) ;
   struct dev_pm_ops const *pm ;
   struct subsys_private *p ;
};
# 185 "include/linux/device.h"
struct device_driver {
   char const *name ;
   struct bus_type *bus ;
   struct module *owner ;
   char const *mod_name ;
   bool suppress_bind_attrs ;
   struct of_device_id const *of_match_table ;
   int (*probe)(struct device *dev ) ;
   int (*remove)(struct device *dev ) ;
   void (*shutdown)(struct device *dev ) ;
   int (*suspend)(struct device *dev , pm_message_t state ) ;
   int (*resume)(struct device *dev ) ;
   struct attribute_group const **groups ;
   struct dev_pm_ops const *pm ;
   struct driver_private *p ;
};
# 222 "include/linux/device.h"
struct driver_attribute {
   struct attribute attr ;
   ssize_t (*show)(struct device_driver *driver , char *buf ) ;
   ssize_t (*store)(struct device_driver *driver , char const *buf , size_t count ) ;
};
# 280 "include/linux/device.h"
struct class_attribute;
# 280 "include/linux/device.h"
struct class_attribute;
# 280 "include/linux/device.h"
struct class {
   char const *name ;
   struct module *owner ;
   struct class_attribute *class_attrs ;
   struct device_attribute *dev_attrs ;
   struct bin_attribute *dev_bin_attrs ;
   struct kobject *dev_kobj ;
   int (*dev_uevent)(struct device *dev , struct kobj_uevent_env *env ) ;
   char *(*devnode)(struct device *dev , mode_t *mode ) ;
   void (*class_release)(struct class *class ) ;
   void (*dev_release)(struct device *dev ) ;
   int (*suspend)(struct device *dev , pm_message_t state ) ;
   int (*resume)(struct device *dev ) ;
   struct kobj_ns_type_operations const *ns_type ;
   void const *(*namespace)(struct device *dev ) ;
   struct dev_pm_ops const *pm ;
   struct subsys_private *p ;
};
# 306 "include/linux/device.h"
struct device_type;
# 306 "include/linux/device.h"
struct device_type;
# 347 "include/linux/device.h"
struct class_attribute {
   struct attribute attr ;
   ssize_t (*show)(struct class *class , struct class_attribute *attr , char *buf ) ;
   ssize_t (*store)(struct class *class , struct class_attribute *attr , char const *buf ,
                    size_t count ) ;
};
# 413 "include/linux/device.h"
struct device_type {
   char const *name ;
   struct attribute_group const **groups ;
   int (*uevent)(struct device *dev , struct kobj_uevent_env *env ) ;
   char *(*devnode)(struct device *dev , mode_t *mode ) ;
   void (*release)(struct device *dev ) ;
   struct dev_pm_ops const *pm ;
};
# 424 "include/linux/device.h"
struct device_attribute {
   struct attribute attr ;
   ssize_t (*show)(struct device *dev , struct device_attribute *attr , char *buf ) ;
   ssize_t (*store)(struct device *dev , struct device_attribute *attr , char const *buf ,
                    size_t count ) ;
};
# 484 "include/linux/device.h"
struct device_dma_parameters {
   unsigned int max_segment_size ;
   unsigned long segment_boundary_mask ;
};
# 551 "include/linux/device.h"
struct dma_coherent_mem;
# 551 "include/linux/device.h"
struct dma_coherent_mem;
# 551 "include/linux/device.h"
struct device {
   struct device *parent ;
   struct device_private *p ;
   struct kobject kobj ;
   char const *init_name ;
   struct device_type const *type ;
   struct mutex mutex ;
   struct bus_type *bus ;
   struct device_driver *driver ;
   void *platform_data ;
   struct dev_pm_info power ;
   struct dev_power_domain *pwr_domain ;
   int numa_node ;
   u64 *dma_mask ;
   u64 coherent_dma_mask ;
   struct device_dma_parameters *dma_parms ;
   struct list_head dma_pools ;
   struct dma_coherent_mem *dma_mem ;
   struct dev_archdata archdata ;
   struct device_node *of_node ;
   dev_t devt ;
   spinlock_t devres_lock ;
   struct list_head devres_head ;
   struct klist_node knode_class ;
   struct class *class ;
   struct attribute_group const **groups ;
   void (*release)(struct device *dev ) ;
};
# 43 "include/linux/pm_wakeup.h"
struct wakeup_source {
   char *name ;
   struct list_head entry ;
   spinlock_t lock ;
   struct timer_list timer ;
   unsigned long timer_expires ;
   ktime_t total_time ;
   ktime_t max_time ;
   ktime_t last_time ;
   unsigned long event_count ;
   unsigned long active_count ;
   unsigned long relax_count ;
   unsigned long hit_count ;
   unsigned int active : 1 ;
};
# 15 "include/linux/blk_types.h"
struct page;
# 16 "include/linux/blk_types.h"
struct block_device;
# 16 "include/linux/blk_types.h"
struct block_device;
# 16 "include/linux/blk_types.h"
struct block_device;
# 33 "include/linux/list_bl.h"
struct hlist_bl_node;
# 33 "include/linux/list_bl.h"
struct hlist_bl_node;
# 33 "include/linux/list_bl.h"
struct hlist_bl_head {
   struct hlist_bl_node *first ;
};
# 37 "include/linux/list_bl.h"
struct hlist_bl_node {
   struct hlist_bl_node *next ;
   struct hlist_bl_node **pprev ;
};
# 13 "include/linux/dcache.h"
struct nameidata;
# 13 "include/linux/dcache.h"
struct nameidata;
# 13 "include/linux/dcache.h"
struct nameidata;
# 14 "include/linux/dcache.h"
struct path;
# 14 "include/linux/dcache.h"
struct path;
# 14 "include/linux/dcache.h"
struct path;
# 15 "include/linux/dcache.h"
struct vfsmount;
# 15 "include/linux/dcache.h"
struct vfsmount;
# 15 "include/linux/dcache.h"
struct vfsmount;
# 35 "include/linux/dcache.h"
struct qstr {
   unsigned int hash ;
   unsigned int len ;
   unsigned char const *name ;
};
# 116 "include/linux/dcache.h"
struct inode;
# 116 "include/linux/dcache.h"
struct inode;
# 116 "include/linux/dcache.h"
struct dentry_operations;
# 116 "include/linux/dcache.h"
struct dentry_operations;
# 116 "include/linux/dcache.h"
struct super_block;
# 116 "include/linux/dcache.h"
struct super_block;
# 116 "include/linux/dcache.h"
union __anonunion_d_u_206 {
   struct list_head d_child ;
   struct rcu_head d_rcu ;
};
# 116 "include/linux/dcache.h"
struct dentry {
   unsigned int d_flags ;
   seqcount_t d_seq ;
   struct hlist_bl_node d_hash ;
   struct dentry *d_parent ;
   struct qstr d_name ;
   struct inode *d_inode ;
   unsigned char d_iname[32] ;
   unsigned int d_count ;
   spinlock_t d_lock ;
   struct dentry_operations const *d_op ;
   struct super_block *d_sb ;
   unsigned long d_time ;
   void *d_fsdata ;
   struct list_head d_lru ;
   union __anonunion_d_u_206 d_u ;
   struct list_head d_subdirs ;
   struct list_head d_alias ;
};
# 159 "include/linux/dcache.h"
struct dentry_operations {
   int (*d_revalidate)(struct dentry * , struct nameidata * ) ;
   int (*d_hash)(struct dentry const * , struct inode const * , struct qstr * ) ;
   int (*d_compare)(struct dentry const * , struct inode const * , struct dentry const * ,
                    struct inode const * , unsigned int , char const * , struct qstr const * ) ;
   int (*d_delete)(struct dentry const * ) ;
   void (*d_release)(struct dentry * ) ;
   void (*d_iput)(struct dentry * , struct inode * ) ;
   char *(*d_dname)(struct dentry * , char * , int ) ;
   struct vfsmount *(*d_automount)(struct path * ) ;
   int (*d_manage)(struct dentry * , bool ) ;
} __attribute__((__aligned__((1) << (6) ))) ;
# 4 "include/linux/path.h"
struct dentry;
# 5 "include/linux/path.h"
struct vfsmount;
# 7 "include/linux/path.h"
struct path {
   struct vfsmount *mnt ;
   struct dentry *dentry ;
};
# 57 "include/linux/radix-tree.h"
struct radix_tree_node;
# 57 "include/linux/radix-tree.h"
struct radix_tree_node;
# 57 "include/linux/radix-tree.h"
struct radix_tree_root {
   unsigned int height ;
   gfp_t gfp_mask ;
   struct radix_tree_node *rnode ;
};
# 14 "include/linux/prio_tree.h"
struct prio_tree_node;
# 14 "include/linux/prio_tree.h"
struct prio_tree_node;
# 14 "include/linux/prio_tree.h"
struct raw_prio_tree_node {
   struct prio_tree_node *left ;
   struct prio_tree_node *right ;
   struct prio_tree_node *parent ;
};
# 20 "include/linux/prio_tree.h"
struct prio_tree_node {
   struct prio_tree_node *left ;
   struct prio_tree_node *right ;
   struct prio_tree_node *parent ;
   unsigned long start ;
   unsigned long last ;
};
# 28 "include/linux/prio_tree.h"
struct prio_tree_root {
   struct prio_tree_node *prio_tree_node ;
   unsigned short index_bits ;
   unsigned short raw ;
};
# 6 "include/linux/pid.h"
enum pid_type {
    PIDTYPE_PID = 0,
    PIDTYPE_PGID = 1,
    PIDTYPE_SID = 2,
    PIDTYPE_MAX = 3
} ;
# 50 "include/linux/pid.h"
struct pid_namespace;
# 50 "include/linux/pid.h"
struct pid_namespace;
# 50 "include/linux/pid.h"
struct upid {
   int nr ;
   struct pid_namespace *ns ;
   struct hlist_node pid_chain ;
};
# 57 "include/linux/pid.h"
struct pid {
   atomic_t count ;
   unsigned int level ;
   struct hlist_head tasks[3] ;
   struct rcu_head rcu ;
   struct upid numbers[1] ;
};
# 69 "include/linux/pid.h"
struct pid_link {
   struct hlist_node node ;
   struct pid *pid ;
};
# 100 "include/linux/pid.h"
struct pid_namespace;
# 18 "include/linux/capability.h"
struct task_struct;
# 94 "include/linux/capability.h"
struct kernel_cap_struct {
   __u32 cap[2] ;
};
# 94 "include/linux/capability.h"
typedef struct kernel_cap_struct kernel_cap_t;
# 376 "include/linux/capability.h"
struct dentry;
# 377 "include/linux/capability.h"
struct user_namespace;
# 377 "include/linux/capability.h"
struct user_namespace;
# 377 "include/linux/capability.h"
struct user_namespace;
# 16 "include/linux/fiemap.h"
struct fiemap_extent {
   __u64 fe_logical ;
   __u64 fe_physical ;
   __u64 fe_length ;
   __u64 fe_reserved64[2] ;
   __u32 fe_flags ;
   __u32 fe_reserved[3] ;
};
# 399 "include/linux/fs.h"
struct export_operations;
# 399 "include/linux/fs.h"
struct export_operations;
# 399 "include/linux/fs.h"
struct export_operations;
# 401 "include/linux/fs.h"
struct iovec;
# 401 "include/linux/fs.h"
struct iovec;
# 401 "include/linux/fs.h"
struct iovec;
# 402 "include/linux/fs.h"
struct nameidata;
# 403 "include/linux/fs.h"
struct kiocb;
# 403 "include/linux/fs.h"
struct kiocb;
# 403 "include/linux/fs.h"
struct kiocb;
# 404 "include/linux/fs.h"
struct kobject;
# 405 "include/linux/fs.h"
struct pipe_inode_info;
# 405 "include/linux/fs.h"
struct pipe_inode_info;
# 405 "include/linux/fs.h"
struct pipe_inode_info;
# 406 "include/linux/fs.h"
struct poll_table_struct;
# 406 "include/linux/fs.h"
struct poll_table_struct;
# 406 "include/linux/fs.h"
struct poll_table_struct;
# 407 "include/linux/fs.h"
struct kstatfs;
# 407 "include/linux/fs.h"
struct kstatfs;
# 407 "include/linux/fs.h"
struct kstatfs;
# 408 "include/linux/fs.h"
struct vm_area_struct;
# 409 "include/linux/fs.h"
struct vfsmount;
# 410 "include/linux/fs.h"
struct cred;
# 460 "include/linux/fs.h"
struct iattr {
   unsigned int ia_valid ;
   umode_t ia_mode ;
   uid_t ia_uid ;
   gid_t ia_gid ;
   loff_t ia_size ;
   struct timespec ia_atime ;
   struct timespec ia_mtime ;
   struct timespec ia_ctime ;
   struct file *ia_file ;
};
# 129 "include/linux/quota.h"
struct if_dqinfo {
   __u64 dqi_bgrace ;
   __u64 dqi_igrace ;
   __u32 dqi_flags ;
   __u32 dqi_valid ;
};
# 50 "include/linux/dqblk_xfs.h"
struct fs_disk_quota {
   __s8 d_version ;
   __s8 d_flags ;
   __u16 d_fieldmask ;
   __u32 d_id ;
   __u64 d_blk_hardlimit ;
   __u64 d_blk_softlimit ;
   __u64 d_ino_hardlimit ;
   __u64 d_ino_softlimit ;
   __u64 d_bcount ;
   __u64 d_icount ;
   __s32 d_itimer ;
   __s32 d_btimer ;
   __u16 d_iwarns ;
   __u16 d_bwarns ;
   __s32 d_padding2 ;
   __u64 d_rtb_hardlimit ;
   __u64 d_rtb_softlimit ;
   __u64 d_rtbcount ;
   __s32 d_rtbtimer ;
   __u16 d_rtbwarns ;
   __s16 d_padding3 ;
   char d_padding4[8] ;
};
# 146 "include/linux/dqblk_xfs.h"
struct fs_qfilestat {
   __u64 qfs_ino ;
   __u64 qfs_nblks ;
   __u32 qfs_nextents ;
};
# 146 "include/linux/dqblk_xfs.h"
typedef struct fs_qfilestat fs_qfilestat_t;
# 152 "include/linux/dqblk_xfs.h"
struct fs_quota_stat {
   __s8 qs_version ;
   __u16 qs_flags ;
   __s8 qs_pad ;
   fs_qfilestat_t qs_uquota ;
   fs_qfilestat_t qs_gquota ;
   __u32 qs_incoredqs ;
   __s32 qs_btimelimit ;
   __s32 qs_itimelimit ;
   __s32 qs_rtbtimelimit ;
   __u16 qs_bwarnlimit ;
   __u16 qs_iwarnlimit ;
};
# 17 "include/linux/dqblk_qtree.h"
struct dquot;
# 17 "include/linux/dqblk_qtree.h"
struct dquot;
# 17 "include/linux/dqblk_qtree.h"
struct dquot;
# 185 "include/linux/quota.h"
typedef __kernel_uid32_t qid_t;
# 186 "include/linux/quota.h"
typedef long long qsize_t;
# 200 "include/linux/quota.h"
struct mem_dqblk {
   qsize_t dqb_bhardlimit ;
   qsize_t dqb_bsoftlimit ;
   qsize_t dqb_curspace ;
   qsize_t dqb_rsvspace ;
   qsize_t dqb_ihardlimit ;
   qsize_t dqb_isoftlimit ;
   qsize_t dqb_curinodes ;
   time_t dqb_btime ;
   time_t dqb_itime ;
};
# 215 "include/linux/quota.h"
struct quota_format_type;
# 215 "include/linux/quota.h"
struct quota_format_type;
# 215 "include/linux/quota.h"
struct quota_format_type;
# 217 "include/linux/quota.h"
struct mem_dqinfo {
   struct quota_format_type *dqi_format ;
   int dqi_fmt_id ;
   struct list_head dqi_dirty_list ;
   unsigned long dqi_flags ;
   unsigned int dqi_bgrace ;
   unsigned int dqi_igrace ;
   qsize_t dqi_maxblimit ;
   qsize_t dqi_maxilimit ;
   void *dqi_priv ;
};
# 230 "include/linux/quota.h"
struct super_block;
# 284 "include/linux/quota.h"
struct dquot {
   struct hlist_node dq_hash ;
   struct list_head dq_inuse ;
   struct list_head dq_free ;
   struct list_head dq_dirty ;
   struct mutex dq_lock ;
   atomic_t dq_count ;
   wait_queue_head_t dq_wait_unused ;
   struct super_block *dq_sb ;
   unsigned int dq_id ;
   loff_t dq_off ;
   unsigned long dq_flags ;
   short dq_type ;
   struct mem_dqblk dq_dqb ;
};
# 301 "include/linux/quota.h"
struct quota_format_ops {
   int (*check_quota_file)(struct super_block *sb , int type ) ;
   int (*read_file_info)(struct super_block *sb , int type ) ;
   int (*write_file_info)(struct super_block *sb , int type ) ;
   int (*free_file_info)(struct super_block *sb , int type ) ;
   int (*read_dqblk)(struct dquot *dquot ) ;
   int (*commit_dqblk)(struct dquot *dquot ) ;
   int (*release_dqblk)(struct dquot *dquot ) ;
};
# 312 "include/linux/quota.h"
struct dquot_operations {
   int (*write_dquot)(struct dquot * ) ;
   struct dquot *(*alloc_dquot)(struct super_block * , int ) ;
   void (*destroy_dquot)(struct dquot * ) ;
   int (*acquire_dquot)(struct dquot * ) ;
   int (*release_dquot)(struct dquot * ) ;
   int (*mark_dirty)(struct dquot * ) ;
   int (*write_info)(struct super_block * , int ) ;
   qsize_t *(*get_reserved_space)(struct inode * ) ;
};
# 325 "include/linux/quota.h"
struct path;
# 328 "include/linux/quota.h"
struct quotactl_ops {
   int (*quota_on)(struct super_block * , int , int , struct path * ) ;
   int (*quota_on_meta)(struct super_block * , int , int ) ;
   int (*quota_off)(struct super_block * , int ) ;
   int (*quota_sync)(struct super_block * , int , int ) ;
   int (*get_info)(struct super_block * , int , struct if_dqinfo * ) ;
   int (*set_info)(struct super_block * , int , struct if_dqinfo * ) ;
   int (*get_dqblk)(struct super_block * , int , qid_t , struct fs_disk_quota * ) ;
   int (*set_dqblk)(struct super_block * , int , qid_t , struct fs_disk_quota * ) ;
   int (*get_xstate)(struct super_block * , struct fs_quota_stat * ) ;
   int (*set_xstate)(struct super_block * , unsigned int , int ) ;
};
# 341 "include/linux/quota.h"
struct quota_format_type {
   int qf_fmt_id ;
   struct quota_format_ops const *qf_ops ;
   struct module *qf_owner ;
   struct quota_format_type *qf_next ;
};
# 395 "include/linux/quota.h"
struct quota_info {
   unsigned int flags ;
   struct mutex dqio_mutex ;
   struct mutex dqonoff_mutex ;
   struct rw_semaphore dqptr_sem ;
   struct inode *files[2] ;
   struct mem_dqinfo info[2] ;
   struct quota_format_ops const *ops[2] ;
};
# 523 "include/linux/fs.h"
struct page;
# 524 "include/linux/fs.h"
struct address_space;
# 524 "include/linux/fs.h"
struct address_space;
# 524 "include/linux/fs.h"
struct address_space;
# 525 "include/linux/fs.h"
struct writeback_control;
# 525 "include/linux/fs.h"
struct writeback_control;
# 525 "include/linux/fs.h"
struct writeback_control;
# 568 "include/linux/fs.h"
union __anonunion_arg_214 {
   char *buf ;
   void *data ;
};
# 568 "include/linux/fs.h"
struct __anonstruct_read_descriptor_t_213 {
   size_t written ;
   size_t count ;
   union __anonunion_arg_214 arg ;
   int error ;
};
# 568 "include/linux/fs.h"
typedef struct __anonstruct_read_descriptor_t_213 read_descriptor_t;
# 581 "include/linux/fs.h"
struct address_space_operations {
   int (*writepage)(struct page *page , struct writeback_control *wbc ) ;
   int (*readpage)(struct file * , struct page * ) ;
   int (*writepages)(struct address_space * , struct writeback_control * ) ;
   int (*set_page_dirty)(struct page *page ) ;
   int (*readpages)(struct file *filp , struct address_space *mapping , struct list_head *pages ,
                    unsigned int nr_pages ) ;
   int (*write_begin)(struct file * , struct address_space *mapping , loff_t pos ,
                      unsigned int len , unsigned int flags , struct page **pagep ,
                      void **fsdata ) ;
   int (*write_end)(struct file * , struct address_space *mapping , loff_t pos , unsigned int len ,
                    unsigned int copied , struct page *page , void *fsdata ) ;
   sector_t (*bmap)(struct address_space * , sector_t ) ;
   void (*invalidatepage)(struct page * , unsigned long ) ;
   int (*releasepage)(struct page * , gfp_t ) ;
   void (*freepage)(struct page * ) ;
   ssize_t (*direct_IO)(int , struct kiocb * , struct iovec const *iov , loff_t offset ,
                        unsigned long nr_segs ) ;
   int (*get_xip_mem)(struct address_space * , unsigned long , int , void ** , unsigned long * ) ;
   int (*migratepage)(struct address_space * , struct page * , struct page * ) ;
   int (*launder_page)(struct page * ) ;
   int (*is_partially_uptodate)(struct page * , read_descriptor_t * , unsigned long ) ;
   int (*error_remove_page)(struct address_space * , struct page * ) ;
};
# 633 "include/linux/fs.h"
struct backing_dev_info;
# 633 "include/linux/fs.h"
struct backing_dev_info;
# 633 "include/linux/fs.h"
struct backing_dev_info;
# 634 "include/linux/fs.h"
struct address_space {
   struct inode *host ;
   struct radix_tree_root page_tree ;
   spinlock_t tree_lock ;
   unsigned int i_mmap_writable ;
   struct prio_tree_root i_mmap ;
   struct list_head i_mmap_nonlinear ;
   struct mutex i_mmap_mutex ;
   unsigned long nrpages ;
   unsigned long writeback_index ;
   struct address_space_operations const *a_ops ;
   unsigned long flags ;
   struct backing_dev_info *backing_dev_info ;
   spinlock_t private_lock ;
   struct list_head private_list ;
   struct address_space *assoc_mapping ;
} __attribute__((__aligned__(sizeof(long )))) ;
# 658 "include/linux/fs.h"
struct hd_struct;
# 658 "include/linux/fs.h"
struct hd_struct;
# 658 "include/linux/fs.h"
struct gendisk;
# 658 "include/linux/fs.h"
struct gendisk;
# 658 "include/linux/fs.h"
struct block_device {
   dev_t bd_dev ;
   int bd_openers ;
   struct inode *bd_inode ;
   struct super_block *bd_super ;
   struct mutex bd_mutex ;
   struct list_head bd_inodes ;
   void *bd_claiming ;
   void *bd_holder ;
   int bd_holders ;
   bool bd_write_holder ;
   struct list_head bd_holder_disks ;
   struct block_device *bd_contains ;
   unsigned int bd_block_size ;
   struct hd_struct *bd_part ;
   unsigned int bd_part_count ;
   int bd_invalidated ;
   struct gendisk *bd_disk ;
   struct list_head bd_list ;
   unsigned long bd_private ;
   int bd_fsfreeze_count ;
   struct mutex bd_fsfreeze_mutex ;
};
# 735 "include/linux/fs.h"
struct posix_acl;
# 735 "include/linux/fs.h"
struct posix_acl;
# 735 "include/linux/fs.h"
struct posix_acl;
# 738 "include/linux/fs.h"
struct inode_operations;
# 738 "include/linux/fs.h"
struct inode_operations;
# 738 "include/linux/fs.h"
union __anonunion____missing_field_name_215 {
   struct list_head i_dentry ;
   struct rcu_head i_rcu ;
};
# 738 "include/linux/fs.h"
struct file_operations;
# 738 "include/linux/fs.h"
struct file_operations;
# 738 "include/linux/fs.h"
struct file_lock;
# 738 "include/linux/fs.h"
struct file_lock;
# 738 "include/linux/fs.h"
struct cdev;
# 738 "include/linux/fs.h"
struct cdev;
# 738 "include/linux/fs.h"
union __anonunion____missing_field_name_216 {
   struct pipe_inode_info *i_pipe ;
   struct block_device *i_bdev ;
   struct cdev *i_cdev ;
};
# 738 "include/linux/fs.h"
struct inode {
   umode_t i_mode ;
   uid_t i_uid ;
   gid_t i_gid ;
   struct inode_operations const *i_op ;
   struct super_block *i_sb ;
   spinlock_t i_lock ;
   unsigned int i_flags ;
   unsigned long i_state ;
   void *i_security ;
   struct mutex i_mutex ;
   unsigned long dirtied_when ;
   struct hlist_node i_hash ;
   struct list_head i_wb_list ;
   struct list_head i_lru ;
   struct list_head i_sb_list ;
   union __anonunion____missing_field_name_215 __annonCompField32 ;
   unsigned long i_ino ;
   atomic_t i_count ;
   unsigned int i_nlink ;
   dev_t i_rdev ;
   unsigned int i_blkbits ;
   u64 i_version ;
   loff_t i_size ;
   struct timespec i_atime ;
   struct timespec i_mtime ;
   struct timespec i_ctime ;
   blkcnt_t i_blocks ;
   unsigned short i_bytes ;
   struct rw_semaphore i_alloc_sem ;
   struct file_operations const *i_fop ;
   struct file_lock *i_flock ;
   struct address_space *i_mapping ;
   struct address_space i_data ;
   struct dquot *i_dquot[2] ;
   struct list_head i_devices ;
   union __anonunion____missing_field_name_216 __annonCompField33 ;
   __u32 i_generation ;
   __u32 i_fsnotify_mask ;
   struct hlist_head i_fsnotify_marks ;
   atomic_t i_readcount ;
   atomic_t i_writecount ;
   struct posix_acl *i_acl ;
   struct posix_acl *i_default_acl ;
   void *i_private ;
};
# 903 "include/linux/fs.h"
struct fown_struct {
   rwlock_t lock ;
   struct pid *pid ;
   enum pid_type pid_type ;
   uid_t uid ;
   uid_t euid ;
   int signum ;
};
# 914 "include/linux/fs.h"
struct file_ra_state {
   unsigned long start ;
   unsigned int size ;
   unsigned int async_size ;
   unsigned int ra_pages ;
   unsigned int mmap_miss ;
   loff_t prev_pos ;
};
# 937 "include/linux/fs.h"
union __anonunion_f_u_217 {
   struct list_head fu_list ;
   struct rcu_head fu_rcuhead ;
};
# 937 "include/linux/fs.h"
struct file {
   union __anonunion_f_u_217 f_u ;
   struct path f_path ;
   struct file_operations const *f_op ;
   spinlock_t f_lock ;
   int f_sb_list_cpu ;
   atomic_long_t f_count ;
   unsigned int f_flags ;
   fmode_t f_mode ;
   loff_t f_pos ;
   struct fown_struct f_owner ;
   struct cred const *f_cred ;
   struct file_ra_state f_ra ;
   u64 f_version ;
   void *f_security ;
   void *private_data ;
   struct list_head f_ep_links ;
   struct address_space *f_mapping ;
   unsigned long f_mnt_write_state ;
};
# 1064 "include/linux/fs.h"
struct files_struct;
# 1064 "include/linux/fs.h"
struct files_struct;
# 1064 "include/linux/fs.h"
typedef struct files_struct *fl_owner_t;
# 1066 "include/linux/fs.h"
struct file_lock_operations {
   void (*fl_copy_lock)(struct file_lock * , struct file_lock * ) ;
   void (*fl_release_private)(struct file_lock * ) ;
};
# 1071 "include/linux/fs.h"
struct lock_manager_operations {
   int (*fl_compare_owner)(struct file_lock * , struct file_lock * ) ;
   void (*fl_notify)(struct file_lock * ) ;
   int (*fl_grant)(struct file_lock * , struct file_lock * , int ) ;
   void (*fl_release_private)(struct file_lock * ) ;
   void (*fl_break)(struct file_lock * ) ;
   int (*fl_change)(struct file_lock ** , int ) ;
};
# 8 "include/linux/nfs_fs_i.h"
struct nlm_lockowner;
# 8 "include/linux/nfs_fs_i.h"
struct nlm_lockowner;
# 8 "include/linux/nfs_fs_i.h"
struct nlm_lockowner;
# 13 "include/linux/nfs_fs_i.h"
struct nfs_lock_info {
   u32 state ;
   struct nlm_lockowner *owner ;
   struct list_head list ;
};
# 19 "include/linux/nfs_fs_i.h"
struct nfs4_lock_state;
# 19 "include/linux/nfs_fs_i.h"
struct nfs4_lock_state;
# 19 "include/linux/nfs_fs_i.h"
struct nfs4_lock_state;
# 20 "include/linux/nfs_fs_i.h"
struct nfs4_lock_info {
   struct nfs4_lock_state *owner ;
};
# 1091 "include/linux/fs.h"
struct fasync_struct;
# 1091 "include/linux/fs.h"
struct fasync_struct;
# 1091 "include/linux/fs.h"
struct __anonstruct_afs_219 {
   struct list_head link ;
   int state ;
};
# 1091 "include/linux/fs.h"
union __anonunion_fl_u_218 {
   struct nfs_lock_info nfs_fl ;
   struct nfs4_lock_info nfs4_fl ;
   struct __anonstruct_afs_219 afs ;
};
# 1091 "include/linux/fs.h"
struct file_lock {
   struct file_lock *fl_next ;
   struct list_head fl_link ;
   struct list_head fl_block ;
   fl_owner_t fl_owner ;
   unsigned char fl_flags ;
   unsigned char fl_type ;
   unsigned int fl_pid ;
   struct pid *fl_nspid ;
   wait_queue_head_t fl_wait ;
   struct file *fl_file ;
   loff_t fl_start ;
   loff_t fl_end ;
   struct fasync_struct *fl_fasync ;
   unsigned long fl_break_time ;
   struct file_lock_operations const *fl_ops ;
   struct lock_manager_operations const *fl_lmops ;
   union __anonunion_fl_u_218 fl_u ;
};
# 1324 "include/linux/fs.h"
struct fasync_struct {
   spinlock_t fa_lock ;
   int magic ;
   int fa_fd ;
   struct fasync_struct *fa_next ;
   struct file *fa_file ;
   struct rcu_head fa_rcu ;
};
# 1364 "include/linux/fs.h"
struct file_system_type;
# 1364 "include/linux/fs.h"
struct file_system_type;
# 1364 "include/linux/fs.h"
struct super_operations;
# 1364 "include/linux/fs.h"
struct super_operations;
# 1364 "include/linux/fs.h"
struct xattr_handler;
# 1364 "include/linux/fs.h"
struct xattr_handler;
# 1364 "include/linux/fs.h"
struct mtd_info;
# 1364 "include/linux/fs.h"
struct mtd_info;
# 1364 "include/linux/fs.h"
struct super_block {
   struct list_head s_list ;
   dev_t s_dev ;
   unsigned char s_dirt ;
   unsigned char s_blocksize_bits ;
   unsigned long s_blocksize ;
   loff_t s_maxbytes ;
   struct file_system_type *s_type ;
   struct super_operations const *s_op ;
   struct dquot_operations const *dq_op ;
   struct quotactl_ops const *s_qcop ;
   struct export_operations const *s_export_op ;
   unsigned long s_flags ;
   unsigned long s_magic ;
   struct dentry *s_root ;
   struct rw_semaphore s_umount ;
   struct mutex s_lock ;
   int s_count ;
   atomic_t s_active ;
   void *s_security ;
   struct xattr_handler const **s_xattr ;
   struct list_head s_inodes ;
   struct hlist_bl_head s_anon ;
   struct list_head *s_files ;
   struct list_head s_dentry_lru ;
   int s_nr_dentry_unused ;
   struct block_device *s_bdev ;
   struct backing_dev_info *s_bdi ;
   struct mtd_info *s_mtd ;
   struct list_head s_instances ;
   struct quota_info s_dquot ;
   int s_frozen ;
   wait_queue_head_t s_wait_unfrozen ;
   char s_id[32] ;
   u8 s_uuid[16] ;
   void *s_fs_info ;
   fmode_t s_mode ;
   u32 s_time_gran ;
   struct mutex s_vfs_rename_mutex ;
   char *s_subtype ;
   char *s_options ;
   struct dentry_operations const *s_d_op ;
   int cleancache_poolid ;
};
# 1499 "include/linux/fs.h"
struct fiemap_extent_info {
   unsigned int fi_flags ;
   unsigned int fi_extents_mapped ;
   unsigned int fi_extents_max ;
   struct fiemap_extent *fi_extents_start ;
};
# 1546 "include/linux/fs.h"
struct file_operations {
   struct module *owner ;
   loff_t (*llseek)(struct file * , loff_t , int ) ;
   ssize_t (*read)(struct file * , char * , size_t , loff_t * ) ;
   ssize_t (*write)(struct file * , char const * , size_t , loff_t * ) ;
   ssize_t (*aio_read)(struct kiocb * , struct iovec const * , unsigned long ,
                       loff_t ) ;
   ssize_t (*aio_write)(struct kiocb * , struct iovec const * , unsigned long ,
                        loff_t ) ;
   int (*readdir)(struct file * , void * , int (*)(void * , char const * , int ,
                                                   loff_t , u64 , unsigned int ) ) ;
   unsigned int (*poll)(struct file * , struct poll_table_struct * ) ;
   long (*unlocked_ioctl)(struct file * , unsigned int , unsigned long ) ;
   long (*compat_ioctl)(struct file * , unsigned int , unsigned long ) ;
   int (*mmap)(struct file * , struct vm_area_struct * ) ;
   int (*open)(struct inode * , struct file * ) ;
   int (*flush)(struct file * , fl_owner_t id ) ;
   int (*release)(struct inode * , struct file * ) ;
   int (*fsync)(struct file * , int datasync ) ;
   int (*aio_fsync)(struct kiocb * , int datasync ) ;
   int (*fasync)(int , struct file * , int ) ;
   int (*lock)(struct file * , int , struct file_lock * ) ;
   ssize_t (*sendpage)(struct file * , struct page * , int , size_t , loff_t * ,
                       int ) ;
   unsigned long (*get_unmapped_area)(struct file * , unsigned long , unsigned long ,
                                      unsigned long , unsigned long ) ;
   int (*check_flags)(int ) ;
   int (*flock)(struct file * , int , struct file_lock * ) ;
   ssize_t (*splice_write)(struct pipe_inode_info * , struct file * , loff_t * , size_t ,
                           unsigned int ) ;
   ssize_t (*splice_read)(struct file * , loff_t * , struct pipe_inode_info * , size_t ,
                          unsigned int ) ;
   int (*setlease)(struct file * , long , struct file_lock ** ) ;
   long (*fallocate)(struct file *file , int mode , loff_t offset , loff_t len ) ;
};
# 1578 "include/linux/fs.h"
struct inode_operations {
   struct dentry *(*lookup)(struct inode * , struct dentry * , struct nameidata * ) ;
   void *(*follow_link)(struct dentry * , struct nameidata * ) ;
   int (*permission)(struct inode * , int , unsigned int ) ;
   int (*check_acl)(struct inode * , int , unsigned int ) ;
   int (*readlink)(struct dentry * , char * , int ) ;
   void (*put_link)(struct dentry * , struct nameidata * , void * ) ;
   int (*create)(struct inode * , struct dentry * , int , struct nameidata * ) ;
   int (*link)(struct dentry * , struct inode * , struct dentry * ) ;
   int (*unlink)(struct inode * , struct dentry * ) ;
   int (*symlink)(struct inode * , struct dentry * , char const * ) ;
   int (*mkdir)(struct inode * , struct dentry * , int ) ;
   int (*rmdir)(struct inode * , struct dentry * ) ;
   int (*mknod)(struct inode * , struct dentry * , int , dev_t ) ;
   int (*rename)(struct inode * , struct dentry * , struct inode * , struct dentry * ) ;
   void (*truncate)(struct inode * ) ;
   int (*setattr)(struct dentry * , struct iattr * ) ;
   int (*getattr)(struct vfsmount *mnt , struct dentry * , struct kstat * ) ;
   int (*setxattr)(struct dentry * , char const * , void const * , size_t , int ) ;
   ssize_t (*getxattr)(struct dentry * , char const * , void * , size_t ) ;
   ssize_t (*listxattr)(struct dentry * , char * , size_t ) ;
   int (*removexattr)(struct dentry * , char const * ) ;
   void (*truncate_range)(struct inode * , loff_t , loff_t ) ;
   int (*fiemap)(struct inode * , struct fiemap_extent_info * , u64 start , u64 len ) ;
} __attribute__((__aligned__((1) << (6) ))) ;
# 1608 "include/linux/fs.h"
struct seq_file;
# 1622 "include/linux/fs.h"
struct super_operations {
   struct inode *(*alloc_inode)(struct super_block *sb ) ;
   void (*destroy_inode)(struct inode * ) ;
   void (*dirty_inode)(struct inode * , int flags ) ;
   int (*write_inode)(struct inode * , struct writeback_control *wbc ) ;
   int (*drop_inode)(struct inode * ) ;
   void (*evict_inode)(struct inode * ) ;
   void (*put_super)(struct super_block * ) ;
   void (*write_super)(struct super_block * ) ;
   int (*sync_fs)(struct super_block *sb , int wait ) ;
   int (*freeze_fs)(struct super_block * ) ;
   int (*unfreeze_fs)(struct super_block * ) ;
   int (*statfs)(struct dentry * , struct kstatfs * ) ;
   int (*remount_fs)(struct super_block * , int * , char * ) ;
   void (*umount_begin)(struct super_block * ) ;
   int (*show_options)(struct seq_file * , struct vfsmount * ) ;
   int (*show_devname)(struct seq_file * , struct vfsmount * ) ;
   int (*show_path)(struct seq_file * , struct vfsmount * ) ;
   int (*show_stats)(struct seq_file * , struct vfsmount * ) ;
   ssize_t (*quota_read)(struct super_block * , int , char * , size_t , loff_t ) ;
   ssize_t (*quota_write)(struct super_block * , int , char const * , size_t ,
                          loff_t ) ;
   int (*bdev_try_to_free_page)(struct super_block * , struct page * , gfp_t ) ;
};
# 1802 "include/linux/fs.h"
struct file_system_type {
   char const *name ;
   int fs_flags ;
   struct dentry *(*mount)(struct file_system_type * , int , char const * , void * ) ;
   void (*kill_sb)(struct super_block * ) ;
   struct module *owner ;
   struct file_system_type *next ;
   struct list_head fs_supers ;
   struct lock_class_key s_lock_key ;
   struct lock_class_key s_umount_key ;
   struct lock_class_key s_vfs_rename_key ;
   struct lock_class_key i_lock_key ;
   struct lock_class_key i_mutex_key ;
   struct lock_class_key i_mutex_dir_key ;
   struct lock_class_key i_alloc_sem_key ;
};
# 23 "include/linux/mm_types.h"
struct address_space;
# 34 "include/linux/mm_types.h"
struct __anonstruct____missing_field_name_223 {
   u16 inuse ;
   u16 objects ;
};
# 34 "include/linux/mm_types.h"
union __anonunion____missing_field_name_222 {
   atomic_t _mapcount ;
   struct __anonstruct____missing_field_name_223 __annonCompField34 ;
};
# 34 "include/linux/mm_types.h"
struct __anonstruct____missing_field_name_225 {
   unsigned long private ;
   struct address_space *mapping ;
};
# 34 "include/linux/mm_types.h"
union __anonunion____missing_field_name_224 {
   struct __anonstruct____missing_field_name_225 __annonCompField36 ;
   struct kmem_cache *slab ;
   struct page *first_page ;
};
# 34 "include/linux/mm_types.h"
union __anonunion____missing_field_name_226 {
   unsigned long index ;
   void *freelist ;
};
# 34 "include/linux/mm_types.h"
struct page {
   unsigned long flags ;
   atomic_t _count ;
   union __anonunion____missing_field_name_222 __annonCompField35 ;
   union __anonunion____missing_field_name_224 __annonCompField37 ;
   union __anonunion____missing_field_name_226 __annonCompField38 ;
   struct list_head lru ;
};
# 132 "include/linux/mm_types.h"
struct __anonstruct_vm_set_228 {
   struct list_head list ;
   void *parent ;
   struct vm_area_struct *head ;
};
# 132 "include/linux/mm_types.h"
union __anonunion_shared_227 {
   struct __anonstruct_vm_set_228 vm_set ;
   struct raw_prio_tree_node prio_tree_node ;
};
# 132 "include/linux/mm_types.h"
struct anon_vma;
# 132 "include/linux/mm_types.h"
struct anon_vma;
# 132 "include/linux/mm_types.h"
struct vm_operations_struct;
# 132 "include/linux/mm_types.h"
struct vm_operations_struct;
# 132 "include/linux/mm_types.h"
struct mempolicy;
# 132 "include/linux/mm_types.h"
struct mempolicy;
# 132 "include/linux/mm_types.h"
struct vm_area_struct {
   struct mm_struct *vm_mm ;
   unsigned long vm_start ;
   unsigned long vm_end ;
   struct vm_area_struct *vm_next ;
   struct vm_area_struct *vm_prev ;
   pgprot_t vm_page_prot ;
   unsigned long vm_flags ;
   struct rb_node vm_rb ;
   union __anonunion_shared_227 shared ;
   struct list_head anon_vma_chain ;
   struct anon_vma *anon_vma ;
   struct vm_operations_struct const *vm_ops ;
   unsigned long vm_pgoff ;
   struct file *vm_file ;
   void *vm_private_data ;
   struct mempolicy *vm_policy ;
};
# 189 "include/linux/mm_types.h"
struct core_thread {
   struct task_struct *task ;
   struct core_thread *next ;
};
# 194 "include/linux/mm_types.h"
struct core_state {
   atomic_t nr_threads ;
   struct core_thread dumper ;
   struct completion startup ;
};
# 216 "include/linux/mm_types.h"
struct mm_rss_stat {
   atomic_long_t count[3] ;
};
# 220 "include/linux/mm_types.h"
struct linux_binfmt;
# 220 "include/linux/mm_types.h"
struct linux_binfmt;
# 220 "include/linux/mm_types.h"
struct mmu_notifier_mm;
# 220 "include/linux/mm_types.h"
struct mmu_notifier_mm;
# 220 "include/linux/mm_types.h"
struct mm_struct {
   struct vm_area_struct *mmap ;
   struct rb_root mm_rb ;
   struct vm_area_struct *mmap_cache ;
   unsigned long (*get_unmapped_area)(struct file *filp , unsigned long addr , unsigned long len ,
                                      unsigned long pgoff , unsigned long flags ) ;
   void (*unmap_area)(struct mm_struct *mm , unsigned long addr ) ;
   unsigned long mmap_base ;
   unsigned long task_size ;
   unsigned long cached_hole_size ;
   unsigned long free_area_cache ;
   pgd_t *pgd ;
   atomic_t mm_users ;
   atomic_t mm_count ;
   int map_count ;
   spinlock_t page_table_lock ;
   struct rw_semaphore mmap_sem ;
   struct list_head mmlist ;
   unsigned long hiwater_rss ;
   unsigned long hiwater_vm ;
   unsigned long total_vm ;
   unsigned long locked_vm ;
   unsigned long shared_vm ;
   unsigned long exec_vm ;
   unsigned long stack_vm ;
   unsigned long reserved_vm ;
   unsigned long def_flags ;
   unsigned long nr_ptes ;
   unsigned long start_code ;
   unsigned long end_code ;
   unsigned long start_data ;
   unsigned long end_data ;
   unsigned long start_brk ;
   unsigned long brk ;
   unsigned long start_stack ;
   unsigned long arg_start ;
   unsigned long arg_end ;
   unsigned long env_start ;
   unsigned long env_end ;
   unsigned long saved_auxv[44] ;
   struct mm_rss_stat rss_stat ;
   struct linux_binfmt *binfmt ;
   cpumask_var_t cpu_vm_mask_var ;
   mm_context_t context ;
   unsigned int faultstamp ;
   unsigned int token_priority ;
   unsigned int last_interval ;
   atomic_t oom_disable_count ;
   unsigned long flags ;
   struct core_state *core_state ;
   spinlock_t ioctx_lock ;
   struct hlist_head ioctx_list ;
   struct task_struct *owner ;
   struct file *exe_file ;
   unsigned long num_exe_file_vmas ;
   struct mmu_notifier_mm *mmu_notifier_mm ;
   pgtable_t pmd_huge_pte ;
   struct cpumask cpumask_allocation ;
};
# 7 "include/asm-generic/cputime.h"
typedef unsigned long cputime_t;
# 84 "include/linux/sem.h"
struct task_struct;
# 122 "include/linux/sem.h"
struct sem_undo_list;
# 122 "include/linux/sem.h"
struct sem_undo_list;
# 135 "include/linux/sem.h"
struct sem_undo_list {
   atomic_t refcnt ;
   spinlock_t lock ;
   struct list_head list_proc ;
};
# 141 "include/linux/sem.h"
struct sysv_sem {
   struct sem_undo_list *undo_list ;
};
# 10 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/signal.h"
struct siginfo;
# 10 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/signal.h"
struct siginfo;
# 10 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/signal.h"
struct siginfo;
# 30 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/signal.h"
struct __anonstruct_sigset_t_230 {
   unsigned long sig[1] ;
};
# 30 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/signal.h"
typedef struct __anonstruct_sigset_t_230 sigset_t;
# 17 "include/asm-generic/signal-defs.h"
typedef void __signalfn_t(int );
# 18 "include/asm-generic/signal-defs.h"
typedef __signalfn_t *__sighandler_t;
# 20 "include/asm-generic/signal-defs.h"
typedef void __restorefn_t(void);
# 21 "include/asm-generic/signal-defs.h"
typedef __restorefn_t *__sigrestore_t;
# 167 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/signal.h"
struct sigaction {
   __sighandler_t sa_handler ;
   unsigned long sa_flags ;
   __sigrestore_t sa_restorer ;
   sigset_t sa_mask ;
};
# 174 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/signal.h"
struct k_sigaction {
   struct sigaction sa ;
};
# 7 "include/asm-generic/siginfo.h"
union sigval {
   int sival_int ;
   void *sival_ptr ;
};
# 7 "include/asm-generic/siginfo.h"
typedef union sigval sigval_t;
# 40 "include/asm-generic/siginfo.h"
struct __anonstruct__kill_232 {
   __kernel_pid_t _pid ;
   __kernel_uid32_t _uid ;
};
# 40 "include/asm-generic/siginfo.h"
struct __anonstruct__timer_233 {
   __kernel_timer_t _tid ;
   int _overrun ;
   char _pad[sizeof(__kernel_uid32_t ) - sizeof(int )] ;
   sigval_t _sigval ;
   int _sys_private ;
};
# 40 "include/asm-generic/siginfo.h"
struct __anonstruct__rt_234 {
   __kernel_pid_t _pid ;
   __kernel_uid32_t _uid ;
   sigval_t _sigval ;
};
# 40 "include/asm-generic/siginfo.h"
struct __anonstruct__sigchld_235 {
   __kernel_pid_t _pid ;
   __kernel_uid32_t _uid ;
   int _status ;
   __kernel_clock_t _utime ;
   __kernel_clock_t _stime ;
};
# 40 "include/asm-generic/siginfo.h"
struct __anonstruct__sigfault_236 {
   void *_addr ;
   short _addr_lsb ;
};
# 40 "include/asm-generic/siginfo.h"
struct __anonstruct__sigpoll_237 {
   long _band ;
   int _fd ;
};
# 40 "include/asm-generic/siginfo.h"
union __anonunion__sifields_231 {
   int _pad[(128UL - 4UL * sizeof(int )) / sizeof(int )] ;
   struct __anonstruct__kill_232 _kill ;
   struct __anonstruct__timer_233 _timer ;
   struct __anonstruct__rt_234 _rt ;
   struct __anonstruct__sigchld_235 _sigchld ;
   struct __anonstruct__sigfault_236 _sigfault ;
   struct __anonstruct__sigpoll_237 _sigpoll ;
};
# 40 "include/asm-generic/siginfo.h"
struct siginfo {
   int si_signo ;
   int si_errno ;
   int si_code ;
   union __anonunion__sifields_231 _sifields ;
};
# 40 "include/asm-generic/siginfo.h"
typedef struct siginfo siginfo_t;
# 280 "include/asm-generic/siginfo.h"
struct siginfo;
# 10 "include/linux/signal.h"
struct task_struct;
# 18 "include/linux/signal.h"
struct user_struct;
# 18 "include/linux/signal.h"
struct user_struct;
# 28 "include/linux/signal.h"
struct sigpending {
   struct list_head list ;
   sigset_t signal ;
};
# 239 "include/linux/signal.h"
struct timespec;
# 240 "include/linux/signal.h"
struct pt_regs;
# 97 "include/linux/proportions.h"
struct prop_local_single {
   unsigned long events ;
   unsigned long period ;
   int shift ;
   spinlock_t lock ;
};
# 10 "include/linux/seccomp.h"
struct __anonstruct_seccomp_t_240 {
   int mode ;
};
# 10 "include/linux/seccomp.h"
typedef struct __anonstruct_seccomp_t_240 seccomp_t;
# 82 "include/linux/plist.h"
struct plist_head {
   struct list_head node_list ;
   raw_spinlock_t *rawlock ;
   spinlock_t *spinlock ;
};
# 90 "include/linux/plist.h"
struct plist_node {
   int prio ;
   struct list_head prio_list ;
   struct list_head node_list ;
};
# 40 "include/linux/rtmutex.h"
struct rt_mutex_waiter;
# 40 "include/linux/rtmutex.h"
struct rt_mutex_waiter;
# 40 "include/linux/rtmutex.h"
struct rt_mutex_waiter;
# 42 "include/linux/resource.h"
struct rlimit {
   unsigned long rlim_cur ;
   unsigned long rlim_max ;
};
# 81 "include/linux/resource.h"
struct task_struct;
# 11 "include/linux/task_io_accounting.h"
struct task_io_accounting {
   u64 rchar ;
   u64 wchar ;
   u64 syscr ;
   u64 syscw ;
   u64 read_bytes ;
   u64 write_bytes ;
   u64 cancelled_write_bytes ;
};
# 18 "include/linux/latencytop.h"
struct latency_record {
   unsigned long backtrace[12] ;
   unsigned int count ;
   unsigned long time ;
   unsigned long max ;
};
# 26 "include/linux/latencytop.h"
struct task_struct;
# 29 "include/linux/key.h"
typedef int32_t key_serial_t;
# 32 "include/linux/key.h"
typedef uint32_t key_perm_t;
# 34 "include/linux/key.h"
struct key;
# 34 "include/linux/key.h"
struct key;
# 34 "include/linux/key.h"
struct key;
# 74 "include/linux/key.h"
struct seq_file;
# 75 "include/linux/key.h"
struct user_struct;
# 76 "include/linux/key.h"
struct signal_struct;
# 76 "include/linux/key.h"
struct signal_struct;
# 76 "include/linux/key.h"
struct signal_struct;
# 77 "include/linux/key.h"
struct cred;
# 79 "include/linux/key.h"
struct key_type;
# 79 "include/linux/key.h"
struct key_type;
# 79 "include/linux/key.h"
struct key_type;
# 81 "include/linux/key.h"
struct keyring_list;
# 81 "include/linux/key.h"
struct keyring_list;
# 81 "include/linux/key.h"
struct keyring_list;
# 124 "include/linux/key.h"
struct key_user;
# 124 "include/linux/key.h"
struct key_user;
# 124 "include/linux/key.h"
union __anonunion____missing_field_name_241 {
   time_t expiry ;
   time_t revoked_at ;
};
# 124 "include/linux/key.h"
union __anonunion_type_data_242 {
   struct list_head link ;
   unsigned long x[2] ;
   void *p[2] ;
   int reject_error ;
};
# 124 "include/linux/key.h"
union __anonunion_payload_243 {
   unsigned long value ;
   void *rcudata ;
   void *data ;
   struct keyring_list *subscriptions ;
};
# 124 "include/linux/key.h"
struct key {
   atomic_t usage ;
   key_serial_t serial ;
   struct rb_node serial_node ;
   struct key_type *type ;
   struct rw_semaphore sem ;
   struct key_user *user ;
   void *security ;
   union __anonunion____missing_field_name_241 __annonCompField39 ;
   uid_t uid ;
   gid_t gid ;
   key_perm_t perm ;
   unsigned short quotalen ;
   unsigned short datalen ;
   unsigned long flags ;
   char *description ;
   union __anonunion_type_data_242 type_data ;
   union __anonunion_payload_243 payload ;
};
# 18 "include/linux/selinux.h"
struct audit_context;
# 18 "include/linux/selinux.h"
struct audit_context;
# 18 "include/linux/selinux.h"
struct audit_context;
# 21 "include/linux/cred.h"
struct user_struct;
# 22 "include/linux/cred.h"
struct cred;
# 23 "include/linux/cred.h"
struct inode;
# 31 "include/linux/cred.h"
struct group_info {
   atomic_t usage ;
   int ngroups ;
   int nblocks ;
   gid_t small_block[32] ;
   gid_t *blocks[0] ;
};
# 83 "include/linux/cred.h"
struct thread_group_cred {
   atomic_t usage ;
   pid_t tgid ;
   spinlock_t lock ;
   struct key *session_keyring ;
   struct key *process_keyring ;
   struct rcu_head rcu ;
};
# 116 "include/linux/cred.h"
struct cred {
   atomic_t usage ;
   atomic_t subscribers ;
   void *put_addr ;
   unsigned int magic ;
   uid_t uid ;
   gid_t gid ;
   uid_t suid ;
   gid_t sgid ;
   uid_t euid ;
   gid_t egid ;
   uid_t fsuid ;
   gid_t fsgid ;
   unsigned int securebits ;
   kernel_cap_t cap_inheritable ;
   kernel_cap_t cap_permitted ;
   kernel_cap_t cap_effective ;
   kernel_cap_t cap_bset ;
   unsigned char jit_keyring ;
   struct key *thread_keyring ;
   struct key *request_key_auth ;
   struct thread_group_cred *tgcred ;
   void *security ;
   struct user_struct *user ;
   struct user_namespace *user_ns ;
   struct group_info *group_info ;
   struct rcu_head rcu ;
};
# 97 "include/linux/sched.h"
struct futex_pi_state;
# 97 "include/linux/sched.h"
struct futex_pi_state;
# 97 "include/linux/sched.h"
struct futex_pi_state;
# 98 "include/linux/sched.h"
struct robust_list_head;
# 98 "include/linux/sched.h"
struct robust_list_head;
# 98 "include/linux/sched.h"
struct robust_list_head;
# 99 "include/linux/sched.h"
struct bio_list;
# 99 "include/linux/sched.h"
struct bio_list;
# 99 "include/linux/sched.h"
struct bio_list;
# 100 "include/linux/sched.h"
struct fs_struct;
# 100 "include/linux/sched.h"
struct fs_struct;
# 100 "include/linux/sched.h"
struct fs_struct;
# 101 "include/linux/sched.h"
struct perf_event_context;
# 101 "include/linux/sched.h"
struct perf_event_context;
# 101 "include/linux/sched.h"
struct perf_event_context;
# 102 "include/linux/sched.h"
struct blk_plug;
# 102 "include/linux/sched.h"
struct blk_plug;
# 102 "include/linux/sched.h"
struct blk_plug;
# 150 "include/linux/sched.h"
struct seq_file;
# 151 "include/linux/sched.h"
struct cfs_rq;
# 151 "include/linux/sched.h"
struct cfs_rq;
# 151 "include/linux/sched.h"
struct cfs_rq;
# 259 "include/linux/sched.h"
struct task_struct;
# 364 "include/linux/sched.h"
struct nsproxy;
# 365 "include/linux/sched.h"
struct user_namespace;
# 58 "include/linux/aio_abi.h"
struct io_event {
   __u64 data ;
   __u64 obj ;
   __s64 res ;
   __s64 res2 ;
};
# 16 "include/linux/uio.h"
struct iovec {
   void *iov_base ;
   __kernel_size_t iov_len ;
};
# 15 "include/linux/aio.h"
struct kioctx;
# 15 "include/linux/aio.h"
struct kioctx;
# 15 "include/linux/aio.h"
struct kioctx;
# 87 "include/linux/aio.h"
union __anonunion_ki_obj_245 {
   void *user ;
   struct task_struct *tsk ;
};
# 87 "include/linux/aio.h"
struct eventfd_ctx;
# 87 "include/linux/aio.h"
struct eventfd_ctx;
# 87 "include/linux/aio.h"
struct kiocb {
   struct list_head ki_run_list ;
   unsigned long ki_flags ;
   int ki_users ;
   unsigned int ki_key ;
   struct file *ki_filp ;
   struct kioctx *ki_ctx ;
   int (*ki_cancel)(struct kiocb * , struct io_event * ) ;
   ssize_t (*ki_retry)(struct kiocb * ) ;
   void (*ki_dtor)(struct kiocb * ) ;
   union __anonunion_ki_obj_245 ki_obj ;
   __u64 ki_user_data ;
   loff_t ki_pos ;
   void *private ;
   unsigned short ki_opcode ;
   size_t ki_nbytes ;
   char *ki_buf ;
   size_t ki_left ;
   struct iovec ki_inline_vec ;
   struct iovec *ki_iovec ;
   unsigned long ki_nr_segs ;
   unsigned long ki_cur_seg ;
   struct list_head ki_list ;
   struct eventfd_ctx *ki_eventfd ;
};
# 165 "include/linux/aio.h"
struct aio_ring_info {
   unsigned long mmap_base ;
   unsigned long mmap_size ;
   struct page **ring_pages ;
   spinlock_t ring_lock ;
   long nr_pages ;
   unsigned int nr ;
   unsigned int tail ;
   struct page *internal_pages[8] ;
};
# 178 "include/linux/aio.h"
struct kioctx {
   atomic_t users ;
   int dead ;
   struct mm_struct *mm ;
   unsigned long user_id ;
   struct hlist_node list ;
   wait_queue_head_t wait ;
   spinlock_t ctx_lock ;
   int reqs_active ;
   struct list_head active_reqs ;
   struct list_head run_list ;
   unsigned int max_reqs ;
   struct aio_ring_info ring_info ;
   struct delayed_work wq ;
   struct rcu_head rcu_head ;
};
# 213 "include/linux/aio.h"
struct mm_struct;
# 441 "include/linux/sched.h"
struct sighand_struct {
   atomic_t count ;
   struct k_sigaction action[64] ;
   spinlock_t siglock ;
   wait_queue_head_t signalfd_wqh ;
};
# 448 "include/linux/sched.h"
struct pacct_struct {
   int ac_flag ;
   long ac_exitcode ;
   unsigned long ac_mem ;
   cputime_t ac_utime ;
   cputime_t ac_stime ;
   unsigned long ac_minflt ;
   unsigned long ac_majflt ;
};
# 456 "include/linux/sched.h"
struct cpu_itimer {
   cputime_t expires ;
   cputime_t incr ;
   u32 error ;
   u32 incr_error ;
};
# 474 "include/linux/sched.h"
struct task_cputime {
   cputime_t utime ;
   cputime_t stime ;
   unsigned long long sum_exec_runtime ;
};
# 510 "include/linux/sched.h"
struct thread_group_cputimer {
   struct task_cputime cputime ;
   int running ;
   spinlock_t lock ;
};
# 517 "include/linux/sched.h"
struct autogroup;
# 517 "include/linux/sched.h"
struct autogroup;
# 517 "include/linux/sched.h"
struct autogroup;
# 526 "include/linux/sched.h"
struct tty_struct;
# 526 "include/linux/sched.h"
struct tty_struct;
# 526 "include/linux/sched.h"
struct taskstats;
# 526 "include/linux/sched.h"
struct taskstats;
# 526 "include/linux/sched.h"
struct tty_audit_buf;
# 526 "include/linux/sched.h"
struct tty_audit_buf;
# 526 "include/linux/sched.h"
struct signal_struct {
   atomic_t sigcnt ;
   atomic_t live ;
   int nr_threads ;
   wait_queue_head_t wait_chldexit ;
   struct task_struct *curr_target ;
   struct sigpending shared_pending ;
   int group_exit_code ;
   int notify_count ;
   struct task_struct *group_exit_task ;
   int group_stop_count ;
   unsigned int flags ;
   struct list_head posix_timers ;
   struct hrtimer real_timer ;
   struct pid *leader_pid ;
   ktime_t it_real_incr ;
   struct cpu_itimer it[2] ;
   struct thread_group_cputimer cputimer ;
   struct task_cputime cputime_expires ;
   struct list_head cpu_timers[3] ;
   struct pid *tty_old_pgrp ;
   int leader ;
   struct tty_struct *tty ;
   struct autogroup *autogroup ;
   cputime_t utime ;
   cputime_t stime ;
   cputime_t cutime ;
   cputime_t cstime ;
   cputime_t gtime ;
   cputime_t cgtime ;
   cputime_t prev_utime ;
   cputime_t prev_stime ;
   unsigned long nvcsw ;
   unsigned long nivcsw ;
   unsigned long cnvcsw ;
   unsigned long cnivcsw ;
   unsigned long min_flt ;
   unsigned long maj_flt ;
   unsigned long cmin_flt ;
   unsigned long cmaj_flt ;
   unsigned long inblock ;
   unsigned long oublock ;
   unsigned long cinblock ;
   unsigned long coublock ;
   unsigned long maxrss ;
   unsigned long cmaxrss ;
   struct task_io_accounting ioac ;
   unsigned long long sum_sched_runtime ;
   struct rlimit rlim[16] ;
   struct pacct_struct pacct ;
   struct taskstats *stats ;
   unsigned int audit_tty ;
   struct tty_audit_buf *tty_audit_buf ;
   struct rw_semaphore threadgroup_fork_lock ;
   int oom_adj ;
   int oom_score_adj ;
   int oom_score_adj_min ;
   struct mutex cred_guard_mutex ;
};
# 687 "include/linux/sched.h"
struct user_struct {
   atomic_t __count ;
   atomic_t processes ;
   atomic_t files ;
   atomic_t sigpending ;
   atomic_t inotify_watches ;
   atomic_t inotify_devs ;
   atomic_t fanotify_listeners ;
   atomic_long_t epoll_watches ;
   unsigned long mq_bytes ;
   unsigned long locked_shm ;
   struct key *uid_keyring ;
   struct key *session_keyring ;
   struct hlist_node uidhash_node ;
   uid_t uid ;
   struct user_namespace *user_ns ;
   atomic_long_t locked_vm ;
};
# 731 "include/linux/sched.h"
struct backing_dev_info;
# 732 "include/linux/sched.h"
struct reclaim_state;
# 732 "include/linux/sched.h"
struct reclaim_state;
# 732 "include/linux/sched.h"
struct reclaim_state;
# 735 "include/linux/sched.h"
struct sched_info {
   unsigned long pcount ;
   unsigned long long run_delay ;
   unsigned long long last_arrival ;
   unsigned long long last_queued ;
};
# 747 "include/linux/sched.h"
struct task_delay_info {
   spinlock_t lock ;
   unsigned int flags ;
   struct timespec blkio_start ;
   struct timespec blkio_end ;
   u64 blkio_delay ;
   u64 swapin_delay ;
   u32 blkio_count ;
   u32 swapin_count ;
   struct timespec freepages_start ;
   struct timespec freepages_end ;
   u64 freepages_delay ;
   u32 freepages_count ;
};
# 1050 "include/linux/sched.h"
struct io_context;
# 1050 "include/linux/sched.h"
struct io_context;
# 1050 "include/linux/sched.h"
struct io_context;
# 1059 "include/linux/sched.h"
struct audit_context;
# 1060 "include/linux/sched.h"
struct mempolicy;
# 1061 "include/linux/sched.h"
struct pipe_inode_info;
# 1064 "include/linux/sched.h"
struct rq;
# 1064 "include/linux/sched.h"
struct rq;
# 1064 "include/linux/sched.h"
struct rq;
# 1084 "include/linux/sched.h"
struct sched_class {
   struct sched_class const *next ;
   void (*enqueue_task)(struct rq *rq , struct task_struct *p , int flags ) ;
   void (*dequeue_task)(struct rq *rq , struct task_struct *p , int flags ) ;
   void (*yield_task)(struct rq *rq ) ;
   bool (*yield_to_task)(struct rq *rq , struct task_struct *p , bool preempt ) ;
   void (*check_preempt_curr)(struct rq *rq , struct task_struct *p , int flags ) ;
   struct task_struct *(*pick_next_task)(struct rq *rq ) ;
   void (*put_prev_task)(struct rq *rq , struct task_struct *p ) ;
   int (*select_task_rq)(struct task_struct *p , int sd_flag , int flags ) ;
   void (*pre_schedule)(struct rq *this_rq , struct task_struct *task ) ;
   void (*post_schedule)(struct rq *this_rq ) ;
   void (*task_waking)(struct task_struct *task ) ;
   void (*task_woken)(struct rq *this_rq , struct task_struct *task ) ;
   void (*set_cpus_allowed)(struct task_struct *p , struct cpumask const *newmask ) ;
   void (*rq_online)(struct rq *rq ) ;
   void (*rq_offline)(struct rq *rq ) ;
   void (*set_curr_task)(struct rq *rq ) ;
   void (*task_tick)(struct rq *rq , struct task_struct *p , int queued ) ;
   void (*task_fork)(struct task_struct *p ) ;
   void (*switched_from)(struct rq *this_rq , struct task_struct *task ) ;
   void (*switched_to)(struct rq *this_rq , struct task_struct *task ) ;
   void (*prio_changed)(struct rq *this_rq , struct task_struct *task , int oldprio ) ;
   unsigned int (*get_rr_interval)(struct rq *rq , struct task_struct *task ) ;
   void (*task_move_group)(struct task_struct *p , int on_rq ) ;
};
# 1129 "include/linux/sched.h"
struct load_weight {
   unsigned long weight ;
   unsigned long inv_weight ;
};
# 1134 "include/linux/sched.h"
struct sched_statistics {
   u64 wait_start ;
   u64 wait_max ;
   u64 wait_count ;
   u64 wait_sum ;
   u64 iowait_count ;
   u64 iowait_sum ;
   u64 sleep_start ;
   u64 sleep_max ;
   s64 sum_sleep_runtime ;
   u64 block_start ;
   u64 block_max ;
   u64 exec_max ;
   u64 slice_max ;
   u64 nr_migrations_cold ;
   u64 nr_failed_migrations_affine ;
   u64 nr_failed_migrations_running ;
   u64 nr_failed_migrations_hot ;
   u64 nr_forced_migrations ;
   u64 nr_wakeups ;
   u64 nr_wakeups_sync ;
   u64 nr_wakeups_migrate ;
   u64 nr_wakeups_local ;
   u64 nr_wakeups_remote ;
   u64 nr_wakeups_affine ;
   u64 nr_wakeups_affine_attempts ;
   u64 nr_wakeups_passive ;
   u64 nr_wakeups_idle ;
};
# 1169 "include/linux/sched.h"
struct sched_entity {
   struct load_weight load ;
   struct rb_node run_node ;
   struct list_head group_node ;
   unsigned int on_rq ;
   u64 exec_start ;
   u64 sum_exec_runtime ;
   u64 vruntime ;
   u64 prev_sum_exec_runtime ;
   u64 nr_migrations ;
   struct sched_statistics statistics ;
   struct sched_entity *parent ;
   struct cfs_rq *cfs_rq ;
   struct cfs_rq *my_q ;
};
# 1195 "include/linux/sched.h"
struct rt_rq;
# 1195 "include/linux/sched.h"
struct rt_rq;
# 1195 "include/linux/sched.h"
struct sched_rt_entity {
   struct list_head run_list ;
   unsigned long timeout ;
   unsigned int time_slice ;
   int nr_cpus_allowed ;
   struct sched_rt_entity *back ;
   struct sched_rt_entity *parent ;
   struct rt_rq *rt_rq ;
   struct rt_rq *my_q ;
};
# 1220 "include/linux/sched.h"
struct css_set;
# 1220 "include/linux/sched.h"
struct css_set;
# 1220 "include/linux/sched.h"
struct compat_robust_list_head;
# 1220 "include/linux/sched.h"
struct compat_robust_list_head;
# 1220 "include/linux/sched.h"
struct ftrace_ret_stack;
# 1220 "include/linux/sched.h"
struct ftrace_ret_stack;
# 1220 "include/linux/sched.h"
struct mem_cgroup;
# 1220 "include/linux/sched.h"
struct mem_cgroup;
# 1220 "include/linux/sched.h"
struct memcg_batch_info {
   int do_batch ;
   struct mem_cgroup *memcg ;
   unsigned long nr_pages ;
   unsigned long memsw_nr_pages ;
};
# 1220 "include/linux/sched.h"
struct task_struct {
   long volatile state ;
   void *stack ;
   atomic_t usage ;
   unsigned int flags ;
   unsigned int ptrace ;
   struct task_struct *wake_entry ;
   int on_cpu ;
   int on_rq ;
   int prio ;
   int static_prio ;
   int normal_prio ;
   unsigned int rt_priority ;
   struct sched_class const *sched_class ;
   struct sched_entity se ;
   struct sched_rt_entity rt ;
   struct hlist_head preempt_notifiers ;
   unsigned char fpu_counter ;
   unsigned int btrace_seq ;
   unsigned int policy ;
   cpumask_t cpus_allowed ;
   struct sched_info sched_info ;
   struct list_head tasks ;
   struct plist_node pushable_tasks ;
   struct mm_struct *mm ;
   struct mm_struct *active_mm ;
   unsigned int brk_randomized : 1 ;
   int exit_state ;
   int exit_code ;
   int exit_signal ;
   int pdeath_signal ;
   unsigned int group_stop ;
   unsigned int personality ;
   unsigned int did_exec : 1 ;
   unsigned int in_execve : 1 ;
   unsigned int in_iowait : 1 ;
   unsigned int sched_reset_on_fork : 1 ;
   unsigned int sched_contributes_to_load : 1 ;
   pid_t pid ;
   pid_t tgid ;
   unsigned long stack_canary ;
   struct task_struct *real_parent ;
   struct task_struct *parent ;
   struct list_head children ;
   struct list_head sibling ;
   struct task_struct *group_leader ;
   struct list_head ptraced ;
   struct list_head ptrace_entry ;
   struct pid_link pids[3] ;
   struct list_head thread_group ;
   struct completion *vfork_done ;
   int *set_child_tid ;
   int *clear_child_tid ;
   cputime_t utime ;
   cputime_t stime ;
   cputime_t utimescaled ;
   cputime_t stimescaled ;
   cputime_t gtime ;
   cputime_t prev_utime ;
   cputime_t prev_stime ;
   unsigned long nvcsw ;
   unsigned long nivcsw ;
   struct timespec start_time ;
   struct timespec real_start_time ;
   unsigned long min_flt ;
   unsigned long maj_flt ;
   struct task_cputime cputime_expires ;
   struct list_head cpu_timers[3] ;
   struct cred const *real_cred ;
   struct cred const *cred ;
   struct cred *replacement_session_keyring ;
   char comm[16] ;
   int link_count ;
   int total_link_count ;
   struct sysv_sem sysvsem ;
   unsigned long last_switch_count ;
   struct thread_struct thread ;
   struct fs_struct *fs ;
   struct files_struct *files ;
   struct nsproxy *nsproxy ;
   struct signal_struct *signal ;
   struct sighand_struct *sighand ;
   sigset_t blocked ;
   sigset_t real_blocked ;
   sigset_t saved_sigmask ;
   struct sigpending pending ;
   unsigned long sas_ss_sp ;
   size_t sas_ss_size ;
   int (*notifier)(void *priv ) ;
   void *notifier_data ;
   sigset_t *notifier_mask ;
   struct audit_context *audit_context ;
   uid_t loginuid ;
   unsigned int sessionid ;
   seccomp_t seccomp ;
   u32 parent_exec_id ;
   u32 self_exec_id ;
   spinlock_t alloc_lock ;
   struct irqaction *irqaction ;
   raw_spinlock_t pi_lock ;
   struct plist_head pi_waiters ;
   struct rt_mutex_waiter *pi_blocked_on ;
   struct mutex_waiter *blocked_on ;
   unsigned int irq_events ;
   unsigned long hardirq_enable_ip ;
   unsigned long hardirq_disable_ip ;
   unsigned int hardirq_enable_event ;
   unsigned int hardirq_disable_event ;
   int hardirqs_enabled ;
   int hardirq_context ;
   unsigned long softirq_disable_ip ;
   unsigned long softirq_enable_ip ;
   unsigned int softirq_disable_event ;
   unsigned int softirq_enable_event ;
   int softirqs_enabled ;
   int softirq_context ;
   u64 curr_chain_key ;
   int lockdep_depth ;
   unsigned int lockdep_recursion ;
   struct held_lock held_locks[48UL] ;
   gfp_t lockdep_reclaim_gfp ;
   void *journal_info ;
   struct bio_list *bio_list ;
   struct blk_plug *plug ;
   struct reclaim_state *reclaim_state ;
   struct backing_dev_info *backing_dev_info ;
   struct io_context *io_context ;
   unsigned long ptrace_message ;
   siginfo_t *last_siginfo ;
   struct task_io_accounting ioac ;
   u64 acct_rss_mem1 ;
   u64 acct_vm_mem1 ;
   cputime_t acct_timexpd ;
   nodemask_t mems_allowed ;
   int mems_allowed_change_disable ;
   int cpuset_mem_spread_rotor ;
   int cpuset_slab_spread_rotor ;
   struct css_set *cgroups ;
   struct list_head cg_list ;
   struct robust_list_head *robust_list ;
   struct compat_robust_list_head *compat_robust_list ;
   struct list_head pi_state_list ;
   struct futex_pi_state *pi_state_cache ;
   struct perf_event_context *perf_event_ctxp[2] ;
   struct mutex perf_event_mutex ;
   struct list_head perf_event_list ;
   struct mempolicy *mempolicy ;
   short il_next ;
   short pref_node_fork ;
   atomic_t fs_excl ;
   struct rcu_head rcu ;
   struct pipe_inode_info *splice_pipe ;
   struct task_delay_info *delays ;
   int make_it_fail ;
   struct prop_local_single dirties ;
   int latency_record_count ;
   struct latency_record latency_record[32] ;
   unsigned long timer_slack_ns ;
   unsigned long default_timer_slack_ns ;
   struct list_head *scm_work_list ;
   int curr_ret_stack ;
   struct ftrace_ret_stack *ret_stack ;
   unsigned long long ftrace_timestamp ;
   atomic_t trace_overrun ;
   atomic_t tracing_graph_pause ;
   unsigned long trace ;
   unsigned long trace_recursion ;
   struct memcg_batch_info memcg_batch ;
   atomic_t ptrace_bp_refcnt ;
};
# 1634 "include/linux/sched.h"
struct pid_namespace;
# 25 "include/linux/usb.h"
struct usb_device;
# 25 "include/linux/usb.h"
struct usb_device;
# 25 "include/linux/usb.h"
struct usb_device;
# 26 "include/linux/usb.h"
struct usb_driver;
# 26 "include/linux/usb.h"
struct usb_driver;
# 26 "include/linux/usb.h"
struct usb_driver;
# 27 "include/linux/usb.h"
struct wusb_dev;
# 27 "include/linux/usb.h"
struct wusb_dev;
# 27 "include/linux/usb.h"
struct wusb_dev;
# 47 "include/linux/usb.h"
struct ep_device;
# 47 "include/linux/usb.h"
struct ep_device;
# 47 "include/linux/usb.h"
struct ep_device;
# 64 "include/linux/usb.h"
struct usb_host_endpoint {
   struct usb_endpoint_descriptor desc ;
   struct usb_ss_ep_comp_descriptor ss_ep_comp ;
   struct list_head urb_list ;
   void *hcpriv ;
   struct ep_device *ep_dev ;
   unsigned char *extra ;
   int extralen ;
   int enabled ;
};
# 77 "include/linux/usb.h"
struct usb_host_interface {
   struct usb_interface_descriptor desc ;
   struct usb_host_endpoint *endpoint ;
   char *string ;
   unsigned char *extra ;
   int extralen ;
};
# 90 "include/linux/usb.h"
enum usb_interface_condition {
    USB_INTERFACE_UNBOUND = 0,
    USB_INTERFACE_BINDING = 1,
    USB_INTERFACE_BOUND = 2,
    USB_INTERFACE_UNBINDING = 3
} ;
# 159 "include/linux/usb.h"
struct usb_interface {
   struct usb_host_interface *altsetting ;
   struct usb_host_interface *cur_altsetting ;
   unsigned int num_altsetting ;
   struct usb_interface_assoc_descriptor *intf_assoc ;
   int minor ;
   enum usb_interface_condition condition ;
   unsigned int sysfs_files_created : 1 ;
   unsigned int ep_devs_created : 1 ;
   unsigned int unregistering : 1 ;
   unsigned int needs_remote_wakeup : 1 ;
   unsigned int needs_altsetting0 : 1 ;
   unsigned int needs_binding : 1 ;
   unsigned int reset_running : 1 ;
   unsigned int resetting_device : 1 ;
   struct device dev ;
   struct device *usb_dev ;
   atomic_t pm_usage_cnt ;
   struct work_struct reset_ws ;
};
# 222 "include/linux/usb.h"
struct usb_interface_cache {
   unsigned int num_altsetting ;
   struct kref ref ;
   struct usb_host_interface altsetting[0] ;
};
# 274 "include/linux/usb.h"
struct usb_host_config {
   struct usb_config_descriptor desc ;
   char *string ;
   struct usb_interface_assoc_descriptor *intf_assoc[16] ;
   struct usb_interface *interface[32] ;
   struct usb_interface_cache *intf_cache[32] ;
   unsigned char *extra ;
   int extralen ;
};
# 305 "include/linux/usb.h"
struct usb_devmap {
   unsigned long devicemap[128UL / (8UL * sizeof(unsigned long ))] ;
};
# 312 "include/linux/usb.h"
struct mon_bus;
# 312 "include/linux/usb.h"
struct mon_bus;
# 312 "include/linux/usb.h"
struct usb_bus {
   struct device *controller ;
   int busnum ;
   char const *bus_name ;
   u8 uses_dma ;
   u8 uses_pio_for_control ;
   u8 otg_port ;
   unsigned int is_b_host : 1 ;
   unsigned int b_hnp_enable : 1 ;
   unsigned int sg_tablesize ;
   int devnum_next ;
   struct usb_devmap devmap ;
   struct usb_device *root_hub ;
   struct usb_bus *hs_companion ;
   struct list_head bus_list ;
   int bandwidth_allocated ;
   int bandwidth_int_reqs ;
   int bandwidth_isoc_reqs ;
   struct dentry *usbfs_dentry ;
   struct mon_bus *mon_bus ;
   int monitored ;
};
# 367 "include/linux/usb.h"
struct usb_tt;
# 367 "include/linux/usb.h"
struct usb_tt;
# 367 "include/linux/usb.h"
struct usb_tt;
# 426 "include/linux/usb.h"
struct usb_device {
   int devnum ;
   char devpath[16] ;
   u32 route ;
   enum usb_device_state state ;
   enum usb_device_speed speed ;
   struct usb_tt *tt ;
   int ttport ;
   unsigned int toggle[2] ;
   struct usb_device *parent ;
   struct usb_bus *bus ;
   struct usb_host_endpoint ep0 ;
   struct device dev ;
   struct usb_device_descriptor descriptor ;
   struct usb_host_config *config ;
   struct usb_host_config *actconfig ;
   struct usb_host_endpoint *ep_in[16] ;
   struct usb_host_endpoint *ep_out[16] ;
   char **rawdescriptors ;
   unsigned short bus_mA ;
   u8 portnum ;
   u8 level ;
   unsigned int can_submit : 1 ;
   unsigned int persist_enabled : 1 ;
   unsigned int have_langid : 1 ;
   unsigned int authorized : 1 ;
   unsigned int authenticated : 1 ;
   unsigned int wusb : 1 ;
   int string_langid ;
   char *product ;
   char *manufacturer ;
   char *serial ;
   struct list_head filelist ;
   struct device *usb_classdev ;
   struct dentry *usbfs_dentry ;
   int maxchild ;
   struct usb_device *children[31] ;
   u32 quirks ;
   atomic_t urbnum ;
   unsigned long active_duration ;
   unsigned long connect_time ;
   unsigned int do_remote_wakeup : 1 ;
   unsigned int reset_resume : 1 ;
   struct wusb_dev *wusb_dev ;
   int slot_id ;
};
# 763 "include/linux/usb.h"
struct usb_dynids {
   spinlock_t lock ;
   struct list_head list ;
};
# 782 "include/linux/usb.h"
struct usbdrv_wrap {
   struct device_driver driver ;
   int for_devices ;
};
# 843 "include/linux/usb.h"
struct usb_driver {
   char const *name ;
   int (*probe)(struct usb_interface *intf , struct usb_device_id const *id ) ;
   void (*disconnect)(struct usb_interface *intf ) ;
   int (*unlocked_ioctl)(struct usb_interface *intf , unsigned int code , void *buf ) ;
   int (*suspend)(struct usb_interface *intf , pm_message_t message ) ;
   int (*resume)(struct usb_interface *intf ) ;
   int (*reset_resume)(struct usb_interface *intf ) ;
   int (*pre_reset)(struct usb_interface *intf ) ;
   int (*post_reset)(struct usb_interface *intf ) ;
   struct usb_device_id const *id_table ;
   struct usb_dynids dynids ;
   struct usbdrv_wrap drvwrap ;
   unsigned int no_dynamic_id : 1 ;
   unsigned int supports_autosuspend : 1 ;
   unsigned int soft_unbind : 1 ;
};
# 918 "include/linux/usb.h"
struct usb_class_driver {
   char *name ;
   char *(*devnode)(struct device *dev , mode_t *mode ) ;
   struct file_operations const *fops ;
   int minor_base ;
};
# 983 "include/linux/usb.h"
struct usb_iso_packet_descriptor {
   unsigned int offset ;
   unsigned int length ;
   unsigned int actual_length ;
   int status ;
};
# 990 "include/linux/usb.h"
struct urb;
# 990 "include/linux/usb.h"
struct urb;
# 990 "include/linux/usb.h"
struct urb;
# 992 "include/linux/usb.h"
struct usb_anchor {
   struct list_head urb_list ;
   wait_queue_head_t wait ;
   spinlock_t lock ;
   unsigned int poisoned : 1 ;
};
# 1183 "include/linux/usb.h"
struct scatterlist;
# 1183 "include/linux/usb.h"
struct scatterlist;
# 1183 "include/linux/usb.h"
struct urb {
   struct kref kref ;
   void *hcpriv ;
   atomic_t use_count ;
   atomic_t reject ;
   int unlinked ;
   struct list_head urb_list ;
   struct list_head anchor_list ;
   struct usb_anchor *anchor ;
   struct usb_device *dev ;
   struct usb_host_endpoint *ep ;
   unsigned int pipe ;
   unsigned int stream_id ;
   int status ;
   unsigned int transfer_flags ;
   void *transfer_buffer ;
   dma_addr_t transfer_dma ;
   struct scatterlist *sg ;
   int num_sgs ;
   u32 transfer_buffer_length ;
   u32 actual_length ;
   unsigned char *setup_packet ;
   dma_addr_t setup_dma ;
   int start_frame ;
   int number_of_packets ;
   int interval ;
   int error_count ;
   void *context ;
   void (*complete)(struct urb * ) ;
   struct usb_iso_packet_descriptor iso_frame_desc[0] ;
};
# 1388 "include/linux/usb.h"
struct scatterlist;
# 28 "include/linux/poll.h"
struct poll_table_struct;
# 35 "include/linux/poll.h"
struct poll_table_struct {
   void (*qproc)(struct file * , wait_queue_head_t * , struct poll_table_struct * ) ;
   unsigned long key ;
};
# 6 "include/asm-generic/scatterlist.h"
struct scatterlist {
   unsigned long sg_magic ;
   unsigned long page_link ;
   unsigned int offset ;
   unsigned int length ;
   dma_addr_t dma_address ;
   unsigned int dma_length ;
};
# 19 "include/linux/mm.h"
struct mempolicy;
# 20 "include/linux/mm.h"
struct anon_vma;
# 21 "include/linux/mm.h"
struct file_ra_state;
# 22 "include/linux/mm.h"
struct user_struct;
# 23 "include/linux/mm.h"
struct writeback_control;
# 41 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/pgtable_64.h"
struct mm_struct;
# 656 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/pgtable.h"
struct vm_area_struct;
# 185 "include/linux/mm.h"
struct vm_fault {
   unsigned int flags ;
   unsigned long pgoff ;
   void *virtual_address ;
   struct page *page ;
};
# 202 "include/linux/mm.h"
struct vm_operations_struct {
   void (*open)(struct vm_area_struct *area ) ;
   void (*close)(struct vm_area_struct *area ) ;
   int (*fault)(struct vm_area_struct *vma , struct vm_fault *vmf ) ;
   int (*page_mkwrite)(struct vm_area_struct *vma , struct vm_fault *vmf ) ;
   int (*access)(struct vm_area_struct *vma , unsigned long addr , void *buf , int len ,
                 int write ) ;
   int (*set_policy)(struct vm_area_struct *vma , struct mempolicy *new ) ;
   struct mempolicy *(*get_policy)(struct vm_area_struct *vma , unsigned long addr ) ;
   int (*migrate)(struct vm_area_struct *vma , nodemask_t const *from , nodemask_t const *to ,
                  unsigned long flags ) ;
};
# 244 "include/linux/mm.h"
struct inode;
# 197 "include/linux/page-flags.h"
struct page;
# 58 "include/linux/kfifo.h"
struct __kfifo {
   unsigned int in ;
   unsigned int out ;
   unsigned int mask ;
   unsigned int esize ;
   void *data ;
};
# 96 "include/linux/kfifo.h"
union __anonunion____missing_field_name_248 {
   struct __kfifo kfifo ;
   unsigned char *type ;
   char (*rectype)[0] ;
   void *ptr ;
   void const *ptr_const ;
};
# 96 "include/linux/kfifo.h"
struct kfifo {
   union __anonunion____missing_field_name_248 __annonCompField41 ;
   unsigned char buf[0] ;
};
# 24 "include/media/lirc_dev.h"
struct lirc_buffer {
   wait_queue_head_t wait_poll ;
   spinlock_t fifo_lock ;
   unsigned int chunk_size ;
   unsigned int size ;
   struct kfifo fifo ;
   u8 fifo_initialized ;
};
# 125 "include/media/lirc_dev.h"
struct lirc_driver {
   char name[40] ;
   int minor ;
   __u32 code_length ;
   unsigned int buffer_size ;
   int sample_rate ;
   __u32 features ;
   unsigned int chunk_size ;
   void *data ;
   int min_timeout ;
   int max_timeout ;
   int (*add_to_buf)(void *data , struct lirc_buffer *buf ) ;
   struct lirc_buffer *rbuf ;
   int (*set_use_inc)(void *data ) ;
   void (*set_use_dec)(void *data ) ;
   struct file_operations const *fops ;
   struct device *dev ;
   struct module *owner ;
};
# 81 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
struct rx_data {
   int count ;
   int prev_bit ;
   int initial_space ;
};
# 81 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
struct tx_t {
   unsigned char data_buf[35] ;
   struct completion finished ;
   atomic_t busy ;
   int status ;
};
# 81 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
struct imon_context {
   struct usb_device *usbdev ;
   int display ;
   int display_isopen ;
   int ir_isopen ;
   int dev_present ;
   struct mutex ctx_lock ;
   wait_queue_head_t remove_ok ;
   int vfd_proto_6p ;
   struct lirc_driver *driver ;
   struct usb_endpoint_descriptor *rx_endpoint ;
   struct usb_endpoint_descriptor *tx_endpoint ;
   struct urb *rx_urb ;
   struct urb *tx_urb ;
   unsigned char usb_rx_buf[8] ;
   unsigned char usb_tx_buf[8] ;
   struct rx_data rx ;
   struct tx_t tx ;
};
# 1 "<compiler builtins>"
void *__builtin_memcpy(void * , void const * , unsigned long ) ;
# 1 "<compiler builtins>"
long __builtin_expect(long , long ) ;
# 100 "include/linux/printk.h"
extern int printk(char const *fmt , ...) ;
# 64 "include/asm-generic/bug.h"
extern void warn_slowpath_fmt(char const *file , int const line , char const *fmt
                              , ...) ;
# 16 "include/linux/string.h"
extern void *memdup_user(void const * , size_t ) ;
# 34 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/string_64.h"
extern void *__memcpy(void *to , void const *from , size_t len ) ;
# 62 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/string_64.h"
extern char *strcpy(char *dest , char const *src ) ;
# 27 "include/linux/err.h"
__inline static long __attribute__((__warn_unused_result__)) PTR_ERR(void const *ptr )
{

  {
# 29 "include/linux/err.h"
  return ((long )ptr);
}
}
# 32 "include/linux/err.h"
__inline static long __attribute__((__warn_unused_result__)) IS_ERR(void const *ptr )
{ long tmp ;

  {
  {
# 34 "include/linux/err.h"
  tmp = __builtin_expect((long )(! (! ((unsigned long )ptr >= 0x0ffffffffffff001UL))),
                         0L);
  }
# 34 "include/linux/err.h"
  return (tmp);
}
}
# 23 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/atomic.h"
__inline static int atomic_read(atomic_t const *v )
{

  {
# 25 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/atomic.h"
  return ((int )*((int volatile *)(& v->counter)));
}
}
# 35 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/atomic.h"
__inline static void atomic_set(atomic_t *v , int i )
{

  {
# 37 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/atomic.h"
  v->counter = i;
# 38 "/anthill/stuff/tacas-comp/inst/current/envs/linux-3.0.1/linux-3.0.1/arch/x86/include/asm/atomic.h"
  return;
}
}
# 93 "include/linux/spinlock.h"
extern void __raw_spin_lock_init(raw_spinlock_t *lock , char const *name , struct lock_class_key *key ) ;
# 32 "include/linux/spinlock_api_smp.h"
extern unsigned long _raw_spin_lock_irqsave(raw_spinlock_t *lock ) __attribute__((__section__(".spinlock.text"))) ;
# 42 "include/linux/spinlock_api_smp.h"
extern void _raw_spin_unlock_irqrestore(raw_spinlock_t *lock , unsigned long flags ) __attribute__((__section__(".spinlock.text"))) ;
# 272 "include/linux/spinlock.h"
__inline static raw_spinlock_t *spinlock_check(spinlock_t *lock )
{

  {
# 274 "include/linux/spinlock.h"
  return (& lock->__annonCompField18.rlock);
}
}
# 338 "include/linux/spinlock.h"
__inline static void spin_unlock_irqrestore(spinlock_t *lock , unsigned long flags )
{

  {
  {
# 340 "include/linux/spinlock.h"
  while (1) {
    while_continue: ;
    {
# 340 "include/linux/spinlock.h"
    _raw_spin_unlock_irqrestore(& lock->__annonCompField18.rlock, flags);
    }
# 340 "include/linux/spinlock.h"
    goto while_break;
  }
  while_break___0: ;
  }
  while_break: ;
# 341 "include/linux/spinlock.h"
  return;
}
}
# 80 "include/linux/wait.h"
extern void __init_waitqueue_head(wait_queue_head_t *q , struct lock_class_key * ) ;
# 156 "include/linux/wait.h"
extern void __wake_up(wait_queue_head_t *q , unsigned int mode , int nr , void *key ) ;
# 115 "include/linux/mutex.h"
extern void __mutex_init(struct mutex *lock , char const *name , struct lock_class_key *key ) ;
# 134 "include/linux/mutex.h"
extern void mutex_lock_nested(struct mutex *lock , unsigned int subclass ) ;
# 169 "include/linux/mutex.h"
extern void mutex_unlock(struct mutex *lock ) ;
# 76 "include/linux/completion.h"
static struct lock_class_key __key___2 ;
# 73 "include/linux/completion.h"
__inline static void init_completion(struct completion *x )
{

  {
# 75 "include/linux/completion.h"
  x->done = 0U;
  {
# 76 "include/linux/completion.h"
  while (1) {
    while_continue: ;
    {
# 76 "include/linux/completion.h"
    __init_waitqueue_head(& x->wait, & __key___2);
    }
# 76 "include/linux/completion.h"
    goto while_break;
  }
  while_break___0: ;
  }
  while_break: ;
# 77 "include/linux/completion.h"
  return;
}
}
# 80 "include/linux/completion.h"
extern int wait_for_completion_interruptible(struct completion *x ) ;
# 91 "include/linux/completion.h"
extern void complete(struct completion * ) ;
# 92 "include/linux/completion.h"
extern void complete_all(struct completion * ) ;
# 830 "include/linux/rcupdate.h"
extern void kfree(void const * ) ;
# 303 "include/linux/moduleparam.h"
extern struct kernel_param_ops param_ops_int ;
# 79 "include/linux/module.h"
int init_module(void) ;
# 80 "include/linux/module.h"
void cleanup_module(void) ;
# 99 "include/linux/module.h"
extern struct module __this_module ;
# 221 "include/linux/slub_def.h"
extern void *__kmalloc(size_t size , gfp_t flags ) ;
# 255 "include/linux/slub_def.h"
__inline static void *( __attribute__((__always_inline__)) kmalloc)(size_t size ,
                                                                    gfp_t flags )
{ void *tmp___2 ;

  {
  {
# 270 "include/linux/slub_def.h"
  tmp___2 = __kmalloc(size, flags);
  }
# 270 "include/linux/slub_def.h"
  return (tmp___2);
}
}
# 318 "include/linux/slab.h"
__inline static void *kzalloc(size_t size , gfp_t flags )
{ void *tmp ;

  {
  {
# 320 "include/linux/slab.h"
  tmp = kmalloc(size, flags | 32768U);
  }
# 320 "include/linux/slab.h"
  return (tmp);
}
}
# 705 "include/linux/device.h"
extern void *dev_get_drvdata(struct device const *dev ) __attribute__((__ldv_model__)) ;
# 706 "include/linux/device.h"
extern int dev_set_drvdata(struct device *dev , void *data ) ;
# 788 "include/linux/device.h"
extern int dev_printk(char const *level , struct device const *dev , char const *fmt
                      , ...) ;
# 799 "include/linux/device.h"
extern int dev_warn(struct device const *dev , char const *fmt , ...) ;
# 803 "include/linux/device.h"
extern int _dev_info(struct device const *dev , char const *fmt , ...) ;
# 891 "include/linux/fs.h"
__inline static unsigned int iminor(struct inode const *inode )
{

  {
# 893 "include/linux/fs.h"
  return ((unsigned int )(inode->i_rdev & (unsigned int const )((1U << 20) - 1U)));
}
}
# 2336 "include/linux/fs.h"
extern loff_t noop_llseek(struct file *file , loff_t offset , int origin ) ;
# 191 "include/linux/usb.h"
__inline static void *usb_get_intfdata(struct usb_interface *intf ) __attribute__((__ldv_model__)) ;
# 191 "include/linux/usb.h"
__inline static void *usb_get_intfdata(struct usb_interface *intf ) __attribute__((__ldv_model__)) ;
# 191 "include/linux/usb.h"
__inline static void *usb_get_intfdata(struct usb_interface *intf )
{ void *tmp___7 ;

  {
  {
# 193 "include/linux/usb.h"
  tmp___7 = dev_get_drvdata((struct device const *)(& intf->dev));
  }
# 193 "include/linux/usb.h"
  return (tmp___7);
}
}
# 196 "include/linux/usb.h"
__inline static void usb_set_intfdata(struct usb_interface *intf , void *data ) __attribute__((__ldv_model__)) ;
# 196 "include/linux/usb.h"
__inline static void usb_set_intfdata(struct usb_interface *intf , void *data ) __attribute__((__ldv_model__)) ;
# 196 "include/linux/usb.h"
__inline static void usb_set_intfdata(struct usb_interface *intf , void *data )
{

  {
  {
# 198 "include/linux/usb.h"
  dev_set_drvdata(& intf->dev, data);
  }
# 199 "include/linux/usb.h"
  return;
}
}
# 497 "include/linux/usb.h"
__inline static struct usb_device *interface_to_usbdev(struct usb_interface *intf )
{ struct device const *__mptr ;

  {
# 499 "include/linux/usb.h"
  __mptr = (struct device const *)intf->dev.parent;
# 499 "include/linux/usb.h"
  return ((struct usb_device *)((char *)__mptr - (unsigned int )(& ((struct usb_device *)0)->dev)));
}
}
# 502 "include/linux/usb.h"
extern struct usb_device *usb_get_dev(struct usb_device *dev ) ;
# 596 "include/linux/usb.h"
extern struct usb_device_id const *usb_match_id(struct usb_interface *interface ,
                                                  struct usb_device_id const *id ) ;
# 601 "include/linux/usb.h"
extern struct usb_interface *usb_find_interface(struct usb_driver *drv , int minor ) ;
# 929 "include/linux/usb.h"
extern int usb_register_driver(struct usb_driver * , struct module * , char const * ) ;
# 931 "include/linux/usb.h"
__inline static int usb_register(struct usb_driver *driver )
{ int tmp___7 ;

  {
  {
# 933 "include/linux/usb.h"
  tmp___7 = usb_register_driver(driver, & __this_module, "lirc_imon");
  }
# 933 "include/linux/usb.h"
  return (tmp___7);
}
}
# 935 "include/linux/usb.h"
extern void usb_deregister(struct usb_driver * ) ;
# 941 "include/linux/usb.h"
extern int usb_register_dev(struct usb_interface *intf , struct usb_class_driver *class_driver ) ;
# 943 "include/linux/usb.h"
extern void usb_deregister_dev(struct usb_interface *intf , struct usb_class_driver *class_driver ) ;
# 1309 "include/linux/usb.h"
__inline static void usb_fill_int_urb(struct urb *urb , struct usb_device *dev , unsigned int pipe ,
                                      void *transfer_buffer , int buffer_length ,
                                      void (*complete_fn)(struct urb * ) , void *context ,
                                      int interval )
{

  {
# 1318 "include/linux/usb.h"
  urb->dev = dev;
# 1319 "include/linux/usb.h"
  urb->pipe = pipe;
# 1320 "include/linux/usb.h"
  urb->transfer_buffer = transfer_buffer;
# 1321 "include/linux/usb.h"
  urb->transfer_buffer_length = (u32 )buffer_length;
# 1322 "include/linux/usb.h"
  urb->complete = complete_fn;
# 1323 "include/linux/usb.h"
  urb->context = context;
# 1324 "include/linux/usb.h"
  if ((unsigned int )dev->speed == 3U) {
# 1325 "include/linux/usb.h"
    urb->interval = 1 << (interval - 1);
  } else
# 1324 "include/linux/usb.h"
  if ((unsigned int )dev->speed == 5U) {
# 1325 "include/linux/usb.h"
    urb->interval = 1 << (interval - 1);
  } else {
# 1327 "include/linux/usb.h"
    urb->interval = interval;
  }
# 1328 "include/linux/usb.h"
  urb->start_frame = -1;
# 1329 "include/linux/usb.h"
  return;
}
}
# 1332 "include/linux/usb.h"
struct urb *usb_alloc_urb(int iso_packets , gfp_t mem_flags ) __attribute__((__ldv_model__)) ;
# 1333 "include/linux/usb.h"
void usb_free_urb(struct urb *urb ) __attribute__((__ldv_model__)) ;
# 1336 "include/linux/usb.h"
extern int usb_submit_urb(struct urb *urb , gfp_t mem_flags ) ;
# 1338 "include/linux/usb.h"
extern void usb_kill_urb(struct urb *urb ) ;
# 1377 "include/linux/usb.h"
void *usb_alloc_coherent(struct usb_device *dev , size_t size , gfp_t mem_flags ,
                         dma_addr_t *dma ) __attribute__((__ldv_model__)) ;
# 1379 "include/linux/usb.h"
void usb_free_coherent(struct usb_device *dev , size_t size , void *addr , dma_addr_t dma ) __attribute__((__ldv_model__)) ;
# 1526 "include/linux/usb.h"
__inline static unsigned int __create_pipe(struct usb_device *dev , unsigned int endpoint )
{

  {
# 1529 "include/linux/usb.h"
  return ((unsigned int )(dev->devnum << 8) | (endpoint << 15));
}
}
# 180 "include/linux/kfifo.h"
__inline static int __attribute__((__warn_unused_result__)) __kfifo_int_must_check_helper(int val )
{

  {
# 183 "include/linux/kfifo.h"
  return (val);
}
}
# 790 "include/linux/kfifo.h"
extern int __kfifo_alloc(struct __kfifo *fifo , unsigned int size , size_t esize ,
                         gfp_t gfp_mask ) ;
# 793 "include/linux/kfifo.h"
extern void __kfifo_free(struct __kfifo *fifo ) ;
# 798 "include/linux/kfifo.h"
extern unsigned int __kfifo_in(struct __kfifo *fifo , void const *buf , unsigned int len ) ;
# 819 "include/linux/kfifo.h"
extern unsigned int __kfifo_in_r(struct __kfifo *fifo , void const *buf , unsigned int len ,
                                 size_t recsize ) ;
# 54 "include/media/lirc_dev.h"
static struct lock_class_key __key___7 ;
# 55 "include/media/lirc_dev.h"
static struct lock_class_key __key___8 ;
# 48 "include/media/lirc_dev.h"
__inline static int lirc_buffer_init(struct lirc_buffer *buf , unsigned int chunk_size ,
                                     unsigned int size )
{ int ret ;
  struct kfifo *__tmp ;
  struct __kfifo *__kfifo ;
  int tmp___7 ;
  int tmp___8 ;
  int tmp ;

  {
  {
# 54 "include/media/lirc_dev.h"
  while (1) {
    while_continue: ;
    {
# 54 "include/media/lirc_dev.h"
    __init_waitqueue_head(& buf->wait_poll, & __key___7);
    }
# 54 "include/media/lirc_dev.h"
    goto while_break;
  }
  while_break___2: ;
  }
  while_break: ;
  {
# 55 "include/media/lirc_dev.h"
  while (1) {
    while_continue___0: ;
    {
# 55 "include/media/lirc_dev.h"
    spinlock_check(& buf->fifo_lock);
    }
    {
# 55 "include/media/lirc_dev.h"
    while (1) {
      while_continue___1: ;
      {
# 55 "include/media/lirc_dev.h"
      __raw_spin_lock_init(& buf->fifo_lock.__annonCompField18.rlock, "&(&buf->fifo_lock)->rlock",
                           & __key___8);
      }
# 55 "include/media/lirc_dev.h"
      goto while_break___1;
    }
    while_break___4: ;
    }
    while_break___1: ;
# 55 "include/media/lirc_dev.h"
    goto while_break___0;
  }
  while_break___3: ;
  }
  while_break___0:
# 56 "include/media/lirc_dev.h"
  buf->chunk_size = chunk_size;
# 57 "include/media/lirc_dev.h"
  buf->size = size;
# 58 "include/media/lirc_dev.h"
  __tmp = & buf->fifo;
# 58 "include/media/lirc_dev.h"
  __kfifo = & __tmp->__annonCompField41.kfifo;
# 58 "include/media/lirc_dev.h"
  if (sizeof(*__tmp) == sizeof(struct __kfifo )) {
    {
# 58 "include/media/lirc_dev.h"
    tmp___7 = __kfifo_alloc(__kfifo, size * chunk_size, sizeof(*(__tmp->__annonCompField41.type)),
                            208U);
# 58 "include/media/lirc_dev.h"
    tmp___8 = tmp___7;
    }
  } else {
# 58 "include/media/lirc_dev.h"
    tmp___8 = -22;
  }
  {
# 58 "include/media/lirc_dev.h"
  tmp = (int )__kfifo_int_must_check_helper(tmp___8);
# 58 "include/media/lirc_dev.h"
  ret = tmp;
  }
# 59 "include/media/lirc_dev.h"
  if (ret == 0) {
# 60 "include/media/lirc_dev.h"
    buf->fifo_initialized = (u8 )1;
  } else {

  }
# 62 "include/media/lirc_dev.h"
  return (ret);
}
}
# 65 "include/media/lirc_dev.h"
__inline static void lirc_buffer_free(struct lirc_buffer *buf )
{ struct kfifo *__tmp ;
  struct __kfifo *__kfifo ;
  int __ret_warn_on ;
  long tmp___7 ;

  {
# 67 "include/media/lirc_dev.h"
  if (buf->fifo_initialized) {
# 68 "include/media/lirc_dev.h"
    __tmp = & buf->fifo;
# 68 "include/media/lirc_dev.h"
    __kfifo = & __tmp->__annonCompField41.kfifo;
# 68 "include/media/lirc_dev.h"
    if (sizeof(*__tmp) == sizeof(struct __kfifo )) {
      {
# 68 "include/media/lirc_dev.h"
      __kfifo_free(__kfifo);
      }
    } else {

    }
# 69 "include/media/lirc_dev.h"
    buf->fifo_initialized = (u8 )0;
  } else {
    {
# 71 "include/media/lirc_dev.h"
    __ret_warn_on = 1;
# 71 "include/media/lirc_dev.h"
    tmp___7 = __builtin_expect((long )(! (! __ret_warn_on)), 0L);
    }
# 71 "include/media/lirc_dev.h"
    if (tmp___7) {
      {
# 71 "include/media/lirc_dev.h"
      warn_slowpath_fmt("include/media/lirc_dev.h", (int const )72, "calling %s on an uninitialized lirc_buffer\n",
                        "lirc_buffer_free");
      }
    } else {

    }
    {
# 71 "include/media/lirc_dev.h"
    __builtin_expect((long )(! (! __ret_warn_on)), 0L);
    }
  }
# 73 "include/media/lirc_dev.h"
  return;
}
}
# 114 "include/media/lirc_dev.h"
__inline static unsigned int lirc_buffer_write(struct lirc_buffer *buf , unsigned char *orig )
{ unsigned int ret ;
  unsigned long __flags ;
  unsigned int __ret ;
  raw_spinlock_t *tmp___7 ;
  struct kfifo *__tmp ;
  unsigned char *__buf ;
  unsigned long __n ;
  size_t __recsize ;
  struct __kfifo *__kfifo ;
  unsigned int tmp___8 ;
  unsigned int tmp___9 ;
  unsigned int tmp___10 ;

  {
  {
# 119 "include/media/lirc_dev.h"
  while (1) {
    while_continue: ;

    {
# 119 "include/media/lirc_dev.h"
    while (1) {
      while_continue___0: ;
      {
# 119 "include/media/lirc_dev.h"
      tmp___7 = spinlock_check(& buf->fifo_lock);
# 119 "include/media/lirc_dev.h"
      __flags = _raw_spin_lock_irqsave(tmp___7);
      }
# 119 "include/media/lirc_dev.h"
      goto while_break___0;
    }
    while_break___2: ;
    }
    while_break___0: ;
# 119 "include/media/lirc_dev.h"
    goto while_break;
  }
  while_break___1: ;
  }
  while_break:
# 119 "include/media/lirc_dev.h"
  __tmp = & buf->fifo;
# 119 "include/media/lirc_dev.h"
  __buf = orig;
# 119 "include/media/lirc_dev.h"
  __n = (unsigned long )buf->chunk_size;
# 119 "include/media/lirc_dev.h"
  __recsize = sizeof(*(__tmp->__annonCompField41.rectype));
# 119 "include/media/lirc_dev.h"
  __kfifo = & __tmp->__annonCompField41.kfifo;
# 119 "include/media/lirc_dev.h"
  if (__recsize) {
    {
# 119 "include/media/lirc_dev.h"
    tmp___8 = __kfifo_in_r(__kfifo, (void const *)__buf, (unsigned int )__n, __recsize);
# 119 "include/media/lirc_dev.h"
    tmp___10 = tmp___8;
    }
  } else {
    {
# 119 "include/media/lirc_dev.h"
    tmp___9 = __kfifo_in(__kfifo, (void const *)__buf, (unsigned int )__n);
# 119 "include/media/lirc_dev.h"
    tmp___10 = tmp___9;
    }
  }
  {
# 119 "include/media/lirc_dev.h"
  __ret = tmp___10;
# 119 "include/media/lirc_dev.h"
  spin_unlock_irqrestore(& buf->fifo_lock, __flags);
# 119 "include/media/lirc_dev.h"
  ret = __ret;
  }
# 122 "include/media/lirc_dev.h"
  return (ret);
}
}
# 202 "include/media/lirc_dev.h"
extern int lirc_register_driver(struct lirc_driver *d ) ;
# 206 "include/media/lirc_dev.h"
extern int lirc_unregister_driver(int minor ) ;
# 52 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static int imon_probe(struct usb_interface *interface , struct usb_device_id const *id ) ;
# 54 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static void imon_disconnect(struct usb_interface *interface ) ;
# 55 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static void usb_rx_callback(struct urb *urb ) ;
# 56 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static void usb_tx_callback(struct urb *urb ) ;
# 59 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static int imon_resume(struct usb_interface *intf ) ;
# 60 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static int imon_suspend(struct usb_interface *intf , pm_message_t message ) ;
# 63 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static int display_open(struct inode *inode , struct file *file ) ;
# 64 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static int display_close(struct inode *inode , struct file *file ) ;
# 67 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static ssize_t vfd_write(struct file *file , char const *buf , size_t n_bytes ,
                         loff_t *pos ) ;
# 71 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static int ir_open(void *data ) ;
# 72 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static void ir_close(void *data ) ;
# 75 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static int imon_init(void) __attribute__((__section__(".init.text"), __no_instrument_function__)) ;
# 76 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static void imon_exit(void) __attribute__((__section__(".exit.text"), __no_instrument_function__)) ;
# 115 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static struct file_operations const display_fops =
# 115 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
     {& __this_module, & noop_llseek, (ssize_t (*)(struct file * , char * , size_t ,
                                                 loff_t * ))0, & vfd_write, (ssize_t (*)(struct kiocb * ,
                                                                                         struct iovec const * ,
                                                                                         unsigned long ,
                                                                                         loff_t ))0,
    (ssize_t (*)(struct kiocb * , struct iovec const * , unsigned long , loff_t ))0,
    (int (*)(struct file * , void * , int (*)(void * , char const * , int , loff_t ,
                                              u64 , unsigned int ) ))0, (unsigned int (*)(struct file * ,
                                                                                            struct poll_table_struct * ))0,
    (long (*)(struct file * , unsigned int , unsigned long ))0, (long (*)(struct file * ,
                                                                            unsigned int ,
                                                                            unsigned long ))0,
    (int (*)(struct file * , struct vm_area_struct * ))0, & display_open, (int (*)(struct file * ,
                                                                                   fl_owner_t id ))0,
    & display_close, (int (*)(struct file * , int datasync ))0, (int (*)(struct kiocb * ,
                                                                         int datasync ))0,
    (int (*)(int , struct file * , int ))0, (int (*)(struct file * , int , struct file_lock * ))0,
    (ssize_t (*)(struct file * , struct page * , int , size_t , loff_t * , int ))0,
    (unsigned long (*)(struct file * , unsigned long , unsigned long , unsigned long ,
                       unsigned long ))0, (int (*)(int ))0, (int (*)(struct file * ,
                                                                       int , struct file_lock * ))0,
    (ssize_t (*)(struct pipe_inode_info * , struct file * , loff_t * , size_t , unsigned int ))0,
    (ssize_t (*)(struct file * , loff_t * , struct pipe_inode_info * , size_t , unsigned int ))0,
    (int (*)(struct file * , long , struct file_lock ** ))0, (long (*)(struct file *file ,
                                                                        int mode ,
                                                                        loff_t offset ,
                                                                        loff_t len ))0};
# 133 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static struct usb_device_id imon_usb_id_table[4] = { {(__u16 )3, (__u16 )2728, (__u16 )32769, (unsigned short)0, (unsigned short)0,
      (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0,
      (unsigned char)0, 0UL},
        {(__u16 )3, (__u16 )1256, (__u16 )65328, (unsigned short)0, (unsigned short)0,
      (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0,
      (unsigned char)0, 0UL},
        {(__u16 )3, (__u16 )2728, (__u16 )65498, (unsigned short)0, (unsigned short)0,
      (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0,
      (unsigned char)0, 0UL},
        {(__u16 )3, (__u16 )5570, (__u16 )65498, (unsigned short)0, (unsigned short)0,
      (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0,
      (unsigned char)0, 0UL}};
# 150 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static struct usb_device_id vfd_proto_6p_list[1] = { {(__u16 )3, (__u16 )5570, (__u16 )65498, (unsigned short)0, (unsigned short)0,
      (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0,
      (unsigned char)0, 0UL}};
# 156 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static struct usb_device_id ir_only_list[2] = { {(__u16 )3, (__u16 )2728, (__u16 )32769, (unsigned short)0, (unsigned short)0,
      (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0,
      (unsigned char)0, 0UL},
        {(__u16 )3, (__u16 )1256, (__u16 )65328, (unsigned short)0, (unsigned short)0,
      (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0,
      (unsigned char)0, 0UL}};
# 163 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static struct usb_driver imon_driver =
# 163 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
     {"lirc_imon", & imon_probe, & imon_disconnect, (int (*)(struct usb_interface *intf ,
                                                           unsigned int code , void *buf ))0,
    & imon_suspend, & imon_resume, (int (*)(struct usb_interface *intf ))0, (int (*)(struct usb_interface *intf ))0,
    (int (*)(struct usb_interface *intf ))0, (struct usb_device_id const *)(imon_usb_id_table),
    {{{{{0U}, 0U, 0U, (void *)0, {(struct lock_class_key *)0, {(struct lock_class *)0,
                                                               (struct lock_class *)0},
                                  (char const *)0, 0, 0UL}}}}, {(struct list_head *)0,
                                                                  (struct list_head *)0}},
    {{(char const *)0, (struct bus_type *)0, (struct module *)0, (char const *)0,
      (_Bool)0, (struct of_device_id const *)0, (int (*)(struct device *dev ))0,
      (int (*)(struct device *dev ))0, (void (*)(struct device *dev ))0, (int (*)(struct device *dev ,
                                                                                  pm_message_t state ))0,
      (int (*)(struct device *dev ))0, (struct attribute_group const **)0, (struct dev_pm_ops const *)0,
      (struct driver_private *)0}, 0}, 0U, 0U, 0U};
# 172 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static struct usb_class_driver imon_class = {(char *)"lcd%d", (char *(*)(struct device *dev , mode_t *mode ))0, & display_fops,
    144};
# 179 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static struct mutex driver_lock = {{1}, {{{{0U}, 3735899821U, 4294967295U, (void *)-1L, {(struct lock_class_key *)0,
                                                          {(struct lock_class *)0,
                                                           (struct lock_class *)0},
                                                          "driver_lock.wait_lock",
                                                          0, 0UL}}}}, {& driver_lock.wait_list,
                                                                       & driver_lock.wait_list},
    (struct task_struct *)0, (char const *)0, (void *)(& driver_lock), {(struct lock_class_key *)0,
                                                                          {(struct lock_class *)0,
                                                                           (struct lock_class *)0},
                                                                          "driver_lock",
                                                                          0, 0UL}};
# 181 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static int debug ;
# 185 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static char const __mod_author185[33] __attribute__((__used__, __unused__, __section__(".modinfo"),
__aligned__(1))) =
# 185 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  { (char const )'a', (char const )'u', (char const )'t', (char const )'h',
        (char const )'o', (char const )'r', (char const )'=', (char const )'V',
        (char const )'e', (char const )'n', (char const )'k', (char const )'y',
        (char const )' ', (char const )'R', (char const )'a', (char const )'j',
        (char const )'u', (char const )' ', (char const )'<', (char const )'d',
        (char const )'e', (char const )'v', (char const )'@', (char const )'v',
        (char const )'e', (char const )'n', (char const )'k', (char const )'y',
        (char const )'.', (char const )'w', (char const )'s', (char const )'>',
        (char const )'\000'};
# 186 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static char const __mod_description186[61] __attribute__((__used__, __unused__,
__section__(".modinfo"), __aligned__(1))) =
# 186 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  { (char const )'d', (char const )'e', (char const )'s', (char const )'c',
        (char const )'r', (char const )'i', (char const )'p', (char const )'t',
        (char const )'i', (char const )'o', (char const )'n', (char const )'=',
        (char const )'D', (char const )'r', (char const )'i', (char const )'v',
        (char const )'e', (char const )'r', (char const )' ', (char const )'f',
        (char const )'o', (char const )'r', (char const )' ', (char const )'S',
        (char const )'o', (char const )'u', (char const )'n', (char const )'d',
        (char const )'G', (char const )'r', (char const )'a', (char const )'p',
        (char const )'h', (char const )' ', (char const )'i', (char const )'M',
        (char const )'O', (char const )'N', (char const )' ', (char const )'M',
        (char const )'u', (char const )'l', (char const )'t', (char const )'i',
        (char const )'M', (char const )'e', (char const )'d', (char const )'i',
        (char const )'a', (char const )' ', (char const )'I', (char const )'R',
        (char const )'/', (char const )'D', (char const )'i', (char const )'s',
        (char const )'p', (char const )'l', (char const )'a', (char const )'y',
        (char const )'\000'};
# 187 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static char const __mod_version187[12] __attribute__((__used__, __unused__, __section__(".modinfo"),
__aligned__(1))) =
# 187 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  { (char const )'v', (char const )'e', (char const )'r', (char const )'s',
        (char const )'i', (char const )'o', (char const )'n', (char const )'=',
        (char const )'0', (char const )'.', (char const )'8', (char const )'\000'};
# 188 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static char const __mod_license188[12] __attribute__((__used__, __unused__, __section__(".modinfo"),
__aligned__(1))) =
# 188 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  { (char const )'l', (char const )'i', (char const )'c', (char const )'e',
        (char const )'n', (char const )'s', (char const )'e', (char const )'=',
        (char const )'G', (char const )'P', (char const )'L', (char const )'\000'};
# 189 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
extern struct usb_device_id const __mod_usb_device_table __attribute__((__unused__,
__alias__("imon_usb_id_table"))) ;
# 190 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static char const __param_str_debug[6] = { (char const )'d', (char const )'e', (char const )'b', (char const )'u',
        (char const )'g', (char const )'\000'};
# 190 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static struct kernel_param const __param_debug __attribute__((__used__, __unused__,
__section__("__param"), __aligned__(sizeof(void *)))) = {__param_str_debug, (struct kernel_param_ops const *)(& param_ops_int), (u16 )420,
    (u16 )0, {(void *)(& debug)}};
# 190 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static char const __mod_debugtype190[19] __attribute__((__used__, __unused__, __section__(".modinfo"),
__aligned__(1))) =
# 190 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  { (char const )'p', (char const )'a', (char const )'r', (char const )'m',
        (char const )'t', (char const )'y', (char const )'p', (char const )'e',
        (char const )'=', (char const )'d', (char const )'e', (char const )'b',
        (char const )'u', (char const )'g', (char const )':', (char const )'i',
        (char const )'n', (char const )'t', (char const )'\000'};
# 191 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static char const __mod_debug191[52] __attribute__((__used__, __unused__, __section__(".modinfo"),
__aligned__(1))) =
# 191 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  { (char const )'p', (char const )'a', (char const )'r', (char const )'m',
        (char const )'=', (char const )'d', (char const )'e', (char const )'b',
        (char const )'u', (char const )'g', (char const )':', (char const )'D',
        (char const )'e', (char const )'b', (char const )'u', (char const )'g',
        (char const )' ', (char const )'m', (char const )'e', (char const )'s',
        (char const )'s', (char const )'a', (char const )'g', (char const )'e',
        (char const )'s', (char const )':', (char const )' ', (char const )'0',
        (char const )'=', (char const )'n', (char const )'o', (char const )',',
        (char const )' ', (char const )'1', (char const )'=', (char const )'y',
        (char const )'e', (char const )'s', (char const )'(', (char const )'d',
        (char const )'e', (char const )'f', (char const )'a', (char const )'u',
        (char const )'l', (char const )'t', (char const )':', (char const )' ',
        (char const )'n', (char const )'o', (char const )')', (char const )'\000'};
# 203 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static void free_imon_context(struct imon_context *context ) ;
# 203 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static struct _ddebug descriptor __attribute__((__used__, __section__("__verbose"),
__aligned__(8))) = {"lirc_imon", "free_imon_context", "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c",
    "%s: iMON context freed\n", 203U, 0U, (char)0};
# 193 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static void free_imon_context(struct imon_context *context )
{ struct device *dev ;
  long tmp___7 ;

  {
  {
# 195 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  dev = (context->driver)->dev;
# 196 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  usb_free_urb(context->tx_urb);
# 197 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  usb_free_urb(context->rx_urb);
# 198 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  lirc_buffer_free((context->driver)->rbuf);
# 199 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  kfree((void const *)(context->driver)->rbuf);
# 200 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  kfree((void const *)context->driver);
# 201 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  kfree((void const *)context);
  }
  {
# 203 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  while (1) {
    while_continue: ;

    {
# 203 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    while (1) {
      while_continue___0: ;
      {
# 203 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      tmp___7 = __builtin_expect((long )(! (! descriptor.enabled)), 0L);
      }
# 203 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      if (tmp___7) {
        {
# 203 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        dev_printk("<7>", (struct device const *)dev, "%s: iMON context freed\n",
                   "free_imon_context");
        }
      } else {

      }
# 203 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto while_break___0;
    }
    while_break___2: ;
    }
    while_break___0: ;
# 203 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto while_break;
  }
  while_break___1: ;
  }
  while_break: ;
# 204 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return;
}
}
# 206 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static void deregister_from_lirc(struct imon_context *context )
{ int retval ;
  int minor ;

  {
  {
# 209 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  minor = (context->driver)->minor;
# 211 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  retval = lirc_unregister_driver(minor);
  }
# 212 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (retval) {
    {
# 213 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: unable to deregister from lirc(%d)\n", "deregister_from_lirc",
           retval);
    }
  } else {
    {
# 216 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<6>lirc_imon: Deregistered iMON driver (minor:%d)\n", minor);
    }
  }
# 219 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return;
}
}
# 225 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static int display_open(struct inode *inode , struct file *file )
{ struct usb_interface *interface ;
  struct imon_context *context ;
  int subminor ;
  int retval ;
  unsigned int tmp___7 ;
  void *tmp___8 ;

  {
  {
# 228 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context = (struct imon_context *)((void *)0);
# 230 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  retval = 0;
# 233 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  mutex_lock_nested(& driver_lock, 0U);
# 235 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp___7 = iminor((struct inode const *)inode);
# 235 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  subminor = (int )tmp___7;
# 236 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  interface = usb_find_interface(& imon_driver, subminor);
  }
# 237 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! interface) {
    {
# 238 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: could not find interface for minor %d\n", "display_open",
           subminor);
# 240 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    retval = -19;
    }
# 241 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto exit;
  } else {

  }
  {
# 243 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp___8 = usb_get_intfdata(interface);
# 243 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context = (struct imon_context *)tmp___8;
  }
# 245 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! context) {
    {
# 246 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: no context found for minor %d\n", "display_open", subminor);
# 248 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    retval = -19;
    }
# 249 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto exit;
  } else {

  }
  {
# 252 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  mutex_lock_nested(& context->ctx_lock, 0U);
  }
# 254 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! context->display) {
    {
# 255 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: display not supported by device\n", "display_open");
# 256 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    retval = -19;
    }
  } else
# 257 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (context->display_isopen) {
    {
# 258 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: display port is already open\n", "display_open");
# 259 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    retval = -16;
    }
  } else {
    {
# 261 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    context->display_isopen = 1;
# 262 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    file->private_data = (void *)context;
# 263 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    _dev_info((struct device const *)(context->driver)->dev, "display port opened\n");
    }
  }
  {
# 266 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  mutex_unlock(& context->ctx_lock);
  }
  exit:
  {
# 269 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  mutex_unlock(& driver_lock);
  }
# 270 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return (retval);
}
}
# 277 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static int display_close(struct inode *inode , struct file *file )
{ struct imon_context *context ;
  int retval ;

  {
# 279 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context = (struct imon_context *)((void *)0);
# 280 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  retval = 0;
# 282 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context = (struct imon_context *)file->private_data;
# 284 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! context) {
    {
# 285 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: no context for device\n", "display_close");
    }
# 286 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    return (-19);
  } else {

  }
  {
# 289 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  mutex_lock_nested(& context->ctx_lock, 0U);
  }
# 291 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! context->display) {
    {
# 292 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: display not supported by device\n", "display_close");
# 293 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    retval = -19;
    }
  } else
# 294 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! context->display_isopen) {
    {
# 295 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: display is not open\n", "display_close");
# 296 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    retval = -5;
    }
  } else {
    {
# 298 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    context->display_isopen = 0;
# 299 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    _dev_info((struct device const *)(context->driver)->dev, "display port closed\n");
    }
# 300 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (! context->dev_present) {
# 300 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      if (! context->ir_isopen) {
        {
# 306 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        mutex_unlock(& context->ctx_lock);
# 307 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        free_imon_context(context);
        }
# 308 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        return (retval);
      } else {

      }
    } else {

    }
  }
  {
# 312 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  mutex_unlock(& context->ctx_lock);
  }
# 313 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return (retval);
}
}
# 320 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static int send_packet(struct imon_context *context )
{ unsigned int pipe ;
  int interval ;
  int retval ;
  unsigned int tmp___7 ;

  {
  {
# 323 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  interval = 0;
# 324 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  retval = 0;
# 327 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp___7 = __create_pipe(context->usbdev, (unsigned int )(context->tx_endpoint)->bEndpointAddress);
# 327 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  pipe = (unsigned int )(1 << 30) | tmp___7;
# 329 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  interval = (int )(context->tx_endpoint)->bInterval;
# 331 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  usb_fill_int_urb(context->tx_urb, context->usbdev, pipe, (void *)(context->usb_tx_buf),
                   (int )sizeof(context->usb_tx_buf), & usb_tx_callback, (void *)context,
                   interval);
# 336 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  (context->tx_urb)->actual_length = (u32 )0;
# 338 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  init_completion(& context->tx.finished);
# 339 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  atomic_set(& context->tx.busy, 1);
# 341 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  retval = usb_submit_urb(context->tx_urb, 208U);
  }
# 342 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (retval) {
    {
# 343 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    atomic_set(& context->tx.busy, 0);
# 344 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: error submitting urb(%d)\n", "send_packet", retval);
    }
  } else {
    {
# 347 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    mutex_unlock(& context->ctx_lock);
# 348 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    retval = wait_for_completion_interruptible(& context->tx.finished);
    }
# 350 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (retval) {
      {
# 351 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      printk("<3>lirc_imon: %s: task interrupted\n", "send_packet");
      }
    } else {

    }
    {
# 352 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    mutex_lock_nested(& context->ctx_lock, 0U);
# 354 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    retval = context->tx.status;
    }
# 355 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (retval) {
      {
# 356 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      printk("<3>lirc_imon: %s: packet tx failed (%d)\n", "send_packet", retval);
      }
    } else {

    }
  }
# 359 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return (retval);
}
}
# 373 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static ssize_t vfd_write(struct file *file , char const *buf , size_t n_bytes ,
                         loff_t *pos )
{ int i ;
  int offset ;
  int seq ;
  int retval ;
  struct imon_context *context ;
  unsigned char vfd_packet6[7] ;
  int *data_buf ;
  void *tmp___7 ;
  long tmp___8 ;
  long tmp___9 ;
  size_t __len ;
  void *__ret ;
  size_t __len___0 ;
  void *__ret___0 ;
  size_t __len___1 ;
  void *__ret___1 ;
  size_t tmp___10 ;
  long tmp ;
  long tmp___11 ;

  {
# 379 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  retval = 0;
# 381 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  vfd_packet6[0] = (unsigned char)1;
# 381 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  vfd_packet6[1] = (unsigned char)0;
# 381 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  vfd_packet6[2] = (unsigned char)0;
# 381 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  vfd_packet6[3] = (unsigned char)0;
# 381 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  vfd_packet6[4] = (unsigned char)0;
# 381 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  vfd_packet6[5] = (unsigned char)255;
# 381 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  vfd_packet6[6] = (unsigned char)255;
# 383 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  data_buf = (int *)((void *)0);
# 385 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context = (struct imon_context *)file->private_data;
# 386 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! context) {
    {
# 387 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: no context for device\n", "vfd_write");
    }
# 388 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    return ((ssize_t )-19);
  } else {

  }
  {
# 391 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  mutex_lock_nested(& context->ctx_lock, 0U);
  }
# 393 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! context->dev_present) {
    {
# 394 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: no iMON device present\n", "vfd_write");
# 395 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    retval = -19;
    }
# 396 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto exit;
  } else {

  }
# 399 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (n_bytes <= 0UL) {
    {
# 400 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: invalid payload size\n", "vfd_write");
# 401 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    retval = -22;
    }
# 402 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto exit;
  } else
# 399 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (n_bytes > 32UL) {
    {
# 400 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: invalid payload size\n", "vfd_write");
# 401 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    retval = -22;
    }
# 402 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto exit;
  } else {

  }
  {
# 405 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp___7 = memdup_user((void const *)buf, n_bytes);
# 405 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  data_buf = (int *)tmp___7;
# 406 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp = (long )IS_ERR((void const *)data_buf);
# 406 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp___9 = tmp;
  }
# 406 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (tmp___9) {
    {
# 407 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    tmp___11 = (long )PTR_ERR((void const *)data_buf);
# 407 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    tmp___8 = tmp___11;
# 407 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    retval = (int )tmp___8;
    }
# 408 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto exit;
  } else {

  }
  {
# 411 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  __len = n_bytes;
# 411 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  __ret = __builtin_memcpy((void *)(context->tx.data_buf), (void const *)data_buf,
                           __len);
# 414 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  i = (int )n_bytes;
  }
  {
# 414 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  while (1) {
    while_continue: ;
# 414 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (i < 32) {

    } else {
# 414 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto while_break;
    }
# 415 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    context->tx.data_buf[i] = (unsigned char )' ';
# 414 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    i = i + 1;
  }
  while_break___2: ;
  }
  while_break:
# 417 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  i = 32;
  {
# 417 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  while (1) {
    while_continue___0: ;
# 417 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (i < 35) {

    } else {
# 417 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto while_break___0;
    }
# 418 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    context->tx.data_buf[i] = (unsigned char)255;
# 417 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    i = i + 1;
  }
  while_break___3: ;
  }
  while_break___0:
# 420 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  offset = 0;
# 421 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  seq = 0;
  {
# 423 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  while (1) {
    while_continue___1: ;
# 424 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    __len___0 = (size_t )7;
# 424 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (__len___0 >= 64UL) {
      {
# 424 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      __ret___0 = __memcpy((void *)(context->usb_tx_buf), (void const *)(context->tx.data_buf + offset),
                           __len___0);
      }
    } else {
      {
# 424 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      __ret___0 = __builtin_memcpy((void *)(context->usb_tx_buf), (void const *)(context->tx.data_buf + offset),
                                   __len___0);
      }
    }
    {
# 425 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    context->usb_tx_buf[7] = (unsigned char )seq;
# 427 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    retval = send_packet(context);
    }
# 428 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (retval) {
      {
# 429 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      printk("<3>lirc_imon: %s: send packet failed for packet #%d\n", "vfd_write",
             seq / 2);
      }
# 431 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto exit;
    } else {
# 433 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      seq = seq + 2;
# 434 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      offset = offset + 7;
    }
# 423 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (offset < 35) {

    } else {
# 423 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto while_break___1;
    }
  }
  while_break___4: ;
  }
  while_break___1: ;
# 439 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (context->vfd_proto_6p) {
# 441 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    __len___1 = sizeof(vfd_packet6);
# 441 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (__len___1 >= 64UL) {
      {
# 441 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      __ret___1 = __memcpy((void *)(context->usb_tx_buf), (void const *)(& vfd_packet6),
                           __len___1);
      }
    } else {
      {
# 441 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      __ret___1 = __builtin_memcpy((void *)(context->usb_tx_buf), (void const *)(& vfd_packet6),
                                   __len___1);
      }
    }
    {
# 442 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    context->usb_tx_buf[7] = (unsigned char )seq;
# 443 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    retval = send_packet(context);
    }
# 444 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (retval) {
      {
# 445 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      printk("<3>lirc_imon: %s: send packet failed for packet #%d\n", "vfd_write",
             seq / 2);
      }
    } else {

    }
  } else {

  }
  exit:
  {
# 450 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  mutex_unlock(& context->ctx_lock);
# 451 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  kfree((void const *)data_buf);
  }
# 453 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! retval) {
# 453 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    tmp___10 = n_bytes;
  } else {
# 453 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    tmp___10 = (size_t )retval;
  }
# 453 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return ((ssize_t )tmp___10);
}
}
# 459 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static void usb_tx_callback(struct urb *urb )
{ struct imon_context *context ;

  {
# 463 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! urb) {
# 464 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    return;
  } else {

  }
# 465 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context = (struct imon_context *)urb->context;
# 466 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! context) {
# 467 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    return;
  } else {

  }
  {
# 469 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context->tx.status = urb->status;
# 472 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  atomic_set(& context->tx.busy, 0);
# 473 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  complete(& context->tx.finished);
  }
# 475 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return;
}
}
# 481 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static int ir_open(void *data )
{ int retval ;
  struct imon_context *context ;

  {
  {
# 483 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  retval = 0;
# 487 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  mutex_lock_nested(& driver_lock, 0U);
# 489 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context = (struct imon_context *)data;
# 492 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context->rx.count = 0;
# 493 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context->rx.initial_space = 1;
# 494 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context->rx.prev_bit = 0;
# 496 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context->ir_isopen = 1;
# 497 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  _dev_info((struct device const *)(context->driver)->dev, "IR port opened\n");
# 499 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  mutex_unlock(& driver_lock);
  }
# 500 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return (retval);
}
}
# 506 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static void ir_close(void *data )
{ struct imon_context *context ;

  {
# 510 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context = (struct imon_context *)data;
# 511 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! context) {
    {
# 512 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: no context for device\n", "ir_close");
    }
# 513 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    return;
  } else {

  }
  {
# 516 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  mutex_lock_nested(& context->ctx_lock, 0U);
# 518 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context->ir_isopen = 0;
# 519 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  _dev_info((struct device const *)(context->driver)->dev, "IR port closed\n");
  }
# 521 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! context->dev_present) {
    {
# 526 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    deregister_from_lirc(context);
    }
# 528 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (! context->display_isopen) {
      {
# 529 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      mutex_unlock(& context->ctx_lock);
# 530 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      free_imon_context(context);
      }
# 531 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      return;
    } else {

    }
  } else {

  }
  {
# 539 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  mutex_unlock(& context->ctx_lock);
  }
# 540 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return;
}
}
# 553 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static void submit_data(struct imon_context *context ) ;
# 553 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static struct _ddebug descriptor___0 __attribute__((__used__, __section__("__verbose"),
__aligned__(8))) = {"lirc_imon", "submit_data", "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c",
    "submitting data to LIRC\n", 553U, 0U, (char)0};
# 547 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static void submit_data(struct imon_context *context )
{ unsigned char buf[4] ;
  int value ;
  int i ;
  long tmp___7 ;

  {
# 550 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  value = context->rx.count;
  {
# 553 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  while (1) {
    while_continue: ;

    {
# 553 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    while (1) {
      while_continue___0: ;
      {
# 553 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      tmp___7 = __builtin_expect((long )(! (! descriptor___0.enabled)), 0L);
      }
# 553 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      if (tmp___7) {
        {
# 553 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        dev_printk("<7>", (struct device const *)(context->driver)->dev, "submitting data to LIRC\n");
        }
      } else {

      }
# 553 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto while_break___0;
    }
    while_break___3: ;
    }
    while_break___0: ;
# 553 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto while_break;
  }
  while_break___2: ;
  }
  while_break:
# 555 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  value = value * 250;
# 556 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  value = value & 16777215;
# 557 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (context->rx.prev_bit) {
# 558 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    value = value | 16777216;
  } else {

  }
# 560 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  i = 0;
  {
# 560 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  while (1) {
    while_continue___1: ;
# 560 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (i < 4) {

    } else {
# 560 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto while_break___1;
    }
# 561 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    buf[i] = (unsigned char )(value >> i * 8);
# 560 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    i = i + 1;
  }
  while_break___4: ;
  }
  while_break___1:
  {
# 563 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  lirc_buffer_write((context->driver)->rbuf, buf);
# 564 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  __wake_up(& ((context->driver)->rbuf)->wait_poll, 3U, 1, (void *)0);
  }
# 565 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return;
}
}
# 594 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static void imon_incoming_packet(struct imon_context *context , struct urb *urb ,
                                 int intf )
{ int len ;
  unsigned char *buf ;
  struct device *dev ;
  int octet ;
  int bit ;
  unsigned char mask ;
  int i ;
  int curr_bit ;

  {
# 597 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  len = (int )urb->actual_length;
# 598 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  buf = (unsigned char *)urb->transfer_buffer;
# 599 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  dev = (context->driver)->dev;
# 607 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! context->ir_isopen) {
# 608 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    return;
  } else {

  }
# 610 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (len != 8) {
    {
# 611 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    dev_warn((struct device const *)dev, "imon %s: invalid incoming packet size (len = %d, intf%d)\n",
             "imon_incoming_packet", len, intf);
    }
# 613 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    return;
  } else {

  }
# 616 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (debug) {
    {
# 617 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<6>raw packet: ");
# 618 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    i = 0;
    }
    {
# 618 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    while (1) {
      while_continue: ;
# 618 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      if (i < len) {

      } else {
# 618 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        goto while_break;
      }
      {
# 619 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      printk("%02x ", (int )*(buf + i));
# 618 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      i = i + 1;
      }
    }
    while_break___2: ;
    }
    while_break:
    {
# 620 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("\n");
    }
  } else {

  }
# 637 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if ((int )*(buf + 7) == 1) {
# 637 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (context->rx.initial_space) {
      {
# 639 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      context->rx.prev_bit = 0;
# 640 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      context->rx.count = 4;
# 641 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      submit_data(context);
# 642 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      context->rx.count = 0;
      }
    } else {

    }
  } else {

  }
# 645 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  octet = 0;
  {
# 645 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  while (1) {
    while_continue___0: ;
# 645 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (octet < 5) {

    } else {
# 645 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto while_break___0;
    }
# 646 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    mask = (unsigned char)128;
# 647 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    bit = 0;
    {
# 647 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    while (1) {
      while_continue___1: ;
# 647 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      if (bit < 8) {

      } else {
# 647 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        goto while_break___1;
      }
# 648 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      curr_bit = ! ((int )*(buf + octet) & (int )mask);
# 649 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      if (curr_bit != context->rx.prev_bit) {
# 650 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        if (context->rx.count) {
          {
# 651 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          submit_data(context);
# 652 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          context->rx.count = 0;
          }
        } else {

        }
# 654 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        context->rx.prev_bit = curr_bit;
      } else {

      }
# 656 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      context->rx.count = context->rx.count + 1;
# 657 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      mask = (unsigned char )((int )mask >> 1);
# 647 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      bit = bit + 1;
    }
    while_break___4: ;
    }
    while_break___1:
# 645 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    octet = octet + 1;
  }
  while_break___3: ;
  }
  while_break___0: ;
# 661 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if ((int )*(buf + 7) == 10) {
# 662 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (context->rx.count) {
      {
# 663 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      submit_data(context);
# 664 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      context->rx.count = 0;
      }
    } else {

    }
# 666 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    context->rx.initial_space = context->rx.prev_bit;
  } else {

  }
# 668 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return;
}
}
# 673 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static void usb_rx_callback(struct urb *urb )
{ struct imon_context *context ;
  int intfnum ;

  {
# 676 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  intfnum = 0;
# 678 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! urb) {
# 679 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    return;
  } else {

  }
# 681 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context = (struct imon_context *)urb->context;
# 682 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! context) {
# 683 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    return;
  } else {

  }
# 686 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (urb->status == -2) {
# 686 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto case_neg_2;
  } else
# 689 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (urb->status == 0) {
# 689 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto case_0;
  } else {
# 693 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto switch_default;
# 685 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (0) {
      case_neg_2:
# 687 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      return;
      case_0:
      {
# 690 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      imon_incoming_packet(context, urb, intfnum);
      }
# 691 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto switch_break;
      switch_default:
      {
# 694 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      dev_warn((struct device const *)(context->driver)->dev, "imon %s: status(%d): ignored\n",
               "usb_rx_callback", urb->status);
      }
# 696 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto switch_break;
    } else {
      switch_break: ;
    }
  }
  {
# 699 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  usb_submit_urb(context->rx_urb, 32U);
  }
# 701 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return;
}
}
# 754 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static struct _ddebug descriptor___1 __attribute__((__used__, __section__("__verbose"),
__aligned__(8))) = {"lirc_imon", "imon_probe", "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c",
    "%s: found iMON device (%04x:%04x, intf%d)\n", 755U, 0U, (char)0};
# 779 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static struct _ddebug descriptor___2 __attribute__((__used__, __section__("__verbose"),
__aligned__(8))) = {"lirc_imon", "imon_probe", "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c",
    "%s: found IR endpoint\n", 779U, 0U, (char)0};
# 785 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static struct _ddebug descriptor___3 __attribute__((__used__, __section__("__verbose"),
__aligned__(8))) = {"lirc_imon", "imon_probe", "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c",
    "%s: found display endpoint\n", 785U, 0U, (char)0};
# 796 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static struct _ddebug descriptor___4 __attribute__((__used__, __section__("__verbose"),
__aligned__(8))) = {"lirc_imon", "imon_probe", "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c",
    "%s: device has no display\n", 796U, 0U, (char)0};
# 812 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static struct _ddebug descriptor___5 __attribute__((__used__, __section__("__verbose"),
__aligned__(8))) = {"lirc_imon", "imon_probe", "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c",
    "%s: vfd_proto_6p: %d\n", 813U, 0U, (char)0};
# 847 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static struct lock_class_key __key___9 ;
# 913 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static struct _ddebug descriptor___6 __attribute__((__used__, __section__("__verbose"),
__aligned__(8))) = {"lirc_imon", "imon_probe", "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c",
    "%s: Registering iMON display with sysfs\n", 914U, 0U, (char)0};
# 707 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static int imon_probe(struct usb_interface *interface , struct usb_device_id const *id )
{ struct usb_device *usbdev ;
  struct usb_host_interface *iface_desc ;
  struct usb_endpoint_descriptor *rx_endpoint ;
  struct usb_endpoint_descriptor *tx_endpoint ;
  struct urb *rx_urb ;
  struct urb *tx_urb ;
  struct lirc_driver *driver ;
  struct lirc_buffer *rbuf ;
  struct device *dev ;
  int ifnum ;
  int lirc_minor ;
  int num_endpts ;
  int retval ;
  int display_ep_found ;
  int ir_ep_found ;
  int alloc_status ;
  int vfd_proto_6p ;
  struct imon_context *context ;
  int i ;
  u16 vendor ;
  u16 product ;
  void *tmp___7 ;
  struct usb_device_id const *tmp___8 ;
  struct usb_device *tmp___9 ;
  long tmp___10 ;
  struct usb_endpoint_descriptor *ep ;
  int ep_dir ;
  int ep_type ;
  long tmp___11 ;
  long tmp___12 ;
  long tmp___13 ;
  struct usb_device_id const *tmp___14 ;
  long tmp___15 ;
  void *tmp___16 ;
  void *tmp___17 ;
  int tmp___18 ;
  unsigned int tmp___19 ;
  long tmp___20 ;
  int tmp___21 ;

  {
  {
# 710 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  usbdev = (struct usb_device *)((void *)0);
# 711 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  iface_desc = (struct usb_host_interface *)((void *)0);
# 712 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  rx_endpoint = (struct usb_endpoint_descriptor *)((void *)0);
# 713 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tx_endpoint = (struct usb_endpoint_descriptor *)((void *)0);
# 714 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  rx_urb = (struct urb *)((void *)0);
# 715 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tx_urb = (struct urb *)((void *)0);
# 716 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  driver = (struct lirc_driver *)((void *)0);
# 717 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  rbuf = (struct lirc_buffer *)((void *)0);
# 718 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  dev = & interface->dev;
# 720 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  lirc_minor = 0;
# 722 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  retval = 0;
# 723 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  display_ep_found = 0;
# 724 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  ir_ep_found = 0;
# 725 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  alloc_status = 0;
# 726 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  vfd_proto_6p = 0;
# 727 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context = (struct imon_context *)((void *)0);
# 731 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp___7 = kzalloc(sizeof(struct imon_context ), 208U);
# 731 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context = (struct imon_context *)tmp___7;
  }
# 732 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! context) {
    {
# 733 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: kzalloc failed for context\n", "imon_probe");
# 734 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    alloc_status = 1;
    }
# 735 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto alloc_status_switch;
  } else {

  }
  {
# 742 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp___8 = usb_match_id(interface, (struct usb_device_id const *)(ir_only_list));
  }
# 742 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (tmp___8) {
# 743 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    context->display = 0;
  } else {
# 745 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    context->display = 1;
  }
  {
# 747 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp___9 = interface_to_usbdev(interface);
# 747 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  usbdev = usb_get_dev(tmp___9);
# 748 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  iface_desc = interface->cur_altsetting;
# 749 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  num_endpts = (int )iface_desc->desc.bNumEndpoints;
# 750 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  ifnum = (int )iface_desc->desc.bInterfaceNumber;
# 751 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  vendor = usbdev->descriptor.idVendor;
# 752 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  product = usbdev->descriptor.idProduct;
  }
  {
# 754 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  while (1) {
    while_continue: ;

    {
# 754 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    while (1) {
      while_continue___0: ;
      {
# 754 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      tmp___10 = __builtin_expect((long )(! (! descriptor___1.enabled)), 0L);
      }
# 754 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      if (tmp___10) {
        {
# 754 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        dev_printk("<7>", (struct device const *)dev, "%s: found iMON device (%04x:%04x, intf%d)\n",
                   "imon_probe", (int )vendor, (int )product, ifnum);
        }
      } else {

      }
# 754 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto while_break___0;
    }
    while_break___14: ;
    }
    while_break___0: ;
# 754 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto while_break;
  }
  while_break___13: ;
  }
  while_break:
  {
# 758 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  mutex_lock_nested(& driver_lock, 0U);
# 765 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  i = 0;
  }
  {
# 765 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  while (1) {
    while_continue___1: ;
# 765 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (i < num_endpts) {
# 765 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      if (ir_ep_found) {
# 765 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        if (display_ep_found) {
# 765 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          goto while_break___1;
        } else {

        }
      } else {

      }
    } else {
# 765 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto while_break___1;
    }
# 769 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    ep = & (iface_desc->endpoint + i)->desc;
# 770 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    ep_dir = (int )ep->bEndpointAddress & 128;
# 771 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    ep_type = (int )ep->bmAttributes & 3;
# 773 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (! ir_ep_found) {
# 773 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      if (ep_dir == 128) {
# 773 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        if (ep_type == 3) {
# 777 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          rx_endpoint = ep;
# 778 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          ir_ep_found = 1;
          {
# 779 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          while (1) {
            while_continue___2: ;

            {
# 779 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
            while (1) {
              while_continue___3: ;
              {
# 779 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
              tmp___11 = __builtin_expect((long )(! (! descriptor___2.enabled)), 0L);
              }
# 779 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
              if (tmp___11) {
                {
# 779 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
                dev_printk("<7>", (struct device const *)dev, "%s: found IR endpoint\n",
                           "imon_probe");
                }
              } else {

              }
# 779 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
              goto while_break___3;
            }
            while_break___17: ;
            }
            while_break___3: ;
# 779 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
            goto while_break___2;
          }
          while_break___16: ;
          }
          while_break___2: ;
        } else {
# 773 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          goto _L___0;
        }
      } else {
# 773 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        goto _L___0;
      }
    } else
    _L___0:
# 781 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (! display_ep_found) {
# 781 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      if (ep_dir == 0) {
# 781 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        if (ep_type == 3) {
# 783 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          tx_endpoint = ep;
# 784 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          display_ep_found = 1;
          {
# 785 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          while (1) {
            while_continue___4: ;

            {
# 785 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
            while (1) {
              while_continue___5: ;
              {
# 785 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
              tmp___12 = __builtin_expect((long )(! (! descriptor___3.enabled)), 0L);
              }
# 785 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
              if (tmp___12) {
                {
# 785 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
                dev_printk("<7>", (struct device const *)dev, "%s: found display endpoint\n",
                           "imon_probe");
                }
              } else {

              }
# 785 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
              goto while_break___5;
            }
            while_break___19: ;
            }
            while_break___5: ;
# 785 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
            goto while_break___4;
          }
          while_break___18: ;
          }
          while_break___4: ;
        } else {

        }
      } else {

      }
    } else {

    }
# 765 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    i = i + 1;
  }
  while_break___15: ;
  }
  while_break___1: ;
# 794 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (context->display == 0) {
# 795 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    display_ep_found = 0;
    {
# 796 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    while (1) {
      while_continue___6: ;

      {
# 796 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      while (1) {
        while_continue___7: ;
        {
# 796 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        tmp___13 = __builtin_expect((long )(! (! descriptor___4.enabled)), 0L);
        }
# 796 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        if (tmp___13) {
          {
# 796 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          dev_printk("<7>", (struct device const *)dev, "%s: device has no display\n",
                     "imon_probe");
          }
        } else {

        }
# 796 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        goto while_break___7;
      }
      while_break___21: ;
      }
      while_break___7: ;
# 796 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto while_break___6;
    }
    while_break___20: ;
    }
    while_break___6: ;
  } else {

  }
# 800 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! ir_ep_found) {
    {
# 801 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: no valid input (IR) endpoint found.\n", "imon_probe");
# 802 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    retval = -19;
# 803 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    alloc_status = 2;
    }
# 804 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto alloc_status_switch;
  } else {

  }
# 808 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (display_ep_found) {
    {
# 809 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    tmp___14 = usb_match_id(interface, (struct usb_device_id const *)(vfd_proto_6p_list));
    }
# 809 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (tmp___14) {
# 810 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      vfd_proto_6p = 1;
    } else {

    }
    {
# 812 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    while (1) {
      while_continue___8: ;

      {
# 812 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      while (1) {
        while_continue___9: ;
        {
# 812 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        tmp___15 = __builtin_expect((long )(! (! descriptor___5.enabled)), 0L);
        }
# 812 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        if (tmp___15) {
          {
# 812 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          dev_printk("<7>", (struct device const *)dev, "%s: vfd_proto_6p: %d\n",
                     "imon_probe", vfd_proto_6p);
          }
        } else {

        }
# 812 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        goto while_break___9;
      }
      while_break___23: ;
      }
      while_break___9: ;
# 812 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto while_break___8;
    }
    while_break___22: ;
    }
    while_break___8: ;
  } else {

  }
  {
# 816 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp___16 = kzalloc(sizeof(struct lirc_driver ), 208U);
# 816 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  driver = (struct lirc_driver *)tmp___16;
  }
# 817 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! driver) {
    {
# 818 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: kzalloc failed for lirc_driver\n", "imon_probe");
# 819 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    alloc_status = 2;
    }
# 820 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto alloc_status_switch;
  } else {

  }
  {
# 822 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp___17 = kmalloc(sizeof(struct lirc_buffer ), 208U);
# 822 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  rbuf = (struct lirc_buffer *)tmp___17;
  }
# 823 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! rbuf) {
    {
# 824 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: kmalloc failed for lirc_buffer\n", "imon_probe");
# 825 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    alloc_status = 3;
    }
# 826 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto alloc_status_switch;
  } else {

  }
  {
# 828 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp___18 = lirc_buffer_init(rbuf, 4U, 128U);
  }
# 828 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (tmp___18) {
    {
# 829 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: lirc_buffer_init failed\n", "imon_probe");
# 830 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    alloc_status = 4;
    }
# 831 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto alloc_status_switch;
  } else {

  }
  {
# 833 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  rx_urb = usb_alloc_urb(0, 208U);
  }
# 834 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! rx_urb) {
    {
# 835 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: usb_alloc_urb failed for IR urb\n", "imon_probe");
# 836 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    alloc_status = 5;
    }
# 837 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto alloc_status_switch;
  } else {

  }
  {
# 839 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tx_urb = usb_alloc_urb(0, 208U);
  }
# 840 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! tx_urb) {
    {
# 841 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: usb_alloc_urb failed for display urb\n", "imon_probe");
# 843 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    alloc_status = 6;
    }
# 844 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto alloc_status_switch;
  } else {

  }
  {
# 847 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  while (1) {
    while_continue___10: ;
    {
# 847 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    __mutex_init(& context->ctx_lock, "&context->ctx_lock", & __key___9);
    }
# 847 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto while_break___10;
  }
  while_break___24: ;
  }
  while_break___10:
  {
# 848 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context->vfd_proto_6p = vfd_proto_6p;
# 850 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  strcpy(driver->name, "lirc_imon");
# 851 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  driver->minor = -1;
# 852 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  driver->code_length = (__u32 )32;
# 853 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  driver->sample_rate = 0;
# 854 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  driver->features = (__u32 )(4 << 16);
# 855 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  driver->data = (void *)context;
# 856 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  driver->rbuf = rbuf;
# 857 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  driver->set_use_inc = & ir_open;
# 858 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  driver->set_use_dec = & ir_close;
# 859 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  driver->dev = & interface->dev;
# 860 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  driver->owner = & __this_module;
# 862 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  mutex_lock_nested(& context->ctx_lock, 0U);
# 864 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context->driver = driver;
# 867 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  lirc_minor = lirc_register_driver(driver);
  }
# 868 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (lirc_minor < 0) {
    {
# 869 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: lirc_register_driver failed\n", "imon_probe");
# 870 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    alloc_status = 7;
    }
# 871 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto unlock;
  } else {
    {
# 873 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    _dev_info((struct device const *)dev, "Registered iMON driver (lirc minor: %d)\n",
              lirc_minor);
    }
  }
# 877 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  driver->minor = lirc_minor;
# 879 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context->usbdev = usbdev;
# 880 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context->dev_present = 1;
# 881 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context->rx_endpoint = rx_endpoint;
# 882 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context->rx_urb = rx_urb;
# 888 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context->tx_endpoint = tx_endpoint;
# 889 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context->tx_urb = tx_urb;
# 891 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (display_ep_found) {
# 892 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    context->display = 1;
  } else {

  }
  {
# 894 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp___19 = __create_pipe(context->usbdev, (unsigned int )(context->rx_endpoint)->bEndpointAddress);
# 894 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  usb_fill_int_urb(context->rx_urb, context->usbdev, ((unsigned int )(1 << 30) | tmp___19) | 128U,
                   (void *)(context->usb_rx_buf), (int )sizeof(context->usb_rx_buf),
                   & usb_rx_callback, (void *)context, (int )(context->rx_endpoint)->bInterval);
# 901 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  retval = usb_submit_urb(context->rx_urb, 208U);
  }
# 903 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (retval) {
    {
# 904 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: usb_submit_urb failed for intf0 (%d)\n", "imon_probe",
           retval);
# 906 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    mutex_unlock(& context->ctx_lock);
    }
# 907 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto exit;
  } else {

  }
  {
# 910 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  usb_set_intfdata(interface, (void *)context);
  }
# 912 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (context->display) {
# 912 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (ifnum == 0) {
      {
# 913 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      while (1) {
        while_continue___11: ;

        {
# 913 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        while (1) {
          while_continue___12: ;
          {
# 913 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          tmp___20 = __builtin_expect((long )(! (! descriptor___6.enabled)), 0L);
          }
# 913 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          if (tmp___20) {
            {
# 913 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
            dev_printk("<7>", (struct device const *)dev, "%s: Registering iMON display with sysfs\n",
                       "imon_probe");
            }
          } else {

          }
# 913 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          goto while_break___12;
        }
        while_break___26: ;
        }
        while_break___12: ;
# 913 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        goto while_break___11;
      }
      while_break___25: ;
      }
      while_break___11:
      {
# 916 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      tmp___21 = usb_register_dev(interface, & imon_class);
      }
# 916 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      if (tmp___21) {
        {
# 918 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        _dev_info((struct device const *)dev, "%s: could not get a minor number for display\n",
                  "imon_probe");
        }
      } else {

      }
    } else {

    }
  } else {

  }
  {
# 923 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  _dev_info((struct device const *)dev, "iMON device (%04x:%04x, intf%d) on usb<%d:%d> initialized\n",
            (int )vendor, (int )product, ifnum, (usbdev->bus)->busnum, usbdev->devnum);
  }
  unlock:
  {
# 928 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  mutex_unlock(& context->ctx_lock);
  }
  alloc_status_switch:
# 932 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (alloc_status == 7) {
# 932 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto case_7;
  } else
# 934 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (alloc_status == 6) {
# 934 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto case_6;
  } else
# 936 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (alloc_status == 5) {
# 936 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto case_5;
  } else
# 939 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (alloc_status == 4) {
# 939 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto case_4;
  } else
# 941 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (alloc_status == 3) {
# 941 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto case_3;
  } else
# 943 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (alloc_status == 2) {
# 943 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto case_2;
  } else
# 946 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (alloc_status == 1) {
# 946 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto case_1;
  } else
# 950 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (alloc_status == 0) {
# 950 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto case_0;
  } else
# 931 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (0) {
    case_7:
    {
# 933 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    usb_free_urb(tx_urb);
    }
    case_6:
    {
# 935 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    usb_free_urb(rx_urb);
    }
    case_5:
# 937 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (rbuf) {
      {
# 938 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      lirc_buffer_free(rbuf);
      }
    } else {

    }
    case_4:
    {
# 940 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    kfree((void const *)rbuf);
    }
    case_3:
    {
# 942 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    kfree((void const *)driver);
    }
    case_2:
    {
# 944 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    kfree((void const *)context);
# 945 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    context = (struct imon_context *)((void *)0);
    }
    case_1:
# 947 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (retval != -19) {
# 948 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      retval = -12;
    } else {

    }
# 949 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto switch_break;
    case_0:
# 951 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    retval = 0;
  } else {
    switch_break: ;
  }
  exit:
  {
# 955 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  mutex_unlock(& driver_lock);
  }
# 957 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return (retval);
}
}
# 963 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static void imon_disconnect(struct usb_interface *interface )
{ struct imon_context *context ;
  int ifnum ;
  void *tmp___7 ;
  int tmp___8 ;

  {
  {
# 969 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  mutex_lock_nested(& driver_lock, 0U);
# 971 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp___7 = usb_get_intfdata(interface);
# 971 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context = (struct imon_context *)tmp___7;
# 972 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  ifnum = (int )(interface->cur_altsetting)->desc.bInterfaceNumber;
# 974 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  mutex_lock_nested(& context->ctx_lock, 0U);
# 976 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  usb_set_intfdata(interface, (void *)0);
# 979 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp___8 = atomic_read((atomic_t const *)(& context->tx.busy));
  }
# 979 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (tmp___8) {
    {
# 980 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    usb_kill_urb(context->tx_urb);
# 981 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    complete_all(& context->tx.finished);
    }
  } else {

  }
  {
# 984 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context->dev_present = 0;
# 985 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  usb_kill_urb(context->rx_urb);
  }
# 986 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (context->display) {
    {
# 987 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    usb_deregister_dev(interface, & imon_class);
    }
  } else {

  }
# 989 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (! context->ir_isopen) {
# 989 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (! context->dev_present) {
      {
# 990 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      deregister_from_lirc(context);
# 991 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      mutex_unlock(& context->ctx_lock);
      }
# 992 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      if (! context->display_isopen) {
        {
# 993 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        free_imon_context(context);
        }
      } else {

      }
    } else {
      {
# 995 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      mutex_unlock(& context->ctx_lock);
      }
    }
  } else {
    {
# 995 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    mutex_unlock(& context->ctx_lock);
    }
  }
  {
# 997 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  mutex_unlock(& driver_lock);
# 999 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  printk("<6>%s: iMON device (intf%d) disconnected\n", "imon_disconnect", ifnum);
  }
# 1001 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return;
}
}
# 1003 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static int imon_suspend(struct usb_interface *intf , pm_message_t message )
{ struct imon_context *context ;
  void *tmp___7 ;

  {
  {
# 1005 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp___7 = usb_get_intfdata(intf);
# 1005 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context = (struct imon_context *)tmp___7;
# 1007 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  usb_kill_urb(context->rx_urb);
  }
# 1009 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return (0);
}
}
# 1012 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static int imon_resume(struct usb_interface *intf )
{ int rc ;
  struct imon_context *context ;
  void *tmp___7 ;
  unsigned int tmp___8 ;

  {
  {
# 1014 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  rc = 0;
# 1015 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp___7 = usb_get_intfdata(intf);
# 1015 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  context = (struct imon_context *)tmp___7;
# 1017 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp___8 = __create_pipe(context->usbdev, (unsigned int )(context->rx_endpoint)->bEndpointAddress);
# 1017 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  usb_fill_int_urb(context->rx_urb, context->usbdev, ((unsigned int )(1 << 30) | tmp___8) | 128U,
                   (void *)(context->usb_rx_buf), (int )sizeof(context->usb_rx_buf),
                   & usb_rx_callback, (void *)context, (int )(context->rx_endpoint)->bInterval);
# 1024 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  rc = usb_submit_urb(context->rx_urb, 32U);
  }
# 1026 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return (rc);
}
}
# 1029 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static int imon_init(void) __attribute__((__section__(".init.text"), __no_instrument_function__)) ;
# 1029 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static int imon_init(void)
{ int rc ;

  {
  {
# 1033 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  printk("<6>lirc_imon: Driver for SoundGraph iMON MultiMedia IR/Display, v0.8\n");
# 1035 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  rc = usb_register(& imon_driver);
  }
# 1036 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (rc) {
    {
# 1037 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    printk("<3>lirc_imon: %s: usb register failed(%d)\n", "imon_init", rc);
    }
# 1038 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    return (-19);
  } else {

  }
# 1041 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return (0);
}
}
# 1044 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static void imon_exit(void) __attribute__((__section__(".exit.text"), __no_instrument_function__)) ;
# 1044 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static void imon_exit(void)
{

  {
  {
# 1046 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  usb_deregister(& imon_driver);
# 1047 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  printk("<6>lirc_imon: module removed. Goodbye!\n");
  }
# 1048 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return;
}
}
# 1050 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
int init_module(void)
{ int tmp___7 ;

  {
  {
# 1050 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp___7 = imon_init();
  }
# 1050 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return (tmp___7);
}
}
# 1051 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
void cleanup_module(void)
{

  {
  {
# 1051 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  imon_exit();
  }
# 1051 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return;
}
}
# 1069 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
void ldv_check_final_state(void) __attribute__((__ldv_model__)) ;
# 1072 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
extern void ldv_check_return_value(int res ) ;
# 1075 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
extern void ldv_initialize(void) ;
# 1078 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
extern int nondet_int(void) ;
# 1081 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
int LDV_IN_INTERRUPT ;
# 1109 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
static int res_imon_probe_13 ;
# 1084 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
void main(void)
{ struct usb_interface *var_group1 ;
  struct usb_device_id const *var_imon_probe_13_p1 ;
  pm_message_t var_imon_suspend_15_p1 ;
  int tmp___7 ;
  int ldv_s_imon_driver_usb_driver ;
  int tmp___8 ;
  int tmp___9 ;

  {
  {
# 1158 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  LDV_IN_INTERRUPT = 1;
# 1167 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  ldv_initialize();
# 1184 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  tmp___7 = imon_init();
  }
# 1184 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  if (tmp___7) {
# 1185 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    goto ldv_final;
  } else {

  }
# 1186 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  ldv_s_imon_driver_usb_driver = 0;
  {
# 1189 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  while (1) {
    while_continue: ;
    {
# 1189 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    tmp___9 = nondet_int();
    }
# 1189 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (tmp___9) {

    } else
# 1189 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (! (ldv_s_imon_driver_usb_driver == 0)) {

    } else {
# 1189 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto while_break;
    }
    {
# 1193 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    tmp___8 = nondet_int();
    }
# 1195 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (tmp___8 == 0) {
# 1195 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto case_0;
    } else
# 1225 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (tmp___8 == 1) {
# 1225 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto case_1;
    } else
# 1252 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (tmp___8 == 2) {
# 1252 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto case_2;
    } else
# 1279 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
    if (tmp___8 == 3) {
# 1279 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto case_3;
    } else {
# 1306 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      goto switch_default;
# 1193 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
      if (0) {
        case_0:
# 1198 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        if (ldv_s_imon_driver_usb_driver == 0) {
          {
# 1214 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          res_imon_probe_13 = imon_probe(var_group1, var_imon_probe_13_p1);
# 1215 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          ldv_check_return_value(res_imon_probe_13);
          }
# 1216 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          if (res_imon_probe_13) {
# 1217 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
            goto ldv_module_exit;
          } else {

          }
# 1218 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          ldv_s_imon_driver_usb_driver = ldv_s_imon_driver_usb_driver + 1;
        } else {

        }
# 1224 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        goto switch_break;
        case_1:
# 1228 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        if (ldv_s_imon_driver_usb_driver == 1) {
          {
# 1244 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          imon_suspend(var_group1, var_imon_suspend_15_p1);
# 1245 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          ldv_s_imon_driver_usb_driver = ldv_s_imon_driver_usb_driver + 1;
          }
        } else {

        }
# 1251 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        goto switch_break;
        case_2:
# 1255 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        if (ldv_s_imon_driver_usb_driver == 2) {
          {
# 1271 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          imon_resume(var_group1);
# 1272 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          ldv_s_imon_driver_usb_driver = ldv_s_imon_driver_usb_driver + 1;
          }
        } else {

        }
# 1278 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        goto switch_break;
        case_3:
# 1282 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        if (ldv_s_imon_driver_usb_driver == 3) {
          {
# 1298 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          imon_disconnect(var_group1);
# 1299 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
          ldv_s_imon_driver_usb_driver = 0;
          }
        } else {

        }
# 1305 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        goto switch_break;
        switch_default:
# 1306 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
        goto switch_break;
      } else {
        switch_break: ;
      }
    }
  }
  while_break___0: ;
  }
  while_break: ;
  ldv_module_exit:
  {
# 1329 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  imon_exit();
  }
  ldv_final:
  {
# 1332 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  ldv_check_final_state();
  }
# 1335 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/staging/lirc/lirc_imon.c.common.c"
  return;
}
}
# 5 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/engine-blast-assert.h"
void ldv_blast_assert(void)
{

  {
  ERROR:
# 6 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/engine-blast-assert.h"
  goto ERROR;
}
}
# 7 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/engine-blast.h"
extern void *ldv_undefined_pointer(void) ;
# 10 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
void ldv_assume_stop(void) __attribute__((__ldv_model_inline__)) ;
# 22 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
void ldv_assume_stop(void) __attribute__((__ldv_model_inline__)) ;
# 22 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
void ldv_assume_stop(void)
{

  {
  LDV_STOP:
# 23 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
  goto LDV_STOP;
}
}
# 29 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
int ldv_urb_state = 0;
# 31 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
int ldv_coherent_state = 0;
# 62 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
void *usb_alloc_coherent(struct usb_device *dev , size_t size , gfp_t mem_flags ,
                         dma_addr_t *dma ) __attribute__((__ldv_model__)) ;
# 62 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
void *usb_alloc_coherent(struct usb_device *dev , size_t size , gfp_t mem_flags ,
                         dma_addr_t *dma )
{ void *arbitrary_memory ;
  void *tmp___7 ;

  {
  {
# 64 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
  while (1) {
    while_continue: ;
    {
# 64 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    tmp___7 = ldv_undefined_pointer();
# 64 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    arbitrary_memory = tmp___7;
    }
# 64 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    if (! arbitrary_memory) {
# 64 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
      return ((void *)0);
    } else {

    }
# 64 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    ldv_coherent_state = ldv_coherent_state + 1;
# 64 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    return (arbitrary_memory);
# 64 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    goto while_break;
  }
  while_break___0: ;
  }
  while_break: ;
# 65 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
  return ((void *)0);
}
}
# 68 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
void usb_free_coherent(struct usb_device *dev , size_t size , void *addr , dma_addr_t dma ) __attribute__((__ldv_model__)) ;
# 68 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
void usb_free_coherent(struct usb_device *dev , size_t size , void *addr , dma_addr_t dma )
{

  {
  {
# 70 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
  while (1) {
    while_continue: ;
# 70 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    if (! ((unsigned long )addr != (unsigned long )((void *)0))) {
      {
# 70 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
      ldv_assume_stop();
      }
    } else {

    }
# 70 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    if (addr) {
# 70 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
      if (ldv_coherent_state >= 1) {

      } else {
        {
# 70 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
        ldv_blast_assert();
        }
      }
# 70 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
      ldv_coherent_state = ldv_coherent_state - 1;
    } else {

    }
# 70 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    goto while_break;
  }
  while_break___0: ;
  }
  while_break: ;
# 71 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
  return;
}
}
# 74 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
struct urb *usb_alloc_urb(int iso_packets , gfp_t mem_flags ) __attribute__((__ldv_model__)) ;
# 74 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
struct urb *usb_alloc_urb(int iso_packets , gfp_t mem_flags )
{ void *arbitrary_memory ;
  void *tmp___7 ;

  {
  {
# 75 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
  while (1) {
    while_continue: ;
    {
# 75 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    tmp___7 = ldv_undefined_pointer();
# 75 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    arbitrary_memory = tmp___7;
    }
# 75 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    if (! arbitrary_memory) {
# 75 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
      return ((struct urb *)((void *)0));
    } else {

    }
# 75 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    ldv_urb_state = ldv_urb_state + 1;
# 75 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    return ((struct urb *)arbitrary_memory);
# 75 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    goto while_break;
  }
  while_break___0: ;
  }
  while_break: ;
# 76 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
  return ((struct urb *)0);
}
}
# 79 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
void usb_free_urb(struct urb *urb ) __attribute__((__ldv_model__)) ;
# 79 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
void usb_free_urb(struct urb *urb )
{

  {
  {
# 80 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
  while (1) {
    while_continue: ;
# 80 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    if (! ((unsigned long )urb != (unsigned long )((struct urb *)0))) {
      {
# 80 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
      ldv_assume_stop();
      }
    } else {

    }
# 80 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    if (urb) {
# 80 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
      if (ldv_urb_state >= 1) {

      } else {
        {
# 80 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
        ldv_blast_assert();
        }
      }
# 80 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
      ldv_urb_state = ldv_urb_state - 1;
    } else {

    }
# 80 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    goto while_break;
  }
  while_break___0: ;
  }
  while_break: ;
# 81 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
  return;
}
}
# 84 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
void ldv_check_final_state(void) __attribute__((__ldv_model__)) ;
# 84 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
void ldv_check_final_state(void)
{

  {
# 86 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
  if (ldv_urb_state == 0) {

  } else {
    {
# 86 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    ldv_blast_assert();
    }
  }
# 88 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
  if (ldv_coherent_state == 0) {

  } else {
    {
# 88 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
    ldv_blast_assert();
    }
  }
# 89 "/anthill/stuff/tacas-comp/work/current--X--drivers/staging/lirc/lirc_imon.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/kernel-rules/files/model0068.c"
  return;
}
}
