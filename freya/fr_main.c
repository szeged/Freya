
/*--------------------------------------------------------------------*/
/*--- Freya: memory access logger tool.                  fr_main.c ---*/
/*--------------------------------------------------------------------*/

/*
   Copyright (C) 2009-2016 Zoltan Herczeg (University of Szeged)
         zherczeg@inf.u-szeged.hu

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
   02111-1307, USA.

   The GNU General Public License is contained in the file COPYING.

   Help: http://webkit.sed.hu/node/29
*/

#include "pub_tool_basics.h"

#include "pub_tool_mallocfree.h"
#include "pub_tool_replacemalloc.h"
#include "pub_tool_debuginfo.h"
#include "pub_tool_stacktrace.h"

#include "pub_tool_tooliface.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_options.h"
#include "pub_tool_machine.h"
#include "pub_tool_hashtable.h"

#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_libcproc.h"
#include "pub_tool_vki.h"
#include "pub_tool_libcfile.h"
#include "pub_tool_clientstate.h"

#include "valgrind.h"

static const HChar* TOOL_NAME    = "Freya";
static const HChar* TOOL_VERSION = "0.5.1";
static const HChar* TOOL_DESC    = "Memory access logger";
static const HChar* TOOL_AUTHOR  =
 "Copyright (C) 2009-2016, and GNU GPL'd, by Zoltan Herczeg (University of Szeged).";

static const HChar* DEFAULT_FORMAT = "freya.dump.%p";

static Bool clo_fr_verb        = False;
static const HChar* clo_config = NULL;
static Bool clo_mmap           = True;
static Bool clo_cross_free     = False;
static Int clo_trace_len       = 10;
static Int clo_report_len      = 5;
static Int clo_min             = 0;
static Int clo_max_trace       = 65536;
static const HChar* clo_output = NULL;

// ---------------------------------------------------------------
//  Common types
// ---------------------------------------------------------------

// Contain an item
typedef
   struct _Trace_Block {
      struct _Trace_Block* parent;      // Parent block
      struct _Trace_Block* next;        // Next in the list
      struct _Trace_Block* first;       // First child

      struct _Trace_Block* hash_next;   // Next item, who has the same ips

      Int                  allocs;      // Number of allocs
      Int                  reallocs;    // Number of reallocs
      Long                 total;       // Total allocated memory
      Int                  current;     // Current memory allocation
      Int                  peak;        // Peak memory consumption

      Addr                 ips;         // Stack trace instruction
      Int                  report_len;  // Report depth. Valid only if ips == 0
      HChar*               name;        // Name of a tree node. Valid only if ips == 0
   }
   Trace_Block;

typedef
   struct _Rule_List {
      struct _Rule_List* next;   // Next item
      HChar* name;                   // Rule name
      SizeT name_len;                // Length of rule name

      HChar* func_name;              // Function name
      SizeT func_name_len;           // Length of function name

      HChar* path;                   // Path
      SizeT path_len;                // Length of path

      Trace_Block* parent;           // Should be used as parent, or NULL for skip
      Bool is_namespace;             // func_name is namespace or not
   }
   Rule_List;

// Syntax (regular expression):
//   ^(-|[0-9]+)[FfNnDdGg][Dd]?;[^;]*(;.+)?$

static Rule_List* rule_head = NULL;
static Trace_Block* default_parent = NULL;

static const HChar* default_rule = "[total]+\n";

// ---------------------------------------------------------------
//  Sort and print results
// ---------------------------------------------------------------

#define DIR_BUFFER_SIZE 2048
static const HChar* fnname_buffer;
static HChar dir_buffer[DIR_BUFFER_SIZE];

// Head of the trace
static Trace_Block* trace_head = NULL;

static void fr_print_block(VgFile* fp, Trace_Block* block)
{
   UInt linenum;
   Bool dirname_available = False;
   const HChar* file_ptr;
   const HChar* dir_ptr;

   if (block->ips) {
      if (VG_(get_fnname)( block->ips, &fnname_buffer ))
         VG_(fprintf)(fp, "%s ", fnname_buffer);

      if (VG_(get_filename_linenum)( block->ips, &file_ptr, &dir_ptr, &linenum)) {
         dirname_available = dir_ptr[0] != '\0';
         if (!dirname_available)
            VG_(fprintf)(fp, "(%s:%d)\n", file_ptr, linenum);
         else
            VG_(fprintf)(fp, "(%s/%s:%d)\n", dir_ptr, file_ptr, linenum);
         return;
      }

      if (VG_(get_objname)( block->ips, &dir_ptr))
         VG_(fprintf)(fp, "(%s)\n", dir_ptr);
      else
         VG_(fprintf)(fp, "(Unknown file)\n");
   } else
      VG_(fprintf)(fp, "Group: %s\n", block->name);
}

static void fr_print_bytes(VgFile* fp, const HChar* name, Long value)
{
    VG_(fprintf)(fp, "%s", name);
    if (value > 1024 * 1024)
        VG_(fprintf)(fp, "%lld.%lldMb ", value / (1024 * 1024), (value * 10 / (1024 * 1024)) % 10);
    else if (value > 1024)
        VG_(fprintf)(fp, "%lld.%lldKb ", value / 1024, (value * 10 / 1024) % 10);
    else {
        VG_(fprintf)(fp, "%lldb ", value);
        return;
    }
    VG_(fprintf)(fp, "(%lldb) ", value);
}

static void fr_sort_and_dump(VgFile* fp, Trace_Block* block, Int indent)
{
   Int i;
   Trace_Block* from;
   Trace_Block* from_prev;
   Trace_Block* max;
   Trace_Block* max_prev;
   Trace_Block* it;
   Trace_Block* it_prev;

   tl_assert((!block->parent && trace_head == block) || (block->parent && block->parent->first == block));

   if (block->parent && block->next == NULL) {
      // One child, no need to sort
      if (block->peak < clo_min)
         return;

      for (i = 0; i < indent; ++i)
         VG_(fprintf)(fp, "  ");
      VG_(fprintf)(fp, "[%d] ", indent);
      fr_print_block(fp, block);

      if (block->first)
         fr_sort_and_dump(fp, block->first, indent + 1);
      return;
   }

   // Sort by total (min sort)
   from_prev = NULL;
   from = block;
   while (from) {
      max_prev = NULL;
      max = from;
      it_prev = from;
      it = from->next;
      while (it) {
         if (it->peak > max->peak) {
            max_prev = it_prev;
            max = it;
         }
         it_prev = it;
         it = it->next;
      }

      if (max != from) {
         if (max != from->next) {
            tl_assert(max_prev != from);
            it = max->next;
            max->next = from->next;
            from->next = it;
            max_prev->next = from;
         } else {
            tl_assert(max_prev == from);
            from->next = max->next;
            max->next = from;
         }

         if (from_prev)
            from_prev->next = max;
         else {
            if (from->parent)
                from->parent->first = max;
            else
                trace_head = max;
            block = max;
         }
      }
      from_prev = max;
      from = max->next;
   }

   while (block) {
      if (block->peak < clo_min)
         return;

      for (i = 0; i < indent; ++i)
         VG_(fprintf)(fp, "  ");

      VG_(fprintf)(fp, "[%d] ", indent);
      fr_print_bytes(fp, "Peak: ", block->peak);
      VG_(fprintf)(fp, "Allocs: %d ", block->allocs);
      VG_(fprintf)(fp, "Reallocs: %d ", block->reallocs);
      fr_print_bytes(fp, "Total: ", block->total);
      if (block->current > 0)
         fr_print_bytes(fp, "Leak: ", block->current);
      VG_(fprintf)(fp, "\n");

      for (i = 0; i < indent; ++i)
         VG_(fprintf)(fp, "  ");
      fr_print_block(fp, block);

      if (block->first)
         fr_sort_and_dump(fp, block->first, indent + 1);

      block = block->next;
   }
}

// ---------------------------------------------------------------
//  Stack tracing
// ---------------------------------------------------------------

// Nb: first two fields must match core's VgHashNode.
typedef
   struct _Trace_Hash {
      struct _Trace_Hash* next;
      Addr                ips;       // Stack trace instruction
      Int                 skip;      // Type of instruction
      Trace_Block*        block;     // Head block
      Trace_Block*        parent;    // Default parent block
   }
   Trace_Hash;

static Bool all_skipped = False;
static Addr *trace_ips;
static Trace_Hash **trace_hash_entries;
static VgHashTable *trace_hash = NULL;

static void check_address(Addr ips, Trace_Hash* hash_entry)
{
   UInt linenum;
   SizeT fnname_len, dir_len;
   Bool dirname_available = False;
   Rule_List* rule_ptr;
   const HChar* file_ptr;
   const HChar* dir_ptr;
   HChar* end;
   const HChar* current;
   Int match;

   // Get function name
   if (VG_(get_fnname)( ips, &fnname_buffer )) {
      fnname_len = VG_(strlen)(fnname_buffer);
   } else {
      fnname_buffer = "";
      fnname_len = 0;
   }

   // Get directory
   end = dir_buffer;
   if (VG_(get_filename_linenum)( ips, &file_ptr, &dir_ptr, &linenum)) {
      dirname_available = dir_ptr[0] != '\0';
      // Concat the names
      VG_(strcpy) (dir_buffer, dir_ptr);
      if (dirname_available) {
         end += VG_(strlen)(dir_buffer);
         *end++ = '/';
         VG_(strcpy) (end, file_ptr);
      }
   } else if (VG_(get_objname)( ips, &dir_ptr )) {
      VG_(strcpy) (dir_buffer, dir_ptr);
   } else
      dir_buffer[0] = '\0';

   while (*end)
      end++;

   // Search for matching rules
   rule_ptr = rule_head;
   while (rule_ptr) {
      match = (rule_ptr->func_name && rule_ptr->path) ? 2 : 1;

      if (rule_ptr->func_name) {
         if (rule_ptr->func_name_len <= fnname_len && fnname_buffer[0] == rule_ptr->func_name[0]
                && VG_(memcmp)(fnname_buffer, rule_ptr->func_name, rule_ptr->func_name_len * sizeof(HChar)) == 0) {

            if (!rule_ptr->is_namespace) {
               if (rule_ptr->func_name_len == fnname_len || fnname_buffer[rule_ptr->func_name_len] == ' ' || fnname_buffer[rule_ptr->func_name_len] == '(')
                  --match;
            } else {
               if (fnname_buffer[rule_ptr->func_name_len] == ':' && fnname_buffer[rule_ptr->func_name_len + 1] == ':')
                  --match;
            }
         }
      }

      if (rule_ptr->path && match == 1) {
         current = end;
         dir_len = 0;

         while (current >= dir_buffer) {
            current--;
            dir_len++;

            while (current >= dir_buffer) {
               if (*current == '/')
                  break;
               current--;
               dir_len++;
            }

            current++;
            dir_len--;

            if (rule_ptr->path_len <= dir_len && current[0] == rule_ptr->path[0]
                  && VG_(memcmp)(current, rule_ptr->path, rule_ptr->path_len * sizeof(HChar)) == 0
                  && (rule_ptr->path_len == dir_len || current[rule_ptr->path_len] == '/')) {
               match = 0;
               break;
            }

            current--;
            dir_len++;
         }
      }

      if (match == 0) {
         hash_entry->parent = rule_ptr->parent;
         if (!rule_ptr->parent)
            hash_entry->skip = 1;
         else
            return;
      }
      rule_ptr = rule_ptr->next;
   }

   hash_entry->parent = default_parent;
}

static Trace_Block* alloc_trace(ThreadId tid)
{
   Addr* ips_ptr;
   UInt n_ips, n_ips_count;
   Trace_Hash* hash_entry;
   Trace_Hash** hash_entry_ptr;
   Trace_Hash** max_skip;
   Trace_Block* parent;
   Trace_Block* block;

   n_ips = VG_(get_StackTrace)(tid, trace_ips, clo_trace_len, NULL, NULL, 0);
   tl_assert(n_ips > 0);

   // Get first non-skipped block
   ips_ptr = trace_ips;
   hash_entry_ptr = trace_hash_entries;
   max_skip = NULL;
   n_ips_count = n_ips;
   do {
      hash_entry = VG_(HT_lookup)(trace_hash, *ips_ptr);
      if (!hash_entry) {
         hash_entry = VG_(malloc)("freya.alloc_trace.1", sizeof(Trace_Hash));
         hash_entry->ips = *ips_ptr;
         hash_entry->skip = 0;
         hash_entry->block = NULL;
         hash_entry->parent = NULL;
         check_address(*ips_ptr, hash_entry);
         VG_(HT_add_node)(trace_hash, hash_entry);
         block = NULL;
      }
      *hash_entry_ptr++ = hash_entry;
      if (hash_entry->skip)
         max_skip = hash_entry_ptr; // Which is one step ahead
      n_ips_count--;
      ips_ptr++;
   } while (n_ips_count > 0);

   ips_ptr = trace_ips;
   hash_entry_ptr = trace_hash_entries;
   if (max_skip) {
      if (max_skip - trace_hash_entries == n_ips) {
         all_skipped = True;
         max_skip--; // At least one should always remain
      }
      n_ips -= max_skip - trace_hash_entries;
      ips_ptr += max_skip - trace_hash_entries;
      hash_entry_ptr += max_skip - trace_hash_entries;
   }

   parent = (*hash_entry_ptr)->parent;

   if (parent) {
      if (n_ips > parent->report_len)
         n_ips = parent->report_len;
   } else if (n_ips > clo_report_len)
      n_ips = clo_report_len;

   tl_assert(n_ips > 0);

   // Insert to the chain
   do {
      hash_entry = *hash_entry_ptr++;
      block = hash_entry->block;
      while (block) {
         tl_assert(block->ips == *ips_ptr);
         if (block->parent == parent)
            break;
         block = block->hash_next;
      }

      if (!block) {
         block = VG_(malloc)("freya.alloc_trace.2", sizeof(Trace_Block));
         block->parent = parent;
         if (parent) {
            block->next = parent->first;
            parent->first = block;
         } else {
            block->next = trace_head;
            trace_head = block;
         }
         block->first = NULL;

         block->hash_next = hash_entry->block;
         hash_entry->block = block;

         block->allocs = 0;
         block->reallocs = 0;
         block->total = 0;
         block->current = 0;
         block->peak = 0;
         block->ips = *ips_ptr;
         block->name = NULL;
      }

      parent = block;
      n_ips--;
      ips_ptr++;
   } while (n_ips > 0);

   return block;
}

// ---------------------------------------------------------------
//  Tracking alloc operations
// ---------------------------------------------------------------

// Metadata for heap blocks.
//
// Nb: first two fields must match core's VgHashNode.
typedef
   struct _HP_Chunk {
      struct _HP_Chunk* next;
      Addr              data;       // Ptr to actual block
      SizeT             req_szB;    // Size requested
      SizeT             slop_szB;   // Extra bytes given above those requested
      Trace_Block*      block;      // Tail block
      ThreadId          tid;
   }
   HP_Chunk;

static VgHashTable *malloc_list  = NULL;   // HP_Chunks

static void register_block (ThreadId tid, void *p, SizeT req_szB, SizeT slop_szB )
{
   HP_Chunk* hc;
   Trace_Block* block;

   // Make new HP_Chunk node, add to malloc_list
   hc           = VG_(malloc)("freya.malloc", sizeof(HP_Chunk));
   hc->data     = (Addr)p;
   hc->req_szB  = req_szB;
   hc->slop_szB = slop_szB;
   block        = alloc_trace(tid);
   hc->block    = block;
   hc->tid      = tid;

   while (block) {
      block->allocs ++;
      block->total += req_szB;
      block->current += req_szB;
      if (block->peak < block->current)
         block->peak = block->current;
      block = block->parent;
   }

   VG_(HT_add_node)(malloc_list, hc);
}

static void* new_block ( ThreadId tid, SizeT req_szB, SizeT req_alignB,
                  Bool is_zeroed )
{
   void* p;
   SizeT actual_szB, slop_szB;

   if ((SSizeT)req_szB < 0) return NULL;

   // Allocate and zero if necessary
   p = VG_(cli_malloc)( req_alignB, req_szB );
   if (!p) {
      return NULL;
   }
   if (is_zeroed) VG_(memset)(p, 0, req_szB);
   actual_szB = VG_(cli_malloc_usable_size)(p);
   tl_assert(actual_szB >= req_szB);
   slop_szB = actual_szB - req_szB;

   register_block(tid, p, req_szB, slop_szB);
   return p;
}

static void cross_thread_free ( ThreadId tid, Trace_Block* block )
{
   Addr* ips_ptr;
   int n_ips;
   UInt linenum;
   Bool dirname_available = False;
   const HChar* file_ptr;
   const HChar* dir_ptr;

   if (!clo_cross_free)
      return;

   VG_(printf)("Warning: free or realloc on a different thread!\n=== Original alloc ===\n");
   while (block) {
      if (block->ips && VG_(get_filename_linenum)( block->ips, &file_ptr, &dir_ptr, &linenum )) {
         dirname_available = dir_ptr[0] != '\0';
         if (!dirname_available)
            VG_(printf)("(%s:%d)\n", file_ptr, linenum);
         else
            VG_(printf)("(%s/%s:%d)\n", dir_ptr, file_ptr, linenum);
      }
      block = block->parent;
   }

   VG_(printf)("=== Current free or realloc ===\n");
   n_ips = VG_(get_StackTrace)(tid, trace_ips, clo_trace_len, NULL, NULL, 0);
   tl_assert(n_ips > 0);
   if (n_ips > clo_trace_len)
       n_ips = clo_trace_len;
   ips_ptr = trace_ips;

   while (n_ips > 0) {
      if (VG_(get_filename_linenum)( *ips_ptr, &file_ptr, &dir_ptr, &linenum )) {
         dirname_available = dir_ptr[0] != '\0';
         if (!dirname_available)
            VG_(printf)("(%s:%d)\n", file_ptr, linenum);
         else
            VG_(printf)("(%s/%s:%d)\n", dir_ptr, file_ptr, linenum);
      }
      --n_ips;
      ++ips_ptr;
   }

   VG_(printf)("=== End ===\n");
}

static void unregister_block ( ThreadId tid, void* p )
{
   // Remove HP_Chunk from malloc_list
   HP_Chunk* hc = VG_(HT_remove)(malloc_list, (UWord)p);
   Trace_Block* block;

   if (NULL == hc) {
      VG_(printf)("Invalid free: %p\n", p);
      return;   // must have been a bogus free()
   }

   if (tid != hc->tid)
       cross_thread_free(tid, hc->block);

   block = hc->block;
   while (block) {
      block->current -= hc->req_szB;
      block = block->parent;
   }

   // Actually free the chunk, and the heap block (if necessary)
   VG_(free)(hc);
}

static void free_block ( ThreadId tid, void* p )
{
   unregister_block(tid, p);
   VG_(cli_free)(p);
}

// Nb: --ignore-fn is tricky for realloc.  If the block's original alloc was
// ignored, but the realloc is not requested to be ignored, and we are
// shrinking the block, then we have to ignore the realloc -- otherwise we
// could end up with negative heap sizes.  This isn't a danger if we are
// growing such a block, but for consistency (it also simplifies things) we
// ignore such reallocs as well.
static void* renew_block ( ThreadId tid, void* p_old, SizeT new_req_szB )
{
   HP_Chunk* hc;
   void*     p_new;
   SizeT     old_req_szB, old_slop_szB, new_slop_szB, new_actual_szB;
   Trace_Block* block;

   // Remove the old block
   hc = VG_(HT_remove)(malloc_list, (UWord)p_old);
   if (hc == NULL) {
      VG_(printf)("Invalid realloc: %p\n", p_old);
      return NULL;   // must have been a bogus realloc()
   }

   if (tid != hc->tid)
      cross_thread_free(tid, hc->block);

   block = hc->block;
   while (block) {
      block->reallocs ++;
      block->current -= hc->req_szB;
      block->total -= hc->req_szB;
      block->current += new_req_szB;
      block->total += new_req_szB;
      if (block->peak < block->current)
         block->peak = block->current;
      block = block->parent;
   }

   old_req_szB  = hc->req_szB;
   old_slop_szB = hc->slop_szB;

   // Actually do the allocation, if necessary.
   if (new_req_szB <= old_req_szB + old_slop_szB) {
      // New size is smaller or same;  block not moved.
      p_new = p_old;
      new_slop_szB = old_slop_szB + (old_req_szB - new_req_szB);

   } else {
      // New size is bigger;  make new block, copy shared contents, free old.
      p_new = VG_(cli_malloc)(VG_(clo_alignment), new_req_szB);
      if (!p_new) {
         // Nb: if realloc fails, NULL is returned but the old block is not
         // touched.  What an awful function.
         return NULL;
      }
      VG_(memcpy)(p_new, p_old, old_req_szB);
      VG_(cli_free)(p_old);
      new_actual_szB = VG_(cli_malloc_usable_size)(p_new);
      tl_assert(new_actual_szB >= new_req_szB);
      new_slop_szB = new_actual_szB - new_req_szB;
   }

   // Update HP_Chunk.
   hc->data     = (Addr)p_new;
   hc->req_szB  = new_req_szB;
   hc->slop_szB = new_slop_szB;
   hc->tid      = tid;

   // Now insert the new hc (with a possibly new 'data' field) into
   // malloc_list.
   VG_(HT_add_node)(malloc_list, hc);
   return p_new;
}

// ---------------------------------------------------------------
//  Tracking mmap operations
// ---------------------------------------------------------------

typedef
   struct _Mmap_Section {
      struct _Mmap_Section* next;
      Addr                  page_addr;
      Trace_Block**         trace_blocks;
      // 0 - do nothing
      // 1 - update on access
      HChar*                used_blocks;
   }
   Mmap_Section;

// 4G pages

#define PAGE_SIZE          4096
#define PAGE_NUMBER        1048576

#if VG_WORDSIZE == 4

#define PAGE_OFFSET_DOWN(a) ((a) >> 12)
#define PAGE_OFFSET_UP(a)   (((a) + 4095) >> 12)

static Mmap_Section mmap_section;

#else

#define PAGE_ADDR(a)        ((a) & 0xffffffff00000000ll)
#define PAGE_OFFSET_DOWN(a) (((a) >> 12) & 0xfffff)
#define PAGE_OFFSET_UP(a)   ((((a) + 4095) >> 12) & 0xfffff)

static Mmap_Section* mmap_sections;
static Mmap_Section* mmap_section_cache;

#endif

static __inline__ void mark_blocks(Trace_Block **trace_blocks_ptr, Trace_Block **trace_blocks_end, HChar* used_blocks_ptr, Trace_Block *block_arg)
{
   Trace_Block *head_block = *trace_blocks_ptr;
   SizeT touched = 0;

   if (block_arg) {
      while (trace_blocks_ptr < trace_blocks_end) {
         tl_assert(*trace_blocks_ptr == head_block);
         // Do not overwrite previously mmaped blocks
         if (!head_block) {
            *trace_blocks_ptr = block_arg;
            *used_blocks_ptr = 'x';
         }
         trace_blocks_ptr++;
         used_blocks_ptr++;
      }
   } else {
      while (trace_blocks_ptr < trace_blocks_end) {
         // X11 workaround...
         if (*trace_blocks_ptr) {
             if (!head_block)
                head_block = *trace_blocks_ptr;
             tl_assert(*trace_blocks_ptr == head_block);
             if (!*used_blocks_ptr)
                touched++;
         }
         *trace_blocks_ptr++ = NULL;
         *used_blocks_ptr++ = '\0';
      }

      if (head_block && touched > 0) {
         touched *= PAGE_SIZE;
         while (head_block) {
            head_block->current -= touched;
            head_block = head_block->parent;
         }
      }
   }
}

static __inline__ Addr page_offset_up(Addr addr)
{
   addr = PAGE_OFFSET_UP(addr);
   return addr ? addr : PAGE_NUMBER;
}

static __inline__ void mem_map(Addr addr, Addr end_addr, Trace_Block *block_arg)
{
   // Must be strictly greater
   tl_assert(end_addr > addr);

#if VG_WORDSIZE == 4
   mark_blocks( mmap_section.trace_blocks + PAGE_OFFSET_DOWN(addr),
                mmap_section.trace_blocks + page_offset_up(end_addr),
                mmap_section.used_blocks + PAGE_OFFSET_DOWN(addr),
                block_arg );
#else
   Addr current_end_addr;
   Mmap_Section* mmap_section;
   Addr page_addr;

   while (addr < end_addr) {
      page_addr = PAGE_ADDR(addr);
      current_end_addr = page_addr + 0x100000000ll;
      if (current_end_addr > end_addr)
         current_end_addr = end_addr;

      mmap_section = mmap_sections;
      while (1) {
         if (mmap_section->page_addr == page_addr)
             break;
         if (!mmap_section->next) {
             mmap_section->next = VG_(calloc)("freya.mem_map.1", 1, sizeof(Mmap_Section));
             mmap_section = mmap_section->next;
             mmap_section->next = NULL;
             mmap_section->page_addr = page_addr;
             mmap_section->trace_blocks = VG_(calloc)("freya.mem_map.2", PAGE_NUMBER, sizeof(Trace_Block*));
             mmap_section->used_blocks = VG_(calloc)("freya.fr_post_clo_init.3", PAGE_NUMBER, sizeof(HChar));
             break;
         }
         mmap_section = mmap_section->next;
      }

      mark_blocks( mmap_section->trace_blocks + PAGE_OFFSET_DOWN(addr),
                   mmap_section->trace_blocks + page_offset_up(current_end_addr),
                   mmap_section->used_blocks + PAGE_OFFSET_DOWN(addr),
                   block_arg );

      addr = current_end_addr;
   }
#endif
}

static VG_REGPARM(2) void trace_store(Addr addr, SizeT size)
{
   Trace_Block *block;

#if VG_WORDSIZE == 4
   addr = PAGE_OFFSET_DOWN(addr);
   if (!mmap_section.used_blocks[addr])
      return;

   block = mmap_section.trace_blocks[addr];
   mmap_section.used_blocks[addr] = '\0';
#else
   Addr page_addr = PAGE_ADDR(addr);
   Mmap_Section* mmap_section;

   if (mmap_section_cache->page_addr == page_addr)
      mmap_section = mmap_section_cache;
   else {
      mmap_section = mmap_sections;
      while (1) {
         if (mmap_section->page_addr == page_addr)
            break;
         mmap_section = mmap_section->next;
         if (!mmap_section)
            return;
      }
      mmap_section_cache = mmap_section;
   }

   addr = PAGE_OFFSET_DOWN(addr);
   if (!mmap_section->used_blocks[addr])
      return;

   block = mmap_section->trace_blocks[addr];
   mmap_section->used_blocks[addr] = '\0';
#endif

   tl_assert(block);
   do {
      block->allocs ++;
      block->total += PAGE_SIZE;
      block->current += PAGE_SIZE;
      if (block->peak < block->current)
         block->peak = block->current;
      block = block->parent;
   } while(block);
}

//------------------------------------------------------------//
//--- malloc() et al replacement wrappers                  ---//
//------------------------------------------------------------//

static void* fr_malloc ( ThreadId tid, SizeT szB )
{
   return new_block( tid, szB, VG_(clo_alignment), /*is_zeroed*/False );
}

static void* fr___builtin_new ( ThreadId tid, SizeT szB )
{
   return new_block( tid, szB, VG_(clo_alignment), /*is_zeroed*/False );
}

static void* fr___builtin_vec_new ( ThreadId tid, SizeT szB )
{
   return new_block( tid, szB, VG_(clo_alignment), /*is_zeroed*/False );
}

static void* fr_calloc ( ThreadId tid, SizeT m, SizeT szB )
{
   return new_block( tid, m*szB, VG_(clo_alignment), /*is_zeroed*/True );
}

static void *fr_memalign ( ThreadId tid, SizeT alignB, SizeT szB )
{
   return new_block( tid, szB, alignB, False );
}

static void fr_free ( ThreadId tid, void* p )
{
   free_block( tid, p );
}

static void fr___builtin_delete ( ThreadId tid, void* p )
{
   free_block( tid, p );
}

static void fr___builtin_vec_delete ( ThreadId tid, void* p )
{
   free_block( tid, p );
}

static void* fr_realloc ( ThreadId tid, void* p_old, SizeT new_szB )
{
   return renew_block(tid, p_old, new_szB);
}

static SizeT fr_malloc_usable_size ( ThreadId tid, void* p )
{
   HP_Chunk* hc = VG_(HT_lookup)( malloc_list, (UWord)p );

   return ( hc ? hc->req_szB + hc->slop_szB : 0 );
}

static void fr_mmap(Addr a, SizeT len, Bool rr, Bool ww, Bool xx, ULong di_handle)
{
   if (clo_mmap)
      mem_map( a, a + len, alloc_trace(VG_(get_running_tid)()) );
}

static void fr_munmap(Addr a, SizeT len)
{
   if (clo_mmap)
      mem_map( a, a + len, NULL );
}

// ---------------------------------------------------------------
//  Client request
// ---------------------------------------------------------------

static Bool fr_handle_client_request ( ThreadId tid, UWord* argv, UWord* ret )
{
   switch (argv[0]) {
   case VG_USERREQ__MALLOCLIKE_BLOCK: {
      void* p   = (void*)argv[1];
      SizeT szB =        argv[2];
      register_block(tid, p, szB, 0);
      *ret = 0;
      return True;
   }
#if 0
   case VG_USERREQ__RESIZEINPLACE_BLOCK: {
      void* p        = (void*)argv[1];
      SizeT newSizeB =       argv[3];
      return True;
   }
#endif
   case VG_USERREQ__FREELIKE_BLOCK: {
      void* p = (void*)argv[1];
      unregister_block( tid, p );
      *ret = 0;
      return True;
   }

   default:
      *ret = 0;
      return False;
   }
}


// ---------------------------------------------------------------
//  Generator
// ---------------------------------------------------------------

static Bool fr_process_cmd_line_option(const HChar* arg)
{
         if (VG_BOOL_CLO(arg, "--frverb", clo_fr_verb))                      {}
    else if (VG_STR_CLO(arg,  "--config", clo_config))                       {}
    else if (VG_BOOL_CLO(arg, "--mmap", clo_mmap))                           {}
    else if (VG_BOOL_CLO(arg, "--crossfree", clo_cross_free))                {}
    else if (VG_BINT_CLO(arg, "--trace", clo_trace_len, 10, clo_max_trace))  {}
    else if (VG_BINT_CLO(arg, "--report", clo_report_len, 1, clo_max_trace)) {}
    else if (VG_BINT_CLO(arg, "--min", clo_min, 0, 1024*1024*1024))          {}
    else if (VG_STR_CLO(arg, "--freya-out-file", clo_output))                {}
    else
        return VG_(replacement_malloc_process_cmd_line_option)(arg);

    return True;
}

static void fr_print_usage(void)
{
   VG_(printf) (
"    --frverb=yes              verbose freya tool\n"
"    --config=<str>            configuration file\n"
"    --mmap=no                 do not trace mmap allocations\n"
"    --crossfree=yes           report cross thread free operations\n"
"    --trace=<number>          maximum depth of stack trace [%d]\n"
"    --report=<number>         report depth of stack trace [%d]\n"
"    --min=<number>            do not report allocations below this size (in bytes) [%d]\n"
"    --freya-out-file=<str>    output filename to report results [%s]\n"
    , clo_trace_len
    , clo_report_len
    , clo_min
    , DEFAULT_FORMAT
   );
}

static void fr_print_debug_usage(void)
{
   VG_(printf)(
"    (none)\n"
   );
}

static
IRSB* fr_instrument(VgCallbackClosure* closure,
                    IRSB* sbIn,
                    const VexGuestLayout* layout,
                    const VexGuestExtents* vge,
                    const VexArchInfo* arch,
                    IRType gWordTy, IRType hWordTy)
{
   Int        i;
   IRSB*      sbOut;
   IRTypeEnv* tyenv = sbIn->tyenv;
   IRDirty*   di;
   IRType     dataTy;
   IRExpr**   argv;
   IRCAS*     cas;

   // We don't care about mmaps
   if (!clo_mmap)
      return sbIn;

   // From lackey tool
   //tl_assert(gWordTy == hWordTy);

   sbOut = deepCopyIRSBExceptStmts(sbIn);

   // Copy verbatim any IR preamble preceding the first IMark
   i = 0;
   while (i < sbIn->stmts_used && sbIn->stmts[i]->tag != Ist_IMark) {
      addStmtToIRSB( sbOut, sbIn->stmts[i] );
      i++;
   }

   for (/*use current i*/; i < sbIn->stmts_used; i++) {
      IRStmt* st = sbIn->stmts[i];
      if (!st || st->tag == Ist_NoOp) continue;

      switch (st->tag) {
         case Ist_NoOp: // Make compiler happy
         case Ist_AbiHint:
         case Ist_Put:
         case Ist_PutI:
         case Ist_MBE:
         case Ist_IMark:
         case Ist_WrTmp:
         case Ist_LoadG:
         case Ist_Exit:
            addStmtToIRSB( sbOut, st );
            break;

         case Ist_Store:
            dataTy = typeOfIRExpr( tyenv, st->Ist.Store.data );
            argv   = mkIRExprVec_2( st->Ist.Store.addr, mkIRExpr_HWord( sizeofIRType( dataTy ) ) );
            di     = unsafeIRDirty_0_N(/*regparms*/2, "trace_store", VG_(fnptr_to_fnentry)( trace_store ), argv);
            addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
            addStmtToIRSB( sbOut, st );
            break;

         case Ist_StoreG:
            dataTy = typeOfIRExpr(tyenv, st->Ist.StoreG.details->data);
            argv   = mkIRExprVec_2( st->Ist.StoreG.details->addr, mkIRExpr_HWord( sizeofIRType( dataTy ) ) );
            di     = unsafeIRDirty_0_N(/*regparms*/2, "trace_store", VG_(fnptr_to_fnentry)( trace_store ), argv);
            addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
            addStmtToIRSB( sbOut, st );
            break;

         case Ist_LLSC:
            if (st->Ist.LLSC.storedata != NULL) {
               dataTy = typeOfIRExpr( tyenv, st->Ist.LLSC.storedata );
               argv   = mkIRExprVec_2( st->Ist.LLSC.addr, mkIRExpr_HWord( sizeofIRType( dataTy ) ) );
               di     = unsafeIRDirty_0_N(/*regparms*/2, "trace_store", VG_(fnptr_to_fnentry)( trace_store ), argv);
               addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
            }
            addStmtToIRSB( sbOut, st );
            break;

         case Ist_Dirty:
            di = st->Ist.Dirty.details;
            if (di->mFx != Ifx_None) {
               // This dirty helper accesses memory.  Collect the details.
               tl_assert(di->mAddr != NULL);
               tl_assert(di->mSize != 0);
               if (di->mFx == Ifx_Write || di->mFx == Ifx_Modify) {
                  argv = mkIRExprVec_2( di->mAddr, mkIRExpr_HWord( di->mSize ) );
                  di   = unsafeIRDirty_0_N( /*regparms*/2, "trace_store", VG_(fnptr_to_fnentry)( trace_store ), argv );
                  addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
               }
            } else {
               tl_assert(di->mAddr == NULL);
               tl_assert(di->mSize == 0);
            }
            addStmtToIRSB( sbOut, st );
            break;

         case Ist_CAS:
            cas = st->Ist.CAS.details;
            tl_assert(cas->addr != NULL);
            tl_assert(cas->dataLo != NULL);
            argv = mkIRExprVec_2( cas->addr, mkIRExpr_HWord( sizeofIRType(typeOfIRExpr(tyenv, cas->dataLo)) * (cas->dataHi != NULL ? 2 : 1) ) );
            di   = unsafeIRDirty_0_N( /*regparms*/2, "trace_store", VG_(fnptr_to_fnentry)( trace_store ), argv );
            addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
            addStmtToIRSB( sbOut, st );
            break;
      }
   }

   return sbOut;
}

static void fr_fini(Int exitcode)
{
   if (all_skipped) {
     VG_(printf)("Warning: --trace should be increased, because the last item of\n"
                 "         the stack trace sometimes matches a skip rule\n\n");
   }

   if (clo_output == NULL)
      clo_output = DEFAULT_FORMAT;

   HChar* filename = VG_(expand_file_name)("--freya-out-file", clo_output);
   VgFile* fp = VG_(fopen)(filename, VKI_O_CREAT|VKI_O_WRONLY|VKI_O_TRUNC, VKI_S_IRUSR|VKI_S_IWUSR);

   if (fp == NULL) {
      VG_(message)(Vg_UserMsg, "Error: can not open output file '%s'\n", filename);
      VG_(exit)(1);
   } else
      VG_(message)(Vg_UserMsg, "Writing %s trace into file: '%s'\n", TOOL_NAME, filename);

   VG_(fprintf)(fp, "%s %s - %s\n", TOOL_NAME, TOOL_VERSION, TOOL_DESC);
   VG_(fprintf)(fp, "Command: %s\n", VG_(args_the_exename));
   VG_(fprintf)(fp, "Parent PID: %d\n", VG_(getppid)());
   VG_(fprintf)(fp, "Current PID: %d\n", VG_(getpid)());
   VG_(fprintf)(fp, "\nTrace: \n\n");

   fr_sort_and_dump(fp, trace_head, 0);

   VG_(fclose)(fp);
   VG_(free)(filename);
}

static HChar* parse_rule(HChar* read_ptr, Rule_List** last_rule_ptr, Int line)
{
   Rule_List* rule;
   Rule_List* rule_ptr;

   rule = VG_(malloc)("freya.parse_rule.1", sizeof(Rule_List));

   rule->next = NULL;
   rule->parent = NULL;

   if (*read_ptr != '-') {
      rule->name = read_ptr;
      while (*read_ptr != ' ') {
         if (*read_ptr == '\0' || *read_ptr == '\r' || *read_ptr == '\n' || *read_ptr == ')' || *read_ptr == '}') {
            VG_(printf)("Invalid rule name at line %d (must start with hypen or a name followed by a space)\n", line);
            tl_assert(0);
         }
         read_ptr++;
      }
      rule->name_len = read_ptr - rule->name;
      *read_ptr = '\0';

      // Must have a unique name
      rule_ptr = rule_head;
      while (rule_ptr) {
         if (rule_ptr->name_len == rule->name_len && VG_(memcmp)(rule->name, rule_ptr->name, rule->name_len * sizeof(HChar)) == 0) {
            VG_(printf)("Redefined rule %s at line %d. Rule names must be unique!\n", rule->name, line);
            tl_assert(0);
         }
         rule_ptr = rule_ptr->next;
      }
   } else {
      rule->name = NULL;
      rule->name_len = 0;
   }
   read_ptr++;

   // Enque this new rule
   if (*last_rule_ptr)
      (*last_rule_ptr)->next = rule;
   else
      rule_head = rule;
   *last_rule_ptr = rule;

   while (*read_ptr == ' ')
      read_ptr++;

   if (*read_ptr == '(' || *read_ptr == '{') {
      rule->is_namespace = *read_ptr == '{';
      read_ptr++;

      rule->func_name = read_ptr;
      while (!(!rule->is_namespace && *read_ptr == ')') && !(rule->is_namespace && *read_ptr == '}')) {
         if (*read_ptr == '\r' || *read_ptr == '\n' || *read_ptr == '\0') {
            VG_(printf)("Unterminated ( or { at line %d\n", line);
            tl_assert(0);
         }
         read_ptr++;
      }
      rule->func_name_len = read_ptr - rule->func_name;
      if (rule->func_name_len == 0) {
         VG_(printf)("Function or namespace name is empty at line %d\n", line);
         tl_assert(0);
      }
      *read_ptr = '\0';
      read_ptr++;

      while (*read_ptr == ' ')
         read_ptr++;
   } else {
      rule->func_name = NULL;
      rule->func_name_len = 0;
      rule->is_namespace = False;
   }

   rule->path = read_ptr;
   while (read_ptr != '\0' && *read_ptr != '\n' && *read_ptr != '\r')
      read_ptr++;

   rule->path_len = read_ptr - rule->path;
   if (rule->path_len == 0)
      rule->path = NULL;

   // Unlike other lines, newline is parsed here
   if (*read_ptr) {
      if (read_ptr[0] == '\r' && read_ptr[1] == '\n') {
         *read_ptr = '\0';
         read_ptr += 2;
      } else {
         *read_ptr = '\0';
         read_ptr++;
      }
   }

   if (clo_fr_verb)
      VG_(printf)("Rule: '%s' (%ld) %s: '%s' (%ld) Path: '%s' (%ld)\n",
         rule->name, rule->name_len,
         rule->is_namespace ? "Namesp" : "Func", rule->func_name, rule->func_name_len,
         rule->path, rule->path_len);
   return read_ptr;
}

static void search_rule(Trace_Block* block, HChar* name, SizeT name_len, Int line)
{
   Rule_List* rule_ptr;

   rule_ptr = rule_head;
   while (rule_ptr) {
      if (rule_ptr->name_len == name_len && rule_ptr->name[0] == name[0]
            && VG_(memcmp)(rule_ptr->name, name, name_len * sizeof(HChar)) == 0) {
         if (rule_ptr->parent != NULL) {
            VG_(printf)("Rule '%s' has been assigned at line %d\n", name, line);
            tl_assert(0);
         }
         rule_ptr->parent = block;
         return;
      }
      rule_ptr = rule_ptr->next;
   }
   VG_(printf)("Rule '%s' not found at line %d\n", name, line);
   tl_assert(0);
}

static void remove_unused_rules(void)
{
   Rule_List* rule_ptr;
   Rule_List* prev_rule_ptr = NULL;

   rule_ptr = rule_head;
   while (rule_ptr) {
      if (rule_ptr->name && !rule_ptr->parent) {
         // Remove this unused rule
         if (prev_rule_ptr) {
            prev_rule_ptr->next = rule_ptr->next;
            VG_(free)(rule_ptr);
            rule_ptr = prev_rule_ptr->next;
         } else {
            rule_head = rule_ptr->next;
            VG_(free)(rule_ptr);
            rule_ptr = rule_head;
         }
      } else {
         prev_rule_ptr = rule_ptr;
         rule_ptr = rule_ptr->next;
      }
   }
}

static HChar* parse_extra_rule(HChar* read_ptr, Trace_Block* block, Int line)
{
   HChar* name;

   if (block == NULL) {
      VG_(printf)("The first group at line %d cannot be started with {\n", line);
      tl_assert(0);
   }

   read_ptr++;
   name = read_ptr;
   while (*read_ptr != '}') {
      if (*read_ptr == '\r' || *read_ptr == '\n' || *read_ptr == '\0') {
         VG_(printf)("Unterminated { at line %d\n", line);
         tl_assert(0);
      }
      read_ptr++;
   }
   if (name == read_ptr) {
      VG_(printf)("The node at line %d has empty name\n", line);
      tl_assert(0);
   }

   *read_ptr = '\0';
   search_rule(block, name, read_ptr - name, line);
   read_ptr++;

   while (*read_ptr == ' ')
      read_ptr++;
   if (*read_ptr != '\n' && *read_ptr != '\r' && *read_ptr != '\0') {
      VG_(printf)("Garbage at the end of line %d\n", line);
      tl_assert(0);
   }
   return read_ptr;
}

static void fr_post_clo_init(void)
{
   Rule_List* last_rule_ptr = NULL;
   HChar* read_ptr;
   Trace_Block* block = NULL;
   Trace_Block* parent = NULL;
   Int* indents = (int*)dir_buffer;
   Int indent;
   Int depth = -1;
   Int report_len;
   Int line = 1;
   Bool is_group;
   SysRes sres;
   Int fd;
   OffT file_size;

   trace_ips = VG_(calloc)("freya.fr_post_clo_init.1", clo_trace_len, sizeof(Addr));
   trace_hash_entries = VG_(calloc)("freya.fr_post_clo_init.1", clo_trace_len, sizeof(Trace_Hash*));

   if (clo_mmap) {
#if VG_WORDSIZE == 4
      mmap_section.next = NULL;
      mmap_section.page_addr = 0;
      mmap_section.trace_blocks = VG_(calloc)("freya.fr_post_clo_init.2", PAGE_NUMBER, sizeof(Trace_Block*));
      mmap_section.used_blocks = VG_(calloc)("freya.fr_post_clo_init.3", PAGE_NUMBER, sizeof(HChar));
#else
      mmap_sections = VG_(calloc)("freya.fr_post_clo_init.1", 1, sizeof(Mmap_Section));
      mmap_sections->next = NULL;
      mmap_sections->page_addr = 0;
      mmap_sections->trace_blocks = VG_(calloc)("freya.fr_post_clo_init.2", PAGE_NUMBER, sizeof(Trace_Block*));
      mmap_sections->used_blocks = VG_(calloc)("freya.fr_post_clo_init.3", PAGE_NUMBER, sizeof(HChar));
      mmap_section_cache = mmap_sections;
#endif
   }

   read_ptr = NULL;
   if (clo_config) {
      sres = VG_(open)(clo_config, VKI_O_RDONLY, 0);
      if (!sr_isError(sres)) {
         fd = (Int) sr_Res(sres);

         file_size = VG_(lseek)(fd, 0, VKI_SEEK_END);
         VG_(lseek)(fd, 0, VKI_SEEK_SET);

         if (clo_fr_verb)
            VG_(printf)("File '%s' (size: %ld bytes) is successfully opened.\n", clo_config, file_size);

         read_ptr = VG_(malloc)("freya.fr_post_clo_init.3", (file_size + 1) * sizeof(HChar));
         VG_(read)(fd, read_ptr, file_size);
         read_ptr[file_size] = '\0';

         VG_(close) (fd);
      }
      else if (clo_fr_verb)
         VG_(printf)("Cannot open '%s'. (Fallback to default config)\n", clo_config);
   }
   else if (clo_fr_verb)
      VG_(printf)("No config file provided. (Fallback to default config)\n");

   if (!read_ptr) {
      // Duplicate
      read_ptr = VG_(malloc)("freya.fr_post_clo_init.4", (VG_(strlen)(default_rule) + 1) * sizeof(HChar));
      VG_(strcpy)(read_ptr, default_rule);
   }

   while (*read_ptr) {
      // Parsing the next line, first skip spaces
      indent = 0;
      while (*read_ptr == ' ') {
         indent++;
         read_ptr++;
      }

      // All newlines are parsed here
      if (*read_ptr == '\r' || *read_ptr == '\n') {
         line++;
         if (read_ptr[0] == '\r' && read_ptr[1] == '\n')
            read_ptr++;
         read_ptr++;
         continue;
      }

      // Skip comments
      if (*read_ptr == '#') {
         while (*read_ptr != '\0' && *read_ptr != '\r' && *read_ptr != '\n')
            read_ptr++;

         continue;
      }

      if (*read_ptr == '{') {
         read_ptr = parse_extra_rule(read_ptr, block, line);
         continue;
      } else if (*read_ptr != '[' && *read_ptr != '(') {
         read_ptr = parse_rule(read_ptr, &last_rule_ptr, line);
         line++;
         continue;
      }

      is_group = *read_ptr == '[';

      block = VG_(malloc)("freya.fr_post_clo_init.4", sizeof(Trace_Block));
      read_ptr++;
      block->name = read_ptr;

      while (!(!is_group && *read_ptr == ')') && !(is_group && *read_ptr == ']')) {
         if (*read_ptr == '\r' || *read_ptr == '\n' || *read_ptr == '\0') {
            VG_(printf)("Unterminated ( or [ at line %d\n", line);
            tl_assert(0);
         }
         read_ptr++;
      }
      if (block->name == read_ptr) {
         VG_(printf)("The node at line %d has empty name\n", line);
         tl_assert(0);
      }

      *read_ptr = '\0';
      if (!is_group)
         search_rule(block, block->name, read_ptr - block->name, line);
      read_ptr++;

      report_len = -1;
      while (*read_ptr == ' ')
         read_ptr++;

      if (*read_ptr >= '1' && *read_ptr <= '9') {
         report_len = 0;
         do {
            report_len = report_len * 10 + (*read_ptr - '0');
            tl_assert2(report_len < clo_max_trace, "Report length must be less than max trace length");
            read_ptr++;
         } while (*read_ptr >= '0' && *read_ptr <= '9');

         if (report_len > clo_report_len)
            report_len = clo_report_len;

         while (*read_ptr == ' ')
            read_ptr++;
      }

      if (*read_ptr == '+') {
         tl_assert2(default_parent == NULL, "Only one default node is allowed");
         default_parent = block;
         read_ptr++;
      }

      while (*read_ptr == ' ')
         read_ptr++;

      if (*read_ptr != '\n' && *read_ptr != '\r' && *read_ptr != '\0') {
         VG_(printf)("Garbage at the end of line %d\n", line);
         tl_assert(0);
      }

      if (clo_fr_verb)
         VG_(printf)("%s '%s' %s\n", is_group ? "Group:" : "Group & Attach:", block->name, default_parent == block ? "(Default)" : "");

      if (depth >= 0) {
         if (indents[depth] != indent) {
            if (indent > indents[depth]) {
               tl_assert2(depth < 63, "Maximum allowed depth is 63 for the tree");
               depth++;
               indents[depth] = indent;
               if (parent)
                  parent = parent->first;
               else
                  parent = trace_head;
            } else {
               do {
                  if (depth == 0) {
                     VG_(printf)("Wrong tree indentation at line %d\n", line);
                     tl_assert(0);
                  }
                  depth--;
                  tl_assert(parent);
                  parent = parent->parent;
               } while (indent != indents[depth]);
               tl_assert((depth == 0 && !parent) || (depth > 0 && parent));
            }
         }
      } else {
         // The indentation of the top element
         tl_assert(!parent);
         indents[0] = indent;
         depth = 0;
      }

      block->parent = parent;
      if (parent) {
         block->next = parent->first;
         parent->first = block;
         if (report_len == -1 || report_len > parent->report_len)
            block->report_len = parent->report_len;
         else
            block->report_len = report_len;
      } else {
         block->next = trace_head;
         if (report_len == -1)
            block->report_len = clo_report_len;
         else
            block->report_len = report_len;
         trace_head = block;
      }
      block->first = NULL;

      block->hash_next = NULL;

      block->allocs = 0;
      block->reallocs = 0;
      block->total = 0;
      block->current = 0;
      block->peak = 0;
      block->ips = 0;
   }

   remove_unused_rules();
}

static void fr_pre_clo_init(void)
{
   VG_(details_name)            (TOOL_NAME);
   VG_(details_version)         (TOOL_VERSION);
   VG_(details_description)     (TOOL_DESC);
   VG_(details_copyright_author)(TOOL_AUTHOR);
   VG_(details_bug_reports_to)  (VG_BUGS_TO);

   VG_(basic_tool_funcs)        (fr_post_clo_init,
                                 fr_instrument,
                                 fr_fini);

   // Needs
   VG_(needs_command_line_options)(fr_process_cmd_line_option,
                                   fr_print_usage,
                                   fr_print_debug_usage);

   VG_(needs_client_requests)     (fr_handle_client_request);

   VG_(needs_malloc_replacement)  (fr_malloc,
                                   fr___builtin_new,
                                   fr___builtin_vec_new,
                                   fr_memalign,
                                   fr_calloc,
                                   fr_free,
                                   fr___builtin_delete,
                                   fr___builtin_vec_delete,
                                   fr_realloc,
                                   fr_malloc_usable_size,
                                   0 );

   VG_(track_new_mem_mmap)        (fr_mmap);
   VG_(track_die_mem_munmap)      (fr_munmap);

   // Memory allocation.
   trace_hash = VG_(HT_construct)( "fr.main.1" );
   malloc_list = VG_(HT_construct)( "fr.main.2" );
}

VG_DETERMINE_INTERFACE_VERSION(fr_pre_clo_init)

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/

