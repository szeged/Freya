
/*--------------------------------------------------------------------*/
/*--- Heimdall: raw memory access logger tool.         heim_main.c ---*/
/*--------------------------------------------------------------------*/

/*
   Copyright (C) 2016 Zoltan Herczeg (University of Szeged)
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
*/

#include "pub_tool_basics.h"

#include "pub_tool_tooliface.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_options.h"
#include "pub_tool_machine.h"
#include "pub_tool_hashtable.h"

#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"

SizeT clo_page_size = 4096;

// Metadata for pages.
//
// Nb: first two fields must match core's VgHashNode.
typedef
   struct _Page {
      struct _Page* next;
      Addr          start_addr;    // Starting address
      struct _Page* ordered_next;  // Next ordered address
   }
   Page;

static VgHashTable *page_list = NULL;    // Page list
static Page* ordered_page_list = NULL;  // Ordered page list

static VG_REGPARM(2) void trace_store(Addr addr, SizeT size)
{
  Page *page_ptr;

  // VG_(printf)("Store: 0x%lx (%d)\n", (long)addr, (int)size);

  // Aligning to page
  addr &= ~(clo_page_size - 1);

  page_ptr = VG_(HT_lookup)(page_list, addr);
  if (!page_ptr) {
    page_ptr = VG_(malloc)("freya.trace_store.1", sizeof(Page));

    page_ptr->start_addr = addr;

    if (!ordered_page_list || (addr < ordered_page_list->start_addr)) {
      page_ptr->ordered_next = ordered_page_list;
      ordered_page_list = page_ptr;
    } else {
      Page* current_page_ptr = ordered_page_list;

      while (current_page_ptr->ordered_next
             && (current_page_ptr->ordered_next->start_addr < addr))
      {
        current_page_ptr = current_page_ptr->ordered_next;
      }

      page_ptr->ordered_next = current_page_ptr->ordered_next;
      current_page_ptr->ordered_next = page_ptr;
    }

    VG_(HT_add_node)(page_list, page_ptr);
  }
}

static
IRSB* heim_instrument(VgCallbackClosure* closure,
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

static void heim_post_clo_init(void)
{
}

static void heim_fini(Int exitcode)
{
  Page* current_page_ptr = ordered_page_list;
  Page* first_page_ptr = current_page_ptr;
  long total_size = 0;

  VG_(printf)("Page size: %ld bytes\n", (long)clo_page_size);

  while (current_page_ptr) {
    if (!current_page_ptr->ordered_next
        || current_page_ptr->ordered_next->start_addr > current_page_ptr->start_addr + clo_page_size)
    {
      long size = (long)(current_page_ptr->start_addr + clo_page_size - first_page_ptr->start_addr);

      VG_(printf)("  Modified area: 0x%lx - 0x%lx size: %ld bytes [%ld.%ld Kb]\n",
                  (long)first_page_ptr->start_addr,
                  (long)(current_page_ptr->start_addr + clo_page_size),
                  size,
                  size / 1024,
                  ((size % 1024) * 10) / 1024);

      total_size += size;
      first_page_ptr = current_page_ptr->ordered_next;
    }

    current_page_ptr = current_page_ptr->ordered_next;
  }

  VG_(printf)("Total modified memory area: %ld bytes [%ld.%ld Kb]\n",
              total_size,
              total_size / 1024,
              ((total_size % 1024) * 10) / 1024);
}

static Bool heim_process_cmd_line_option(const HChar* arg)
{
         if (VG_BINT_CLO(arg, "--page_size", clo_page_size, 16, 65536))  {}
    else
        return VG_(replacement_malloc_process_cmd_line_option)(arg);

    if ((clo_page_size & (clo_page_size - 1)) != 0) {
      VG_(message) (Vg_FailMsg, "--page_size must be power of 2.\n");
      VG_(exit)(1);
    }

    return True;
}

static void heim_print_usage(void)
{
   VG_(printf) (
"    --page_size=<number>            page size [%d]\n",
                clo_page_size
   );
}

static void heim_print_debug_usage(void)
{
   VG_(printf)(
"    (none)\n"
   );
}

static void heim_pre_clo_init(void)
{
   VG_(details_name)            ("Heimdall");
   VG_(details_version)         ("0.5");
   VG_(details_description)     ("Raw memory access logger");
   VG_(details_copyright_author)(
      "Copyright (C) 2016, and GNU GPL'd, by Zoltan Herczeg (University of Szeged).");
   VG_(details_bug_reports_to)  (VG_BUGS_TO);

   VG_(basic_tool_funcs)        (heim_post_clo_init,
                                 heim_instrument,
                                 heim_fini);

   // Needs
   VG_(needs_command_line_options)(heim_process_cmd_line_option,
                                   heim_print_usage,
                                   heim_print_debug_usage);


   // Memory allocation.
   page_list = VG_(HT_construct)( "heim.main.1" );
}

VG_DETERMINE_INTERFACE_VERSION(heim_pre_clo_init)

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/


