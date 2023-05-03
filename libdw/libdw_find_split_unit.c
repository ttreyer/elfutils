/* Find the split (or skeleton) unit for a given unit.
   Copyright (C) 2018 Red Hat, Inc.
   This file is part of elfutils.

   This file is free software; you can redistribute it and/or modify
   it under the terms of either

     * the GNU Lesser General Public License as published by the Free
       Software Foundation; either version 3 of the License, or (at
       your option) any later version

   or

     * the GNU General Public License as published by the Free
       Software Foundation; either version 2 of the License, or (at
       your option) any later version

   or both in parallel, as here.

   elfutils is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received copies of the GNU General Public License and
   the GNU Lesser General Public License along with this program.  If
   not, see <http://www.gnu.org/licenses/>.  */

#ifdef HAVE_CONFIG_H
# include <config.h>
#endif

#include "libdwP.h"
#include "libelfP.h"

#include <limits.h>
#include <search.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <assert.h>
#include <glob.h>

enum SectionIdentifier {
  SECT_NULL = 0,
  SECT_INFO = 1,
  SECT_TYPES, // Reserved/Removed
  SECT_ABBREV,
  SECT_LINE,
  SECT_LOC,
  SECT_STR_OFFSETS,
  SECT_MACINFO,
  SECT_MACRO,
  SECT_LAST,
};

/* See DWARF Debugging Information Format Version 5, section 7.3.5.3 for the details */
typedef struct IndexTable {
  uint16_t version;
  uint32_t section_count, entry_count, slot_count;
  const uint64_t *signatures;
  const uint32_t *indices;
  const uint32_t *sections, *offsets, *sizes;
} IndexTable;

typedef uint32_t IndexRow[SECT_LAST];

/* Result of a search for a matching split unit.
 * `found` indicates whether a match was found.
 * `signature_searched` is the signature that was searched for.
 * `offsets` and `sizes` contains the Unit's contributions to the dwp file.
 */
typedef struct IndexSearchResult {
  IndexRow offsets, sizes;
  uint64_t signature_searched;
  bool found;
} IndexSearchResult;

static IndexTable IndexTable_new(const void *buf, size_t sz) {
  struct IndexTable index = {0};

  // TODO: Use `read_Xubyte_unaligned` to handle different byte-orders.
  const uint32_t *hdr = (uint32_t *)buf;
  index.version = ((uint16_t *)hdr)[0];
  index.section_count = hdr[1];
  index.entry_count = hdr[2];
  index.slot_count = hdr[3];

  /* See https://gcc.gnu.org/wiki/DebugFissionDWP for the details about these pointers. */
  index.signatures = buf + 4 * sizeof(uint32_t);
  index.indices = (const void *)index.signatures + index.slot_count * sizeof(uint64_t);
  index.sections = (const void *)index.indices + index.slot_count * sizeof(uint32_t);
  index.offsets = (const void *)index.sections + index.section_count * sizeof(uint32_t);
  index.sizes = (const void *)index.offsets + index.entry_count * index.section_count * sizeof(uint32_t);

  assert(((const void *)index.sizes + index.entry_count * index.section_count * sizeof(uint32_t)) <= (buf + sz));

  return index;
}

/* Search for the matching `signature` in the `index` table. */
static IndexSearchResult IndexTable_search(const IndexTable *index, uint64_t signature) {
  IndexSearchResult result = {
	.offsets = { 0 },
	.sizes = { 0 },
	.signature_searched = signature,
	.found = false
  };

  if (index->slot_count == 0)
    return result;

  const uint64_t mask = index->slot_count - 1;
  const uint64_t secondary_hash = ((signature >> 32) & mask) | 1;

  // TODO: Use `read_Xubyte_unaligned` to handle different byte-orders.
  /* Iterate through the hashtable until we find a matching signature, or an empty slot. */
  uint64_t hash = signature & mask;
  while (index->signatures[hash] != 0 && index->signatures[hash] != signature)
    hash = (hash + secondary_hash) & mask; // We can use (& mask) instead of (% slot_count) for speed

  if (index->signatures[hash] == signature) {
    result.found = true;

    // TODO: Use `read_Xubyte_unaligned` to handle different byte-orders.
    /* The indices start at one, instead of zero, so subtract one. */
    size_t idx = index->indices[hash] - 1;

    // TODO: Use `read_Xubyte_unaligned` to handle different byte-orders.
    const uint32_t *offsets = &index->offsets[idx * index->section_count];
    const uint32_t *sizes = &index->sizes[idx * index->section_count];
    for (size_t i = 0; i < index->section_count; i++) {
      result.offsets[index->sections[i]] = offsets[i];
      result.sizes[index->sections[i]] = sizes[i];
    }
  }

  return result;
}

void IndexTable_print_search_result(const IndexSearchResult *result) {
	if (!result->found) {
		printf("No match for signature 0x%016lu\n", result->signature_searched);
	} else {
		printf("Found match for signature 0x%016lu\n", result->signature_searched);
		for (size_t i = 1; i < SECT_LAST; i++) {
			printf("  %lu: offset 0x%08x, size 0x%08x\n", i, result->offsets[i], result->sizes[i]);
		}
	}
}

void
try_split_file (Dwarf_CU *cu, const char *dwo_path)
{
  int split_fd = open (dwo_path, O_RDONLY);
  if (split_fd != -1)
    {
      Dwarf *split_dwarf = dwarf_begin (split_fd, DWARF_C_READ);
      if (split_dwarf != NULL)
	{
	  /* For dwp, we need to adjust the offsets of the CU
	   * to align with its contributions within the dwp file.
	   */
	  IndexSearchResult res = { 0 };
	  Elf_Data *cu_index = split_dwarf->sectiondata[IDX_debug_cu_index];
	  if (cu_index != NULL)
	    {
	      IndexTable index = IndexTable_new(cu_index->d_buf, cu_index->d_size);
	      res = IndexTable_search(&index, cu->unit_id8);
	    }

	  Dwarf_CU *split = NULL;
	  while (dwarf_get_units (split_dwarf, split, &split,
				  NULL, NULL, NULL, NULL) == 0)
	    {
	      if (split->unit_type == DW_UT_split_compile
		  && cu->unit_id8 == split->unit_id8)
		{
		  if (tsearch (split->dbg, &cu->dbg->split_tree,
			       __libdw_finddbg_cb) == NULL)
		    {
		      /* Something went wrong.  Don't link.  */
		      __libdw_seterrno (DWARF_E_NOMEM);
		      break;
		    }

		    if (res.found) {
			/* Check the offsets are set, or default to zero.
			 * Then adjust the offsets by the Unit's contributions.
			 */
#define OFFSET_OR(off, default) ((off) != (Dwarf_Off) -1 ? (off) : (default))
			split->str_off_base = __libdw_cu_str_off_base(split) + res.offsets[SECT_STR_OFFSETS];
			split->orig_abbrev_offset = OFFSET_OR(split->orig_abbrev_offset, 0) + res.offsets[SECT_ABBREV];
			split->last_abbrev_offset = OFFSET_OR(split->last_abbrev_offset, 0) + res.offsets[SECT_ABBREV];
			split->locs_base = __libdw_cu_locs_base(split) + res.offsets[SECT_LOC];
#undef OFFSET_OR
		    }

		  /* Link skeleton and split compile units.  */
		  __libdw_link_skel_split (cu, split);

		  /* We have everything we need from this ELF
		     file.  And we are going to close the fd to
		     not run out of file descriptors.  */
		  elf_cntl (split_dwarf->elf, ELF_C_FDDONE);
		  break;
		}
	    }
	  if (cu->split == (Dwarf_CU *) -1)
	    dwarf_end (split_dwarf);
	}
      /* Always close, because we don't want to run out of file
	 descriptors.  See also the elf_fcntl ELF_C_FDDONE call
	 above.  */
      close (split_fd);
    }
}

Dwarf_CU *
internal_function
__libdw_find_split_unit (Dwarf_CU *cu)
{
  /* Only try once.  */
  if (cu->split != (Dwarf_CU *) -1)
    return cu->split;

  /* We need a skeleton unit with a comp_dir and [GNU_]dwo_name attributes.
     The split unit will be the first in the dwo file and should have the
     same id as the skeleton.  */
  if (cu->unit_type == DW_UT_skeleton)
    {
      Dwarf_Die cudie = CUDIE (cu);
      Dwarf_Attribute dwo_name;
      /* It is fine if dwo_dir doesn't exists, but then dwo_name needs
	 to be an absolute path.  */
      if (dwarf_attr (&cudie, DW_AT_dwo_name, &dwo_name) != NULL
	  || dwarf_attr (&cudie, DW_AT_GNU_dwo_name, &dwo_name) != NULL)
	{
	  /* First try the dwo file name in the same directory
	     as we found the skeleton file.  */
	  const char *dwo_file = dwarf_formstring (&dwo_name);
	  const char *debugdir = cu->dbg->debugdir;
	  char *dwo_path = __libdw_filepath (debugdir, NULL, dwo_file);
	  if (dwo_path != NULL)
	    {
	      try_split_file (cu, dwo_path);
	      free (dwo_path);
	    }

	  if (cu->split == (Dwarf_CU *) -1)
	    {
	      /* Try compdir plus dwo_name.  */
	      Dwarf_Attribute compdir;
	      dwarf_attr (&cudie, DW_AT_comp_dir, &compdir);
	      const char *dwo_dir = dwarf_formstring (&compdir);
	      if (dwo_dir != NULL)
		{
		  dwo_path = __libdw_filepath (debugdir, dwo_dir, dwo_file);
		  if (dwo_path != NULL)
		    {
		      try_split_file (cu, dwo_path);
		      free (dwo_path);
		    }
		}
	    }
	  /* XXX If still not found we could try stripping dirs from the
	     comp_dir and adding them from the comp_dir, assuming
	     someone moved a whole build tree around.  */

          /* Finally try the dwp file */
          if (cu->split == (Dwarf_CU *)-1)
            {
              /* Try to locate the dwp file next to the ELF binary. */
	    glob_t glob_result;
	    char dwpglob[PATH_MAX];
	    strcpy(dwpglob, debugdir);
	    strcat(dwpglob, "*.dwp");
	    int ret = glob(dwpglob, 0, NULL, &glob_result);

	    if(ret == 0) {
	      for(size_t i = 0; i < glob_result.gl_pathc; i++) {
		try_split_file (cu, glob_result.gl_pathv[i]);
		if (cu->split != (Dwarf_CU *) -1) break;
	      }
	    }
	    globfree(&glob_result);
            }
	}
    }

  /* If we found nothing, make sure we don't try again.  */
  if (cu->split == (Dwarf_CU *) -1)
    cu->split = NULL;

  return cu->split;
}
