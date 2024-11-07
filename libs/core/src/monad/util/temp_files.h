#pragma once

#include <monad/config.h>

#include <stddef.h>

#ifdef __cplusplus
extern "C"
{
#endif

//! \brief Returns a temporary directory in which `O_DIRECT` files definitely
//! work
extern char const *monad_working_temporary_directory();

//! \brief Creates a temporary file, writing the path created into the buffer.
//! You will need to unlink this after yourself and close the file descriptor it
//! returns.
extern int monad_make_temporary_file(char *buffer, size_t buffer_len);

//! \brief Creates already deleted file so no need to clean it up
//! after. You will need to close the file descriptor it returns.
extern int monad_make_temporary_inode();

//! \brief How this Linux accounts for memory
enum monad_memory_accounting_kind
{
    monad_memory_accounting_kind_unknown,
    //! \brief This Linux has been configured for strict memory accounting
    monad_memory_accounting_kind_commit_charge,
    //! \brief This Linux has been configured for over commit memory accounting
    monad_memory_accounting_kind_over_commit
};
//! \brief Return how this Linux accounts for memory
extern enum monad_memory_accounting_kind monad_memory_accounting();

#ifdef __cplusplus
}
#endif
