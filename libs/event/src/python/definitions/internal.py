from event_ctypes import *

#
# NONE
#

register_event('NONE', None,
    "reserved code so that 0 remains invalid")

#
# RING_INIT
#

register_event('RING_INIT', None,
    "Posted when a recorder ring is enabled after being reset")

#
# THREAD CREATE
#

class thread_info(ctypes.Structure):
  _fields_ = (
    ('seqno', ctypes.c_uint64),
    ('epoch_nanos', ctypes.c_uint64),
    ('process_id', ctypes.c_uint64),
    ('thread_id', ctypes.c_uint64),
    ('source_id', ctypes.c_uint8),
    ('thread_name', ctypes.c_char * 31)
  )

register_event('THREAD_CREATE', thread_info,
    "Sent when a new thread starts recording data")

#
# THREAD_EXIT
#

register_event('THREAD_EXIT', None,
    "Sent immediately before a thread exits")

#
# HEARTBEAT
#

register_event('HEARTBEAT', None,
    "Periodic heartbeat emitted by the event server")

#
# TEST_COUNTER
#

class test_counter(ctypes.Structure):
  _fields_ = (
    ('writer_id', ctypes.c_uint8),
    ('counter', ctypes.c_uint64),
  )

register_event('TEST_COUNTER', test_counter,
    "A special event emitted only by the test suite")
