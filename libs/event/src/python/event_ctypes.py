import ctypes

bytes32 = ctypes.c_uint8 * 32

class address(ctypes.c_uint8 * 20):
  pass

# "ne" here is "native encoding", i.e., either big or little depending on the
# host system
class uint256_ne(bytes32):
  pass

class transaction_type(ctypes.c_uint8):
  pass
