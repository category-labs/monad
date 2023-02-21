add_unit_test(
    TARGET monad-rlptests
    SOURCES
    decode.cpp
    decode_encode_account.cpp
    decode_encode_helpers.cpp
    decode_encode_transaction.cpp
    encode.cpp encode_receipt.cpp
    LIBRARIES
    monad)
