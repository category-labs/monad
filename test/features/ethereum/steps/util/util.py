log_mapping = {
    "TraceL3": 0,
    "TraceL2": 1,
    "TraceL1": 2,
    "Debug": 3,
    "Info": 4,
    "Warning": 5,
    "Error": 6,
    "Critical": 7,
    "Backtrace": 8,
}

logger_and_level_to_output = {
    ("trie_db_logger", "Info"): "ACCOUNT_UPDATES",
    ("block_logger", "Info"): "Start executing Block",
    ("block_logger", "Debug"): "BlockHeader Fields",
    ("txn_logger", "Info"): "Start executing Transaction",
}
