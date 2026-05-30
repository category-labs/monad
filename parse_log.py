import json
import ast
import requests
import argparse
import concurrent.futures
import time

session = requests.Session()

parser = argparse.ArgumentParser(description='Parse RPC log file and resubmit requests.')
parser.add_argument('--log-path', nargs='?', default='rpc.log', help='Path to the log file (default: rpc.log)')
parser.add_argument('--rpc-url', dest='eth_rpc_url', help='RPC endpoint URL')
parser.add_argument('--max-requests', type=int, default=None, help='Maximum number of requests to process from the log file')
parser.add_argument('--workers', type=int, default=10, help='Number of parallel workers (default: 10)')
parser.add_argument('--shard', type=int, default=None, help='Shard index (0-based)')
parser.add_argument('--num-shards', type=int, default=None, help='Total number of shards')
parser.add_argument('--debug', action='store_true', help='Enable debug output')
args = parser.parse_args()

log_path = args.log_path
ETH_RPC_URL = args.eth_rpc_url

max_requests = args.max_requests
num_workers = args.workers
shard = args.shard
num_shards = args.num_shards
debug = args.debug

def parse_rust_bytes_debug(s):
    assert s.startswith('b"') and s.endswith('"')
    s = s[2:-1]
    out = bytearray()
    i = 0
    while i < len(s):
        if s[i] == '\\':
            i += 1
            if s[i] == 'n':
                out.append(0x0A)
            elif s[i] == 'r':
                out.append(0x0D)
            elif s[i] == 't':
                out.append(0x09)
            elif s[i] == '0':
                out.append(0x00)
            elif s[i] == '"':
                out.append(ord('"'))
            elif s[i] == '\\':
                out.append(ord('\\'))
            elif s[i] == 'x':
                out.append(int(s[i+1:i+3], 16))
                i += 2
            else:
                raise ValueError(f"Unknown escape: \\{s[i]}")
        else:
            out.append(ord(s[i]))
        i += 1
    return bytes(out)

def send_rpc_call(log_obj):
    if debug:
        print(f'Executing as Ethereum RPC call: {log_obj["body_json"]}')
    try:
        resp = session.post(ETH_RPC_URL, json=log_obj['body_json'])
        if debug:
            print('RPC response:', resp.status_code, resp.text)
        return resp.status_code, resp.text
    except Exception as e:
        print('RPC call failed:', e)
        return None, str(e)


# Collect all log objects to send in parallel
log_objs = []
with open(log_path, 'r') as f:
    count = 0
    n = 0
    for line in f:
        # Sharding: skip lines if n % num_shards != shard (if both specified)
        if num_shards is not None and shard is not None:
            if n % num_shards != shard:
                n += 1
                continue
        n += 1
        if max_requests is not None and count >= max_requests:
            break
        line = line.strip()
        if not line:
            continue
        # Find the first '{' to skip syslog prefix
        json_start = line.find('{')
        if json_start == -1:
            continue
        try:
            log_obj = json.loads(line[json_start:])
            # Try to parse the 'body' field if present
            fields = log_obj.get('fields', {})
            body = fields.get('body')
            if body:
                body_bytes = parse_rust_bytes_debug(body)
                if body_bytes is not None:
                    try:
                        body_str = body_bytes.decode('utf-8')
                        log_obj['body_json'] = json.loads(body_str)
                        # Replace explicit block number with 'finalized' in params if present
                        params = log_obj['body_json'].get('params')
                        if (
                            isinstance(params, list)
                            and len(params) > 1
                        ):
                            log_obj['body_json']['params'][1] = 'finalized'
                        log_objs.append(log_obj)
                        count += 1
                    except Exception:
                        log_obj['body_json'] = None
        except json.JSONDecodeError:
            continue

if log_objs:
    start_time = time.time()
    with concurrent.futures.ThreadPoolExecutor(max_workers=num_workers) as executor:
        futures = [executor.submit(send_rpc_call, log_obj) for log_obj in log_objs]
        for future in concurrent.futures.as_completed(futures):
            status, text = future.result()
    elapsed = time.time() - start_time
    print(f"Total requests sent: {len(log_objs)}")
    print(f"Elapsed time: {elapsed:.2f} seconds")
