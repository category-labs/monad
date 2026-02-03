import json
import ast
import argparse
import asyncio
import httpx
import time

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

async def send_rpc_call(client, url, body_json, debug):
    if debug:
        print(f'Executing as Ethereum RPC call: {body_json}')
    try:
        resp = await client.post(url, json=body_json)
        if debug:
            print('RPC response:', resp.status_code, resp.text)
        return resp.status_code, await resp.aread()
    except Exception as e:
        if debug:
            print('RPC call failed:', e)
        return None, str(e)

async def main():
    parser = argparse.ArgumentParser(description='Parse RPC log file and resubmit requests (asyncio version).')
    parser.add_argument('--log-path', nargs='?', default='rpc.log', help='Path to the log file (default: rpc.log)')
    parser.add_argument('--rpc-url', dest='eth_rpc_url', required=True, help='RPC endpoint URL')
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

    log_objs = []
    with open(log_path, 'r') as f:
        count = 0
        n = 0
        for line in f:
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
            json_start = line.find('{')
            if json_start == -1:
                continue
            try:
                log_obj = json.loads(line[json_start:])
                fields = log_obj.get('fields', {})
                body = fields.get('body')
                if body:
                    body_bytes = parse_rust_bytes_debug(body)
                    if body_bytes is not None:
                        try:
                            body_str = body_bytes.decode('utf-8')
                            log_obj['body_json'] = json.loads(body_str)
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

    queue = asyncio.Queue()
    for log_obj in log_objs:
        await queue.put(log_obj)

    start_time = time.time()
    async def worker():
        async with httpx.AsyncClient(timeout=30) as client:
            while not queue.empty():
                log_obj = await queue.get()
                await send_rpc_call(client, ETH_RPC_URL, log_obj['body_json'], debug)
                queue.task_done()

    tasks = [asyncio.create_task(worker()) for _ in range(num_workers)]
    await queue.join()
    elapsed = time.time() - start_time
    print(f"Total requests sent: {len(log_objs)}")
    print(f"Elapsed time: {elapsed:.2f} seconds")

if __name__ == '__main__':
    asyncio.run(main())
