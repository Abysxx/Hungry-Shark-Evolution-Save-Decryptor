import hashlib
import json
import struct
import sys
import time
from pathlib import Path

from Crypto.Cipher import AES
from Crypto.Hash import SHA1
from Crypto.Protocol.KDF import PBKDF2

# ---------------------------------------------------------------------------
# banner / tiny console helpers
# ---------------------------------------------------------------------------
RESET = "\033[0m"
CYAN = "\033[96m"
GREY = "\033[90m"
GREEN = "\033[92m"
RED = "\033[91m"
YELLOW = "\033[93m"

def show_banner():
    art = r"""
 ⠀ ⢯⠙⠲⢤⣀⠀⠀⠀⠀⠀⠀⠀⠀⠀
⠀⠀⠸⡆⠀⠀⠈⠳⣄
⠀⠀⠀⡇⠀⠀⠀⠀⠈⢳⡀
⠀⠀⢰⠇⠀⠀⠀⠀⠀⠈⢷⠀⠀⠀⠀⠀
⣀⡴⠒⢾⡀⣀⡴⠒⢦⣀⢀⡼⠓⢦⣀
⣩⠴⠒⢶⣉⣉⡴⠒⢦⣉⣉⡴⠒⠶⣌
⠁⠀⠀⠀⠈⠁⠀⠀⠀⠈⠁⠀⠀⠀⠈
"""
    print(f"{CYAN}{art}{RESET}")
    print(f"{CYAN}        Hungry Shark Evolution{RESET}")
    print(f"{CYAN}           Save Decryptor{RESET}")
    print(f"{GREY}              By Abysxx{RESET}")
    print(f"{GREY}{'-' * 42}{RESET}\n")


def info(msg):
    print(f"{CYAN}[*]{RESET} {msg}")


def ok(msg):
    print(f"{GREEN}[+]{RESET} {msg}")


def warn(msg):
    print(f"{YELLOW}[!]{RESET} {msg}")


def err(msg):
    print(f"{RED}[-]{RESET} {msg}")


# ---------------------------------------------------------------------------
# LZF compression / decompression
# ---------------------------------------------------------------------------
def lzf_decompress(data: bytes) -> bytes:
    """Standard LZF decompression (as produced by the CLZF2 library)."""
    out = bytearray()
    i = 0
    n = len(data)
    while i < n:
        ctrl = data[i]
        i += 1
        if ctrl < 32:
            # Literal run of (ctrl + 1) bytes.
            length = ctrl + 1
            out.extend(data[i:i + length])
            i += length
        else:
            length = ctrl >> 5
            if length == 7:
                length += data[i]
                i += 1
            ref_offset = ((ctrl & 0x1F) << 8) | data[i]
            i += 1
            ref = len(out) - ref_offset - 1
            length += 2
            for _ in range(length):
                out.append(out[ref])
                ref += 1
    return bytes(out)


def lzf_compress(data: bytes) -> bytes:
    """LZF compression compatible with lzf_decompress above."""
    n = len(data)
    out = bytearray()
    i = 0
    literals = []
    HASH_BITS = 16
    HASH_SIZE = 1 << HASH_BITS
    htab = [-1] * HASH_SIZE

    def hash3(pos):
        return (((data[pos] << 16) | (data[pos + 1] << 8) | data[pos + 2]) *
                2654435761) >> (32 - HASH_BITS) & (HASH_SIZE - 1)

    def flush_literals():
        while literals:
            chunk = literals[:32]
            out.append(len(chunk) - 1)
            out.extend(chunk)
            del literals[:len(chunk)]

    while i < n:
        match_pos = -1
        if i + 3 <= n:
            h = hash3(i)
            match_pos = htab[h]
            htab[h] = i

        best_len = 0
        offset = 0
        if match_pos >= 0:
            offset = i - match_pos - 1
            if 0 <= offset < 8192:
                max_len = min(264, n - i)
                l = 0
                while l < max_len and data[match_pos + l] == data[i + l]:
                    l += 1
                if l >= 3:
                    best_len = l

        if best_len >= 3:
            flush_literals()
            length = best_len - 2
            if length < 7:
                out.append((length << 5) | (offset >> 8))
                out.append(offset & 0xFF)
            else:
                out.append((7 << 5) | (offset >> 8))
                out.append(length - 7)
                out.append(offset & 0xFF)
            # index a few positions inside the match to help later matches
            end = i + best_len
            k = i + 1
            while k < end and k + 3 <= n:
                htab[hash3(k)] = k
                k += 1
            i = end
        else:
            literals.append(data[i])
            i += 1
            if len(literals) == 32:
                flush_literals()

    flush_literals()
    return bytes(out)


# ---------------------------------------------------------------------------
# header parsing / building
# ---------------------------------------------------------------------------
def parse_header(data: bytes):
    """Parse the plaintext SaveUtilities header. Returns (header_dict, payload_offset)."""
    version = struct.unpack_from('<i', data, 0)[0]
    header_len = struct.unpack_from('<i', data, 4)[0]
    off = 8
    modified_time = struct.unpack_from('<i', data, off)[0]
    off += 4
    progress = struct.unpack_from('<I', data, off)[0]
    off += 4
    name_len = struct.unpack_from('<i', data, off)[0]
    off += 4
    device_name = data[off:off + name_len].decode('ascii', errors='replace')
    off += name_len
    md5_hash = data[off:off + 32].decode('ascii', errors='replace')
    off += 32
    content_length = struct.unpack_from('<i', data, off)[0]
    off += 4

    header = {
        'version': version,
        'header_len': header_len,
        'modified_time': modified_time,
        'progress': progress,
        'device_name': device_name,
        'md5_hash_of_ciphertext': md5_hash,
        'content_length': content_length,
    }
    return header, off


def build_header(version, modified_time, progress, device_name, md5_hash, content_length):
    device_bytes = device_name.encode('ascii', errors='replace')
    rest = (
        struct.pack('<i', modified_time) +
        struct.pack('<I', progress) +
        struct.pack('<i', len(device_bytes)) +
        device_bytes +
        md5_hash.encode('ascii') +
        struct.pack('<i', content_length)
    )
    header_len = len(rest)
    return struct.pack('<i', version) + struct.pack('<i', header_len) + rest


# ---------------------------------------------------------------------------
# crypto
# ---------------------------------------------------------------------------
def derive_key_iv(user_id: str):
    """PBKDF2-HMAC-SHA1(password=user_id, salt=repeated-length-string, 100 iters) -> (key16, iv16)."""
    password = user_id.encode('utf-8')
    salt = ','.join([str(len(user_id))] * 8).encode('utf-8')
    key_iv = PBKDF2(password, salt, dkLen=32, count=100, hmac_hash_module=SHA1)
    return key_iv[:16], key_iv[16:32]


def decrypt_save(raw: bytes, user_id: str):
    header, payload_offset = parse_header(raw)
    ciphertext = raw[payload_offset:payload_offset + header['content_length']]
    if len(ciphertext) % 16 != 0:
        raise ValueError(
            f"Ciphertext length {len(ciphertext)} isn't a multiple of 16 -- "
            "file may be truncated or the header wasn't parsed correctly."
        )
    key, iv = derive_key_iv(user_id)
    cipher = AES.new(key, AES.MODE_CBC, iv)
    padded = cipher.decrypt(ciphertext)
    pad_len = padded[-1]
    if not (1 <= pad_len <= 16) or padded[-pad_len:] != bytes([pad_len]) * pad_len:
        raise ValueError(
            "PKCS7 padding is invalid after decryption -- wrong user-id/password most likely. "
            "The save's filename (minus .sav) is usually the correct user-id."
        )
    compressed = padded[:-pad_len]
    decompressed = lzf_decompress(compressed)
    text = decompressed.decode('utf-8')
    parsed = json.loads(text)
    return header, parsed


def encrypt_save(parsed, user_id: str, device_name="Device", version=1, progress=0, modified_time=None):
    text = json.dumps(parsed, ensure_ascii=False)
    compressed = lzf_compress(text.encode('utf-8'))

    pad_len = 16 - (len(compressed) % 16)
    if pad_len == 0:
        pad_len = 16
    padded = compressed + bytes([pad_len]) * pad_len

    key, iv = derive_key_iv(user_id)
    cipher = AES.new(key, AES.MODE_CBC, iv)
    ciphertext = cipher.encrypt(padded)

    md5_hash = hashlib.md5(ciphertext).hexdigest().upper()
    if modified_time is None:
        modified_time = int(time.time())

    header = build_header(
        version=version,
        modified_time=modified_time,
        progress=progress,
        device_name=device_name,
        md5_hash=md5_hash,
        content_length=len(ciphertext),
    )
    return header + ciphertext


# ---------------------------------------------------------------------------
# main flow
# ---------------------------------------------------------------------------
def get_input_path() -> Path:
    if len(sys.argv) > 1:
        return Path(sys.argv[1])
    raw = input(f"Drag & drop a .sav or .json file here, then press Enter:{RESET} ").strip()
    raw = raw.strip('"').strip("'")
    return Path(raw)


def handle_sav(path: Path):
    info(f"Detected .sav file -> decrypting")
    raw = path.read_bytes()
    user_id = path.stem

    try:
        header, parsed = decrypt_save(raw, user_id)
    except ValueError as e:
        err(f"Decryption failed: {e}")
        alt = input(f"{YELLOW}Enter a different user-id to try (blank to cancel):{RESET} ").strip()
        if not alt:
            sys.exit(1)
        try:
            header, parsed = decrypt_save(raw, alt)
            user_id = alt
        except ValueError as e2:
            err(f"Decryption failed again: {e2}")
            sys.exit(1)

    info("Header:")
    for k, v in header.items():
        print(f"    {GREY}{k}:{RESET} {v}")
    print(f"    {GREY}user_id used:{RESET} {user_id}")

    out_path = path.with_suffix('.json')
    out_path.write_text(json.dumps(parsed, indent=2, ensure_ascii=False), encoding='utf-8')
    ok(f"Decrypted {len(parsed)} fields -> {out_path}")

    header_path = path.with_suffix('.header.json')
    header_sidecar = {
        'version': header['version'],
        'modified_time': header['modified_time'],
        'progress': header['progress'],
        'device_name': header['device_name'],
    }
    header_path.write_text(json.dumps(header_sidecar, indent=2), encoding='utf-8')
    ok(f"Saved original header (for re-encrypting later) -> {header_path}")


def handle_json(path: Path):
    info("Detected .json file -> encrypting")
    parsed = json.loads(path.read_text(encoding='utf-8'))
    user_id = path.stem

    header_path = path.with_suffix('.header.json')
    if header_path.exists():
        saved_header = json.loads(header_path.read_text(encoding='utf-8'))
        info(f"Found original header at {header_path} -- reusing its modified_time/version/progress/device_name")
        data = encrypt_save(
            parsed, user_id,
            device_name=saved_header.get('device_name', 'Device'),
            version=saved_header.get('version', 1),
            progress=saved_header.get('progress', 0),
            modified_time=saved_header.get('modified_time'),
        )
    else:
        warn(f"No {header_path.name} found next to this file -- stamping a fresh modified_time. "
             "If this content came from a real save, the game may reject it as tampered/rolled back.")
        data = encrypt_save(parsed, user_id)

    out_path = path.with_name(f"{user_id}.sav")
    out_path.write_bytes(data)
    ok(f"Encrypted {len(parsed)} fields -> {out_path}")


def main():
    show_banner()
    path = get_input_path()

    if not path.exists():
        err(f"File not found: {path}")
        sys.exit(1)

    suffix = path.suffix.lower()
    if suffix == '.sav':
        handle_sav(path)
    elif suffix == '.json':
        handle_json(path)
    else:
        err(f"Unrecognized extension '{suffix}' -- expected .sav or .json")
        sys.exit(1)


if __name__ == '__main__':
    main()
