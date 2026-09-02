#!/bin/bash
# build-gcc15.sh — the upstream ZisK DMA lowering, ported to GCC 15.2.0.
#
# Upstream targets 14.3.0, which cannot build the Monad guest: its interpreter
# needs __attribute__((musttail)), and that arrived in GCC 15. The port is
# mechanical -- riscv.h and riscv.md apply with fuzz, and the three remaining
# hunks are pure additions whose context moved. See README.md.
#
# Only the compiler is built (make all-gcc); the target side is grafted from the
# xPack the guest already uses, so the versions match by construction.
set -euo pipefail
GCC_VERSION=15.2.0
PREFIX="${ZISK_DMA_GCC_PREFIX:-$HOME/.local/xPacks/zisk-dma-gcc-$GCC_VERSION}"
if [ -n "${ZISK_XPACK_DIR:-}" ]; then
    XPACK="$ZISK_XPACK_DIR"
elif [ -x "$HOME/.local/xPacks/xpack-riscv-none-elf-gcc-$GCC_VERSION-1/bin/riscv-none-elf-gcc" ]; then
    XPACK="$HOME/.local/xPacks/xpack-riscv-none-elf-gcc-$GCC_VERSION-1"
else
    XPACK="$HOME/riscv_gcc_multilib"
fi
SRC="${ZISK_DMA_GCC_SRC:?set ZISK_DMA_GCC_SRC to the patched gcc-$GCC_VERSION source}"
BUILD="${ZISK_DMA_GCC_BUILD:-$SRC/../build}"
JOBS=$(sysctl -n hw.ncpu 2>/dev/null || echo 4)
say() { printf '==> %s\n' "$*"; }
die() { printf 'error: %s\n' "$*" >&2; exit 1; }

[ -x "$XPACK/bin/riscv-none-elf-as" ] || die "GCC $GCC_VERSION xPack not at $XPACK (set ZISK_XPACK_DIR)"
"$XPACK/bin/riscv-none-elf-gcc" --version | head -1 | grep -q "$GCC_VERSION" ||
    die "xPack is not $GCC_VERSION; its headers and binutils must match exactly"
grep -q riscv_zisk_expand_cpymem "$SRC/gcc/config/riscv/riscv-string.cc" ||
    die "source at $SRC is not patched"
command -v g++-13 >/dev/null || die "no g++-13 for the host build"

# The xPack's binutils must be visible *at configure time*, not just grafted in
# afterwards. GCC probes the target assembler for COMDAT group support, and with
# no assembler to probe it falls back to .gnu.linkonce: the guest then links with
# 1,983 sections instead of 16 and reads a wild address on the first run. The
# compiler proper is byte-identical either way, so this is invisible until the
# guest actually executes.
export PATH="$XPACK/bin:$PATH"

say "configuring (compiler only), $JOBS jobs"
rm -rf "$BUILD" && mkdir -p "$BUILD" && cd "$BUILD"
CC=gcc-13 CXX=g++-13 "$SRC/configure" \
    --target=riscv-none-elf --prefix="$PREFIX" \
    --with-as="$XPACK/bin/riscv-none-elf-as" \
    --with-ld="$XPACK/bin/riscv-none-elf-ld" \
    --with-arch=rv64ima_zicsr --with-abi=lp64 \
    --disable-multilib --disable-nls --disable-shared --disable-threads \
    --disable-libssp --disable-libquadmath --disable-libgomp --disable-libatomic \
    --enable-languages=c,c++ --without-headers --with-newlib >configure.log 2>&1 ||
    { tail -25 configure.log; die "configure failed"; }

say "building"
make all-gcc -j"$JOBS" >build.log 2>&1 ||
    { grep -E "[Ee]rror" build.log | head -15; die "build failed (see $BUILD/build.log)"; }
make install-gcc >install.log 2>&1 || die "install failed"

say "grafting the xPack target side"
# Not a symlink to the whole tree: the xPack is multilib and its base lib/ is the
# 32-bit variant, which links as "incompatible with elf64-littleriscv". This
# compiler is --disable-multilib, so lib/ has to *be* the variant the guest wants.
MULTI=$("$XPACK/bin/riscv-none-elf-gcc" -march=rv64ima -mabi=lp64 -print-multi-directory)
rm -rf "$PREFIX/riscv-none-elf"; mkdir -p "$PREFIX/riscv-none-elf/lib"
ln -s "$XPACK/riscv-none-elf/include" "$PREFIX/riscv-none-elf/include"
ln -s "$XPACK/riscv-none-elf/bin"     "$PREFIX/riscv-none-elf/bin"
for f in "$XPACK/riscv-none-elf/lib/$MULTI"/*; do
    ln -sf "$f" "$PREFIX/riscv-none-elf/lib/$(basename "$f")"
done
ln -sf "$XPACK/riscv-none-elf/lib/ldscripts" "$PREFIX/riscv-none-elf/lib/ldscripts"
for t in as ld ar ranlib nm objcopy objdump strip readelf; do
    [ -e "$XPACK/bin/riscv-none-elf-$t" ] && ln -sf "$XPACK/bin/riscv-none-elf-$t" "$PREFIX/bin/"
done
# libgcc and the crt objects: `make all-gcc` builds none of them, and the guest's
# CMake fails on `-print-libgcc-file-name` without one. Take the multilib variant
# the xPack itself selects for the guest's flags -- the base directory holds a
# different ABI, and this compiler is --disable-multilib so it only looks in `.`.
SRCLIB="$XPACK/lib/gcc/riscv-none-elf/$GCC_VERSION/$MULTI"
DSTLIB="$PREFIX/lib/gcc/riscv-none-elf/$GCC_VERSION"
[ -f "$SRCLIB/libgcc.a" ] || die "no libgcc.a at $SRCLIB"
say "grafting libgcc from multilib $MULTI"
for f in "$SRCLIB"/*; do ln -sf "$f" "$DSTLIB/$(basename "$f")"; done

# The guest's build.sh drives riscv64-unknown-elf-*, the xPack's own alias set.
for f in "$PREFIX"/bin/riscv-none-elf-*; do
    b=$(basename "$f"); ln -sf "$f" "$PREFIX/bin/riscv64-unknown-elf-${b#riscv-none-elf-}"
done

say "checking the flag parses AND lowers"
tmp=$(mktemp -d)
printf '#include <cstring>\nextern void sink(void*);\nvoid f(void*d,const void*s){std::memcpy(d,s,32);sink(d);}\n' > "$tmp/t.cpp"
"$PREFIX/bin/riscv-none-elf-g++" -O2 -march=rv64ima_zicsr -mabi=lp64 -mcmodel=medany \
    -mzisk-dma -S -o "$tmp/t.s" "$tmp/t.cpp" || die "compile with -mzisk-dma failed"
grep -qE 'csrs?[[:space:]]+.*0x813' "$tmp/t.s" || { cat "$tmp/t.s"; die "flag parses but emits no DMA marker"; }
say "marker emitted:"; grep -E 'csr' "$tmp/t.s" | head -3
rm -rf "$tmp"
say "done: $PREFIX"
"$PREFIX/bin/riscv-none-elf-g++" --version | head -1
