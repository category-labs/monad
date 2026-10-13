#!/bin/bash
# Build patched GCC 15.2.0: the guest needs GCC 15's musttail support.
# Reuse xPack's target tools and libraries. See README.md for patch order.
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

# Expose binutils before configure so GCC detects assembler COMDAT support.
# Otherwise it falls back to .gnu.linkonce, which broke the guest at runtime.
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
# Install xPack's RV64 library variant directly: this compiler has no multilib
# selection, and xPack's default libraries are 32-bit.
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
# make all-gcc omits libgcc and crt objects; reuse the same RV64 variant.
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
