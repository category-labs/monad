#include <monad/contract/uint256.hpp>

MONAD_NAMESPACE_BEGIN

/////////////////////
//  Little Endian  //
/////////////////////
Uint256Native::Uint256Native(uint256_t x)
    : uint256_t(std::move(x))
{
}

Uint256Native &Uint256Native::add(uint256_t const &other)
{
    *this += other;
    return *this;
}

Uint256Native &Uint256Native::sub(uint256_t const &other)
{
    *this -= other;
    return *this;
}

Uint256BE Uint256Native::to_be() const noexcept
{
    return Uint256BE{
        intx::be::store<evmc_uint256be>(static_cast<uint256_t>(*this))};
}

//////////////////
//  Big Endian  //
//////////////////

Uint256BE::Uint256BE(evmc_uint256be r)
    : raw{std::move(r)}
{
}

bool Uint256BE::operator==(Uint256BE const &other) const noexcept
{
    return 0 == memcmp(this, &other, sizeof(other));
}

Uint256Native Uint256BE::native() const noexcept
{
    return Uint256Native{intx::be::load<uint256_t>(raw)};
}

MONAD_NAMESPACE_END
