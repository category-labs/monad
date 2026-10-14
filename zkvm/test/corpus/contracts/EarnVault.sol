// SPDX-License-Identifier: GPL-3.0-or-later
pragma solidity ^0.8.24;

interface IVaultAsset {
    function transferFrom(address from, address to, uint256 value)
        external
        returns (bool);
    function transfer(address to, uint256 value) external returns (bool);
}

/// The payout case's yield venue: the design's third-party vaults, where
/// "access to the vault is gated by closed-loop allowlisting ... so that only
/// verified contractors can route funds into it", with explicit opt-in, no
/// lock-up and withdrawal at any time.
///
/// Shares are one to one with what was deposited. The return accrues outside
/// the transactions a block carries, so modelling it would change the numbers
/// in a slot and not which slots a block touches -- and it is the slots that
/// cost.
///
/// Seeded at genesis, so no constructor: slot 0 is the asset, slot 1 the
/// allowlist, slot 2 each depositor's shares, slot 3 their total, slot 4 who
/// keeps the allowlist.
contract EarnVault {
    IVaultAsset public asset;
    mapping(address => bool) public verified;
    mapping(address => uint256) public sharesOf;
    uint256 public totalShares;
    address public admin;

    event Deposit(address indexed owner, uint256 assets);
    event Withdraw(address indexed owner, uint256 assets);
    event Verified(address indexed owner, bool ok);

    function deposit(uint256 assets) external {
        require(verified[msg.sender], "not verified");
        require(asset.transferFrom(msg.sender, address(this), assets), "pull");
        sharesOf[msg.sender] += assets;
        totalShares += assets;
        emit Deposit(msg.sender, assets);
    }

    /// Open to anyone holding shares, verified or no longer: removing a
    /// contractor from the allowlist stops new deposits, not their exit.
    function withdraw(uint256 assets) external {
        uint256 s = sharesOf[msg.sender];
        require(s >= assets, "shares");
        unchecked {
            sharesOf[msg.sender] = s - assets;
            totalShares -= assets;
        }
        require(asset.transfer(msg.sender, assets), "push");
        emit Withdraw(msg.sender, assets);
    }

    function setVerified(address owner, bool ok) external {
        require(msg.sender == admin, "admin");
        verified[owner] = ok;
        emit Verified(owner, ok);
    }
}
