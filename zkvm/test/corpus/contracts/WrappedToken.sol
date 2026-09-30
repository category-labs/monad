// SPDX-License-Identifier: GPL-3.0-or-later
pragma solidity ^0.8.24;

interface INamespaceSpokeSend {
    function sendNamespaceMessage(address to, bytes calldata data) external;
}

/// An L1 token natively wrapped into the L2, as the design's setup creates one
/// per configured token ("creation of ERC-20 L2 smart contracts for the wrapped
/// tokens"). Three things the design asks of it that a plain ERC-20 does not
/// do:
///
/// - Eligibility is enforced by the token, because "a transferable balance can
///   be moved by its holder to destinations the platform does not control": a
///   balance only moves between holders the token's admin has admitted. The
///   flag is the top bit of the holder's balance slot, the way USDC v2.2 packs
///   its blacklist state, so checking it reads no slot a transfer would not
///   read anyway. Balances stay below 2**255, which is what keeps the flag and
///   the amount apart: every balance is part of totalSupply, and totalSupply is
///   created below that bound and only falls.
/// - Leaving the L2 burns: `withdrawToL1` destroys the L2 balance and sends the
///   L1 bridge, through the spoke, whom to pay -- "the sending L2 burns the L2
///   tokens".
/// - There is no mint. The design mints on a deposit message from the L1. The
///   spoke does record L1 anchors, but the operator posts them and nothing the
///   proof publishes ties them to the hub, so a mint against one would be money
///   the operator creates. Every balance is created at genesis instead.
///
/// The corpus seeds this contract's code and storage at genesis rather than
/// deploying it, so it has no constructor and no immutables: everything it
/// reads is in the storage layout below, and workload.cpp writes to exactly
/// those slots.
contract WrappedToken {
    uint256 private constant ELIGIBLE = 1 << 255;

    /// Slot 0: balance | ELIGIBLE.
    mapping(address => uint256) private _balances;
    /// Slot 1.
    mapping(address => mapping(address => uint256)) public allowance;
    /// Slot 2.
    uint256 public totalSupply;
    /// Slot 3: who admits holders and removes them.
    address public admin;
    /// Slot 4: the spoke a withdrawal is sent through.
    address public spoke;
    /// Slot 5: the L1 contract a withdrawal is addressed to, which releases
    /// the native token once the message is proven there.
    address public l1Bridge;

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(
        address indexed owner, address indexed spender, uint256 value);
    event Eligibility(address indexed holder, bool eligible);

    function balanceOf(address holder) external view returns (uint256) {
        return _balances[holder] & ~ELIGIBLE;
    }

    function eligible(address holder) external view returns (bool) {
        return (_balances[holder] & ELIGIBLE) != 0;
    }

    function transfer(address to, uint256 value) external returns (bool) {
        _move(msg.sender, to, value);
        return true;
    }

    function approve(address spender, uint256 value) external returns (bool) {
        allowance[msg.sender][spender] = value;
        emit Approval(msg.sender, spender, value);
        return true;
    }

    function transferFrom(address from, address to, uint256 value)
        external
        returns (bool)
    {
        uint256 allowed = allowance[from][msg.sender];
        if (allowed != type(uint256).max) {
            require(allowed >= value, "allowance");
            unchecked {
                allowance[from][msg.sender] = allowed - value;
            }
        }
        _move(from, to, value);
        return true;
    }

    /// A payroll run: "a single instruction covering many recipients".
    function batchTransfer(address[] calldata to, uint256[] calldata value)
        external
        returns (bool)
    {
        require(to.length == value.length, "length");
        for (uint256 i = 0; i < to.length; ++i) {
            _move(msg.sender, to[i], value[i]);
        }
        return true;
    }

    /// Leaves the L2: the balance is burnt here, and the message tells the L1
    /// bridge which L2 holder it came from and which L1 account to pay.
    function withdrawToL1(uint256 value, address l1Recipient) external {
        uint256 b = _balances[msg.sender];
        require((b & ELIGIBLE) != 0, "ineligible");
        require((b & ~ELIGIBLE) >= value, "balance");
        unchecked {
            _balances[msg.sender] = b - value;
            totalSupply -= value;
        }
        emit Transfer(msg.sender, address(0), value);
        INamespaceSpokeSend(spoke).sendNamespaceMessage(
            l1Bridge, abi.encode(msg.sender, l1Recipient, value));
    }

    function setEligible(address holder, bool ok) external {
        require(msg.sender == admin, "admin");
        uint256 b = _balances[holder];
        _balances[holder] = ok ? b | ELIGIBLE : b & ~ELIGIBLE;
        emit Eligibility(holder, ok);
    }

    function _move(address from, address to, uint256 value) private {
        uint256 f = _balances[from];
        require((f & ELIGIBLE) != 0, "ineligible");
        require((_balances[to] & ELIGIBLE) != 0, "ineligible");
        require((f & ~ELIGIBLE) >= value, "balance");
        unchecked {
            _balances[from] = f - value;
            // Read again rather than reuse f, so a transfer to oneself nets
            // to zero.
            _balances[to] += value;
        }
        emit Transfer(from, to, value);
    }
}
