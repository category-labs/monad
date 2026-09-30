// SPDX-License-Identifier: GPL-3.0-or-later
pragma solidity ^0.8.24;

interface IWrappedToken {
    function transferFrom(address from, address to, uint256 value)
        external
        returns (bool);
}

/// The two interbank legs of a cross-currency wholesale payment, settled
/// together or not at all. The design's example: 72 AAA move from bank A1 to
/// bank A2 in one currency's tokens, and 60 BBB from A2 to B1 in the other's,
/// and "the two interbank legs are conditioned on one another and settle
/// together or not at all".
///
/// The design leaves atomic swaps to the contract level and gives the
/// cross-L2 version, with a lock on each L2 and a coordinator on the L1. Here
/// both currencies are on one L2, where a transaction is already atomic, so
/// two calls are enough: the debtor's bank proposes the terms, and the
/// intermediary -- paid by the first leg, paying the second, and supplying the
/// conversion between them -- settles both legs in one transaction. Either leg
/// failing reverts both.
///
/// Only the hash of the terms is stored; whoever settles or cancels passes
/// them again, as they appear in the Proposed event. Every bank has approved
/// this contract on every token it holds, so the legs move by transferFrom,
/// and the token's own eligibility check still applies to each of them.
///
/// Seeded at genesis like the tokens, so no constructor. Slot 0 is `pending`.
contract PvpSettlement {
    struct Payment {
        /// The debtor's own reference, so that two otherwise equal payments
        /// are two payments.
        uint256 ref;
        address tokenA;
        address debtor;
        address intermediary;
        uint256 amountA;
        address tokenB;
        address creditor;
        uint256 amountB;
    }

    /// The payments proposed and neither settled nor cancelled, by the hash
    /// of their terms.
    mapping(bytes32 => bool) public pending;

    event Proposed(bytes32 indexed id, Payment terms);
    event Settled(bytes32 indexed id);
    event Cancelled(bytes32 indexed id);

    function propose(Payment calldata p) external returns (bytes32 id) {
        require(msg.sender == p.debtor, "not the debtor");
        id = keccak256(abi.encode(p));
        require(!pending[id], "pending");
        pending[id] = true;
        emit Proposed(id, p);
    }

    /// By the intermediary: both legs, or neither.
    function settle(Payment calldata p) external {
        require(msg.sender == p.intermediary, "not the intermediary");
        bytes32 id = keccak256(abi.encode(p));
        require(pending[id], "not pending");
        delete pending[id];
        require(
            IWrappedToken(p.tokenA).transferFrom(
                p.debtor, p.intermediary, p.amountA),
            "leg A");
        require(
            IWrappedToken(p.tokenB).transferFrom(
                p.intermediary, p.creditor, p.amountB),
            "leg B");
        emit Settled(id);
    }

    /// By the debtor, while the intermediary has not settled.
    function cancel(Payment calldata p) external {
        require(msg.sender == p.debtor, "not the debtor");
        bytes32 id = keccak256(abi.encode(p));
        require(pending[id], "not pending");
        delete pending[id];
        emit Cancelled(id);
    }
}
