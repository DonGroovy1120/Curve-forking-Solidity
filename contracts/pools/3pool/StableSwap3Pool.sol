//SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

interface IERC20Metadata is IERC20 {
    /**
     * @dev Returns the name of the token.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the symbol of the token.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the decimals places of the token.
     */
    function decimals() external view returns (uint8);
}


contract ERC20 is Context, IERC20, IERC20Metadata {
    mapping(address => uint256) private _balances;

    mapping(address => mapping(address => uint256)) private _allowances;

    uint256 private _totalSupply;

    string private _name;
    string private _symbol;

    /**
     * @dev Sets the values for {name} and {symbol}.
     *
     * The default value of {decimals} is 18. To select a different value for
     * {decimals} you should overload it.
     *
     * All two of these values are immutable: they can only be set once during
     * construction.
     */
    constructor(string memory name_, string memory symbol_) {
        _name = name_;
        _symbol = symbol_;
    }

    /**
     * @dev Returns the name of the token.
     */
    function name() public view virtual override returns (string memory) {
        return _name;
    }

    /**
     * @dev Returns the symbol of the token, usually a shorter version of the
     * name.
     */
    function symbol() public view virtual override returns (string memory) {
        return _symbol;
    }

    /**
     * @dev Returns the number of decimals used to get its user representation.
     * For example, if `decimals` equals `2`, a balance of `505` tokens should
     * be displayed to a user as `5.05` (`505 / 10 ** 2`).
     *
     * Tokens usually opt for a value of 18, imitating the relationship between
     * Ether and Wei. This is the value {ERC20} uses, unless this function is
     * overridden;
     *
     * NOTE: This information is only used for _display_ purposes: it in
     * no way affects any of the arithmetic of the contract, including
     * {IERC20-balanceOf} and {IERC20-transfer}.
     */
    function decimals() public view virtual override returns (uint8) {
        return 18;
    }

    /**
     * @dev See {IERC20-totalSupply}.
     */
    function totalSupply() public view virtual override returns (uint256) {
        return _totalSupply;
    }

    /**
     * @dev See {IERC20-balanceOf}.
     */
    function balanceOf(address account) public view virtual override returns (uint256) {
        return _balances[account];
    }

    /**
     * @dev See {IERC20-transfer}.
     *
     * Requirements:
     *
     * - `to` cannot be the zero address.
     * - the caller must have a balance of at least `amount`.
     */
    function transfer(address to, uint256 amount) public virtual override returns (bool) {
        address owner = _msgSender();
        _transfer(owner, to, amount);
        return true;
    }

    /**
     * @dev See {IERC20-allowance}.
     */
    function allowance(address owner, address spender) public view virtual override returns (uint256) {
        return _allowances[owner][spender];
    }

    /**
     * @dev See {IERC20-approve}.
     *
     * NOTE: If `amount` is the maximum `uint256`, the allowance is not updated on
     * `transferFrom`. This is semantically equivalent to an infinite approval.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function approve(address spender, uint256 amount) public virtual override returns (bool) {
        address owner = _msgSender();
        _approve(owner, spender, amount);
        return true;
    }

    /**
     * @dev See {IERC20-transferFrom}.
     *
     * Emits an {Approval} event indicating the updated allowance. This is not
     * required by the EIP. See the note at the beginning of {ERC20}.
     *
     * NOTE: Does not update the allowance if the current allowance
     * is the maximum `uint256`.
     *
     * Requirements:
     *
     * - `from` and `to` cannot be the zero address.
     * - `from` must have a balance of at least `amount`.
     * - the caller must have allowance for ``from``'s tokens of at least
     * `amount`.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) public virtual override returns (bool) {
        address spender = _msgSender();
        _spendAllowance(from, spender, amount);
        _transfer(from, to, amount);
        return true;
    }

    /**
     * @dev Atomically increases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {
        address owner = _msgSender();
        _approve(owner, spender, _allowances[owner][spender] + addedValue);
        return true;
    }

    /**
     * @dev Atomically decreases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `spender` must have allowance for the caller of at least
     * `subtractedValue`.
     */
    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns (bool) {
        address owner = _msgSender();
        uint256 currentAllowance = _allowances[owner][spender];
        require(currentAllowance >= subtractedValue, "ERC20: decreased allowance below zero");
        unchecked {
            _approve(owner, spender, currentAllowance - subtractedValue);
        }

        return true;
    }

    /**
     * @dev Moves `amount` of tokens from `sender` to `recipient`.
     *
     * This internal function is equivalent to {transfer}, and can be used to
     * e.g. implement automatic token fees, slashing mechanisms, etc.
     *
     * Emits a {Transfer} event.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `from` must have a balance of at least `amount`.
     */
    function _transfer(
        address from,
        address to,
        uint256 amount
    ) internal virtual {
        require(from != address(0), "ERC20: transfer from the zero address");
        require(to != address(0), "ERC20: transfer to the zero address");

        _beforeTokenTransfer(from, to, amount);

        uint256 fromBalance = _balances[from];
        require(fromBalance >= amount, "ERC20: transfer amount exceeds balance");
        unchecked {
            _balances[from] = fromBalance - amount;
        }
        _balances[to] += amount;

        emit Transfer(from, to, amount);

        _afterTokenTransfer(from, to, amount);
    }

    /** @dev Creates `amount` tokens and assigns them to `account`, increasing
     * the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     */
    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: mint to the zero address");

        _beforeTokenTransfer(address(0), account, amount);

        _totalSupply += amount;
        _balances[account] += amount;
        emit Transfer(address(0), account, amount);

        _afterTokenTransfer(address(0), account, amount);
    }

    /**
     * @dev Destroys `amount` tokens from `account`, reducing the
     * total supply.
     *
     * Emits a {Transfer} event with `to` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     * - `account` must have at least `amount` tokens.
     */
    function _burn(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: burn from the zero address");

        _beforeTokenTransfer(account, address(0), amount);

        uint256 accountBalance = _balances[account];
        require(accountBalance >= amount, "ERC20: burn amount exceeds balance");
        unchecked {
            _balances[account] = accountBalance - amount;
        }
        _totalSupply -= amount;

        emit Transfer(account, address(0), amount);

        _afterTokenTransfer(account, address(0), amount);
    }

    /**
     * @dev Sets `amount` as the allowance of `spender` over the `owner` s tokens.
     *
     * This internal function is equivalent to `approve`, and can be used to
     * e.g. set automatic allowances for certain subsystems, etc.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `owner` cannot be the zero address.
     * - `spender` cannot be the zero address.
     */
    function _approve(
        address owner,
        address spender,
        uint256 amount
    ) internal virtual {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    /**
     * @dev Spend `amount` form the allowance of `owner` toward `spender`.
     *
     * Does not update the allowance amount in case of infinite allowance.
     * Revert if not enough allowance is available.
     *
     * Might emit an {Approval} event.
     */
    function _spendAllowance(
        address owner,
        address spender,
        uint256 amount
    ) internal virtual {
        uint256 currentAllowance = allowance(owner, spender);
        if (currentAllowance != type(uint256).max) {
            require(currentAllowance >= amount, "ERC20: insufficient allowance");
            unchecked {
                _approve(owner, spender, currentAllowance - amount);
            }
        }
    }

    /**
     * @dev Hook that is called before any transfer of tokens. This includes
     * minting and burning.
     *
     * Calling conditions:
     *
     * - when `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * will be transferred to `to`.
     * - when `from` is zero, `amount` tokens will be minted for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens will be burned.
     * - `from` and `to` are never both zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _beforeTokenTransfer(
        address from,
        address to,
        uint256 amount
    ) internal virtual {}

    /**
     * @dev Hook that is called after any transfer of tokens. This includes
     * minting and burning.
     *
     * Calling conditions:
     *
     * - when `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * has been transferred to `to`.
     * - when `from` is zero, `amount` tokens have been minted for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens have been burned.
     * - `from` and `to` are never both zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _afterTokenTransfer(
        address from,
        address to,
        uint256 amount
    ) internal virtual {}
}

library SafeERC20 {
    using Address for address;

    function safeTransfer(
        IERC20 token,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(
        IERC20 token,
        address from,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender) + value;
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        unchecked {
            uint256 oldAllowance = token.allowance(address(this), spender);
            require(oldAllowance >= value, "SafeERC20: decreased allowance below zero");
            uint256 newAllowance = oldAllowance - value;
            _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
        }
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) {
            // Return data is optional
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}

library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     *
     * [IMPORTANT]
     * ====
     * You shouldn't rely on `isContract` to protect against flash loan attacks!
     *
     * Preventing calls from contracts is highly discouraged. It breaks composability, breaks support for smart wallets
     * like Gnosis Safe, and does not provide security since it can be circumvented by calling from a contract
     * constructor.
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize/address.code.length, which returns 0
        // for contracts in construction, since the code is only stored at the end
        // of the constructor execution.

        return account.code.length > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        (bool success, ) = recipient.call{value: amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        require(isContract(target), "Address: call to non-contract");

        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        (bool success, bytes memory returndata) = target.delegatecall(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Tool to verifies that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason using the provided one.
     *
     * _Available since v4.3._
     */
    function verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryAdd(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            uint256 c = a + b;
            if (c < a) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the substraction of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function trySub(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b > a) return (false, 0);
            return (true, a - b);
        }
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryMul(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
            // benefit is lost if 'b' is also tested.
            // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
            if (a == 0) return (true, 0);
            uint256 c = a * b;
            if (c / a != b) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the division of two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryDiv(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a / b);
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryMod(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a % b);
        }
    }

    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        return a + b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return a - b;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        return a * b;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator.
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return a % b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {trySub}.
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        unchecked {
            require(b <= a, errorMessage);
            return a - b;
        }
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a / b;
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting with custom message when dividing by zero.
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {tryMod}.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a % b;
        }
    }
}

abstract contract ReentrancyGuard {
    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.

    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    uint256 private _status;

    constructor() {
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and making it call a
     * `private` function that does the actual work.
     */
    modifier nonReentrant() {
        // On the first call to nonReentrant, _notEntered will be true
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;

        _;

        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }
}

abstract contract SphCurveToken is IERC20 {
    function totalSupply() external virtual override view returns (uint256);
    function mint(address _to, uint256 _value) virtual external returns (bool);
    function burnFrom(address _to, uint256 _value) virtual external returns (bool);
}

contract Swap3pool is Ownable, ReentrancyGuard{

    uint128 constant public N_COINS = 3;
    uint256 constant public FEE_DENOMINATOR = 10 ** 10;
    uint256 constant public LENDING_PRECISION = 10 ** 18;
    uint256 constant public PRECISION = 10 ** 18;
    uint256[N_COINS] public PRECISION_MUL = [1, 1000000000000, 1000000000000];
    uint256[N_COINS] public RATES = [1000000000000000000, 1000000000000000000000000000000, 1000000000000000000000000000000];
    uint128 constant public FEE_INDEX = 10 ** 18;
    uint256 constant public MAX_ADMIN_FEE = 10 * 10 ** 9;
    uint256 constant public MAX_FEE = 5 * 10 ** 9;
    uint256 constant public MAX_A = 10 ** 6;
    uint256 constant public MAX_A_CHANGE = 10;
    uint256 constant public ADMIN_ACTIONS_DELAY = 3 * 86400;
    uint256 constant MIN_RAMP_TIME = 86400;
    uint256 constant KILL_DEADLINE_DT = 2 * 30 * 86400;
    address[N_COINS] public coins;
    uint256[N_COINS] public balances;
    uint256 public fee ;
    uint256 public admin_fee;

    SphCurveToken token;

    uint256 public initial_A;
    uint256 public future_A;
    uint256 public initial_A_time;
    uint256 public future_A_time;
    
    uint256 public admin_actions_deadline;
    uint256 public transfer_ownership_deadline;
    uint256 public future_fee;
    uint256 public future_admin_fee;
    address public future_owner;

    bool is_killed;
    uint256 kill_deadline;

    event TokenExchange (address indexed buyer, uint128 sold_id, uint256 tokens_sold, uint128 bought_id, uint256 tokens_bought);
    event AddLiquidity (address indexed provider, uint256[N_COINS] token_amounts, uint256[] fees, uint256 invariant, uint256 token_supply);
    event RemoveLiquidity (address indexed provider, uint256[] token_amounts, uint256[] fees, uint256 token_supply);
    event RemoveLiquidityOne (address indexed provider, uint256 token_amount, uint256 coin_amount);
    event RemoveLiquidityImbalance (address indexed provider, uint256[N_COINS] token_amounts, uint256[] fees, uint256 invariant, uint256 token_supply);
    event CommitNewAdmin (uint256 indexed deadline, address indexed admin);
    event NewAdmin (address indexed admin);
    event CommitNewFee (uint256 indexed deadline, uint256 fee, uint256 admin_fee);
    event NewFee (uint256 fee, uint256 admin_fee);
    event RampA (uint256 old_A, uint256 new_A, uint256 initial_time, uint256 future_time);
    event StopRampA (uint256 A, uint256 t);
    
    constructor (address[N_COINS] memory _coins, address _pool_token, uint256 _initA, uint256 _fee, uint256 _admin_fee) {
        coins = _coins;
        initial_A = _initA;
        future_A = _initA;
        fee = _fee;
        admin_fee = _admin_fee;
        kill_deadline = block.timestamp + KILL_DEADLINE_DT;
        token = SphCurveToken(_pool_token);
    }

    function _A () view internal returns (uint256){
        uint256 t1 = future_A_time;
        uint256 A1 = future_A;
        if (block.timestamp < t1) {
            uint256 A0 = initial_A;
            uint256 t0 = initial_A_time;
            if (A1 > A0) 
                return A0 + (A1 - A0) * (block.timestamp - t0) / (t1 - t0);
            else
                return A0 - (A0 - A1) * (block.timestamp - t0) / (t1 - t0);
        } else {
            return A1;           
        }
    }

    function A() view external returns (uint256) {
        return _A();
    }

    function _xp() view internal returns (uint256[N_COINS] memory result) {
        result = RATES;
        uint i = 0;
        for(i = 0; i < N_COINS; i++) {
            result[i] = result[i] * balances[i] / LENDING_PRECISION; 
        }
        return result;
    }
    
    function _xp_mem(uint256[N_COINS] memory _balances ) view internal returns (uint256[N_COINS] memory result) {
        result = RATES;
        uint i = 0;
        for(i = 0; i < N_COINS; i++) {
            result[i] = result[i] * _balances[i] / PRECISION; 
        }
        return result;
    }
    
    function get_D(uint256[N_COINS] memory xp, uint256 amp) pure internal returns(uint256) {
        uint256 S = 0;
        for (uint8 i = 0; i < N_COINS; i++) {
            S += xp[i];
        }
        if (S == 0) return 0;
        uint256 DPrev = 0;
        uint256 D = S;
        uint256 Ann = amp * N_COINS;
        for (uint16 _i = 0; _i < 255; _i++) {
            uint256 D_P = D;
            for( uint8 _x; _x < N_COINS; _x++ )
                D_P = D_P * D / (xp[_x] * N_COINS);
            DPrev = D;
            D = (Ann * S + D_P * N_COINS) * D / ((Ann - 1) * D + (N_COINS + 1) * D_P);
            if (D > DPrev) {
                if (D - DPrev <= 1)
                    break;
                else
                    if (DPrev - D <= 1)
                        break;         
            }
                
        }
        return D;
    }

    function get_D_mem (uint256[N_COINS] memory _balances, uint256 amp) view internal returns (uint256) {
        return get_D(_xp_mem(_balances), amp);
    }

    function get_virtual_price() view external returns(uint256) {
        uint256 D = get_D(_xp(), _A());
        uint256 token_supply = token.totalSupply();
        return D * PRECISION / token_supply;
    }



    function calc_token_amount(uint256[N_COINS] memory amounts, bool deposit) external view returns (uint256) {
        uint256[N_COINS] memory _balances = balances;
        uint256 amp = _A();
        uint256 D0 = get_D_mem(_balances, amp);
        for (uint8 i = 0; i < N_COINS; i++) {
            if (deposit) 
                _balances[i] += amounts[i];
            else
                _balances[i] -= amounts[i];
        }
        uint256 D1 = get_D_mem(_balances, amp);
        uint256 token_amount = token.totalSupply();
        uint256 diff = 0;
        if (deposit)
            diff = D1 - D0;
        else
            diff = D0 - D1;
        return diff * token_amount / D0;
    }

    function add_liquidity (uint256[N_COINS] memory amounts, uint256 min_mint_amount) external nonReentrant {
        require(is_killed, "pool is dead");
        uint256[] memory fees = new uint256[](N_COINS);
        uint256 _fee = fee * N_COINS / (4 * (N_COINS - 1));
        uint256 _admin_fee = admin_fee;
        uint256 amp = _A();
        uint256 token_supply = token.totalSupply();
        uint256 D0 = 0;
        uint256[N_COINS] memory old_balances = balances;
        if (token_supply > 0)
            D0 = get_D_mem(old_balances, amp);
        uint256[N_COINS] memory new_balances = old_balances;
        for (uint8 i = 0; i < N_COINS; i++) {
            uint256 in_amount = amounts[i];
            if (token_supply == 0) {
                require(in_amount > 0, "initial deposit requires all coins");
            }
            address in_coin = coins[i];
            if (in_amount > 0 ) {
                if (i == FEE_INDEX) {
                    in_amount = ERC20(in_coin).balanceOf(address(this));
                    ERC20(in_coin).transferFrom(msg.sender, address(this), in_amount);
                    in_amount = ERC20(in_coin).balanceOf(address(this)) - in_amount ;
                }
            }
            new_balances[i] = old_balances[i] + in_amount;
        }
        uint256 D1 = get_D_mem(new_balances, amp);
        uint256 D2 = D1;
        if (token_supply > 0 ) {
            for (uint8 i = 0; i < N_COINS; i++) {
                uint256 ideal_balance = D1 * old_balances[i] / D0;
                uint256 difference = 0;
                if (ideal_balance > new_balances[i])
                    difference = ideal_balance - new_balances[i];
                else
                    difference = new_balances[i] - ideal_balance;
                fees[i] = _fee * difference / FEE_DENOMINATOR;
                balances[i] = new_balances[i] - (fees[i] * _admin_fee / FEE_DENOMINATOR);
                new_balances[i] -= fees[i];
            }
            D2 = get_D_mem(new_balances, amp);
        }
        uint256 mint_amount = 0;
        if (token_supply == 0)
            mint_amount = D1;
        else
            mint_amount = token_supply * (D2 - D0) / D0;
        require(mint_amount >= min_mint_amount, "Slippage screwed you");
        token.mint(msg.sender, mint_amount);
        emit AddLiquidity(msg.sender, amounts, fees, D1, token_supply + mint_amount);
    }

    function get_y(uint128 i, uint128 j, uint256 x, uint256[N_COINS] memory xp_) view internal returns(uint256) {
        require( i != j, "same coin");
        require( j >= 0, "j below zero");
        require( j < N_COINS, "j above N_COINS");
        require( i >= 0, "i below zero");
        require( i < N_COINS, "i above N_COINS");
        uint256 amp = _A();
        uint256 D = get_D(xp_, amp);
        uint256 c = D;
        uint256 S_ = 0;
        uint256 Ann = amp * N_COINS;
        uint256 _x = 0;
        for (uint8 _i = 0; i < N_COINS; i++) {
            if (_i == i )
                _x = x;
            else if(_i != j) 
                _x = xp_[_i];
            else continue;
            S_ += _x; 
            c = c * D / (_x * N_COINS);
        }
        c = c * D / (Ann * N_COINS);
        uint256 b = S_ + D / Ann;
        uint256 y_prev = 0;
        uint256 y = D;
        for (uint8 _i = 0; _i < 255; _i++) {
            y_prev = y;
            y = (y*y + c) / (2 * y + b - D);
            if (y > y_prev)
                if (y - y_prev <= 1)
                    break;
            else
                if (y_prev - y <= 1)
                    break;

        }
        return y;
    }

    function get_dy(uint128 i, uint128 j, uint256 dx ) view internal returns(uint256) {
        uint256[N_COINS] memory rates = RATES;
        uint256[N_COINS] memory xp = _xp();
        uint256 x = xp[i] + (dx * rates[i] / PRECISION);
        uint256 y = get_y(i, j, x, xp);
        uint256 dy = (xp[j] - y - 1) * PRECISION / rates[j];
        uint256 _fee = fee * dy / FEE_DENOMINATOR;
        return dy - _fee; 
    }

    function get_dy_underlying(uint128 i, uint128 j, uint256 dx ) view internal returns(uint256) {        
        uint256[N_COINS] memory xp = _xp();
        uint256[N_COINS] memory precisions = PRECISION_MUL;
        uint256 x = xp[i] + dx * precisions[i];
        uint256 y = get_y(i, j, x, xp);
        uint256 dy = (xp[j] - y - 1) / precisions[j];
        uint256 _fee = fee * dy / FEE_DENOMINATOR;
        return dy - _fee; 
    }

    function exchange(uint128 i, uint128 j, uint256 dx, uint256 min_dy) external nonReentrant {
        require(!is_killed, "is killed");
        uint256[N_COINS] memory rates = RATES;
        uint256[N_COINS] memory old_balances = balances;
        uint256[N_COINS] memory xp = _xp_mem(old_balances);

        uint256 dx_w_fee = dx;
        address input_coin = coins[i];
        if (i == FEE_INDEX)
           dx_w_fee = ERC20(input_coin).balanceOf(address(this));

        ERC20(input_coin).transferFrom(msg.sender, address(this), dx);
        if (i == FEE_INDEX)
           dx_w_fee = ERC20(input_coin).balanceOf(address(this)) - dx_w_fee;
        uint256 x = xp[i] + dx_w_fee * rates[i] / PRECISION;
        uint256 y = get_y(i, j, x, xp);
        // -1 just in case there were some rounding errors
        uint256 dy = xp[j] - y - 1;
        uint256 dy_fee = dy * fee / FEE_DENOMINATOR;
        dy = (dy - dy_fee) * PRECISION / rates[j]; 
        require(dy >= min_dy, "Exchange resulted in fewer coins than expected");
        uint256 dy_admin_fee = dy_fee * admin_fee / FEE_DENOMINATOR;
        dy_admin_fee = dy_admin_fee * PRECISION / rates[j];
        balances[i] = old_balances[i] + dx_w_fee;
        balances[j] = old_balances[j] - dy - dy_admin_fee;

        ERC20(coins[j]).transfer(msg.sender, dy);
        // emit TokenExchange(address(msg.sender), i, dx, j, dy);
    }

    function remove_liquidity( uint256 _amount, uint256[N_COINS] memory min_amounts) external nonReentrant {
        uint256 total_supply = token.totalSupply();
        uint256[] memory amounts = new uint256[](N_COINS);
        uint256[] memory fees = new uint256[](N_COINS);
        for (uint8 i = 0; i < N_COINS; i++) {
            uint256 value = balances[i] * _amount / total_supply;
            require(value >= min_amounts[i], "Withdrawal resulted in fewer coins than expected" );
            balances[i] -= value;
            amounts[i] = value;
            ERC20(coins[i]).transfer(msg.sender, value);
        }
        token.burnFrom(msg.sender, _amount);
        emit RemoveLiquidity(msg.sender, amounts, fees, total_supply - _amount);
    }

    function remove_liquidity_imbalance( uint256[N_COINS] memory amounts, uint256 max_burn_amount) external nonReentrant {
        require(!is_killed, "is killed");
        uint256 token_supply = token.totalSupply();
        require(token_supply != 0, "zero total supply");
        uint256 _fee = fee * N_COINS / (4 * (N_COINS -1));
        uint256 _admin_fee = admin_fee;
        uint256[N_COINS] memory old_balances = balances;
        uint256[N_COINS] memory new_balances = old_balances;
        uint256 amp = _A();
        uint256 D0 = get_D_mem (old_balances, amp);
        for (uint8 i = 0; i < N_COINS; i++){
            new_balances[i] -= amounts[i];
        }
        uint256 D1 = get_D_mem (new_balances, amp);
        uint256[] memory fees = new uint256[](N_COINS);
        for (uint8 i = 0; i < N_COINS; i++){
            uint256 ideal_balance = D1 * old_balances[i]/D0;
            uint256 difference = 0;
            if (ideal_balance > new_balances[i])
                difference = ideal_balance - new_balances[i];
            else
                difference = new_balances[i] - ideal_balance;
            fees[i] = _fee * difference / FEE_DENOMINATOR;
            balances[i] = new_balances[i] - (fees[i] * _admin_fee / FEE_DENOMINATOR);
            new_balances[i] -= fees[i];
        }
        uint256 D2 = get_D_mem(new_balances, amp);
        uint256 token_amount = (D0 - D2) * token_supply / D0;
        require(token_amount != 0, "zero tokens burned");
        token_amount += 1;
        require(token_amount <= max_burn_amount, "Slippage screwed you");
        token.burnFrom(msg.sender, token_amount);
        for (uint8 i = 0; i < N_COINS; i++) {
            uint256 amount = amounts[i];
            if (amount != 0) {
                ERC20(coins[i]).transfer(msg.sender, amount);
            }
        }
        // emit RemoveLiquidityImbalance(msg.sender, amounts, fees, D1, token_supply - token_amount);
    }

    function get_y_D(uint256 A_, uint128 i, uint256[N_COINS] memory xp, uint256 D) pure internal returns(uint256) {
        require( i >= 0, "i below zero");
        require(i < N_COINS,  "i above N_COINS");
        uint256 c = D;
        uint256 S_ = 0;
        uint256 Ann = A_ * N_COINS;
        uint256 _x = 0;
        for(uint8 _i = 0;  _i < N_COINS; _i ++) {
            if (_i != i)
                    _x = xp[_i];
                else
                    continue;
                S_ += _x;
                c = c * D / (_x * N_COINS);
        }
        c = c * D / (Ann * N_COINS);
        uint256 b =  S_ + D / Ann;
        uint256 y_prev = 0;
        uint256 y = D;
        for(uint8 _i = 0;  _i < 255; _i ++) {
            y_prev = y;
            y = (y*y + c) / (2 * y + b - D);
            // Equality with the precision of 1
            if (y > y_prev)
                if (y - y_prev <= 1)
                    break;
            else
                if (y_prev - y <= 1)
                    break;
        }
        return y;
    }

    function _calc_withdraw_one_coin(uint256 _token_amount, uint128 i) internal view returns(uint256, uint256) {
        uint256 amp = _A();
        uint256[N_COINS] memory precisions = PRECISION_MUL;
        uint256 _fee = fee * N_COINS / (4 * (N_COINS - 1));
        uint256 total_supply = token.totalSupply();
        uint256[N_COINS] memory xp = _xp();
        uint256 D0 = get_D(xp, amp);
        uint256 D1 = D0 - _token_amount * D0 / total_supply;
        uint256[N_COINS] memory xp_reduced = xp;
        uint256 new_y = get_y_D(amp, i, xp, D1);
        uint256 dy_0 = (xp[i] - new_y) / precisions[i];
        for(uint8 j = 0;  j < N_COINS; j ++) {
            uint256 dx_expected = 0;
            if (j == i)
                dx_expected = xp[j] * D1 / D0 - new_y;
            else
                dx_expected = xp[j] - xp[j] * D1 / D0;
            xp_reduced[j] -= _fee * dx_expected / FEE_DENOMINATOR;    
        }
        uint256 dy = xp_reduced[i] - get_y_D(amp, i, xp_reduced, D1);
        dy = (dy - 1) / precisions[i];
        return (dy, dy_0 - dy);
    }
    

    function calc_withdraw_one_coin(uint256 _token_amount, uint128 i ) external view returns (uint256){
        (uint256 dy, ) = _calc_withdraw_one_coin(_token_amount, i);
        return dy;
    }

    function remove_liquidity_one_coin(uint256 _token_amount, uint128 i, uint256 min_amount) external nonReentrant {
        require(!is_killed, "dev is killed");
        uint256 dy = 0;
        uint256 dy_fee = 0;
        (dy, dy_fee) = _calc_withdraw_one_coin(_token_amount, i);
        require(dy >= min_amount, "Not enough coins removed");
        balances[i] -= (dy + dy_fee * admin_fee / FEE_DENOMINATOR);
        // dev: insufficient funds
        token.burnFrom(msg.sender, _token_amount);
        ERC20(coins[i]).transfer(msg.sender, dy);
        emit RemoveLiquidityOne(msg.sender, _token_amount, dy);
    }

    function ramp_A(uint256 _future_A, uint256 _future_time) external onlyOwner{
        require(block.timestamp >= initial_A_time + MIN_RAMP_TIME, "time is over");
        require(_future_time >= block.timestamp + MIN_RAMP_TIME, "insufficient time");
        uint256 _initial_A = _A();
        require(_future_A > 0 && _future_A < MAX_A, "A is wrong");
        require(((_future_A >= _initial_A) && (_future_A <= _initial_A * MAX_A_CHANGE) ||
            (_future_A < _initial_A) && (_future_A * MAX_A_CHANGE >= _initial_A)), "wrong param");
        initial_A = _initial_A;
        future_A = _future_A;
        initial_A_time = block.timestamp;
        future_A_time = _future_time;
        emit RampA(_initial_A, _future_A, block.timestamp, _future_time);
    }

    function stop_ramp_A() external onlyOwner{
        uint256 current_A = _A();
        initial_A = current_A;
        future_A = current_A;
        initial_A_time = block.timestamp;
        future_A_time = block.timestamp;
        emit StopRampA(current_A, block.timestamp);
    }

    function commit_new_fee(uint256 new_fee, uint256 new_admin_fee) external onlyOwner{
        require(admin_actions_deadline == 0, "active action");
        require(new_fee <= MAX_FEE,  "fee exceeds maximum");
        require(new_admin_fee <= MAX_ADMIN_FEE, "admin fee exceeds maximum");
        uint256 _deadline =  block.timestamp + ADMIN_ACTIONS_DELAY;
        admin_actions_deadline = _deadline;
        future_fee = new_fee;
        future_admin_fee = new_admin_fee;
        
        emit CommitNewFee(_deadline, new_fee, new_admin_fee);
    }
    
    function revert_new_parameters() external onlyOwner{
        admin_actions_deadline = 0;
    }
    
    function commit_transfer_ownership(address _owner) external onlyOwner {
        require(transfer_ownership_deadline == 0, "# dev: active transfer");
        uint256 _deadline = block.timestamp + ADMIN_ACTIONS_DELAY;
        transfer_ownership_deadline = _deadline;
        future_owner = _owner;
        emit CommitNewAdmin(_deadline, _owner);
    }

    function apply_transfer_ownership() external onlyOwner {
        require(block.timestamp >= transfer_ownership_deadline, "insufficient time");
        require(transfer_ownership_deadline != 0, "# dev: no active transfer");
        transfer_ownership_deadline = 0;
        transferOwnership(future_owner);
        emit NewAdmin(future_owner);
    }
    
    function revert_transfer_ownership() external onlyOwner {
        transfer_ownership_deadline = 0;
    }
    
    function admin_balances(uint256 i) view external returns(uint256) {
        return ERC20(coins[i]).balanceOf(address(this)) - balances[i];
    }

    function withdraw_admin_fees() external onlyOwner{
        for (uint8 i = 0; i < N_COINS; i++ ) {
            address c = coins[i];
            uint256 value = ERC20(c).balanceOf(address(this)) - balances[i];
            if (value > 0) {
                ERC20(c).transfer(msg.sender, value);
            }
        }
    }

    function donate_admin_fees() external onlyOwner {
        for (uint8 i = 0; i < N_COINS; i++ ) {
            balances[i] = ERC20(coins[i]).balanceOf(address(this));
        }
    }

    function kill_me() external onlyOwner {
        require(kill_deadline > block.timestamp, "# dev: deadline has passed");
        is_killed = true;
    }

    function unkill_me() external onlyOwner {
        is_killed = false;
    }
}