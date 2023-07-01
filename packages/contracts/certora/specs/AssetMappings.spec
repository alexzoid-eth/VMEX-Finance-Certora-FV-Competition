import "./methods/erc20Methods.spec";

/////////////////// METHODS ////////////////////////

methods {
    // getters
    function assetMappings(address) internal;
    function approvedAssetsHead() internal returns(address);
    function approvedAssetsTail() internal returns(address);

    // VersionedInitializable
    function _VersionedInitializable.initializing() internal;

    // addressesProvider functions
    function _.getGlobalAdmin() external => ALWAYS(333);
    function _.getLendingPoolConfigurator() external => CONSTANT; 
    function _.getLendingPool() external => CONSTANT;

    // ILendingPoolConfigurator functions
    function _.totalTranches() external => NONDET;

    // Lending Pool functions
    function _.getReserveData(address,uint64) external => DISPATCHER(true);

    // Assume that passed addresses are contracts
    function _.isContract(address) internal => ALWAYS(true); 
}

///////////////// DEFINITIONS //////////////////////

definition PERCENTAGE_FACTOR() returns uint64 = 10^18;

////////////////// FUNCTIONS //////////////////////

/**
* @notice Getter for assetMappings[asset].exists
**/

ghost mapping (address => bool) assetExists {
    init_state axiom forall address asset. assetExists[asset] == false;
}

hook Sstore assetMappings[KEY address asset].(offset 66) bool val (bool _old) STORAGE {
    assetExists[asset] = val;
}

/**
* @notice Getter for assetMappings[asset].liquidationThreshold
**/

ghost mapping (address => uint64) assetLiqThreshold {
    init_state axiom forall address asset. assetLiqThreshold[asset] == 0;
}

hook Sstore assetMappings[KEY address asset].liquidationThreshold uint64 val (uint64 _old) STORAGE {
    assetLiqThreshold[asset] = val;
}

/**
* @notice Getter for assetMappings[asset].liquidationBonus
**/

ghost mapping (address => uint64) assetLiqBonus {
    init_state axiom forall address asset. assetLiqBonus[asset] == 0;
}

hook Sstore assetMappings[KEY address asset].liquidationBonus uint64 val (uint64 _old) STORAGE {
    assetLiqBonus[asset] = val;
}

/**
* @notice `VersionedInitializable.initializing` always `false`
* @dev Assuming that `initializing` initially is `false` because it chnaged only inside 
* a `initialize()` function
**/

hook Sload bool val initializing STORAGE {
    require val == false;
}

/**
* @notice Assume that initial values of `approvedAssetsHead` and `approvedAssetsTail` are zeros
**/

ghost bool approvedAssetsHeadFirstRead {
    init_state axiom approvedAssetsHeadFirstRead == true;
}

hook Sload address val approvedAssetsHead STORAGE {
    if(approvedAssetsHeadFirstRead) {
        approvedAssetsHeadFirstRead = false;
        require val == 0;
    } 
}

ghost bool approvedAssetsTailFirstRead {
    init_state axiom approvedAssetsTailFirstRead == true;
}

hook Sload address val approvedAssetsTail STORAGE {
    if(approvedAssetsTailFirstRead) {
        approvedAssetsTailFirstRead = false;
        require val == 0;
    } 
}

/**
* @notice Save `approvedAssetsHead` and `approvedAssetsTail` previous values
**/

ghost bool approvedAssetsHeadFirstWrite {
    init_state axiom approvedAssetsHeadFirstWrite == true;
}

ghost address approvedAssetsHeadOld {
    init_state axiom approvedAssetsHeadOld == 0;
}

hook Sstore approvedAssetsHead address val (address val_old) STORAGE {
    if(approvedAssetsHeadFirstWrite) {
        approvedAssetsHeadFirstWrite = false;
    } else {
        // could not be zero because isContract() check
        require val != 0;
        approvedAssetsHeadOld = val_old;
    }
}

ghost bool approvedAssetsTailFirstWrite {
    init_state axiom approvedAssetsTailFirstWrite == true;
}

ghost address approvedAssetsTailOld {
    init_state axiom approvedAssetsTailOld == 0;
}

hook Sstore approvedAssetsTail address val (address val_old) STORAGE {
    if(approvedAssetsTailFirstWrite) {
        approvedAssetsTailFirstWrite = false;
    } else {
        // could not be zero because isContract() check
        require val != 0;
        approvedAssetsTailOld = val_old;
    }
}

///////////////// PROPERTIES ///////////////////////

/**
* @notice Prove bug1.patch
* Hight level: only global admin can add a new asset
**/
rule onlyGlobalAdminCanAddAsset(method f, env e, calldataarg args, address asset) 
    filtered { f -> !f.isView }
{
    bool before = assetExists[asset];

    f(e, args);

    bool after = assetExists[asset];

    // `333` set as owner in methods block summary for `getGlobalAdmin()`
    assert before != after => e.msg.sender == 333; 
}

/**
* @notice Prove bug2.patch
* Valid state: `liquidationBonus` > `PercentageMath.PERCENTAGE_FACTOR`
* @dev if `liquidationThreshold` is zero, then disabled as collateral
**/
invariant reasonableLiquidationBonus(address asset) 
    assetExists[asset] && assetLiqThreshold[asset] != 0 
        => assetLiqBonus[asset] > PERCENTAGE_FACTOR()
    filtered { f -> !f.isView }

/**
* @notice Prove bug3.patch
* Unit test: initialization could be called once
**/
rule initializeCalledOnce() {

    env e1;
    address provider1;
    initialize(e1, provider1);

    env e2;
    address provider2;
    initialize@withrevert(e2, provider2);

    // Second call of `initialize()` always reverts
    assert lastReverted;
}

/**
* @notice Prove bug4.patch
* Variable transition: `approvedAssetsHead` and `approvedAssetsTail`
**/

invariant approvedAssetsHeadTransition(env e) 
    // Head set to zero only once in `initialize()` alongside with a tail
    (approvedAssetsHead(e) == 0 => approvedAssetsTailOld == 0 && approvedAssetsTail(e) == 0) 
    // Head should set to non-zero once in `addAssetMapping()` function
    && (approvedAssetsHeadOld == 0)
    // First element in the list should point to head
    && (approvedAssetsTailOld == 0 && approvedAssetsTail(e) != 0 => approvedAssetsTail(e) == approvedAssetsHead(e))
    // Could not uninitialize a list
    && (approvedAssetsTailOld != 0 => approvedAssetsTail(e) != 0)
    // Second and more element in the list could not point to the head
    // && (approvedAssetsTailOld != 0 => approvedAssetsTail(e) != approvedAssetsHead(e))
        filtered { f -> !f.isView }
    {
        preserved initialize(address provider) with (env e2) {
            require approvedAssetsHead(e2) == 0;
            require approvedAssetsTail(e2) == 0;
        }
    }
