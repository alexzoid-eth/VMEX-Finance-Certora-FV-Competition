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
}

///////////////// DEFINITIONS //////////////////////

// `PercentageMath.PERCENTAGE_FACTOR`
definition PERCENTAGE_FACTOR() returns uint64 = 10^18;

// `view` functions
definition VIEW_FUNCTIONS(method f) returns bool = f.isView;

// `initialize()` function
definition INITIALIZE_FUNCTION(method f) returns bool 
    = f.selector == sig:initialize(address).selector;

definition EXCLUDE_FUNCTIONS(method f) returns bool 
    = !VIEW_FUNCTIONS(f) && !INITIALIZE_FUNCTION(f); 

// `onlyGlobalAdmin` functions
definition GLOBAL_ADMIN_FUNCTIONS(method f) returns bool
    = f.selector == sig:setVMEXReserveFactor(address, uint256).selector
    && f.selector == sig:setBorrowingEnabled(address, bool).selector
    ;

////////////////// FUNCTIONS //////////////////////

/**
* @notice Getter for assetMappings[asset].exists
**/

ghost mapping (address => bool) assetExists {
    init_state axiom forall address asset. assetExists[asset] == false;
}

hook Sstore assetMappings[KEY address asset].(offset 66) bool val STORAGE {
    // Assuming `asset` is not zero because of `Address.isContract(currentAssetAddress)` check
    require asset != 0;
    // Save `assetMappings[asset].exists` value
    assetExists[asset] = val;
}

/**
* @notice Getter for assetMappings[asset].liquidationThreshold
**/

ghost mapping (address => uint64) assetLiqThreshold {
    init_state axiom forall address asset. assetLiqThreshold[asset] == 0;
}

hook Sstore assetMappings[KEY address asset].liquidationThreshold uint64 val STORAGE {
    assetLiqThreshold[asset] = val;
}

/**
* @notice Getter for assetMappings[asset].liquidationBonus
**/

ghost mapping (address => uint64) assetLiqBonus {
    init_state axiom forall address asset. assetLiqBonus[asset] == 0;
}

hook Sstore assetMappings[KEY address asset].liquidationBonus uint64 val STORAGE {
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
* @notice `approvedAssetsHead` and `approvedAssetsTail` values
**/

ghost address assetsHeadOld {
    init_state axiom assetsHeadOld == 0;
}

hook Sstore approvedAssetsHead address val (address val_old) STORAGE {
    havoc assetsHeadOld assuming assetsHeadOld@old == 0 && val == 0
        ? assetsHeadOld@old == assetsHeadOld@new : assetsHeadOld@new == val_old;
}

ghost address assetsTailOld {
    init_state axiom assetsTailOld == 0;
}

hook Sstore approvedAssetsTail address val (address val_old) STORAGE {
    havoc assetsTailOld assuming assetsTailOld@old == 0 && val == 0
        ? assetsTailOld@old == assetsTailOld@new : assetsTailOld@new == val_old;
}

///////////////// PROPERTIES ///////////////////////

/**
* @notice Prove bug1.patch
* Hight level: only global admin can add a new asset
**/

rule onlyGlobalAdminCanAddAsset(method f, env e, calldataarg args, address asset) 
    filtered { f -> !VIEW_FUNCTIONS(f) }
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
    filtered { f -> !VIEW_FUNCTIONS(f) }

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
* Variable transition: list's head could be changed only once
**/
invariant listSetHeadOnlyOnce() assetsHeadOld == 0
    filtered { f -> EXCLUDE_FUNCTIONS(f) } 

/**
* @notice Prove bug5.patch
* Valid state: list's head or tail could not be uninitialized 
**/
invariant listUninitializable(env e) approvedAssetsHead(e) == 0 || approvedAssetsTail(e) == 0 
    => approvedAssetsHead(e) == 0 && approvedAssetsTail(e) == 0 && assetsTailOld == 0
    filtered { f -> EXCLUDE_FUNCTIONS(f) } 

/**
* @notice Prove bug6.patch
* High level: only global admin can execute administrative functions
**/
