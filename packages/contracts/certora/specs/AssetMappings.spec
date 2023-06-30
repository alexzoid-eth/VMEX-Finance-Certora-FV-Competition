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
* @notice `approvedAssetsHead` and `approvedAssetsTail` previous values
**/

ghost approvedAssetsHeadOld() returns address {
    init_state axiom approvedAssetsHeadOld() == 0;
}

ghost approvedAssetsTailOld() returns address {
    init_state axiom approvedAssetsTailOld() == 0;
}

ghost approvedAssetsHeadTouched() returns bool {
    init_state axiom approvedAssetsHeadTouched() == false;
}

hook Sstore approvedAssetsHead address val (address val_old) STORAGE {
    require approvedAssetsHeadOld() == val_old;
    require approvedAssetsHeadTouched() == true;
}

hook Sstore approvedAssetsTail address val (address val_old) STORAGE {
    require approvedAssetsTailOld() == val_old;
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
* Unit test: `initialize()` could be called once
* @dev `approvedAssetsHead` is set to zero here
**/
invariant initializeCalledOnce() approvedAssetsHeadTouched() == false
    filtered { f -> f.selector == sig:initialize(address).selector }
